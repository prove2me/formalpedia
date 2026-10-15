-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4984
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:21:57.535674+00:00
-- url     : https://prove2.me/submissions/f33df817-d5bb-452b-a8e7-b223b34033eb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 896223021 ≤ n < 896402877 has `n! + 1` a square.
For every such `n` a prime `p > n + 1` (from a per-sub-range list, each prime certified by a
gcd against a product of all primes below its square root) with `j = p - 1 - n`,
`Q = (-1)^j j! mod p` and `N = Q (Q - 1) mod p` has `N ^ ((p - 1) / 2) ≡ -1 (mod p)`; by Wilson
`Q^2 (n! + 1) ≡ N`, so `n! + 1` is not a square mod `p`. Checked by the kernel
(`decide +kernel`) through the frame `BRFrame`. -/

set_option autoImplicit false
set_option linter.all false
set_option Elab.async false

namespace BRFrame

/-! ## 1. The criterion (Wilson + Euler)

For a prime `p = n + j + 1`, Wilson's theorem gives `n! * Q = -1` in `ZMod p` with
`Q = (-1) ^ j * j!`. If `n! + 1 = m ^ 2` then `Q * (Q - 1) = (Q * m) ^ 2` is a square, so its
`(p - 1) / 2`-th power is `0` or `1`, never `-1`. -/

theorem fact_split (p : ℕ) : ∀ j n : ℕ, n + j + 1 = p →
    (((p - 1).factorial : ℕ) : ZMod p) =
      ((n.factorial : ℕ) : ZMod p) * ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) := by
  intro j
  induction j with
  | zero =>
    intro n h
    have e : p - 1 = n := by omega
    rw [e]
    simp
  | succ j ih =>
    intro n h
    rw [ih (n + 1) (by omega), Nat.factorial_succ n, Nat.factorial_succ j]
    have h0 : ((n + 1 + (j + 1) : ℕ) : ZMod p) = 0 := by
      rw [show n + 1 + (j + 1) = p by omega]
      exact ZMod.natCast_self p
    push_cast at h0 ⊢
    linear_combination ((-1) ^ j * ((j.factorial : ℕ) : ZMod p) * ((n.factorial : ℕ) : ZMod p)) * h0

theorem crit (p n j m : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hj : n + j + 1 = p) (Q N : ℕ)
    (hQ : (Q : ZMod p) = (-1) ^ j * ((j.factorial : ℕ) : ZMod p))
    (hN : (N : ZMod p) = (Q : ZMod p) * ((Q : ZMod p) - 1))
    (he : (N : ZMod p) ^ ((p - 1) / 2) = -1) : Nat.factorial n + 1 ≠ m ^ 2 := by
  intro hm
  haveI := Fact.mk hp
  have hw : ((n.factorial : ℕ) : ZMod p) * (Q : ZMod p) = -1 := by
    rw [hQ, ← fact_split p j n hj]
    exact @ZMod.wilsons_lemma p _
  have hm' : ((n.factorial : ℕ) : ZMod p) + 1 = (m : ZMod p) ^ 2 := by
    have := congrArg (fun x : ℕ => (x : ZMod p)) hm
    push_cast at this
    exact this
  have hsq : (N : ZMod p) = ((Q : ZMod p) * (m : ZMod p)) ^ 2 := by
    rw [hN, mul_pow, ← hm']
    linear_combination (-(Q : ZMod p)) * hw
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have h2e : 2 * ((p - 1) / 2) = p - 1 := by omega
  rw [hsq, ← pow_mul, h2e] at he
  by_cases hx : (Q : ZMod p) * (m : ZMod p) = 0
  · rw [hx, zero_pow (by omega)] at he
    have h1 : (1 : ZMod p) = 0 := by linear_combination he
    exact one_ne_zero h1
  · rw [ZMod.pow_card_sub_one_eq_one hx] at he
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination he
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).1 h2
    have := Nat.le_of_dvd (by norm_num) hd
    omega

/-! ## 2. Modular powering: four windows (8, 7, 7, 7 bits; fast for `e < 2 ^ 29`; exact for all `e`) -/

def w7 (p a e : ℕ) : ℕ :=
  Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow
    (Nat.mod (Nat.pow a (Nat.shiftRight e 21)) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 14) 127))) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 7) 127))) p) 128)
    (Nat.pow a (Nat.land e 127))) p

theorem win (p a x u d : ℕ) (hx : x ≡ a ^ u [MOD p]) :
    Nat.mod (Nat.mul (Nat.pow x 128) (Nat.pow a d)) p ≡ a ^ (u * 128 + d) [MOD p] := by
  refine (Nat.mod_modEq (x ^ 128 * a ^ d) p).trans ?_
  rw [pow_add, pow_mul]
  exact (hx.pow 128).mul_right _

theorem sh_div (e k : ℕ) : Nat.shiftRight e k = e / 2 ^ k := by
  show e >>> k = e / 2 ^ k
  rw [Nat.shiftRight_eq_div_pow]

theorem w7_spec (p a e : ℕ) : w7 p a e ≡ a ^ e [MOD p] := by
  have d14 : Nat.land (Nat.shiftRight e 14) 127 = e / 2 ^ 14 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d7 : Nat.land (Nat.shiftRight e 7) 127 = e / 2 ^ 7 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d0 : Nat.land e 127 = e % 2 ^ 7 := Nat.and_two_pow_sub_one_eq_mod _ 7
  unfold w7
  rw [d14, d7, d0, sh_div e 21]
  have h0 : Nat.mod (Nat.pow a (e / 2 ^ 21)) p ≡ a ^ (e / 2 ^ 21) [MOD p] := Nat.mod_modEq _ _
  have h1 := win p a _ _ (e / 2 ^ 14 % 2 ^ 7) h0
  have h2 := win p a _ _ (e / 2 ^ 7 % 2 ^ 7) h1
  have h3 := win p a _ _ (e % 2 ^ 7) h2
  refine h3.trans ?_
  have ee : ((e / 2 ^ 21 * 128 + e / 2 ^ 14 % 2 ^ 7) * 128 + e / 2 ^ 7 % 2 ^ 7) * 128 + e % 2 ^ 7 = e := by
    norm_num
    omega
  rw [ee]

/-! ## 3. The factorial table

`mkT W k j f acc` appends `f = j!`, `(j+1)!`, ... (`k` entries, `W` bits each) below `acc`, so in
`TB W J = mkT W (J + 1) 0 1 0` the entry `j` sits at bit `W * (J - j)`. Nothing is assumed about it:
`tabOK` checks every entry against a running factorial in the kernel. -/

def mkT (W : ℕ) (k : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ) (fun _ _ acc => acc)
    (fun _ ih j f acc => ih (Nat.add j 1) (Nat.mul f (Nat.add j 1)) (Nat.lor (Nat.shiftLeft acc W) f)) k

def ext (T W M J j : ℕ) : ℕ := Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M

/-- `tabOK T W M J k j f`: entries `j, j+1, ..., j+k-1` equal `f, f*(j+1), ...` -/
def tabOK (T W M J : ℕ) (k : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => true)
    (fun _ ih j f => Nat.beq (ext T W M J j) f && ih (Nat.add j 1) (Nat.mul f (Nat.add j 1))) k

theorem tabOK_sound (T W M J : ℕ) : ∀ k j, tabOK T W M J k j (Nat.factorial j) = true →
    ∀ i, j ≤ i → i < j + k → ext T W M J i = Nat.factorial i := by
  intro k
  induction k with
  | zero => intro j _ i h1 h2; omega
  | succ k ih =>
    intro j h i h1 h2
    have h' : (Nat.beq (ext T W M J j) (Nat.factorial j) &&
        tabOK T W M J k (Nat.add j 1) (Nat.mul (Nat.factorial j) (Nat.add j 1))) = true := h
    rw [Bool.and_eq_true] at h'
    by_cases hij : i = j
    · subst hij
      exact Nat.eq_of_beq_eq_true h'.1
    · have hf : Nat.mul (Nat.factorial j) (Nat.add j 1) = Nat.factorial (j + 1) := by
        show Nat.factorial j * (j + 1) = Nat.factorial (j + 1)
        rw [Nat.factorial_succ, Nat.mul_comm]
      have h2' := h'.2
      rw [hf] at h2'
      exact ih (j + 1) h2' i (by omega) (by omega)

/-! ## 4. Prime pools

`chk6 P T`: `6 ∣ P` and `6t+5`, `6t+7` share a factor with `P` for every `t < T`; then every prime
`q ≤ 6T+1` divides `P`. A number `q < Bd` with `gcd q P = 1` and every prime `r` with `r * r < Bd`
dividing `P` is prime. -/

def chk6 (P : ℕ) (T : ℕ) : Bool :=
  Nat.beq (Nat.mod P 6) 0 &&
  Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T

theorem chk6_rec (P : ℕ) : ∀ T, Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T = true →
    ∀ t, t < T → Nat.gcd (6 * t + 5) P ≠ 1 ∧ Nat.gcd (6 * t + 7) P ≠ 1 := by
  intro T
  induction T with
  | zero => intro _ t ht; omega
  | succ T ih =>
    intro h t ht
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨h5, h7⟩, hr⟩ := h
    by_cases htT : t = T
    · subst htT
      constructor
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 5) P) 1 = true
          rw [hc]; rfl
        rw [this] at h5; exact absurd h5 (by decide)
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 7) P) 1 = true
          rw [hc]; rfl
        rw [this] at h7; exact absurd h7 (by decide)
    · exact ih hr t (by omega)

theorem chk6_sound (P T : ℕ) (h : chk6 P T = true) :
    ∀ q : ℕ, q.Prime → (q ≤ 3 ∨ q ≤ 6 * T + 1) → q ∣ P := by
  unfold chk6 at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h6, hr⟩ := h
  have h6' : P % 6 = 0 := Nat.eq_of_beq_eq_true h6
  have hall := chk6_rec P T hr
  intro q hq hb
  have hq2 := hq.two_le
  have hdvd : ∀ t, (q = 6 * t + 5 ∨ q = 6 * t + 7) → t < T → q ∣ P := by
    intro t ht htT
    rcases Nat.coprime_or_dvd_of_prime hq P with hc | hc
    · rcases ht with ht | ht
      · rw [ht] at hc; exact absurd hc (hall t htT).1
      · rw [ht] at hc; exact absurd hc (hall t htT).2
    · exact hc
  by_cases h23 : q ≤ 3
  · have : q = 2 ∨ q = 3 := by omega
    rcases this with e | e
    · subst e; omega
    · subst e; omega
  · have hb' : q ≤ 6 * T + 1 := by omega
    have hm : q % 6 = 1 ∨ q % 6 = 5 := by
      have h2 : ¬ 2 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 hd
        omega
      have h3 : ¬ 3 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1 hd
        omega
      omega
    rcases hm with hm | hm
    · exact hdvd (q / 6 - 1) (Or.inr (by omega)) (by omega)
    · exact hdvd (q / 6) (Or.inl (by omega)) (by omega)

theorem prime_of_pool (P Bd q : ℕ) (hP : ∀ r : ℕ, r.Prime → r * r < Bd → r ∣ P) (h2 : 2 ≤ q)
    (hq : q < Bd) (hc : Nat.gcd q P = 1) : q.Prime := by
  by_contra hnp
  have hq1 : q ≠ 1 := by omega
  have hmp := Nat.minFac_prime hq1
  have hsq := Nat.minFac_sq_le_self (by omega) hnp
  have hsq' : q.minFac * q.minFac ≤ q := by rw [← pow_two]; exact hsq
  have hdP := hP q.minFac hmp (by omega)
  have hd : q.minFac ∣ Nat.gcd q P := Nat.dvd_gcd (Nat.minFac_dvd q) hdP
  rw [hc] at hd
  have := Nat.le_of_dvd one_pos hd
  have := hmp.two_le
  omega

/-- pools: `6` below `16`, `30030` below `196`, `P3` below `32761`, `P4` below `1024000000` -/
def pOK (P3 P4 p : ℕ) : Bool :=
  Nat.ble 5 p && cond (Nat.blt p 16) (Nat.beq (Nat.gcd p 6) 1)
    (cond (Nat.blt p 196) (Nat.beq (Nat.gcd p 30030) 1)
      (cond (Nat.blt p 32761) (Nat.beq (Nat.gcd p P3) 1)
        (Nat.blt p 1024000000 && Nat.beq (Nat.gcd p P4) 1)))

theorem blt_t {a b : ℕ} (h : a < b) : Nat.blt a b = true := by simpa using h

theorem blt_f {a b : ℕ} (h : ¬ a < b) : Nat.blt a b = false := by
  cases hb : Nat.blt a b
  · rfl
  · exact absurd (by simpa using hb) h

theorem P6_ok : chk6 6 0 = true := by decide +kernel
theorem P30030_ok : chk6 30030 2 = true := by decide +kernel

theorem pOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) (p : ℕ)
    (h : pOK P3 P4 p = true) : p.Prime ∧ 5 ≤ p := by
  unfold pOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h5, h⟩ := h
  have h5' := Nat.le_of_ble_eq_true h5
  refine ⟨?_, h5'⟩
  by_cases c1 : p < 16
  · rw [blt_t c1, cond_true] at h
    exact prime_of_pool 6 16 p (fun r hr hrr => chk6_sound 6 0 P6_ok r hr (by
      left; by_contra hc; have : 4 * 4 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c1 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c1, cond_false] at h
  by_cases c2 : p < 196
  · rw [blt_t c2, cond_true] at h
    exact prime_of_pool 30030 196 p (fun r hr hrr => chk6_sound 30030 2 P30030_ok r hr (by
      right; by_contra hc; have : 14 * 14 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c2 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c2, cond_false] at h
  by_cases c3 : p < 32761
  · rw [blt_t c3, cond_true] at h
    exact prime_of_pool P3 32761 p (fun r hr hrr => chk6_sound P3 30 h3 r hr (by
      right; by_contra hc; have : 182 * 182 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c3 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c3, cond_false, Bool.and_eq_true] at h
  have c4 := Nat.le_of_ble_eq_true h.1
  exact prime_of_pool P4 1024000000 p (fun r hr hrr => chk6_sound P4 5333 h4 r hr (by
      right; by_contra hc; have : 32000 * 32000 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c4 (Nat.eq_of_beq_eq_true h.2)

/-! ## 5. One `n`: the test

`fm`: `j!` from the table for `j ≤ J`, else from entry `J` by the loop `lp` (rare).
`nN = f * (f + s) mod p` with `f ≡ j! (mod p)`, `s = p - 1` (`j` even) or `1` (`j` odd); this is
`Q * (Q - 1)` for `Q = (-1)^j j!`. -/

def lp (p : ℕ) (k : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ acc => acc)
    (fun _ ih i acc => ih (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p)) k

theorem lp_spec (p : ℕ) : ∀ k i acc, acc ≡ Nat.factorial i [MOD p] →
    lp p k i acc ≡ Nat.factorial (i + k) [MOD p] := by
  intro k
  induction k with
  | zero => intro i acc h; exact h
  | succ k ih =>
    intro i acc h
    have e : lp p (k + 1) i acc = lp p k (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p) := rfl
    rw [e]
    have h2 : Nat.mod (Nat.mul acc (Nat.add i 1)) p ≡ Nat.factorial (i + 1) [MOD p] := by
      refine (Nat.mod_modEq (acc * (i + 1)) p).trans ?_
      rw [Nat.factorial_succ, Nat.mul_comm (i + 1)]
      exact h.mul_right _
    have := ih (i + 1) _ h2
    rw [show i + 1 + k = i + (k + 1) by omega] at this
    exact this

def fm (T W M J p j : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
    (ext T W M J j) (Nat.ble j J)

theorem fm_spec (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    fm T W M J p j ≡ Nat.factorial j [MOD p] := by
  unfold fm
  by_cases hj : j ≤ J
  · have hb : Nat.ble j J = true := by rw [Nat.ble_eq]; exact hj
    rw [hb]; dsimp only; rw [hT j hj]
  · have hb : Nat.ble j J = false := by
      cases h : Nat.ble j J
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true h) hj
    rw [hb]; dsimp only
    have h0 : Nat.mod (ext T W M J J) p ≡ Nat.factorial J [MOD p] := by
      rw [hT J le_rfl]; exact Nat.mod_modEq _ _
    have := lp_spec p (Nat.sub j J) J _ h0
    rw [show J + Nat.sub j J = j by show J + (j - J) = j; omega] at this
    exact this

def nN (T W M J p j : ℕ) : ℕ :=
  Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p

theorem cast_nN (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) (hp : 2 ≤ p) :
    ((nN T W M J p j : ℕ) : ZMod p) =
      ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) * (((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) - 1) := by
  have hm : ((fm T W M J p j : ℕ) : ZMod p) = ((j.factorial : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 (fm_spec T W M J p j hT)
  have hl : Nat.land j 1 = j % 2 := Nat.and_one_is_mod j
  unfold nN
  rw [show Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p =
    (fm T W M J p j * (fm T W M J p j + (p - (1 + j % 2 * (p - 2))))) % p by rw [hl]; rfl]
  rw [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_add, hm]
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · rw [h, zero_mul, add_zero, Nat.cast_sub (by omega), ZMod.natCast_self]
    have : Even j := Nat.even_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring
  · rw [h, one_mul, show p - (1 + (p - 2)) = 1 by omega]
    have : Odd j := Nat.odd_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring

theorem good_of (T W M J n p : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (hp : p.Prime) (hp5 : 5 ≤ p) (h1 : Nat.blt (Nat.add n 1) p = true)
    (h3 : Nat.beq (w7 p (nN T W M J p (Nat.sub p (Nat.add n 1))) (Nat.shiftRight p 1)) (Nat.sub p 1) = true)
    (m : ℕ) : Nat.factorial n + 1 ≠ m ^ 2 := by
  have h1' : n + 1 < p := Nat.le_of_ble_eq_true h1
  set j := Nat.sub p (Nat.add n 1) with hj
  have hjv : j = p - (n + 1) := rfl
  have hN := cast_nN T W M J p j hT (by omega)
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with e | e
    · omega
    · exact e
  have hsh : Nat.shiftRight p 1 = (p - 1) / 2 := by
    rw [sh_div]
    omega
  have : NeZero p := ⟨by omega⟩
  have hw := w7_spec p (nN T W M J p j) (Nat.shiftRight p 1)
  rw [Nat.eq_of_beq_eq_true h3, hsh] at hw
  have he : ((nN T W M J p j : ℕ) : ZMod p) ^ ((p - 1) / 2) = -1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 hw
    push_cast at this
    rw [← this]
    show ((p - 1 : ℕ) : ZMod p) = -1
    rw [Nat.cast_sub (by omega), ZMod.natCast_self]
    simp
  exact crit p n j m hp (by omega) (by omega) ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)).val
    (nN T W M J p j) (by rw [ZMod.natCast_zmod_val]) (by rw [ZMod.natCast_zmod_val]; exact hN) he

/-! ## 6. The prime stream

A stream is a head prime `ph` and the packed gaps `Gp` (8 bits each, gap / 2, low first).
`sp i ph Gp` is its `i`-th element. Once `Gp = 0` the stream is constant. `sOK` checks every
element against the pools. -/

def sp (i : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun ph _ => ph)
    (fun _ ih ph Gp => ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8)) i

theorem sp_zero (ph Gp : ℕ) : sp 0 ph Gp = ph := rfl

theorem sp_succ (i ph Gp : ℕ) :
    sp (i + 1) ph Gp = sp i (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := rfl

theorem sp_const : ∀ i ph, sp i ph 0 = ph := by
  intro i
  induction i with
  | zero => intro ph; rfl
  | succ i ih =>
    intro ph
    rw [sp_succ]
    have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
      show ph + 2 * (0 &&& 255) = ph
      simp
    have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
    rw [e1, e2, ih]

def sOK (P3 P4 : ℕ) (f : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => false)
    (fun _ ih ph Gp => pOK P3 P4 ph && (Nat.beq Gp 0 ||
      ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) f

def SP (ph Gp : ℕ) : Prop := ∀ i, (sp i ph Gp).Prime ∧ 5 ≤ sp i ph Gp

theorem sOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) :
    ∀ f ph Gp, sOK P3 P4 f ph Gp = true → SP ph Gp := by
  intro f
  induction f with
  | zero => intro ph Gp h; exact absurd h (by simp [sOK])
  | succ f ih =>
    intro ph Gp h
    have h' : (pOK P3 P4 ph && (Nat.beq Gp 0 ||
      sOK P3 P4 f (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) = true := h
    rw [Bool.and_eq_true, Bool.or_eq_true] at h'
    obtain ⟨hp, hr⟩ := h'
    have hph := pOK_sound P3 P4 h3 h4 ph hp
    intro i
    cases i with
    | zero => exact hph
    | succ i =>
      rw [sp_succ]
      rcases hr with h0 | h1
      · have hG : Gp = 0 := Nat.eq_of_beq_eq_true h0
        subst hG
        have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
          show ph + 2 * (0 &&& 255) = ph
          simp
        have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
        rw [e1, e2, sp_const]
        exact hph
      · exact ih _ _ h1 i

theorem SP_next (ph Gp : ℕ) (h : SP ph Gp) :
    SP (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := by
  intro i
  have := h (i + 1)
  rw [sp_succ] at this
  exact this

/-! ## 7. The walk

State: `n`, the prime stream `(ph, Gp)` (`ph` = the first prime `≥ n + 2`) and the record codes `R`
(low bits first). The code `t` (see `tsel`) selects the prime `sp t ph Gp` for `n`. The fuel is the
number of `n` still to check; at fuel `0` the walk requires `n = nE`. The body is written flat (lets,
`Bool.rec`) for kernel speed; `walk_succ` gives its meaning. -/

def wr (b : Bool) : Bool := b

/-- the record code: 2 bits `c`; `c < 3` gives `t = c`, else `t = 3 + ` the next 6 bits -/
def tsel (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) (Nat.land R 3)
    (Nat.blt (Nat.land R 3) 3)

def rnx (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) (Nat.blt (Nat.land R 3) 3)

def adP (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3))

def adG (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3))

theorem SP_adv (n ph Gp : ℕ) (h : SP ph Gp) : SP (adP n ph Gp) (adG n ph Gp) := by
  unfold adP adG
  cases hb : Nat.blt ph (Nat.add n 3)
  · dsimp only; exact h
  · dsimp only; exact SP_next ph Gp h

noncomputable def walk (T W M J nE : ℕ) (f : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → Bool) (fun n _ _ _ => Nat.beq n nE)
    (fun _ ih n ph Gp R =>
      let c0 := Nat.land R 3
      let b0 := Nat.blt c0 3
      let t := Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) c0 b0
      let p := sp t ph Gp
      let j := Nat.sub p (Nat.add n 1)
      let fj := Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
        (Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M) (Nat.ble j J)
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (ih (Nat.add n 1)
            (Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) b0)))
          (Nat.beq (w7 p (Nat.mod (Nat.mul fj (Nat.add fj (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1)
            (Nat.sub p 2)))))) p) (Nat.shiftRight p 1)) (Nat.sub p 1)))
        (Nat.blt (Nat.add n 1) p)) f

theorem walk_zero (T W M J nE n ph Gp R : ℕ) : walk T W M J nE 0 n ph Gp R = Nat.beq n nE := rfl

theorem walk_succ (T W M J nE f n ph Gp R : ℕ) :
    walk T W M J nE (f + 1) n ph Gp R =
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R)))
          (Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
            (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
            (Nat.sub (sp (tsel R) ph Gp) 1)))
        (Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)) := rfl

/-- `Cov A n`: no `x ∈ [A, n)` has `x! + 1` a square -/
def Cov (A n : ℕ) : Prop := ∀ x, A ≤ x → x < n → ∀ m, Nat.factorial x + 1 ≠ m ^ 2

theorem walk_sound (T W M J nE A : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    ∀ (f n ph Gp R : ℕ), walk T W M J nE f n ph Gp R = true → SP ph Gp → Cov A n → Cov A nE := by
  intro f
  induction f with
  | zero =>
    intro n ph Gp R h _ hC
    rw [walk_zero] at h
    rw [← Nat.eq_of_beq_eq_true h]
    exact hC
  | succ f ih =>
    intro n ph Gp R h hS hC
    rw [walk_succ] at h
    cases h1 : Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)
    · rw [h1] at h; dsimp only at h; exact absurd h (by decide)
    rw [h1] at h; dsimp only at h
    cases h3 : Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
          (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
          (Nat.sub (sp (tsel R) ph Gp) 1)
    · rw [h3] at h; dsimp only at h; exact absurd h (by decide)
    rw [h3] at h; dsimp only at h
    have hw : walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R) = true := h
    refine ih _ _ _ _ hw (SP_adv n ph Gp hS) ?_
    intro x hx1 hx2 m
    by_cases hxn : x < n
    · exact hC x hx1 hxn m
    · have hxe : x = n := by
        have : x < n + 1 := hx2
        omega
      subst hxe
      exact good_of T W M J x _ hT (hS _).1 (hS _).2 h1 h3 m

/-- one sub-range: the prime stream passes the pools and the walk reaches `nE` -/
noncomputable def sub (P3 P4 T W M J nE f n ph Gp fs R : ℕ) : Bool :=
  sOK P3 P4 fs ph Gp && walk T W M J nE f n ph Gp R

theorem sub_sound (P3 P4 T W M J nE A f n ph Gp fs R : ℕ)
    (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true)
    (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (h : sub P3 P4 T W M J nE f n ph Gp fs R = true) (hC : Cov A n) : Cov A nE := by
  unfold sub at h
  rw [Bool.and_eq_true] at h
  exact walk_sound T W M J nE A hT f n ph Gp R h.2 (sOK_sound P3 P4 h3 h4 fs ph Gp h.1) hC

theorem cov_init (A : ℕ) : Cov A A := fun x h1 h2 => absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)

theorem tab_all (T W M J : ℕ) (h : tabOK T W M J (J + 1) 0 1 = true) :
    ∀ i, i ≤ J → ext T W M J i = Nat.factorial i := by
  intro i hi
  exact tabOK_sound T W M J (J + 1) 0 (by simpa using h) i (by omega) (by omega)

/-- assemble a big number from 8192-bit groups, low group first -/
def asm (L : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun a _ ih => Nat.lor a (Nat.shiftLeft ih 8192)) L

end BRFrame

namespace BRData

def TB : ℕ := BRFrame.mkT 1680 256 0 1 0

def MM : ℕ := Nat.sub (Nat.shiftLeft 1 1680) 1

theorem TOK : BRFrame.tabOK TB 1680 MM 255 256 0 1 = true := by decide +kernel

theorem TAB : ∀ i, i ≤ 255 → BRFrame.ext TB 1680 MM 255 i = Nat.factorial i :=
  BRFrame.tab_all TB 1680 MM 255 TOK

/-- the product of the primes up to 181 -/
def P3 : ℕ := 0x30e06b35ee39cf75358315a5c3b9b2bdd2e46e25fd10a14382537a2e71312

/-- the product of the primes up to 32000, in 8192-bit groups -/
def P4 : ℕ := BRFrame.asm [
  0xdf0c850baeddb2128ac9d0fd36dd0ec2f329ef90aca3308ae6b7bcedec1424921497fc345111e60cc412113537268a736f809fc9cefc2bcbe959a57ecf6fcdc7dc216df46f82fa5bf3720c4270cf6fb13e1dcf489d98985e4f734ee9fac8505c106eb7b2acdb6bb26b79b9cd02729d2a2b215b45d1ad39b752020674f4f03993d6c7a96c9df2c43cdd5fcdd4a2a82b5082c3e0eab548cededa2cc10cfb2c34e6f98c290160b64fdf83e7d3438e6077c84a97d92b85d47ac7b128a35167b6e0531f91938128b16ed40b0ea8ed276a4a879f7c745e779c2215fa0572e7a15cae72ee309c077cfb5b3d707818405d883f07d24cd50cd5cefb61fd23ae30b49766951623101af6e194dae9d45749c5926504c31b2e31d16b3a1d8d8f628e30e1137c5dd8637ac50c416fb56e780354d53f83146505e0b75b3fd791dfb6d1cccdf46dd3bacd8c80998bafeec517c181f3bb39e1a7ff75b63960e7e4fbfa4ab3cd18f8673b3d211d62f5e0b3e98f4fcf16bc36e8d7000957b714c4798645de1678e06a21c7cc25ca8fd857afcda85428c1cff131cba807766664cd1ef92b24719ad71a1cacc089d80d1baf2446d3f91edab2290690b4fb849083f3506e79ef43443cfe351c5874753757cdb387af230e22804870783e587646125c93d5e22899c55a15ce29a46aa788de770abed396e6fa35fc451018422e12cda42c1968eb0b94f01da5b9943508ea2fe4ba6651d5d47287366890f2cd535e3789780c5933d6df7e974200cef40380b365f780703c6c344beeb37d043d1ef50ebe5b4b1dc45ace9088eb5474968a0e3305d300ae7a40322ab01357e0cffcf44216a95c444ff2a19bac8a80242e5b642615b266fa3b82e4ebec98b03bd5f61703e03d249324888f88edca090f5ed1243e0a4675f6ae3953d13092b10e09246ac59dc44eba77e164dbfe0f4949818965554093616dc9e4d28ec2f4206870ee44b9ad38fba67c42730b4845e2204f42dcb968564cf342d81da1dbbcb2ad1f705abde27272ca6eb434e635441102a00bb1b3837369200971d33813d146a5507c16e5102a5474ae182d25b8f97aee76e787fb717b4826f264800d01b229407e10b46c31d717cace03707e9813842dde7b9c675f84a599ec1ee76abcbcd5643683142b3af9a5e3ba165a9c8a2d3a8d31de317adde8d146dae44c42d3d79b56996c6c55111ea3f81174d232c5ae8bcf0f11585f68cb32a6395e58907339157f0717bc3ea165222c9ec5363162cf78432b92d4ae5025439cbe242ad10e1460f96a3b9257bb1a9075a34866508f80116c20e59d9ef0bcc790262003e760d1d5a97248b955f6cc61eab2893f5cb8e57f2f293c308165efec92b10c382c1a7f4d7b6b32691a1b62141c02811f4b3027674bebab643b34a70f166e082f1a3489b265b5b1fee25e582b1b076210fe9a,
  0xea98014cae2ac4237f4b4213a735cb3415a1380744196e3371ef349273475b1a9a19eea2b2d83e892b4404ffc9ec8f00c804866f9a9ce72904a292c8101dcfff2039576180f44def879add63b1eccb590677693cae9f49dbf554c6ceba32faf6e84616a64ecc2681a2c895e1090378b6222b56e1bd9cb731fa2064f7b7f066b45169170ba0d08741bd1b0820d77238b47918f994c8aced205746fc0ff5ddd8cf95dd8ef62dd050286266519e45e40e5b2950b8b223c07f101ce162963018ecebd501267eaddb02f56ee6b654257d20d3bf13f73db708520ed0117af6564bb8b0a469856a8cc3e2cae84a242db11e2b060f957bfdc5baa0d4c74a319342609401e3be3e2cf7e1993561e8784857ff0965514a4a9f7a10dcbb1fea1c8cf72786bf6e32594aa1d4908db83d4dfb1c3f8cd9d7a4aa673346618dca07b597d1815974f7e7e86e6d40001b0442574f4404912ee91e38bd7d52aa3eb4ba0fbd5446f731b1baa64f5d05d16a29f33c5cf42cf1f8c2f1d0f96b9a325944e8f02b0169806f2efa153ceefd95679ff923ecc80ceafb98996c16305b5e644d2071399cb7883f6b8a85be82455a9824ef5c3288e149fd62ecee29447798e1f5ea7d3919c51b567ea37288bbefe5b6d943b1edeccad5d4a1284aeddf22256e16e5017fe48dda91d4a4172047b9b6ebdbb35f04afab8a3534b41b758159b035c092cc36876c6db744cdc4558288c5ada4a7c4ca4ef963e05eb3b79ee9f2ba92cca910e4fe4419e33cd12dbd87527274732251e53c0c447842cca8504abf89fb2a0fe66269142a99315d9cfd1cb18ff00a8c0cc9b7d21e6b2d9bba36823cae88b84340801e5c81472d1211357bf791b4b9a83cb8f885a19b4d93e68561301fa92d04eac64892047c44106b572731bc2bc586f7d428463bf12880ddf84b9bcb8b75d18f68f07b2d3a4529f33c265efaa9046e94f310aa9a47d70bf8cca38f0a707a6ce8c2756003dc094a30edb3a17ef3aa4894be8e5d72e22421f097677b90ef6274cb0fe493550d58529e9b9331d11bb641d336d163489ce32364bdf6ed4b327e5a56409b1e276f1ed03f5afc4b1f1eb46f50ea2bd818b6ce560fcf4033323b7f46aab313f4bc2688a9e8ccc1545c5c811b34d48d14308a334a169c2016d94e11129100571fa1dd1c841f5a7bfccbabbc545dba69de8cd04f05f4ad32d476559836d35aca9a7381fa618e0c7e7855e9cd829a0cabdbe9e3c01746e3ae03c2e18f4aa76ef419e3de8bfe4b21500785d9b6964477b8a840ec2cdc45f3227e280e2c5f8f6c6a26c3881003f03b9c89575763154d252dc974ecf290538b9105fcea649307d65a15a817627084c27089384b6073f28023d245a2d78437adc9909abf78ae77d00006f6386c40a33acffa01cdf3667bf58b5a38e6502cd21718fca0d04aeabb5d7635e4b4,
  0x1728b345ae1d105890be726995db87cb8d8643422401f2b9d4fd947140af5fdd89523ad14c14787386bde21dc9610b22e07e931ba28009eb69a71e1cfbc0df11d42c4526b66824c91f442c5636d120007e4d24e3bad931045a7365deef650235aae6a3996d4288b7a45118f689202f6eb7631f39ccfe3ed30df63f6dfa1eaea9abcfc0fbb1889d08158387786d5babb4711aeca73bc3b3e7f510660123273125559e32ae86789b3eea846b65e518bd1b82f86a68b6622dee93c66f28b57bb32c66c334eb0e4e18da04a01e1458f10bfb1b91ada31354048151dc2f7b5e1d35cd094790b3a592983b79c98f2002554d6ac0753e09d4c95de4b0a2dc4af58bc18ba1c404b3cf1f6f5e6353388ba00542736dafb6b3890ed4eb1aa021baa0a1027503756833e069161f3b5df47575a40f2ed8ae5cf84444b7fb646bd1ccb521788b5d39ee4e9492f45b5052f2f8d973d0e798ef2bea1edb9884c1f5ad82ff9f2da775d8c1abba03a5c92ff2c3ccc31a8afb22947e1d06745a05cf02d819e21c1b9eeb81560ef0e999cbf56d4bdb20ee9ae7563555bafaaa67efb0cb235529236a4abc3bbed82dcdf54e45470f179f2174157be3c2cad7e76c7b9fa12a3cedcea2a33cdb5facb5327aead5e2ee441ebfe4a944440623d53d4bdb3e5fa4e7f03a0f3ce18b1b2507fe33b65c49534c5ef0e31577cb2e11c80dd4827e40e09ce1cef2aa8a0b6d04973a6431ea0e721a266ed55b1d51682cf24816a6ef7c28d315fd2c4efd94b46caeb7fa54aa9b6e0b0061cbdd73b551b7a80783e8e600f9a9162f2199788c98a444e28ebb46b57043028fe6c474260640a987cbb7babaf34191506f6a669df1064bb5d3a4522f3706dd1a5615ca291b33cdcc418266d52fda48d187a9bd0c40513361bd5652581c1b2ab80879f9b9c802787745e17a9791fe2d94f2bbbf9e8bd08fed5d2fc21b095a1d18135390d99ffac0dba4a55c77a4ccdef9c1b63ab95770f5296498093b9806389530270a161a78b2759215b5156f0b69960117f858d201d20305aac1d8936d3d8c70293ead432613a327abd5d6b7ec767a694bccfceffb2f505bb0e8cf019e8ba6c25ba9c8a66d8ab729be0c889e5c33b9b003a2777b2ee1a7f1ac50a0b600f9df13abc417f92e56a627fec3318cfec09c3ce8ed11cd38beecc9fe62800f28b554bbb032d54ec3265b9510da2763ffbffa465ebba8541e162029eb43803ead99cc036eac2906e2508acfd0b87815960f33f1250c4c93c84772fcf343e319166a963b9438080e93537495f38e222f30b9388f432d57e061f06db832fc76cd7c2246cdbc725791eedbb0f020e4518bb711c9947fd13da39b34eeaa20b783fda7c7fd6bb5a6bfc5ae0aac9be0260efd746edb56cbad7adf1f59b4ef5590ebf5dc901afac752539f95fa616c0121643f4021b923b,
  0x3c458fee709566842171df4fdf91d1866173d1b733c3309816fb19e69ff4d6644f481709bd1680e21b432a184cfcde4bd4f9b43742cb46b2f3ffd58b5ca10366aa342a9454eedf37ffe61d5b7b01c242438d0aa617697b258e4b6e05f86953963e9b1fb21af5ca4ee94189cb1a9899de56581900c1cb81777ee13638ac508ece1dd9c8bf76060130ee98831d9c1fb6548e12387a276ccb9a1faf40a2ee45223252152bd2949b6b5a7ee3ed5c2879d3abcd1a50c7fafe7d7464053500e063887b01e11ff8f5c27000443e192c9ec6511816a4ef4f6c73c364b4b4e11e4b0f6f2bbe6941fc1002d33c2ea0d80d7c2e37e70d298651f344f10070630a47cd0f686b749590c52fe4333d58a21b210eb744d4e7df8a6d79ce7137a4ba9425114e86d112ff16e899cd2041bb3781489ce56232fa4de91c7ae07bd635bf1f0e554e20163b0a43ed81ab1095811abc702564c76b49adcbc3f5264e74823a695e1847b559021d6babbe9d6989a4eb4d5ff4dff6de9169bddcac984a8bf3d9f653c91cd620b187bdf4e086e2cff33827ccf543d72f80d31c0cfa9b0ec3344ac92fd84b3a3671009f4929fca57466981b49b59806ec5b95115c1d11b21099d94bf85ef0b7bdfdcf30ef86cc521e5a4d267c48da55d3b81706d40dd2e26357d7c865da72c94fd723e3cd37aab7bc2e17c9ae1368ca36ae70f1bb5432a861bc0a79709b81f23807835b1bd97dd958f89f546ca0e74a4d91f2231841b97abae7f63d1dfa52d8d2ecbeb25f730e389347efe4030f78f44b1349e216256ce33d6dcbfd14f9b722f85a32cfcc28fb734de661fad78e2c6065b1a970274a9d4c4b238078e5ef2675620ebe8efc5874a7560f17ae9186eba32895c80e9ab5a9367ceaab065805a41b340cf88a6316b15964530bdee05e98635f268eb9aefe7c81d872c1f52d89472c117d4ead5cabd5874110e0a849337c38acfc60a476b55091afdb9c59ea0200bc2c98cb8fafcdb89a5593e6169294a2d7ad79b4d4bd02449d332f5f101f8a95a668b28a9aa5d4ee6f63265932a22b93e6b08c3cb4ce49b2114839ae8d669db30e78886393dfa8e92535a3232ce2d3b388df674137547d46af3ac76aa08a3962b010a924cecef13be7fc1ee1f857c0c1b148c8350206d93cc1c26bdf2f2083e0632187a7170294c132c8c96452ed414567d17115f3d810463dc5845b0e4b2150676860213d04f9e6b1ee1530faab6ee6281c815dc26cd93cc02c8ed58742168b4bcfe102c25dcf152f8c36ededf5c24b756d43201d572e5ec91e785f50244eac7936a17ebe3e80d537492d9ddbfbc53ed3828000ae06dd1478f12304cfaeaf8b594901c5010f524a109d67422dcf2e00b03dddfcb9ee1060b28f0156ff8707686b109c780e98ff3732bd116d2f70c96ca688419b65cdc52070b6929bfff088a3be5f,
  0x33fb30670ccc9d9161ee291159b243d56af86e6c0d29675ffa2c459c998f0c513dd30d097fc73d45684ecd2c87d420a96eddb72894cfb6b134d8599ab23ca2ce27ef0706a741bda8807b24ea39ef3e5da8774e5f2219c3cbb5573bccfa96c4c5f9b3a11dd2cc735f288dc3a82281b63255a99bc8a5e1c55002df7fda7afac36a1d276383158d287c2a4db62276a331b0b14239ceb7b72b9229337e828e76bd3b13316c1bc98279fb890663222d6f91722909d219a67282cad6eed54326f5e3ea9b7aa50d70e0e9caeec704373d0bf36057bfed71c9e794676fcf07be1e1c0ad66e7790c09f157620dfca3e522db1ac9e18ff6aa4f5ee9f682e9b4a56211d5d51aa3fb19b25926b06393d3c4c47ae87ed8c52d4f19f54ba73ad3fa32cc3da4857c98d0fa5363a46671d532322b398f90422bd732d02d272ed70fbfd0cf7be141b677000847b96d192296c900eda94ea4023fdf00bf2e7a6a9381d832e4e1189a35136b481179ba243c5661a527b140c93d9997eb066a8554bb1b07ac04974f076092dfc159a231f26ff9e7fec54a1a4afc94c723cbc812012373c707e0c81c5783247e3416ec84e3a4aa240527a9339adade0e966d9acc3a1867b2e62b4ab1f43d342508113196ac649cf973d1f98067ebe3662022398d0617ba378bc09596a6403112db6adcca330e099daa38cf9f921c1459c9f97d4be291cb38007fc34a018edb5af08589e98b71ab0e99acfda859889c4a0360109261ff6e40c85327af396767fdac713adfe8caaec684bbcab3fea995f660af05b974c5ba6ebf52d1f8e2b31117cb8faf93a0e939836d3b6af25604d7d5b4f6e144a0485d0c5b5400d4713de63a2736fdbbd20ebb835cc9591b48e10764f4744729730117cf94bd42e70f0f2e86b609f59053a2f94f83d2c855f49bc0563edc62683301a6f1af059fbedbfcf1769c0e1fe4ce07b65de8b71ade682636d0abde0bd94cdde2e1cef86e715d495cddfcdf0e420d7fc6c7b523f6cc2a181df5c50d713f7142e22812e9b36d83d5c41a754fe1e2243d67bcc372a7bc1f7b3cd66155a6d68f2d78535f6ead61180b20a9b7345e87ee56618dcbe69453bfb5db4ed7337f698e5b98735b83d30c6b59ca226c04df477bae76bb50da3ba91f4f324c51588c99d2b8258edfe273d77883d519f5059f50178c73612660f88af6f622035e53bb5cb8421128833d0e2963696885b2672976bc22bdef66a3f79a1eeb5745b266abaae035f56d7da1f92773d588519cfb671cf7f840b8c0eece8eaafaa8cdc7bd8e95db47b86de2f99a5c118b3d336c0cf108f8b13199d11f183c61a0e7fe7d42a609536ad880d22ef9acd6e7a26f94aa1aaf1cddea57ca24edf80e18bb54dc9142b3f9de36aa66add5c83fa9a1b3827de04c3ac9a362fe20443937a0dc21250e8d6183c51a530b2ff77d24,
  0x556d7e991792de0f391465729fa66f7cb4cd30e9aeda0d488686bbeaccac9ce166df07cb523e600a3b36496464fd6e277847eea66bbfbbda8d20d01bd4dac96841254b0ff6c61a90385a3239eaab5887ebdd5a6bcf72691ab6644a094162fe467ce8c72e372883ce54ca28eb67362b5b180ca57cfc027037004145ac514e280b4249af145522f74ad3b0f6eb124e1ba8e994e4ddc0dbdd8cf3f80b42f338206e5313438d9856c4af110573fa215009a4a69f506da8f1fc03695d08ba2ea83ba5b5a7e289910d1ded13d31f5810300e41bc97799d709db61c06dd64bac664891f71d68e45800f73cda9d18f19015497d2048b5193e343f89677fa0fc96fac78929ca8a69f8eb195e7705bb820a2c1d044b922b3b6cd5504ff78a3cbededfb7f1ddaa0ed0869a39884c6f13673cd0cf984a8bfdb025a3bb1af56f4031d5d5b37016db05548dedce76724a7fd52bfdec469e49a2080da2082e93fb0e7b8984d7515b69b3237649436f27c00b00035ef33f41f982ea205940153bfc318e858a5987c952474bca14aac913b1b4ab909216ee44902547a558dee848dd30c0c77b4d2794e7b6b4757e9816025934a0ca36430fe238884e8e64fadbb0d3bcaba4a39af73014f4c5e97e70e5de24c3fd9d2783b3a430158d1a672220b22612a92cf52e32121f8a5aa83d3d87fcfed7751c93bad78d5787354ebe4574d159fff7971b47dc3e0bb5c71f97a51f75996eb949d7565f8e6a18beb27aab1db5b87394d2b1525140e3493920f7b50ea878a9be48bb9e59ffc3746855d8bdf084cf0ce93a39f6f14d5b3a7d76372b40e5870bd37b3449fe5689e]

theorem P3OK : BRFrame.chk6 P3 30 = true := by decide +kernel

theorem P4OK : BRFrame.chk6 P4 5333 = true := by decide +kernel

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 896224271 1250 896223021 896223049
    0x1e03070503121615050405030403060c0f0801030303021303020a090c02011805100c0521060a15080a050403020304170a170705031204051c0e04050a050702061503010b09010303080f0105010509 84
    0x11404085801c0044c11800391103070313a01a00c400d0105081c0f42c00c080d5181c0d401031108039442ca140c4621105c000f8000d5a0740f1488142e591911111a861341c0c500354041c3d84038511183d01240081008001a41c81c40244006890103100020b00c50700c2d1504083d007150781284044416081c002034138400a800022961040300945001240e440312841068030346000d44691a180c009001c0c0001049203812840e41e481100100c40002d807942c2c0d60f204000321844007c030110b0000b00401e0000d6006400e41c2c0020742c1203440f078812a89002c0c0d50b90450400081144031050380394110f44100001c0c4100101d0f0300c006482ca01c400c6d0780c9082903550300d440c3da9102d0441103c0d100703014000010107200081c0500d0900001600308108400c00b0308100130040c98041c90803520031b503c1c120129082c0d040f24849c4e0f621501c2a5001230030300307465182c3d42070b11007005070040030f03410341d00d4840717182840d151650503600175440f03a2103c3c0140e06014858891440050b044141005002c0c0030981031035540200d500d07511 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 896225521 1250 896224271 896224297
    0xb04050a0308070222091a07020307030305041407080d020705040c09090506040f0f0609051014121c111c0933021e0604080910030b1e0307050312 64
    0x111040d202241183c1c0c40c000c9000c00d1780000080c880004002d0780c0114840070310420b10410310080020042c8048101520f1000c01a801030015000083c003a90245400c24003c0c4052a07981506044140c41c1c41c0d0700b50800c08450300031075641e12000b601041101c0c0a414200d0f0b0a00c44548070900c000c002d00e000f03102e100c007400c3c1ca85c0c0101384541c90307580c802400000100010702c05041809109400740c10944684110f05180c0b00c002100403d10b0a0104203488202042d101001e078804108135a075580d0b02040c080a00908030420240411544a0809408140c884c004400c0242564505041401200a0307039108944840d00340702d1307402902700c000c0e1211940f8610000b0072810181d030001d41e00b2404040e08c500070850040b2590340005d41d41c03041c0d880359003441c803856262141154542c0e1080c0c4005000c98400c0c494500302e468035140c039111002003458002507100b20240010858003540c0e001e41c3c18656100000c0036a0300b03080c0b01100290406070020450000291a448058800c2e44080e90394 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 896226771 1250 896225521 896225527
    0x903090d0b1306240f03020603040204020304170d0603030e010f020d080714030103050312180c060928050918031e1207170106090e0f04170c03130b04050a0308 70
    0x15040c2040101e062500300001304185045400c2081a04580e40c0744104005064100061569850320022044d01e50140030982141c4655081c4400707508050001c40d00c0c044040c0f025201641588040c0c0014549a080814941c0c510b080107044c0401101c501d034108200d21130b03000304107500060702c030750f544402e807074485042e50f101c01c005c50b1506c8500001d018041d5000000005010000001c3c01100940c1c04c4a6696615640504900b03201e41d8489582d0a820041c46040a440d240024040711840a040000001c00500b10404002c4540000b08801300c4044c406000350308210301d0003035200c1050b43e102c409443c412080f075513a80c041e1100c0327200001d03072010001c90a00d401c40142c41510042000c406100d050102010f001411640c3c07100b23010805283c0000b403e40d128803025812101d03800c01c0001c84e5101c118175180c900780001c00c00c0d00c00b070b4003481c0c085c0045100345c80180140c0460744017454542d0300c1800605041203440e4850b49001006002c24804c5a64189010b81102d500003901c6076 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 896228021 1250 896226771 896226781
    0xc070c091122050411090f040905070b16060501080618160e25080711070506030a18050d0201020703170108060105010804050f03040b280e041107020d030f080903090d0b 74
    0x380b40320950440d64215003019890b142c4004103401800c44200111a441c41c82e810f56018081100c0d00e81c1006032269002c90000c011101d451070040c1b09483da40c00c0c5d0b500d400c034965110301042c0c890a070711066483d8083d0040040a00510040003c0c000c4904003401c1a4041410320004190300e0b409102211101c281c045024500301c48031400c03e4201c00760350350aa11807100f030050709107401141c0b00c0001c20b40c0c1c1c0b480203c4100c404902c842c240c0384002e04440c29603c2c1c0c00c03442c9000b802c2c2812b98034040c8000e070034003c001c5002013100d000c020700a0342c0003583c0d0b42c10510703000f00561012860805241082070040c4802180460b60506656083c0b0781114196141d040c140d1408171700002c409104c1c000050b012500b5040c250040c8540905241001540100c0100300d200344044161040001404e03e070480d81c0502d056001000701d0701c4030208160822086400058800040050072804600e503003014140700d40e042042944d00841143c061030800b034605c070204402d0790035041c0042908803c0e01c0012 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 896229271 1250 896228021 896228077
    0xf0405030a0f05160302060709080a0b0a0207030302070510020405040605120714191d1509011401120501090204080105011a070f0c0b030717091b0402210c070c0911 72
    0x5018045400340d1100c4c4001905002c0d440e5007082d25500d0014110030004644a000040e121b9001c50f441251140d1a94a84400f00c00a4000e81c40031010150204410408100b0810400c03416065032140180ea0390b25102c2040b04076641030b401035000c0e0340c5180e0003151140f804100c12044510030300741c07004462442800200403600700d103041c69010a807020045a0341d10a80d648101c6401c4011008925031601400d8501003021200c1342640a0607400040c04004400006441509410305000000107001f07100c06041c2c40098000c0759450341c2c046801c011018003401840d00403c0c00c000d13400038180703c8040442c151b208208000e4034140c03911080d00300b042001a962001482141005505c034140985c004020104840c01d081c09850720300082000c21502040700c902e841401c252441283d04440c01380b1029420a05042c001c1c005405404c211031954604080e204140d0007a0b8030340e4030300c11440c2038666141c01b9005009070b10310308481d203880072410b001107420810080311f92928518a0040c24 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 896230521 1250 896229271 896229277
    0x901030902060403030f0f080123011101061202040609020a12022206030b03010b100219050c060a2a1104020903070b0f0a031a03030703050c070506120702060f0405030a0f05 76
    0xc2d08400002030004c141a0b02907896103000049555441c0d0962100c2e0b01181c401c0c20a010b0123200540642000d00c0802d0303004030055a1880c10304002c2000803002003e5801c4070896444010b1402103a501c4030114905449a400944000d140c11810b0600740360000300080c0000814450b031641c000381c100d40c400c0480103071181d8640017000c0c2d064403a03102c65009002c2c4c0000c4204074041e6081244a111500e406107a241c5140c1d40c2d035005091116442c001d4030b411821040b0250f805004591044106031240001070a003480a502e4040701e0b108803181c40146810114403407100f00c0314900210300002d40c28180018110000c98016850303107001c6000905186095005034200e01e40058203640d60090304024240080007a03d04100d90444207490610305202c0c1020307030350706400802c8000d0020340200c001d00002e80c015411600030701c0c2c451000c07070391540c4130103030709880c42d24810b080203c2d60381e04200f11540f04601c41f8842601f41071543e02d25540380280605881403004800791200258814820f03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 896231771 1250 896230521 896230523
    0xf0b0304050f0a150e0a032f0a080c0f030c031e13030606090b0d0203030a03270c090b030316030f05131d0108060c0901080601120f050a062909010309 66
    0x2a51034010140c5801c0a00507213a0031003d0340941032074904103079800c002c2820320300550036480d00c51048088030b04565021003040480e5226401150340e2110303030401000303000c8030f079480390258a6446c050440340c2441d0418185640d14150300410111400030004410354030154549003a081507517800c40c08009403400381c25480d086480340054004144203281e0814000c0f5071181e042080780d03000d80d40600451454248020f500b581c002c0001c00d002d00c0c071a5100201c0802c080396240030a81303040c0300c0122165500315040e60755003038007001484424214465026aa002100103614041034103e5050002c8094034000e4140904a00e010a6190285c000c89680142d00030610741e8890303c03850781c031031784024098070240480840000440c2c03000c0001000c6000d8a4500143c9003410a800011502c80b000204211704203c044403117801c2501042c001c44a824000d1040440e040c84c28400000c110741ea01c0c2e112041d00c4650341c0e042001c000840e203481c00300420a810b620395503410400141d010300031543c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 896233021 1250 896231771 896231773
    0xb0316030f031e08070f0e031f0b2e0c024207060b040b0d1709100c03171902090409021f0315030c0e07020c040f0905070f0f0b0304050f 60
    0x4904210b113944241518401c5c64039840782c5c00a0002c000741140d00c0c1c0c1903914240d401d58420b078646401c0005000c10035080a80c010300209499030800045580200005004498452592000b450051b0244c0c05241c10803518905008280e4040c0c0006031000c0c44040a0141c0500800c0c0a8400c8110882c4803020610a0070342410500102855264030340c0c094a015074009140452135941ca18140c000c079100000000c1110748820002e880302c02205407a120700c1d0000d40c40401600d84180c46039016044401c0243d00c80002c0a012070034040c0000a082d507444107c48212010006000303010100a92070f139446600c0141ca8110020100c2e0003083d40c001d001e507010a840c0b06642a504104080d51703401d0f40103a8003171014090f200400380001c0001d010043c954610b08100344503c1000042640d44211184110b9a003090f050700840c0071146891955084103842d0000c0d41d050010820600009003590005100705601c2e1000744040d10045001d8120a03031000804203080c41820004c010144444c08 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 896234271 1250 896233021 896233067
    0x120609060509030c060a02030606040b0c031c05011503051b070c080703050a030207080c0a0b070201051209011a01080f060405040c0305030f040f270506151201090b0316030f03 77
    0x1104483d40c03a040108100d00e2807040340c0001c1e01c008068001d0301e0280c24081c0c0420f04007400e10252590f143c00001e605041d910041c00440b840c501c204c0403001403003041220001e03555040c45018140e83c24001a0b482c00d1508040c1071025054004a06102640e1810245a107840c56817801c0e1256003ea0fa2084640e48140b038008814480701103126902240301e50201e855003980c4d050704946840ca604003055000f10704200802c582030b4910010443c982c4140f601d030b494078109480c109a1280d060703c4240080e99134a000c030001010070014444040d1003400e140c000b40c644400f0140c0f9551000304098066500c0e5400f2030200700c035600444014545c0002520f0301d428005084d100741c0d41007803003403843c80f51081c840040c03401415008150b405103458140c0751500210701609019001c05403080342c0042c1d2580c038940c3d81c1d48050000d400090b011003000240c40d4034040f9014165864110268400c1e00042881c544480600700841300f229030000700048801c200d03040c1900c0950340e03810705205201d041 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 896235521 1250 896234271 896234281
    0x40b0409060506090105011b170d05100f080a020a150507120c06050606040b1b0f10050405160e04152306030d020d020c010809070f060c0308010503161206090605 71
    0xb900300c82d2040c2d10940300e13090700744e0f0b884004642041500200520b4900ca200e41c010120352034140c3c0300c0a64499603056840c05a20309080402c0340c03030450380035201640c1014140041c1c00440c0c20500145161402001051015000240072150710702c100c0340c031030303003440c40c0300f04101c0c0200140e890381034005400005c031541c04a00940f00e001c400c601141c0251030711000490600c0c1c04400c0c0d0301680d48184c0a1401c02c99440304c40b014154541c600300220b8800d00c04040d04201c000c002c0c1c04429000c3d01c00c003003041d0500b1700c0d200340b4181400d640d03002031003800072081c040d5100035030001ea446074000d200722201021040e00c120007864020490790804929102402404600d0340d00c00f4020901a03007115004001444100d0f115082401102c0050300044119409503200c1c45100342c0214005090340c607010b82d10710907045400c05036480718011804400b071070000d05801692190051606401910704924010b0184400764824007a8894007a800f5110390300388140da42c003001f4200d900c8002005a4280 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 896236771 1250 896235521 896235533
    0x1062c06040e190903050f07140d03060806090c030a1205210114120d140d0606030b01021209011b061d0615040b0f0105030c0c0d0f030b101d040b0409 66
    0x4540c000383c2030084210701c100345036a92081030110b1350180d031840c1c149101e84404045139400942c2c2501d6210101d0f504240d900340a02c0f20a480500380c0d103000850600e081da0041c02c0c00b800030481c89494000c14080e0b102e585011400d14820380d2300c01c0c001c4a58644881040c1c5950241d642d05000220f01608032042102c0c00d0700e243c030306072561401c043c40e40b4500c8900708800d107029013504130a1130704007000800446014900a014030701041903018205500b0f0603940382101c1c0b06920140001740c9482e450034071960103000030003040b582601c0440c0307002248400a05a41c10310105003e5100c5c0d481585001d100c00da81c040580039000448181ca22002c00008940e161015210031001400a10039441c1d2868541700d001211040545802c3c0600108801515250001400f0087c0b1541c10800d94001c0c0c1424000c0096411582d228045440c02d1058028112050600d42038044c941281c00140d2494001c0c1080b001221a06110701e51819100045030180c00030504031604941091514010401 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 896238021 1250 896236771 896236799
    0x9041104080a240c170901091707061506091a090301021803010f020423010c050f01051603450809040e030703140a1e0206190501062c0604 61
    0x5680c07100700215844410b107441156104c0340000e0201d121060200341c0320701c0e200321860f0b1005090000103140c20b4982c4504506271164680a803d03d174002034013800304607892080d03540d80d83c4c00210441e040c030b041400251076017a44d03010306080300e1404440850642c580d00c0840c1e08582001e07009640300d8280c4c0c000f00291300549201c00e80300f03508240d01ca2072951618420b5070216501c1061400c18901150610890081c04085041c10004080c0210000c600104591182011140c000248514010076500400403080303035190100760410b203000c130940250046420600080880b05282c801092440410054070f1101c0005500203240c051814000c000700035200f0a8016101031021400380c000c45501c1c0e1081301002070201c0d940305101c03401005000b002e401d2489490410358604000000080f099207400352401d030069004004101b82903900031380d0380e000303108128400c0c01194100b04010b4540c40d80c0c104590020510210f14650400ca0440118040303000501181e64035920340b142c20f14000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 896239271 1250 896238021 896238053
    0x60703030c091a0d0b06121009111204021e030708030a0207051503041b030203070b030a0f0501081e1005131b060206040f021906031b031109041104080a 67
    0x42d14030600040c401c0c4600ca61100700781600025a10f01000002500b005051158845801c0345082c024103100349854100140100741c4501c12008143c0707002c1a41c0f09032812410740005e1400d0a0000418a07404c0700350b0a500300340d0459030b2101508080511a8100312150a01d507854440c03840001907101011005040d60700803582900c1c505600e541c02e200700e841d100140c90040d407030100009004281c444031a11402030302e0700f4000494598a400007481c00394690070840d80c0000000503c508000f00303201d1301c04e00f499042002e004961518401686840e51043c041e01144404051100341190902402e16481c40d803a00070407003030400e595a0908985e02c140100c034400014650141c21800d1046950100c0705a50300a02160b40d45a030390b8410340b080c1c500200d0304042009a0310a1103020038103071601a01007540c00080303883c5615040809046603001e000145842c00d002010040d0b02c441c11101505402c0d00d010801d42040f002644442c404c07640080402d000b6440390038104040070700240d8801d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 896240521 1250 896239271 896239277
    0x7290105010315290c0a0c2c0106030b0121230c0d09032c041d03120408040509010315060902030123040b060a08160f0f031505060703030c 61
    0x200d80c44500f003190000355001ea0300c905009072404000000b004c06504807030001099402c2d041a9041c1812464414040c60842c0c0c1d500e00b025040c0300e0000005070507000d0a003d2050099101c4046c0843c41c0c01650600a600400d0303110300851140c1e901540b03c1034400c1d0043c0c18100381d094403010300f00d0010003101c3d49104c1104079420700341c0501601d406038a0f00442c5440c2800e49040f03078101c00c1c0303001410042c80c00c501f0700500c030700005a01600030104c8000e0b040145413900d60741a011040000b21144100f0515101c203100000f4590f248000040e00e441c40c88040c4111941e0300d071070409034614010703039201c143e00070800800803007001818440b0483c40c24040c2d0b010311900e42c407807130414142d0009002c0c2503402c508404003041ca05011421607011030501901c0042c0000303498001c00d489610003403195012610441c248a0400c080f030060b0300c090515450702481001e8040c00091902c42c140d0703c034204058907a00c00310441c510b040080b0303000b00b1380100030542d80d48544c0380240150100d40000004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 896241771 1250 896240521 896240531
    0x605010906050303071a06130606020d0221091c0204050c1809130305160c0f0f0f14060d0e100c120903020c1509060a0c050d0203120c072901050103 65
    0x1506001050b00e00646d480307036403a020881d40c03840c4903560140080c00310b035020303610004442c1005494843c00b0041c1040742d025101c490181040079250843c6000d031441440f426045d4095007400203c03c0e01c2c1c440208440c01307180904a040d164107a21710284010358001c0c544070900c800074800500901c032040401e9584844000c8107800c01144540464002c1000103000c088032001074030070802000c0b4080c42102028849000340c0b108030300841146c000401c0320801d40070500500c0f880b0302e16503004110b8502c5901c8040d040c000300d200340101280c403060047c400481e2004a21030150031003034030300340e245007114002d000c0005000301401001d00040d0100d1140414001003403039600807003242c950107400030284100b2a10501200c504c410701c243c5071000044c4500390035540c481d0020a001459640c0308a10300300c0c43e0400c1c500700171000a04105551040007203005480b81d00800a9005402010458075540701d400c040345842d2811100350400d075a56910032441b0b500c0e44850328144c1c0c20aa0701004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 896243021 1250 896241771 896241779
    0xf0318101805040504061b110f0a050309060702030f010f0b0405180a12020114040b0403090e070c020105090d021c0c320307050d0b07140a0c06050a02090d0605010906 73
    0x900c00001c1c0c1030a2079091203240c81484a8141500100d030010f200c0da0300002c0542c802034481101c0510b04243c81d0000329081c0411102540400850900600d41c2d0007818042600c5d550300d80c0c1d28840d511856008140108903a400e564050004c4d83e2181d4101009114507409012060001c20400d4a0300f440350b0320707050100f03501c07846000c0d424000708440001070140395141d4580700e01400100701c1c0c2104540d2521102240d01c040401594001d0b40304224070105810070f4074010b001c010380c03031708200b44120410b010403c18940c0010307054086502070800399a101c081d080807808407030700800046e4025240b0f006c14404540c070580d4400703070b80d401030441050702a150100c90a40c02c000990700364403c600c040002000e000b0013030344510307140c0000b0301b142c5440755920082401d08a1020040d541e070081c50702001161071b00211080c02007440d2034000f500d071100104010708002c0b211000a404983c0e50400100031105a038111650514000c01c0b4000c40d010900d4003c010380750074003a0364995403c00710001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 896244271 1250 896243021 896243027
    0x215030c03190902090a09110303070f02030f010c0804030e04020f1206100f0e1314010602060403020f010b0a03031808030c010e210f13031b0e0603070f15020f031810 73
    0x3c076030039500a19a140786c0e10703100030030405003184440941c4e08040c42080c840c0c403030f0340800040c02c0e090b110b140218001801801058100100c0c0e16010040303034180380c0d06040140d0320080c1c070365019a02d41000b428860a90020134000e006100603050304501c0020143c0e100c4100d105124446c2a088030f400307807650701e0302c44200c5030001d440040c1008030302d030501450143c2c0790180000c04000b441e000c00159403025494440001c0c40c0a03880302c0f01507000901403000703140d414800806c42480c0038000348900300418001c038100410600c0041e08001c0c010408004404038201c83d04000d200704001c032034072400440d200a000300360345514400140314642c4200600384000360400c041c0d00c0300ca14151b0519018100300ea6240c3d12000e0002c003140704441001c40001c003c1111200b03880640c4284c1a8203904018030b4207158400540090320036440500304000005107542540261085080c2000c24201c80c00010f0b07140c01c03414904040c3ca4007011034000c6a000c9000c0c002001000304684000f581c00181d0426 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 896245521 1250 896244271 896244281
    0x120c090708042319051f0618020a0503011a0c0a03080118060e040212030c07060801050906300a05071d1308070816140f0105180a0f0215030c0319 64
    0x400540c10600340d41109940c450300001300c690060055404031541303280d40a4052001c003555822083d5540000d001007201044d801303c651401800440c9440b03208103001d0004d00052082201000103061425400c1941c102a5816030768840708403050351410749009840f048003401800b03001141080b00b501400080c2c0540f03c100d80700921605981c2d04c541e000e112181503810801e84151004001e994100f4201700403c0008004a540d040999410b200410401c1d41d0050056441501300140211581c90610f0300b49542c0325015400114424100c80c2c1030703003001c01500000d40680a541000a0454405200c515494814030300c074442c00c0d5104020515194081034014000c1c241c10b00c20440082c4081000b46242d240300b03460084d03100c16565820f02e0091030b080314070031160403095a000d0f8440d001d018a42c0c024044416110104200450640e900c484a00d00034004403041d484903001e54503006007035110902105a61640c034074080b0500d0304158000d50710031195031503a10741d44034105030314411 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 896246771 1250 896245521 896245583
    0x907200c090c0a11100c090e0c030a0b031f0e010507030c0207030803040510020406020a3e060f12040b060a050604030305030a060b0409060306060f14120c09070804 72
    0x207440140d0300c401c1c82c12069500410482011300c040324a801004e920208201240c54040703000c0400e43c10f04c072400003840d042d03043d803000c1d044081681c140030218071400300b541d0b840000b00800103001c0031b580c1c0c002442e0224041195642008041c01c0001c20362041c4c01040e41e5035000740003807220782c542d84000c504880300301380fa03200140c02000003031000505a800558005000c1d0045611641c00501314108985c8142c2c4030070302507480000050304000d5021117141c50710f80110000304a040390740d2815207c000b20703001900026660f40040751515984d140c141c8041c04021a1a1525089091000041600240c4044d5817003107588000074181e1420004900641d80050031581c01c00d07203181c0e420f45103074002414511409481340004600a14503902500c0101303105031011603074038a58100107040340d0442d00030305910022503200707002400260b05449149501a0f5100725089503541d02d441c100ba00b4210f069a11550100c00d1007515980040002c1c0101e00803c140003039184402c1e0501d41e00c90020503 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 896248021 1250 896246771 896246779
    0x30a021e0405030606061809180d0e1012090507030f021302030402010e010f0318050124080c12070b0c15010e0f0412230a09210f030e0907200c 63
    0x20006807075041500281826a800601c2d850381e0b202c847d40001c0404c0740803694120700400d204000301c84603800304201100c201d16402c03d035600c0a10030b004940350b001d0480c10941480010305184010407a990b100c8881550003500f55401181c4234a4140143c1c40e09180070b0384140340104140328032044074800c0b680500c0d4161a800030280e42c02d00107441104800d40700c08280745d914400d00502d110148540c80c00148104000a10000c0c129260384210365200e0307a90042d104500c84c10311003040d0003e038907054a01d00320707034030f10703180d894001a24648250b6410400840b440400e0b580145680003030859000d40c030301205052941e0301c40300040b560b0740d011218407000b101c52402260205001d03a800203e1a1924580b191074000400701c0f9411020000240c120070203000541c03200346a901c02ca0080c060b003e08035806c0108034850300e40f8500003082400140c072031044a802c070020140102c448001015014202d08050320300120050901c1e156800960031021052041944041000c41e6600c4800b0f4014 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 896249271 1250 896248021 896248033
    0x3041a030f2206050403170a090503030a020d1113180b0f241602180f0705030705040314030706050c090d030e12030301030506011a3408030a021e040503 67
    0x5402c4910a1040c18000e00030b005006600200d0740600855108600035124480c6c0003240322030300c43c62040c00603c0e542201c0c2c500041383c80041c90120450390082502c030780158a81008a0701d000c020300801440101002e0f0004410341d03006c840400d500308985501e428403030f0402c0b0406446003030398042c00b1100c1d40240ba144c56071041d03247c80e000003002550031070381c5d10340718544152000307005900c400810031030301c803d001c806402c41c41e11039002001e4504422a016140c200b10230100b000d81170241501040c880d011000030301c09845142a50021600444905400300c1ca5543c06600c82d88440019611141044002210000c06004135400c6030809454641d034030155031401c6440d10211540540d1040300342e080c001d10302c10b040010b0340c00f850007a400781005501d4079412000440f02268011b0f03a42c80103015941c00c1c1042e0301210008680030119100041240f80f051108010300a04020311468001c01031040707510f441c0d8081d20844506c0381002603d900c500034100e0960003203201d5558554804 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 896250521 1250 896249271 896249281
    0x601152109051002030a090c0803040b0a0c0618200108070e040b010504030606090c02101e0e030d06090c030b010c05060c0f0f0409050402040f021e13030501020c03041a030f 76
    0xa901c11240c40e40124159100c604041c03075041d00b640d006503044c4c0d0303046894180c2c00c000e100d944c002c00c500415402c00114500307894203080d59104d0060140d050140100b002a080034004950401c049440c44a01c00c03103414151490003c0340440c0100720b0f0501070101540e408441e5020b03041d100e020b40c08603100e88008109900804c00a4030300700909604004040c4800400150203001e1003010b0040c003600882c0d03044100302c000b443c0040c4c41c4003c02c140d0381050b045d503900e0205e0f4400c0411058411402081441d0003403203040c40c6110394200402154a8a02e00096184141d0301004240c141580d06004e1100c1840044903000c0c1d103100c000d810b50704244041a034500c2c000005010406843c8156810038003000a1740a07144c100c0d900250b000ca0b201c1c420070003185003621900ca015800c1841c11801e20101500105600d100400d009070003900015202c109695120b405200542e8864029591080c030301d000ca907182d0300107104030310503040101d1404422080d8542960b06c03602004454441d0783d0f445c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 896251771 1250 896250521 896250587
    0x20d090e180f0d0e01080c1c06120c17030715021806071a0f0f0a090303020f041e090912030c090f0801090c08010513060f1d060115 58
    0x103004521445000c003100e07141e080c8288103030200074040801605001807001c0026282c2104090214100a11041001504451034054600311090581052011141c0c072200000810340754200b0350f8406201100c0404001c0c02c4600f030001d40f100c0d003100c2e0a03444140102555280a0142c004181800d00a80d0b0304e400504d503400f501f50402146035221030906008041110b40d40020320a49000e1542c0e0000c410080a442065802c0760403150403209524003411107000781c0c0c42c003800402c402600d403a0403006040c820b4050714200000004100e507910b94454a4107042c0da0810b10700c104049a1010000f1107041c980f00d0508106e402c0700980c6a84910074808900038038017403400d0300910840c0f000c0444c0c4984000c0c26440a40703251000003403004041e09041d00c2612091303001c110300740e0410007003040303011003e220881c03a541d01100110701c02d085080c041e40503002c0900d03240c248194821403800c10300e100090070b60480e94001082c58130801100030031100366002c0c0000400340441e0516480402c04 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 896253021 1250 896251771 896251799
    0x180a0f0b1b1912020106050108100915051c03031103090303010e040503070819110106152f070e07020118020607021f031e1b08041a0405010507030507020d09 69
    0x8150000d8070710a418100703590500d0b101d801c0382030780c1d00310b07002d0310100c44039809201d0312010708000d0914980510b040c40d5603c444124034012080b20548450113031202080107030001014040c01020111080f40c404a0300341c03a42080107090b800a800c040d400d040014259040b03078003402003036000c1c0d8556803d040d000010084060f204440d14403040051801043c4200090814040c0e84500c1d406040c400316002080409030015012991b45040400c21030441224010b54091449047c90b0190308506102d4001c1d0741c1c0410306250811403c0681c440034202c000c01c5210907107503000180e0846443d8508100d00700c841c1d8800304201406200006030248c0340c04005010082c3c401402c1003400030520400d0411000c4000503100400c0c1c40d52403503210302d140035044020300f4124000c100114212514070b9850702410f090094280000100483d090108281c0c0c80340c161480015841e04500b0180b6140f402000c084510700000313803074071020401c1581f001c10200c0b140d00140d50390303610060030034000303c00001c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 896254271 1250 896253021 896253067
    0x41d0c0613030b06130e0102031509091507050403020d063623150f0612030415050702060a050d15120b092404020a15021f020708180a0f0b 61
    0x1025200000517118081c501c1d800d084c8800140e00c9003001c00900001108400c0c4c4240720b000044100001120009481402450441110400c584a480090f038051140f03030000fa4100001c00744000c1845103039006030020060800b12075a00d501155071818100e50034a10001d001440114034101044030410400044d6081282410043c82c203501e88501e420014800b41d4050a031010070070000c80454204141d202c03000382c0b601802030001049454491042d401480d017000418044007001601c80c00603180c1103580548091358404042c0e42c0a00147c009011044a03181888032a100c9595500c095204540209135403d05c4810704e9618904030850003414400c2c02c0c0304030000b203001104410404251154505820545e0303091900501a042c452074202d403500c0011031401220865001401c81403100b200f904411041c0c0800143c40b007c2d100d501c0020340b040002152021640d0003078114000302000803103080344810394950417001108400d01c151310341d07903c0034012415180006c6110504c04 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 896255521 1250 896254271 896254279
    0x2040b070615090e0d0801140609011d0a08030d0b04060609031101030b0303180112060e0c0f13063506040e030d050c12090c030616030b041d0c0613030b06 68
    0x450325180c036035084802c41210000f10340e0201145c0050243c12020250141064044004040c00350b00041103081c40380b4807009042002400d8560099600c03046445c2420300024800c060329540c43d00081d5880d000003601d903019510b40b03003021030301d45081d1003048211222901c03440d0b0464a9501c90602c046004d2041905240e1030702c042c81d03080c1d41c0500c0100b0900746072003c040307802d10b00c1800060080c07152002400d102450200240700b11080e0200c000c0d400050b880c80c1680c1c0d20000d190f500300900924101211102e0420400700c0c690350400f0740019541511080c9852000814200c100c00d14500c550504001c0441404a092418260402c4070000d40c8401140d140c42954044802203800c1218000d8602401040080c0c035941100300068000002d4801003000f00341110009440d194050013031403890780c0c4094000c2880d03009810100340c4c548002c008020a500c180c202440904201405200e03a0048211140841c68110151441241c240b07444424040c02e5070388000c56000068100c40d88 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 896256771 1250 896255521 896255561
    0x8090a0c0603020a0201060902090915061b06010617070e123f0a080a0915150812041212051608072003031204020103181b0902040b0706 60
    0x11802100c600c8009041035070340180c4d185001d010090031101036800c5254007600401860743c0070707500c00c00c0c0700c0d8104808d00b07003511450072800c0010341c0e0303845020034004994008a802ca101424081313186c0741295085d0b226078580665090009480d21804c8a02d0b0000c1500e811481e126400d1404101c5844148034080780c0d03401c0720011054205050342e500c00e4100c011081d84000c40b95554103200c030480514005001e0425800e850013408214004010001a03590380561303000b4050001d802c100c9848a02c0000c00c2751844011641001c13500c2400384105038861800a210f001541104880440d110140821b50130f0b0400d513501040340842030361000401005018410340c0d02c40c1c10303614503003580c82018504e950312214a01144207801003400100b0500d4607210b8080b46460203c12200710540d40203854105940798030050300109002c02940280c0801d03240414204012000391001a54503250001e0313207240d680c007200c0164130403802040c1440c01d05204850024400c1c3d04072025010641d014090 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 896258021 1250 896256771 896256773
    0x7120509061314010c0b0714070212030703020105091c050c0f010204060903030207091e020c0111030a0b03010605040b030c0108100b2b090c1202060903010c02030c1b0a0608090a 78
    0x1260781000d403280b202d082c21030340c0400c180c2e000c0d4443c500f038810382820301e40c0c0b81e1065501c40d001d00180041101090040340000c1840000c006c03402c1710712040c1c0c001c040b03c4420007460f0100d035407504040c004030059841e120201d5101c400c000340100f204c901814000c1c40c0e90103c0da81c2111103070402566410140b003480c00341150300000b070011f0800f500f031a6840340200751440c10020714180e000e910050320b00d481d120f2050703202586070b000c0107490b01e094040075a8603115001c03104d004061481000005c40d90100c140500ea40a03900860308140b401c40081c0105d58580c0100004c41d0004c402c01070307041d84140e503844851b5014204140c4d000364062201d9038915564a1902403075881031081c041c0955000c090203a44000006101001c14400300d002c0203100102d036280704401c0340034080c0c10407110038a01038604640c1c2c1c401c211031580341c015000344201041040046d41c3d0343c01c5600900da080c005e680210680c20390b1542c540c90318540080400302040e1070003c06840e22007025007048800c0c050515450 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 896259271 1250 896258021 896258029
    0x110c1005100b09060c0601140306011508130f12020102130b030609070c21120524040b040915020d1d03090105030a1d0d02010b0a0303050f0d200d051302030307120509 73
    0x6d4001e203140542c00e004c0d205003404041c20701c2c005800500704900e01012490f00c0a40c04684d5560214011010b5990040b00d810400e00041006200600b58800328504c09152541900038006021000359049101a228544c0028a000868440d6000352968000802040c4298406224203000b1004441140c2141038aa80d424482000040102d555214000000912072003225400b4140801b51000041c0042003021040030001840388129245c1820003040c0c1d6456101d5191298002c54502c026000d2019000c081e411100301010018540401e0003620082041c0c01e1400520101c061803500d0620001540c480c2c10103488a104191745612012001d4800300200c102e611105000b40030b0600810b40082c00c3d5200b83d860f86d8003c0111030010400641c020b825a04403914080e500c1751100d0f8441650700003405080340f07000030315070250f9070303100034003002d400501080e01c0304070040c001a5180c20803941082402117000303400da40100181d070081880300c080422640d031540b0b042c40c60862440f0000e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 896260521 1250 896259271 896259283
    0x1110d02130b07060e060f160f120606020709060b0a05040623120402190f030f050c0307030f0302010b01020129041d010222030f12090801110c1005100b09060c 70
    0x80756130ba9517507000041e980c08100070740e80c4d201c00c0aa540d06003e19000081c0c404101c1100003010134014030f0340315110081d000700ca0a003a001108501003000075a10b0000075960a5148550f140c0340b0300c0c1002c0424200d08842c11984091440e4591318a42850603030119940310000d240c1c2c41200c0700b1402c44410064105000b051030102024400006082c10300403c1041d128151095024042c00b00041040c40840c0d07081c0340403030f030300103030420550034260134001e041a40709030709a541802a060080204482c210783d00c50154000d6000308400d5080400580c01c82d00240d5070244181050f070400c4642030300a0500080c201009800880c0948240c0b4082442500d0000308080c5d507500840c040c200c10350442802c2c1c112139002003284d106c0c40d2650b100c40d2050116080041c2900c1d03094580010745500800d5101c0091100b00c008000a246810001d2401c1d04030b01003c130658014203070100e003c460140112401034064141d40d0823001d16003204800141d02180b41d040e0440410b00c103401c1c0b1b5060500c25 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 896261771 1250 896260521 896260523
    0x90910022a03210405030f210609071d03010f15080708120904090f060f06090b0402030c0a0f02150709030309140a0b1608041e060c0b040201030c0c05010c0e0a050301110d02130b07 79
    0x40409000b1000150b040c0d4500e000b80190301503942402045503c90303024840d100c205080c4544109334000c8030003c2405400310555282d50039041001140c0c1d9050040880000c941481c0705a500b940d484519198551105e4a0600e1a03480207000e075036513a00d455806582154820b4440721031200695a4480c16101c4009007055401d9032900100524242e034081c012450b14101d40440c598501079154007068028404402c04008079641e091074007500800a414050140d80b042d40190301e42000300510000260004070001064107500082c128001a07106200020043c41130f4503440c2000c0b0900e072980c00041007410000494008203010880100041020b0030070791300b0070410100c40001e0f09c029030409a0050f400c10814a2500e40420441c018183c0c0083e0f0900c0d002c10050007071141100d0304122104040c08a5107084800c11030380b9082815105100025251025907550300c0c8105800c0760504400720507252410050a82d01501d980e000b842803401007080400c00680743d085840c0301e6000414 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 896263021 1250 896261771 896261797
    0x1508061611061f06020106060203040b03100b0f09040605040b030604240624020a1a0411060c0312101215060b0c070816050f090910022a03210405030f 66
    0x3a003080342a0789600c8409401310b80000e110007454084000d50b00e11651052800030070303001c004201e400048001c440010321402107140d0700e9035520a031100655118007122885030f03242040c000342e05e08150280c1d20040c00000e000d041580c0e40d5880702111400c1b201d0b000d00905050000c4c007480600d071071042c00050281d11030f6008030042c2d00301d83c841d00c21142515010565000700340343c2c00001c40d440c005102013520381a203101c203030b102c51606620f84202d041740c06030310040220350740445070000006080130010481441d0345940301c0615071200103040d8011a0b0780711241d1080000490f005201020400c00202400a9000c0d9541c0c403601e07568005e102c00f60120340086a0400c046402080050f2050518a040c03002ca00c1c40c0000003030ba41125000c185006c0c0344207000149400006000850745458501d000750f42e05c01c2e4449101c003111059495151490008450300d11100c080041540d00e141300810708101c490a00c4885c032214508020000c6840f0300c410085c0540502d604005021100f903071038 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 896264271 1250 896263021 896263051
    0x1a0607110406060e030106082b260a1817071704290a1205040204090c140a0e04150902120109080405010809030a021002090607210201150806161106 65
    0xb104040c02c3d141940d01210392a400f8121011f08614410001c101032541c944031501d604c9401036041d1421052b01010709079160400c04416820038100100ba07209410b00b0a0800c6030340c040a070b41d80038010390007030082e152501c0322150303e0441c10404010a0018060300c245d0360308040c14010b03905960b1144d0460050700c035a01c10031003051541c2c1281c4002a40050001d68101008517000401c194060201c8488840c2c9640100b025500c3d03650000300c0c002d4100422001032500c81c0283c5c1e00d918201031546000d0740001d007000403462035100c03049002d240c4c810000741d400d14a10440b20054540c88400380d9000300c02c8140000781450920419032103511035080e00707803600c0c94480007600034000100301d078180d034100b00040c0355040d40c08078070a46441261030006842d000343c0000b08026002e08503004086a078006400305284050300c28942c1603201e294004d0203040f410303500310002d02807103201702e80c02d0380d00a0011400c03031034500f81a802030b030754180b815412410a42e0f480d00d01d850010307103080c5d10040d9a0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 896265521 1250 896264271 896264297
    0x30b01120302070e01081002030403090806090a0c0603150902070203031219050c03041a070912060e01050a270503120406141b0a0509030c0a15121a060711040606 71
    0x14000b000003030000703001480c6150f1401b452151204800c1180441c00340c0d00000003000c05004022180181c20044101c0d00a498a40e2655a4940c0030349001d80d000e644c81d110000b56180300e0b010b412041c80313002d0a240010703860095044081d4000c1271080b64140070a0081155001412100b070784100f44103000d0741410110240c01d10111000548100c00e6040204100000302d007000d4003041072101c231050040c243d62b44840007200c0a00c680c0e00041d17030481a0344008800c0c4401a04560803062450f0005c00c05a19642107601c00c41c3d1000d0501c0e0210854403d440000072100011010000c0c0501c09030f9240c210051000c0056071400c0b5000c480160b91640004520b00140d4030315544941c0c0b500c1501c00c441e28465082255000340010b12080010001340030320036803000d01010200c140081c08078800720751564141175449840c06030307500001303200c121000c0300548140a40000e1241e48441021004901405e0100c2d5511540c01520034189459014205460f1442030800410550382d60000a42203 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 896266771 1250 896265521 896265523
    0x31703041401092d050607110c09040f081e04030b0108010b0108040b011203120e010b10020a0237090506030d11060105060304151113080f07060810030b01120302 71
    0x1d0741112480e103a01d0030700c0c07070f43c00500c4101d0030b443d801d10214955614031042185450181c441103100411600400007404029500005052081c010f01c80568500d62101c0c4103000c002101114007034403d680141c88007002c5007000004080c141811501c031440c44414084403d0290b000383e10441e107040414004200340c1000384078034119000700b443c00d00b1460801d500d441c2c0b10044180035440501c5041c0404408260141c0b41c141d05031074641c40e0900c040508168010f000b80050340c221800b46491044208400c0d1010501c015040d030300400425801b40904400020b20b510400c50760f01c0b80f1000307440c501141e0300e20081d840c0200030768080404c0500d0203405041c10002040132070014008070440d0581500004502c0038150380c01a00c00780d48a50300c908220540f9604103685900c0030f03103412011803c40081a000f07005203214129400159651405910f6542c1004a001049608a00d20500c0042c3c4201a440e030407403074010364210410380f6a04c511070064000c1e4070010645e00401e240c00201030b0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 896268021 1250 896266771 896266793
    0x7120309141f0201090501090c080d020307171312050a0c05060702130908070f0b01050906060a1718010f0204090b12060f061f0c1b060c020103020d0603170304 70
    0x21028022903440c1c804900e880d103070b550246000700d107440b10070502c1600c02d600511480b0f400c107000340701904003800c14034841e1a05005120050003005900d00b2014000000c4809955110400f043c0025142104040c190042d4144103150056482c0004064050304069107050380624060121b030812441d084a0440c12540a94041e040900c00140940e072002500600c005695030046003c100300c0c039000a952180040c0101b6104031091044140400c114103903040c1c0f10151418019606c1e1581003103c68010080c6032800260340703889070078a00c0b0100440d00c0c1c00604802d802c0d120300390401046402d480c440003140490b80e6021500304100c07000c41c05821184481618210318403880c0c503000365100e071001810050400300c6500410300685403801c01d12211a09180f00700c8244071388000c018528200c210045d1110035400e400c50128012099841d41107903220384690442804560055010750010088070304085ea5030080040420041498858a0620304210755620b103401d140c4030034801 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 896269271 1250 896268021 896268029
    0x9031e051c0606050d05040609080c060a0c02030f070210020a08040b0a0e040207020108130317010b0d0e0601060206011521150905060618041e0c02151303080c040807120309 76
    0x2d0410000b042010380000448002401c415800300f5180d8685c103000b00980300a5a005001c1c100014000441500110b9450701030070680500b8081c500140303500300e90b0b13170041ca402d42c286284104441401881c0030030400620383d8490051b189080003948440409030026401305246500c001100040c25910042949040305c1c1100c045081c900141c000900d010802000c940d98280000700c40380c103041c0541c020002100c0c007000c010301250313140e1000560740d4000d05508141d807800d000c108040750801203901c6e41a501c45900034941d9a1030081119040410307202c1c6c6909101d85100b410000f145003400540a0f03292904003c078814900140d25030098829074803000b40340d480e00040c0a007d130741c3c00b0300302c1c2d0170000c080c0c051104030b11a40c00000c004107207580c51002d5400e06c485000b024104c1d150002486d00c140c1d034082d14440c007030030040070120307410840d4044419008040400000382c041d46d40300f46c10400c1240303203a082544a0003414a40311032500214120044111078000700b5078880b68a074060 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 896270521 1250 896269271 896269327
    0x30c1a0a0b0904080a051c020406020c10111c03180b012103050a030f0e0313031707020102030d0903030b0d0503030124020615030f03220807051309031e05 68
    0x3a180a8690782030034042d0b411000304110001070020010035001c04005582003891f601156125580da902950b03030060f00d14410302a005400d0400c842500510b2136560405102024000c100b14894584118005004070042456915042c0198903203030720504001041c031030610803600c0d5060610486c2c018048000703a40803c0451440703840002d038440151071071184981404914085183da610000c2c010000b101c080610020582039841380b00414031000300e030b00036014044010405480614a841001e1001c0e000d40d1013001541070954030307507220001c903601a1400069240d00b4000203840e218071a1001d8445607c04001401544155541038102060411a150300d0038100d500281d1103940051464080030441420070340140c4040c000d8130b5a298051013070b6565140c424014102c01c02e8443d818880c0c10b0100580400d10307a800054490a850f030040a10040f8401d80100f203018200218007141000104586642140d800300d00300340301c828242d16029196003c00e80002d801e0142a0070283d0f030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 896271771 1250 896270521 896270539
    0x121404090b151c1505130c1218031404051507110102190f060f0c0203040303030b0a080a330506040506040504030503060d080412050c15030c0d0207030c1a0a0b 70
    0x40e5101160051803c0050000104811480c084088103042050780402e800001d0408026041d1000b40d00103036524240c1d8403005a501c3c0740101c0030088405403e001c034940c00022405002190080f000b20781c1c550b2019110741d18141d140c0012524031841904244200034020604408010b511003140c40c0d100c0302031005080098000c122503803515400e54000d810003440b20344c008240069034000092614011b1410700009010309002980c1b60300c5848103030700080c645051480c01c0c0c5400c0e08010102c0d07810350020500344d6042e440340c900140c8041c244030b120140b01c0070040d0028541c003c8a50f003401c003c80c0c00254900d40b180600050351001052103114614001c10040000c0d0801c0940f9007010040c0e0300c0e0b040c104114075101c0014451074010645018800c0b42040401c840060707445c0940a094442c01512091030b03010301ca00c4c0c081a04d0907071822000380850400301840d40d01a1030028002e00d0030b001c6034240c40d125503010700108003001a000c11604108100b841c0103000d00d02400074162804c0e01 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 896273021 1250 896271771 896271787
    0x1a0a06052206111209060301050f130c0818070f0519030c0e070e030a0f03050f07020909160e0903030601120b131a030c0d110a05120f0d0801030f121404090b15 70
    0x101b00e21050090030710400025805c0b03e15503c3d10100208400c81c103403010040050320480c00340c0305007411100201e00c0d455860300c034401018040b41e80c81c2102c0350170480340030280c202020000a25806400d040101711172071000000300d2440c005580081440300c1d403800315030800d648010100310210400070301951003007c1178000030f00125584d19003a505458107940fa00703150301400d959882580c2c00654407403c00405d1182c81034010030806008680c4840104100ea601d62401015030760480e61003040707410900c0001c01650081403921480e091450380003c03060214030002c1d802188203000e00d20100c1d9102e0954185001110f9004105ca90450003802610007101c0000c4281c4e01c04076008110040e10800c0d030074151a0300c82c4141c050a402402c084084d48101e5032184d48500d508009405840740c0c0d00380030440d0b800b5204050580c2d40000c2200c10700300c1e8980b515407220020140440402245c80100290000b0041c0600007402d01c400d008100032448034104281e081c590721140f031100d007041090f04 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 896274271 1250 896273021 896273029
    0x602120109020a08270d080a05181e03070c0603090201031a0a03080d060306060303051206010c020f011d03030f0927040210090302061c1a0a06052206111209 69
    0x41c1d0701886030307002a031070304681d412034280d05c1d40c0246031080c2c94451050300c11385680d080b2210750b210b5001d4220400440e40c4070300f00200d9801031181c004109800800c01e251003801c1c4880e03000b260345107980841342750641a0750b400781443c3d03041d0300000000e591204090704541c0d2500500304140302c0e82290703156424980002400e802c20910001304100000500a0103003001604940015500071008006213503503810003901c1907205420340340120022200007810381d8081c0342d001c41e4035500503080d09081c0e00000e005460010005d44a14440d0384a074900b000760351b800b0402001c0d844482c1c406191511303041024032010343e010501c40c0289c0d5030503101184455040303090140d03100b0307011200b01095900e0341c0029100e488980d04081d41010001618824a050348140c4a007280b802903402c03c58403140036007214a0032500390f51141e01c0383d503220040044c5440350000e03001100e0b0904c454040090540400c800c0501c071a40300802007840c1c820f0070b80f0074200c06d02885e101d000c4002e440c6464003114400003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 896275521 1250 896274271 896274287
    0x206100311010c0203010603081602091e0708040204020705060106110d031e112104021c1104020a0201140405060109060b0304050a0b0411060c0c03061e1515070602120109020a 77
    0x2410003d5402d148002c0d07603001d400c0702c401107400c8090240e41d081414503a0701c00101c49030050740034107800004180c1c00c1084000781c07280080c0300200800c154841003000c40d42c1c0301016000717a03841a006d10500c400702c3e2003800064024045500c600c4071680441c10b080d4240b00140c0d1141041c0340c80c2881d00c20110490022512038202c019000152048240b20842018054030240580074103440e95100301ea64800c101c814090340c001c0710000c0c0110661110031030301d03c00c00e003c01040c55001407021081401d00e900a40a4801c0354000403030004a0500d1417044000110b4096a140d80280c00400007603d180c4140009061800701c0d10349545020703140c1658420152400034141c032088000207080c401c000380c0841e4146002400b0780d681e0100c4001143d81d940302c181416202e4020100440c080c4071800c1042081600307012003040c0143d84044070402c80500a950041c3c000f84074003003406032400040b0082602502c10400103844965200b090f03134030f9480581150400500c100301080720f4940141c90 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 896276771 1250 896275521 896275553
    0x516050c0a021c05030f0304050c0a2111040e030721051c110301120b060f1e06040506070c030b0c0406140a11010f0f051b0a12090510090302061003 65
    0x550032040c480f030241054210241a80940640404200c0700e403407001c91001140180d0058048601484030700c002c101c9000d426205840c0d00120b108400c0740c92281010065040f0f6010700382c40c006218480011805592810018140035040050a81c081000c02081012001c0010802c41c0140445001c00b0305140316007280001e000350a8010341040b0101c03134200706640c100c009452a280d50796080212451002d40c03c1c01c07103401030740740c0001c1d101e424101c24003d51041d00511402104031040b0284280d00d451845071038201c54104000721f00d40d1555001080007500c100352580d50300d4070710f0810110784080a040b4901c14201004100900ca500811000f0500f0251318000d80c1c5d03407420340003501c0b06107800640f80b10079424041604a040c0b01e9900020801080201c1030000395109000700c401c5001c00c1c03418500d40d0030309008401c030503441f0f000c40001c030300c0185030001040100c0b9281c0380c1c640b5240c080003010081d1038803107070301c2010f42c1031005030380040904441100284c1584e847d8020748440c410 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 896278021 1250 896276771 896276779
    0x10c05040608220f05150c030a02070807060629070209060622030b100803090d03080601022503020a06170403030509120318010506060a1e03020408010e010516050c0a02 74
    0x400700e07140c3c848012004103001c3c0158599542c20700c1500e07200d50480003400050700e5a0040d18400c0d0345891051641074415403000c0d030700c249540e46c1c900c0c814000b50030854065a20460922489001412600c01d00003d40303540940e49010b42c441c2c19041502e00400e110081c2c2854043c0030910050319107035903403174101d003040b03c1e16922f500c3c4413200140407011402100c2d1001485440c000203010404070840d002d05a04022040036544a0303403000c2e070768400c200000e13030040c11255030360020038460700a068012030305105031420320800c0b02d1408a070100c114021040d026114104204514090242d84001c15240c00c1800c3c1516140b0b0707041d01a0b000051000e0145030b140c0001980c0003a050100b0701c1c2040c0304000a075101c1c00c1c4448500c028500603c1c5000c100e6183c000402c40c10318019054540c00341c031540c0c0341c03108403420261120019030312060940030305800f400045242c9600303001d84000c11541c2e0000103a180750040b03102c0d81c400c01c2c940808041c0b00042014170b044440215001c1c01c0190107075 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 896279271 1250 896278021 896278037
    0xd08070204090609051e07120206070f050309030607020706030b09251407140c060304051e0c0a0608060f01080c090607050c0d030f260112030c05061512010c050406 72
    0x402e082c4054413a80c01c004200c0d002e1703000100e9003155078140d00e9224186003421a541035031154440e80d012064154041e510039070512803400020700000e2100e01c0741c1d2060080e00d051251510200e0720b840000c3d10448056006000d05000d40e507814810b40c200c5181c12900c1e25800d06050003071032000351040d2010a041d02c68001d451043c9805036a03101034001d8298501c40d0303510042c3c1800409182110310a41441c0200d11b0408130502c0d02405583c002c0342c11002501c910034170515901e03c1c00c402c20700070403194014104103503129552200d00c00001c18060301c41c4410ba00c2c10070100810100c00526960520502c0c1060000229001040c2d8039040001d5500c0c9989101c03038180307503141159294500341d000404e0f5046170b0405501c058070441c0d60b0810348410344030048034503016038504143c04000082c42d0851004000c04101116500f00d85406400c2c01d4203800c076942c5841e41072160840381440000d415039234100450400e2181c480600d803190000b001002e861250090880c8a00d2040c4410081c01e0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 896280521 1250 896279271 896279273
    0x70302071a0a060e01121e030e0315040605180c0f0f04060b070c0801410c0306010e0d12080601090801090f0618031e050409050c180d0807020409 64
    0x122400c0c046692803031500c1021842c1482c4081c0c00760883c0c0c055041c83c480641c0c000981030078069818032015030710a9600b495401203042c00c00d00d24940800c00e40403c030600c00c83c1802c64038144214164040510144d200c40e05d481c4c245241a110054050f60826001140c680c0c0230340d601007842130180b082243d4180c49800b90030b00090f0303083c12410300150320030314044000500710341d8000109000d40c844c80c1149001d0b5641d40d2003030b01f240c0c04a01018080401050003200702c450540035412075014074401864114403070311a901001c50210380c8071100c0d4100100b803011039a00200d841c21016002c0710400c04c440965507465040c41c90303407030308103040c442e10300e0100e0f040368011032001003d00049402000050440d04240b8096084000150f0f220380c5000706410426103030000d06403519800d6104c7ea16100d26503002e460b46c0702c0106580b40100328007400003041408842c01501d00a840c202c500b80d49408045e10104565508006910300c10050b21189100207044442625519038046600180618103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 896281771 1250 896280521 896280533
    0xa0b0c0c04060b0a021212010302100309050a0506010915060909020a090315021c14060f03160611060a06082806020c061807060e090903090316030512040b0307030207 73
    0x4205040c507403241c10044086201012500a8038810045500301c4841c81280c04000450348604044002c1107590f24005102604241300c202e10b441e229440e0004403031405454090410001c0d59044407580c210000403c460500c1e401000b841001c551680d0080d00d2070708002600c01c42d698851400c0b0203801243d8040c1aa029455001c011908840d101c2840c81d18803c00c180258000010519064842c1c403040710301d46054410f01c80300340c0001254502948500080085000781007400f56407511a60040003c428002c1d03088900505003a150500c3c200343c0001040c3c10094001e00021100e45400380030000030b02d001840b085484500041d0b4800d145105014158a060b00c100c060152400041c00c80912040040c0141c46042c80c038081d80309100503070100d15284e10700c070f2080c04002083c0503000d510910300552119080003220048a180454220101b410301603100b000340701862400c071041082c041c05002c0f210711a241d4005441c40d083c2003d0320000c0c60302014008108159000ca030703600070009 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 896283021 1250 896281771 896281783
    0xf021e0109120c030311160201030509210418180201110a0b010b1902010605090a02130e0403021e01050708270717010c020102090f0108061306030302010f0b0108060a0b0c 75
    0x203040b03000708100c5503842002400180740e5040c200c00084c13a08142d2010001071805444180b641c070070080341c68019030740044018160162640300e20340124840c0c0320440c1c508030081d480350780c868003180da02e80d46003040c001c000d50b99540804035641d061124000e8011480240f1904003682428810180c0700c0c142040da142032090780c0c000303104031020400800c040c10300e0000303030001c0f02e20944000a1004c0703c410403400e8079014811103030040d20740c00100760f000f0803d03005003428422100030324004540d281007110b801d80003030780e090300507070401e07082403403c484032404180784806190002d001e03e0401c0f440c0200300260041001000c00046038500d01101000e2040160b001c2289044440c0640c0714104039501c65510b4490001562078a44044074140c018003da9010800017401d48800c14486001541d01200040105501448603100c0b4841d0070728074442c0720b004d10301a80c00064900e110031005012248503581003070511981d5801c0000c95500c90a06c01d00355500f08940544400d400c1044901d048 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 896284271 1250 896283021 896283023
    0x909150b210a090606061b110d020d082a06071209080304110f01030e06011e03050708250308030a11160b041a0903070303180b011d01060f021e0109 65
    0x2201074001e020400005801c035100c5075000f500304110f003650343c0c031003500d94200709103405a40c094002e10030070100e2001340b8203034603031180644a100b08a1481d0b000401c541d81d9044d040312030394030209001091500190081010b5140b0700b000c00c01c16120b58180540c1d81d00000e12640400046040e4200240c01e182c0066017850b901181080e2241081d280a00502c131060030810302941d208502c0d2a400d610034043d1a040c0d0403054090000ba03400e24980400250302010920981040c03040000000344040000d40b005020200c0a03180100149000082e561110440320a00010b0f1050071f0001c1101d940441340c02031502c610024080034010340b0441140a203d03d80200d501030011440706010100c030744a80b040c1e2045504146039100703011860f604241c10350718130b2800d80c824030512000900a50118401c4003842103028510342d9550b0300e03042d00480c01d800c45a00014618240301b9406200000305014110908120244649039030380255105c07440036000b909000d000c42141265602036010720403103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 896285521 1250 896284271 896284327
    0x91b0303090a090b01020c0906010e0108090a080c030a120615030b0a170705030c090f0408030403091a0c010e071a0d020f190f0e03031e0c0615010909150b 68
    0x316554501060081100d00c0e0f0f44c50150248526500c428549410124070a02d0161102005206d040c001101d09040040400c06c15200d0450424042505070000d007074200d1904008580e1003020132802044001000040e420322400d0032400d100c0740d88069103207034904890307180c0029981680c100149200415600c5841c1c4c210201012212140c4041121820740e9802d40c00c441143c5401000c0c070201200c115405620115088046800620801e006607049402440d00c0711405488603001c0c50584040501245080000203c2c00c0da036100038014070240c05004800780c03801343e1400b900300d110b41f0b001d02c2034100c02c1180001c0030329240446034103461442d01020051034440700e100055502045011001d00d0101d80b0703a40d014900284541c520240c030010140185090100c01c0880f1401241807d1034580c00c42804e0190749030039142049140e126144401d0140e511905d000005003080c0c00783d070000c0d4442070412200c08103e8403d005800d00300c5000c085515600d00f07040d46107003010300030202e1440b55 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 896286771 1250 896285521 896285539
    0x30f031202091f090b040b030105060f0706141603140714040e0a05010302090c03090d1b291f1e05060310030203190f030305040201030621120206091b030309 69
    0x5100041a41c483c95006140c80b018903494840f0551100c42c0950b2282076207849040005000034280000902300340500801e00505110640d0350340c1080d03e03441c1c0000e4283c40302a1041110780d80070000042c0014080b42400c0010400c000b43d04e4a003460300420040a001f4219110103c10b00300c03604640c010a0145081d28407401e0000c90710010740710070303c0160300c00d00e00180420400400082104d02422801e401842c0804100318140e0b03003040150158910340e0700c01086040130513001e9107882c500c11348081c0d031400c2c0c00c40c06809036080c50102400140c00804203038410380444c0349600f00e00080d91a01c4c590075404440f00084511514002d0f000290400c1010003444040d034411110442505d1003101a03e110300c100c40070003c582074190801400c000c00114601c0046402540910b4100d03006260114809848819841401304200849608a00390301701000511021103947d60034100188064589030078108240e0b55110b800c1040500148440280502c1503a000c10840b011040d015014100c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 896288021 1250 896286771 896286799
    0x31b0c0f031218070630021210051503040204090515091c050301030305030405070b0c0d02060a0c020705091e01090614010801320603041101090f030f03120209 70
    0x14480c1c024440000b0a4a41030300410980740709148940c48118243c0d00a040443c80e18004a80c580540b01c1c0e00440e4002e0a075480c02281825a9002c0c0041c80746000980c3d5101280802d425068000303280440c14031400c5014440da41d2045883c0000064200d401512600c2c1c600002d00286400600200680f003240703c124210f103c503590301403003083c603401034800c12400110000b40103c3c500080780d0028400300014000640646c01443d040ba00407000c448450b9212203d18203503510803034002c2c440780d00c0703102c0c402c4806904002d601e600c8154024240807035a0014030217562241103020b028420008200042c0e6110043c41881051084403288103029595540e0004010540c500501c4100329210004034034a500555036103040366040c80d0103202e100031002c01c2c00a40700480413100a03c07000da5030300b05619a1180095400b440c0501458821041060009401280d659000040007a44d040042000c10f10910160003081d40600b0000b110702000c0c1c500a009200300c2c1002c907401041c0b201501 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 896289271 1250 896288021 896288023
    0x73915050f01051c03020309060a18060801092d0506010c050a03050405010314060f010f11070e0f0624491e020702041103040b07020105060114031b0c0f 67
    0x18100e40d0b044d03412246000b00e54891000501c0d00c03020140250b4030800c0404500d003010b00c004c14510b02c0c03d280001e521340010f40040f54500490744410002080c41005003c801e405200b0000f0528926000302c0c2007540c0840720b2807082c0c0c2541044007040d5940c44c0050656400b4640b5004456445000d0300c146e980c1a107005445500f050085e280040c0c0fa11441c81400744100600c02e01645009200880008800780111070b4807044a89210400540c900c280c52218820000e040103400e01c402d6155041ca0003c500b560821801406a4402c2d40180c801540c402d85c032284880900d100b40209550b01d40e429103010882d07100907900c904044207110a500b080c1d00c413040281403014070fa01fa01e00041d10045400d0801c1e206400a20241c0c541060b218006204903580103004041c4082c0020860541e4802140034903001100c007a2181d0041e5001c000700c856085c810755a200d9400d080c40700124101c40c00c404040d020091425036a004001e152444400b80d41068a48a2444000715402c00c51220142 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 896290521 1250 896289271 896289301
    0x309080a020303091605010804110102030d15172802150d0203040501051b0a031e093c02040504020409120203130f080a1209150807391505 61
    0x103481e080c05030004905040d45041c0105040361b405030748044c040c0d10380f40ca5110381c10380c031408010305521040010604611840c0502c06e21600146200004549082120196106c5599003000c00c4c0d04070a40351124104410680303800f4100030100b03000400c2c000d1020840417412052030001480e004581318640c114503400452040c0c1c4640c0c0203110503140c000741000c0c003003611034014540541c00d00484400c0c1c2e1003940404180c06490a03607d907501c0324003c4100807140066000d450b02d03004024002188500825240c290026800103449500407001c1181e03103c101514009104a072200c000c02e082d541e96800102d58241c0000090201e0090508081e40c0c0c1ea1100b008042c101480400c009030740e0000c1140c0c030f8211a4040040c000d5010980d0782c890701d00584102450900c024410042084000007a04440070b01c0b46444407011411f10311303405401d0002c00f099448030306241040114010000444c100c1c000351180c56411851391080c030b09240c407030f01154088044103140000300180d9140102d58 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 896291771 1250 896290521 896290531
    0x40b030118060806063609151b071511090f0105030408073504090f02030601020c2b050c0406080604320d0806040c0e030c100309080a020303 62
    0x607545202040d0450034181d40c1c061045010719007000001580ea8104074450060019007424100380d0000c1c2e16a048044a4481982d0340555a40004201d14042c0070404983c440c449607071480d43c00d1501c00c40c43c00000e25039103900d4000803004643c1c0c000f001035165401e0036001041906001500030841c90035000d410102c1680c2c4200d0890f8917007503083d4000cbc41140d001d250030500d4589060b40907120445080c0582801d0b148007101d5840c910b5211501a40d6003540e09001240c0035541d40c541441282541d9800c0e4060030940d1041041c440d8a0381c0000d0604c0054106031401c1d0342018400010320015041904a00391482281c41803008011011a55481d2001c046504001d030729100c060066072080304440041481e66003200d0070b040c5810f09101c1404400f00380e10100501240f10400600303003618156024080b03030b034076401d0207402e140c0741c044c40d903040b5443c2ca806494807445d280020750b940c0901d107a440c012a0b16031115240c1c94402d41000030700c50f40203190250b4402c0c0042001350780c0da00480d5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 896293021 1250 896291771 896291789
    0x2304021b0f010b01050f07060e0a080d0b0a06030c270909060605090106081e060f041a010305061f0e030c040603080d0c14070209070c02040e010605030f0f03030f041502040b0301 78
    0x12001443e98040c40554501141d1010714504107500d50b23980c58020250b50000c80170500c1602c0400300010307079200c02888800a1842c002c60399030900350900044224a4118406050820080b42e4410f548402800c03115581c29490180103501452000714071011900010010341c1400c58103014012141c01c03907001c40b0401e55160250740c5e60348004480c0306030143c40c100d08042e08921035443e4003102c07440c2642c2014000345091403c513160320008085480d80704182560703a00c18051007180b0b6030036101d007540c0540c080c1c9138403140580c00c01440c11800700f19403241c414090f0743c6400321200d03201000030900800380030b003040101648a0038007410f40d8100310303081850541001a4150000d01ca401e0b1482c8240403120458100a003a030f00304076214800074401401c018000f401070001d83c5e59800781c58081380030704000159880c00c003801e260500c0100ca042c07500c1130b8000781c240c441c3c9043c0001240e034460440d40c02c1034080d445502d0710310a0740480c84004582d050020801041403041800214101d8074524 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 896294271 1250 896293021 896293031
    0xf1e0312020a020607050d06050616050f010e0309060c0a14060f0a0b01140a020c150c07060813030309020d080307050327060402041a03010f140c03012304021b0f01 72
    0x1203103109900c100e158240041c3c1150b404aa1680c2c0980081c0c1486041c0e408003240103031301c81000c0360707460300520700c2946400c003400c1546080c48404c1c401807800c202c140c002030028581886c1510741d01d10603d544607005500010b84800501014050110207681c084091006072510058103a0b40d103034207640260340c0441341c001040c0002030070f214030040c1d0a010384401d0b501800e0b1180c001c0071600500c0c500e0040d40219062034245580742210795070311500d0400351a031140d4070f90301014079048860708414180320580e801c0c0b00038581c0460702d418a0683c54500450481124800307e4044204a00001c00c46140070091103000b98100c006188102120540c1443c510070a840f5508410401e0300c10781860f0300000041000350034540c0161000f180760102c1a4000315880c00400d0031508a001d80101c450fa41d0800b0880701141c0b003c01c0345e001000c040c1084d0030f40d414030b1803290640e481201d0116040c50300714255000b584407a015a50a00c61040030f515041040d004130603142c644100c411601ba52802c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 896295521 1250 896294271 896294297
    0x5060114030f16030807080d0c0c03090b0403080403060f06170124260115060507121103040b030a1d150a05010f050108040f02090c07110307120f0f1e03 67
    0x1034450300502040350041082891900d17a0310f416445071400780c400103001c1015107180032003401240404103d50740c1c0d015624409045c01404000150007200754283c0170001003020590000c15182504e0304007000140c030b5001c0110f050005c001c075500681c40041907450003080c58206620902480c03030104140007181145100049081c0f9030b0740140c40c00813900019200c2940444400450744401d400c000159010b44091290100b51059100fa00090f400150100030400450722120100050303042c8400302000c000340c010745900440c0984498000c02000181d4843d000340c200000b400b0700700c0104008008440913003500d408220205950244a2601040a48240344100760403074000710001d40010341000e004544150740a4000c0d2428104042150050707540c12186a0148691181243e07035900f0b986081c030402150f0700d030709504c283c020740401c20071451a2900c0303580d07056010f5060b41d40400545031103201c072200b204d03000e000c0090301041d0b860700c4aa0301408400031402512940400781c5c0c5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 896296771 1250 896295521 896295523
    0xc0d0f0f110c07080613080c070e280209031203131a0a050f071b0804050901080d0914030705130906060609050319020d080702010c05120a090501031407080c0705060114030f 76
    0x26506911030324401e810500111f030401001c0c045501085080d155103a0380d5a00b1300410b2801607800c248020400c04000b1410280f01c6042462440805025428a1000400617171520284001c10342203910001c00600c0d88001d00318003a00150713001129007031142030403182c0c2d000f0401c1103076941c1c0e80614200208030003005400000d4416000c969401042401071703100c0d54026101b00b07200b103c80c08401e200205250ba07802d028940a080c1c07260080004606040b801010703044543d101c59074410b4217a0943d10a07071001329400c0305940003943e94040c50600380c1c1c02e10005003d0014080c2565140100100720298450002c00844008604a4582d01a28030341150441700c0380d01d0095000048089150000c0c8040c8040c06445005050000400f0b0054441c2070600100320740042e10030000103003111110390840501000341c2001c0c601000490000302e01d20907410005403410342401122000100700694510403a40b4640d4400d041c0c483c5540d41e00501d10307216120580581c8280584066035007040c030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 896298021 1250 896296771 896296783
    0x3050307140c160e19180605040f060c0801030c290c1005010f050d020d030318120f0306060e220c080a06090e030a08060406030b0405030306180c0d0f0f110c0708 71
    0x5c100511240e030a9031390210100900490031092030508044003000003154a0384202841940035807190940c03002a49004c20803500b5001504041c41140401440483e8461224a050f642620342c0f54400485001282c1c51544808a0f1240c40020010760030000071030201d503e5403035000c0154103011a0b600c940491460091034003420b500140c0d07074110f100243c0782c0b59601c0b51590780a401d0004205600b0301d0a1000c4d049441400e0300c040d00106203a03d00070b42d121598007c41c0d08503141c104003550800d0b4008001d6400f5181081c424001c042d420805210f0100311400300d64000300f804c1001450f0054090050002150094001464200c00003100c03900f600454045503010070103149016240017040d0354401010b40000c5e040f40e9108070100c0014465000d060149004030000c45d01ca01c0c040d800c102c2c0d0044048c420360701d01020903042c805803203003000c25242403102080000c80c40d101740041c010010003041410941d400c0c14440c030242458155001011724011710390664006a03200c0d14410381d251 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 896299271 1250 896298021 896298031
    0xf060c1806230408331e0a05060105030622050a1a040605010e09100803040b0421120e12070e040c090501050f0d051e060604060e010f0303050307140c160e 68
    0x5086900741004072403400644a040d40c1c41c010099500350607003170400300109400c8410075a281850320800c20399640900300c283d404108010140181d2802c01e000030081d00014003442d000e41250a180a940f1800301e801c80c0d0410624074080046150010860f0003912082119800240c8490b98035850360400d13005000a4403410786900341604441c2042c01642c410092598066942c12103000c601e41d0402d000800081074a880a02d0711382d8242202a40481d83c000c3c200c1140c00711030f00d40400000c50b01e00c02000c12600c80d0a01d01e00c080140800718000748403401150fa090f0007019000310310307101d50b601c00d540070b1406094511100381d1079044c6002110420300441358880d07071065800f0050303d00210180903d45c07003901600d030070301610698000008401d808420154000104121450406104030001807003520b07545c0800354034140700c1100807055030001400304103001000503a503901808039500c0100d1243c82240c1e803496404103a544400c4681c0c041e4010190403d00040c00384a9840c1c290300030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 896300521 1250 896299271 896299273
    0x70e040614030a030e0a030f03050d24090b030f0f0a030e010203070803060409060603020409060f11040f0306020306060c12040e070e0319060e0a03030e0c0901030f060c1806230408 79
    0x9502036440c15a1061207007402030307600506e0070401200190f0b41d221600206da02c40c0d02c500341c07560310030750596043e50120301c0f00344072003088468031a0300d040384461141e0032203920003000103500403101c02003400c003015000d4800151007408503148008000150145280e4043d40c0c03070a80412903117004a84a100350000500400e20500101d070851034075078403046220b440341d03000040c040e03a00e41c041826606042001e4601640c0c030300310440d120f80b0900641c8481001d500145260900303191720144944024080905225400300004540c0d8441e0b07000c48003642c142d0011506610b17440c041c84803c0350f2081c0030b8001e0008484021812141c000ca80c40060200000e024100180070485000014800043c1c207450961b00c03640358244041090003100403460084d500400e0301041034003034501d020244c541c40d5004024950042002c40c01400c105a03a07a90302880c04181044c51280c00c6034108006d01030414644a142400280590080c084603a89545420400a00060444000d1302800755101d20003007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 896301771 1250 896300521 896300533
    0x703110a0807021c0305181f02030606370e0108220b070207140907050a053402120d2007080f150f1905070512070e04061403 55
    0x102409114542ea01c950507204585407511010040c1501240b08801400803950301d1341800300c150007894014102031402c0c0028560300d800344041c169020484152065681e50101c04500b960b0303139200071907030146400c0c502c024070302d901a111b510070700810020380c2c140c41c08150603040311180078990020362854161a14905a91200000700c0820b00d6061031003402d01c1c07440000d00000e440d110481e401480f0303a600030420a41070a00d600e507074580d48020f5034401d03100401001940756201d0308603031841045190060300c0700b2604007450004c0d84002880c46c01040400303800581c19003204002d01406000b101c00c0c982030500c14224503100e01030500345500092204960621991039040303502c0d444207a640c105c610041d5112821401d08810f6035607030b02c10703410035051590b80c804e140da4102d170130041d09100207034203003000599880d21640c14a001107102d40c07601e0015810602500a071090390340340301e0401059241c988002846e16100000e12841280340160105d08843c1c955811040307e04041d00400e0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 896303021 1250 896301771 896301787
    0x1c200630011a12060424170a12030c2604110402270324010302010f0906020309010e2206050907020a170c01060b04090e0601150e04050c04090204081005070311 70
    0x101e80c841c014120343c0c01c04d1302d9001942000708041b01c0b05005c640300d07100032541103092601c1507500000300b051500003544180842070102d0b141c6507200d05119072904001a03000084001a601301c03400c41c0410358403d030b019405800c0d1011100c402c80c41148103607000448582e4031420807080713024504001c03419045d1520002585012024288840d21009084070742280040790300f5416000300100010386040f048c00108210b50300500204504440340c00c10199550400d070000b0341c1e0703000d005401c07810085840e8400040e5110080c520000d01001c1d100c40e14032401c2c807541100944075507c03400b40515442c1000403400e51020070b5815403e68070041100160141c41e5584030315802582c10001d003556174290000b40b141504004000418501c0b07408a0900d000840042c00c01c2c0b016803140c8074001210b80c0760451264089038404101200b2140000c01e81c6070100030030b2080c05180c1013400014400103011500c03442c006105400316540c003906102c0e079543c0c43c81c1202580e00111480345401c0c41806044 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 896304271 1250 896303021 896303047
    0xb030f07060914122a04090f140f12030c2523030406050708040f12060606031406102c0906060702010e060d0f0f0207021c200630011a 59
    0x28582c040424004817076400140001c00311380040a0031541e07001d044030341404001c00c1c0074014441050640141c0003030105940c0040d12041d00c1460b1080d5400d0010004060421090546011541502c141680502c1155818000d103001190070399901e010a0b416003e0b4205014142c0e0046075508091820280342c4081690550880b4008540220050001040307608941c20014028883c005000c4805101170510701c0032503407690130003010942003500317090071504000c40d81070300070038161041d8241070b90701c80b0210b0b0b4a01801d44400d031307440f002900070702c1156064541c041c2001021103414006885070410040075101e07000000b030100701d80300b403010b9140c135080019090980d240380010a90850a6081c002110b10f607000d1080f600781d01103042025400c0078841e40a6550040f4094512030300c16403201c0c0541200b11a5400f1403100b540c2e042c040075241c40041d1111650741c0b012131070490b4208030191080008025400000081004c000a4800c000100c02c106070003001820030303d0030070414050 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 896305521 1250 896304271 896304313
    0x901060e1507021026070503040201050912060f061503060d060903090801140114040203060f04020c0c0d0506010618060e04110f030a050411061201090b030f0706091412 74
    0x394121a40c18405000540c80b130000032405601203a55a21a407201e031400c60020601d00130040d0955030044042052050308501100c0e0450313024242035441c2c080010000b48108203000070440240110300c20311108541c42c041042c09080110703107810440103206900702d010700007210031a9201400c80031110100b02c140e030200d441130f4042e2420407a619240c075010350a40351078111070701026051000400108000032488035040f64102c4003546142401030004180e00c000b001202d224560000d465112000200540c450901019007007034140b9100d818195110942449000007044500e10108a980c1ca041c811405481264480c2c1911040300c00070312000b071103581e41c0c8510b046402c0001d1075490200704080c51142c400d8040119451401d4900070313025860880c0aa80540c0041c801807a1041d01005034905503103120000040100e0b07007400207031904c8803542c00071805024403400800c4866001c202c0c0401c0d9002921080440044033042c0980380e54050105841e80c0c00010500d20540f600c0612 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 896306771 1250 896305521 896305549
    0x15010e150c030a05180d12080c0903011d0d0c05030a0309030912110f040213050d06060b0c03030406060503160311130c0903030e0d020307030b1f03061a0901060e 71
    0x3a080c1803084081e19503280d903000c1c0c4884000300d100403508406420001d1a4140c0321101600c03981e00c03400240d900c1245480c0c00c0541070040c844c042c40010343c1d428081c0290798400800400030302025a0310002c01105031100b18601e81e00d030083c40c0c0100030b13081c020340c1090020303603000c0011440e00e110700004130002c00e424842142040042c0c040041c4480c443c0e01d800c00518001c00390704610070800001c1240031403884209a00460052103c0000c40d184070303222400300d032005e4484a00043ca0b03031a041008007a560458100e840010030441c1c008100000598880d030300c210070070090a5284c000701075441c1e101c0590103400b04413010040c07000a800f844c01284048016004109144183c1550350554081c3d901150001d41d030100204103040d440b44003a41000d1003550080c1e244201340c2c0120392201d1403400007038000314140020840c485031440b0038141c110716103682c01054a4481c0740000180c080740c11010001c0f8450513044a2038580880064100d68141e11039241c419a40000d10607000c1001d04 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 896308021 1250 896306771 896306809
    0x50a0903050412081e19090501020c0d02040e01090c171513050c0306010902130902030624040e0f180606030703032601030c0618120609022107060815010e 68
    0x240d1008014481218410781c1c5c452568440180002144804059907901c038200048490204410b036008947c1d21820082510b4041c506074442c000b040240103e00c0c11800a9840c00049a0a0010000c103010903500d04c6103000c401090f04134451907440c1031402c414055850f040011030b9480f549000b160858520440a488900b00b1f200300180c00c0c00e001340d214101c0c85d500001e0759a031070443d00310000301800050808504600b80080460300d41c1041c0b0091194071140d02ca0040e0409a20f141503400804a80024889503c2c0042140e82000b00513568001c0c0c20300c1c5413100304e0041d00c2c0411200e109500141c020513180c1e2440d14101d40c0a00049000100051101c07045603040c0174003494235001c1d60188911000c1949003200040140e42446170449444c26100f0b010700c00c1d1041e007501114041c0d041000458069150b00000da4290140e45540001c18185030304404d400c040414000100c805903110458681d8402d142800341c0000004841d00103a840301e411651460014030b086602c0702010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 896309271 1250 896308021 896308027
    0xc04060818011a0a2c0406060f0b0415080c18010311071b050a0f1802040506040303030c0906090b161a090a17190507060b0303030a0f050a090305041208 67
    0x126042d00311401c00c815408107403140e8416610ba0b06289944800402005641e54001e060310002d210131903280740c003203c00c4984c014000c10180440f0f90055000f40c460030880c400072a036501c5001850b1f5201e4443c0143c2e00c8141c800c2c00e8911170041c01c94620406c0f107000420719150300560707031007856800110b207107042c5581d924600700c000f5000d101419845124240c200c00045440b40e00f07200c080002e9006500c41c000d666018070201c00d04074519021680400100701c01c0860090440c000303400307142c2240d9001030b00450000185585908220042c08490b1640300c0041d4032482c080700d00030720a000c0c84034242001c010101185800300c03410640b0b103001e4484180c603600a40741885100e00d040d103100c01c2c240e006001d10400c2c4120007440440701c02820341000e14103104952600e00e80a140d4800c8002d02401007044807d000e141d4014081c2c210004084e039580c1e241034101c2000601074201c3e8854031a2600d00010340d008464400c0542107909902c07034a04152400d00038241321b00c1c201d1b8045501c56828 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 896310521 1250 896309271 896309311
    0x50702190f050a05101b050a0f0623040809060d020405280819060c050904060801061403030c0606220207030c030809150403081008060901020408150c040608 69
    0x940d2900300a0400320910040781031078101003021060098100b603204411051203560010380105c181c80004c08519813103401c00116040c1141000341e40180545442c04607007a40d020840c240d48003801000c0c6005000400c030100143d030003c008021600144400f004110000712441c0c14405080c5031001ca40e805803a0a8440c0003007450703029080b070f40304249070055441008140740d8042940c054200c0c81c0c01808076841d44040e140800740c120030082e000c1c030303562590142c404d8410b5040700d6070600c020f00203000c01a60340840c903009003014803541c1c09c1403521444024903407401004031080d400c2c006008040980300d43c0c04200300c1920b02d402c0d07540e10705402200710070b16180c14000750082c0740c0a03440790a0345d900c040c213024003412801403201d0407a810020504206c030b00a00c1c3c481d604145c1602c2d00b400941c1ea1290841d03003507985070700444814460f450030041000d005400034401d544030030060b10b61807a06000e8031845944181da48001c40c0074240428030941c0e12445549900c80030070b240890f046119 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 896311771 1250 896310521 896310559
    0x60c11060a020c03040f0308073e0d0204051f0503190b060a2d0905090615030309060706060503101407030b04090f1a0c0a0c0807260a02060108070f030201050702 71
    0x40d48100c490b108c000c281c007000e00000d0703001061180c0001d044070342c0c9a1030300c45000320302d40108290a42e15001da105981825103405440003019640604104440c1c2008030312040d03010801119046802c0c0080b20110380c0d802c011640d04650f40d00c1428407554000c07a6600c01c010704030010a025040071180f03500041506076224903400c0c0141104c05c40611700301000d010ba030171030f034503170820784806080c03809000240c1c100251560b0f00c0350410110752107000c02e0340c00181c00c0d1310441d00d01941c011808240d10081c009242d0007041254411011036a0300903800044501340c44121490800a80103100007684550003a0002c1c0000302c40100b0018515085988a18080c0500d80c01541c032903000140010b850910f01805a401c040c1801c503ca0410b03007011030081401450182c000d00d880000320b452030400c500b4000e2204c6092900341002e034040030f812189003c9400c80410b02c40148104030000800030701c0891b0031010741d0188045c8100b9141190010f4038140d0007007508030780060012920410500e8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 896313021 1250 896311771 896311799
    0x1140d022508030f060a0b0405040209031e160905100621060e060102011505100c030c05010f090213050f040f03171512150601081b16060c11060a020c0304 68
    0x111a9002e1522814800e50005403602c1c01400640a403007480014850054050181c1e022144100c034090781c1c417502c0d100403070b040c20b0040c0e45020044030010100c07008400e010601d4030795200c1130050580c900c0e984090396000ea80065501d45251060f0b48424803413148114004441c107002c0034808a01144040402c004035a81540000ca03134604c03102c1405002e41e428009d9100840142d403468009a0402000401c6941e4002c40001840b1501e03085d481003501801c0e2941806401000800001d101e10410310041c11600504901c103c40b004603403109850ba43c80ba0034003441000140700355542d1241d07507940b00900004002d60a0181d03041200c00d00d0b07941c03d1031082c4110380d2420051458405101800449080c0400f000364603001480d03d0002c03240d40a05e200d5003d0424a002c584a44905c401010300115100303055030103000018440d10004d85011815620911603202000754a100038011909612502640040c3e90001d0300403c106818039006041440e15039010399181540d5801e0b0144040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 896314271 1250 896313021 896313023
    0xd06020f040312031a061306050a030f020c0a05010b220f0b13200a1b0c0302060a0c0308060a120204050403090f0602060417090108010b0715050a1a01140d0225 70
    0x261140282820094001c007018032124094030b02d20704094068040c50030041c01c90040f032342007060101307d403141c0b50300c00c1c1c2000b9020501020215139404501d550700e5190b8048003400d0303038990301704401d20303856043c50303414203020b0141481c1d001000d030302c000e8400002e0824902c16022060321760703180d000706540e0030800303152112010800290b0035131021140304805020000d90100348405001380c0c581250040c56400220f03980f05040e01c4a00460301c0e0035042002c560300041e4010070042240a601508800380300c810340d00a458100003991010104207030a00349000d445032448032500b00b00c00500f0903800080d08244281480700d0150385502000b002d07445c5592003003005070b0050044c40103022150b01d10914400307a0203c1d00d8a40306980002812080c01803180d2448000001800307070500c0240802c0345690031404c82d0a02c424245400210060710705a200d402d0780c4070441030032104a40c00740d03041c1c0340085920220301d42003107001c00188000b50001c03000d00001651006102c0b0403c102002d50074182 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 896315521 1250 896314271 896314277
    0x3070302190827040b01050f120c0721090936060c030f05100303090314151003020f0108010e061e101707080105060708070813090c02010f0b0d06020f040312 69
    0x702140c3c5040105641524001d60305108041064000c070044540458160502c40804604191244c2d05540c0c42d41c400c1940c05002400922200041074140900e4000f12141d42e03035079107070525103418071901154000d41e24450340c5c82c00280f8400c1c01e61a044240c1481d07071a40c0140004510064031101c054842d1171820800007542c4410320a1800f0907880b803c0d030000d442080301035801e404d56a010307003e01100e000203404003043e0f01e01100d43d45000c114a090402d815a02001d140c00d04912400000b0584d00040b4883d803e804410034865103d041800e040718140300c0c1003107080d217404c0144040d801c08003441c0311050300860003042d2030340c89159210022007013036694080c09603050341003048000e40c041d00c40010000000010852031b9660f41c00c2d540c4090f041365100c0c2d500c40e42881c0a190754407071440b13040515400c1090010b62070131507a1140b8a0300c01c442d00280b007100304180c40001201c00c100341040c0c0c0f00f10100c04d0305001c6110755000d4000304070400d83c0f59203004e441c0e45400300b504048486803000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 896316771 1250 896315521 896315587
    0x509031b03030714070b0c0c0a15052e0e060315090703020a0e0f01090b06090d1a070315031e081602031006050306040f1b0b0d0b0102030703021908 65
    0xc0c164080ba44841d2030740100e401c03504010301031b0b9039103149900141051a200702c0c00714240302101e00034001c00c01e0325075001d040244c4e20084428440042c013012034148000700002c1540101242c040c0308081c80c0400b00c000141500c5040024034511050094036080e0507104590f01c00c40380044050b800c60085140074000d1085034914410000314000c1a003194039021100f80c2444032000324050f00301d06561600c100492102d1401001c140280151008903500080b002200824407144100c580b8500901030403030b007130a5896410a0f0292070b20480007440c1e18030b800004102040004140c01c0d5070b59040b107600c0d00c2c0702d00030b40c5030f00c140c90304a116100c5505207101c9440c800c6280800c140b41e040290344000b846941d01e0000069140d010007070002d48114912030b884810400071008480c101d40784003900c0140f982e110500d03819280c100f070f40900e040c945007030400c8126600010540301081c0e4158010550b6041c0d10301c0000d12085540000c5402e81000d00c060710050420b022105031900108080040b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 896318021 1250 896316771 896316781
    0x1b06090c01030b010c03030b062115041506111203090303071d010e04050a0f020d09020307050a050d1506180209091308030c131208040e0903040803030a0509031b0303 73
    0xc00d099038540881d060600e440c20740196a600280700c0056203030035060000d801d013013210100343d030b80c03055082c1c4411009005030161402c0007000015030043d61b0044606030311031a00c000340720445440200003220110020010000e45100d01e0b540300004142c44252041c60203090003040f038903081a1901c000c00d800100c10060916800580c9002c40c40546d00d01419000d4040006031904858030141402307580c50b44002000110f01e0f82141421008090341150b6850f801d9500200500060204030300ca8011007000140d1494450340d103c1c01d8a00041100849682d036a0b5280100c413190340c0010705003912400006450700ca024071915001c50700480169403a05c00d0f204006840314001d124418400302c1503401c078040b80c20541aa80d00c9102d45800c255504030f4110007032520141c580c4007601070703503081c0360315803c100c0117601404c1201e01c4985034564070748401c0c0c140f94680c0500d0241840c40c1d4020310000314140c0b1260070440c0c001d4022810340f46401c00030000080701e4000501009813030751000003884 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 896319271 1250 896318021 896318023
    0x2a0618050c1002121e13030305270f0d2d0309080f060406021e04090e0118082514010c020d0c02150901030209120f01110307170403051b0609 62
    0xb2011410b51000d0500c041e044090300c0130342c1c010342c0d1000285040284031003642150040444051145010307840204a07505c1c500100070350b0040440640c8aa100d401181008007107001506030800018884008038859009024080211082c29210180070240280c403110580701208501481010010031009607401c001c5c0c1200000c1d4800b00307903540003c1c0c040d00b40705004950fa035007041d481040503a881a442d1010306800ea41e034515070040513800200080c11400c01e45c0702246a00c1100024005169001b01440b00407000030406401018104140d031307002015041c0b00512007184007071200843d007094560800d0640310595200c2683e6580e80f442a40e10b4040200070303000401c40c50030418050955010400070400a84070078a500750100e03080b002030f8020b0701550441c490241901e0740d02140010010f5646010310020000382d440d21520b030390078003c001d0441c3e100e0b000c01c1e106d4907490070b00034201864000000f44168208a8180f0030305d201c007400c03880b6940036200c240c0000e010700d0620840361 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 896320521 1250 896319271 896319289
    0xe0913020d1a070c120804080f0c0102090f12060a15120b04021e01090e040804080a051c030203040b010e04030207091b02070b070b0c03100807060f08072a0618050c 72
    0x3107001c0c090344003800c4c3c2c0050050644c200c5803403482d141c002c10940700e900c0c00c0441c60040c0512541202070108100d0345100d01503018154504045030181c40400c104024404204540c0c10748074655007010002641340c540e02d0300f002c0d41e0000c00038103c03200c80d5130b036544c00010b0381610401114a0031081e000c0c40300b50301d0a01d10100b516107100380d00c540c0280042d00081c120b81c02a104044130720112100190a01c4040ca058030300900c6d00f1419a5910265031500039152144c901402c2d41071803c402c0c1d0140240d210380701340c7c1e20030f591002e00350301c582c3d08003030302480d4000004100310110720131000040394071500c1c0d01880e94000012007103001421070318140a030074412180c0120194030300501001e00402d0480c04100c1c0c10001d130007101da07a80e807500b8801c130162155a4022030458440c9040018001d80d0000f0714403480000780c1d07a0f420107a140d6810450f1036545240407454500c0450b50b5415042d111840800882071040d40e000402c0481c1c0c03000c02c2c2c851221010241c82030307000324040480b541002d03001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 896321771 1250 896320521 896320531
    0x90608030f0f070f11130506010504090b0a0806130c06110318061e0d0b040b0d0305090a0b0a0234030204321803030709090b1201090c0f0602030a0e0913020d1a 70
    0x1d07c003e16060b800203205002c0d620a005000303450b800380e40b080740c88042d40b14020744546000e84000f49056011454012250b00c400c48013501c202000040300c03403007030f902c00b00002d42050286141c041c0a003450f2002800e4011a10790080741040320b00c15104030443c5542006040c07030360480e2a12440080c01c4c0c01c0b0790032400c0c1c07140582c4c10b04002c100b45558043ca00f1070401e5050038500d485410000106102c00ba0a4210140454002400520481d00000e07540c1500c1c103103c100480780e074020741e2440507016a00d0030321188400442c10500042c5400d0b0040150390f21001c40c12649c0409040c0040e40100088201e800307040f500c00c051102911781c614076072522a00c0e08008503c0c2d8107007074500401e4507005118034548941d0f03d0300d11295079541d000c22481d01c0502032000303020005140c02c00c00f110490030311502c0c100d010840000102c0c1b500201c156100d401c21030f1174040e8581c00d40d01c2806080c42c4000d040320101c91900c504000180d4406030642d80840c0170302c03031860f03000110341c0f03085005c0a400f0300 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 896323021 1250 896321771 896321809
    0x6060f1a03072106080f0d120b010c020904140d2d05091318030c060b03061308030601090e0f160219080904230a0609090818030a2307090608030f0f070f11 68
    0x41c9009d200c0e60840d800303040140d81171301d4038000303550703107041c05590984894014545801088200384035607070b01031010341003031102d900c5040f0100c00b80215a00300d41748071070801e40858800e015148446c0350864980414091011000c140b1803c00660300080c55400c0c40e08602080d0b41c094410f0a1008a01c14801c8585095008002a0070700e004200c420210661004208140010003e509a40314240307140041008a20050305810442044010014204c411100c0a0483c0000c20600c2c0d1000825082c3e428000155910203200c5884840f2a5400245419000340e1180c54a0754064500a14494100242c5074403030000c0c100030405e9000e840c0c8650254200300d0500303070040041034445040344c803584040084282240c0c000808203061020380070300900a81c14a40e071a071703c8001002240440b8290321800d136140c40c0e440303401070340c00c88009001e0120349900a00c001e105c818508802480e00c0405051800d080583c03960342e600c005500000125461490020406924201f02d5011804d2000b121 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 896324271 1250 896323021 896323031
    0x306070f0e0f0a08030703020115120f0c09060311270705090d080c0d080903040f061b06050a15270c090e01060509270609060a0306060f1a03072106080f0d12 69
    0x2001202a8a013400c01a00440c9445522000c100f400032183cdc00400300326005125240d520b0400e0718504144081c243c1c0215105240300c612211110711564021480d120f401c0d05076280c042c41290710750000400d07241c010f41440f4024022842c02400f9187c00000c5d04000c010100e840c1400400d250301c0076088210369401800240940d00f0a1346000d0b040d0b80f028a441c1d815805e1141c1e13690b002120381030000d00102e00d81024894884003e4000b100c90014072041a01000d40d80d00054aa075055a1035010302d0700c0d0503c14629407100300d50880f8181010900d4170150964540b004014520000c2c0d0000c4049500026810082e0410405d40318860081e1140d403070500406428103002034030000c000a100f0815a130020700d056441c240b00001440d0001d508000340e136140c80050004171498041c2a0428080c001190f08000748107044a12139149651440740329034070040b80c3d400b4029480790400390b09d9182e034004565004200084c4070030342002402042110030b0403401601c1c501c7e08110144c0d42508203 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 896325521 1250 896324271 896324279
    0x30906020601080604060f02092d4f06030201170f15011e121a03030f0d0f09060b011404081e011404030c0b060306070f0e0f0a08030703020115 63
    0x41140ca900c140c0100020401030b014042500027031150a000035841401030000d1840c04070710547d12488000810b1044c0713140e00000c410020307504140d41c2c084c04006481e41c0043c03a01442c4400700c1c0300500d21291110346001d00c940c15039085c12a2640903a0900c0d5450408000355a4490308454660001c41c44514690030051500e60807004014444003803000c00325251042a403281c0546031030f804505121099440980800600d50803001c9040e00c0c481e811300c1c1c2218030088401c0c2c09a2888440140110701e88054a0b0051402d13401c100c0d20580c0c0c0b41d90320009075405031710500402508502c149800604030b600780c00050b058840c0702014000e4414244001d0020a03c00103401c0c60240e410a50032104604803041507024012032840c40070503140c0442400105034200b000308071107510884885000303550300c1051698440782121010005174188001d120164000c120440114070040c000711503800000d000b03e42022425401003441ea800060240705155080c46403101c4000540a044902e03460 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 896326771 1250 896325521 896325523
    0x5151605160f05120316020c0a080307020910180504140114240a08061801020c120307121e1104050f01350a0f0203040209010306050a18080703090602060108 69
    0x45035005004540780e007450740c03d01008128401601000880007992450806071501001c050b007030485000d0300c06c003020401c80340b8041368140103075100b41005508014080d001c201641d000600b9680031358866201c00b04500000380b0320380d01c090050340380100721400c240c60954034208200c1000d00b800d900d0541e01014000e114004180c02080706004040c5030408181d241000584401c07410798000e00010300022400008200c0d80c3c442c101104130040c1c0410f100040900381d1107003102c2c141090700311205008002c0072480c05180c10901c1841c002181a4112260004a6940c03140c40320302c3c401007a40d500c010782224002c00528144007490203090a2030070002c20300c81c95401742c5c89810b00c811248201862080705008411400b2110f00d0900c0c0c210300c0c81c00903c2c0d425820b07240100c105041186074241c810282c001c0728040e036800360424029a2868450400030300020340301051054a9101c1800b11912801c0c11000303c5000c0d4005555424181c0b0300034100810355480001550081030040100d00b00c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 896328021 1250 896326771 896326807
    0x4030309120c09020f0c010f09031106190203150d050106030b0a110d18211407030f03150b04080705180106090b07080d05040f05010617030a0c060905151605 69
    0x340c1c150003603201d00c01c581d4103410f14001c4101b82c021a600c1e002004040b0720858220f10281e41c041d44801145034000c030f03400c1c1e45460040719200d00907940168902901e820710f0340219888040d0f2071803440ca403080140091480080024141c0365a91a41402d00600054104507908249506030400040100510550003400b5119000b040c2d6035580040c11032900c180000780050f5a84450304108240307a00c4140e012444601040c48001001c0000d0025110701c518200d4092541584481854850084c42100030388403580303500b410907088910020710f8102442c00781c4058045400a021034a04002c14001d1504428080c1003480004c0001000240c2d00a0780201c01c3d10f48005031182c1e255040d041a54040c410001219045031620040100380b00200c1c0e00421a0342c13161000340072255035140c07200ba001500e510310303902d01e400c01c0028041c034034010402ea010047c4240000320710480300d600c50a040c804011207051203500e0000070172200b8002a00b04403590b0b02541081030800d2903034140c84020306 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 896329271 1250 896328021 896328029
    0xf03090a05011101090204020c07060206011a0d0b13020301080c1521070905030a151b0801060c0321060f0b0a02030f090f15090f1f2303010b04030309120c 68
    0x2440d00700c00c21200360039002880c45c1500a442075513a00b017401c1c10166650400e100e0000140104000802c1d00018181800800e8003440c02550800c2c4424207080e006094588103664003a4401e00001e207041814005580240903490280a4940b036640c248503200c10307902200c08842008219884034513142035280e2241d04101141505143c0c3d030036405403031000345600710543c14403895100e03008208409904204481d170554050007440c0c043c0c0d840d45008424040c1e424045510600184031551050031030b600b809000b807410b0508040e5040c4541a40007400195480300c0c0e4954806101e92030903020b0003402040d110721280c1c07410842000007901c078004c0f5100c601c11100c00083e1a035007565051242c9451050082c0242c4030720a29000d2035003a035000e40390480c002e100722000c4408601d400ca0700c02042d00003e11241d802c5070f00800c800c840400105145142c0301c3d0b079116000c1840f9207005d010f107000c0c25034a84225515829801d0142c1019495445208410641448080003c0d1015800e404031 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 896330521 1250 896329271 896329277
    0x100f050f060409320115032a0c1e02030729030a020c010c020a150903020c153c0a051b0c03030d1508150412031b02030c0f03090a0501 59
    0x3419400700d0511006402e841c01322100d5140051080c0c451300c961452038100d54103003100d40100703190840281e0990b00800c1c0000074903040c0c0301d0b0702d202045d070421484c041c0184903d0540c00740000c65440c05060541054065012400300d4980c20071400c0c00c01201c1d0150503003000c80c041d444034003c0d40004c04204800744450b00300300817010480d14901a010303a6401c5106e0002841500c24110340290b90700403c210580320060401c0d450308551440b40300300e024a64056014002210030801803000500d130505040650100030858400c660004410072585240156400002c14004c40902d015184402078406140d00c0300700b00c42c40949400ca0704031104004940e503214680c44c0da40c1c0f2124101488450b2240d01400009a141070390070640e03000c2080821440d03c81418551103004060f95440070141c428100522040480c01044601c1100400004185408245031885d00c00c0340700700d40c81500140000d40d10114018030010005d02c9007a174000743c290021420310b0384120024046155502c500d81c18 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 896331771 1250 896330521 896330531
    0x3020a0b250302031218070b1e07020a03050d0c062909060310051003031206050117040f0818040b151c11030103030921020a1502010212100f050f060409 67
    0x806000307000b501d81c21101c0c101a600c0c00e1a010b590740c1da040d086c010940c020b0b4011510081000400c1d50301703588101d18144680581414030380da411a207030b030115005a903c40400000040020010004500c070a400d0baa40c407000d441041c43c100050740c581d40c1c4400124400ea191804801c5401c68140701042c1041758082d041c0e403108008a4103040c50000d4170032a031410003080085100030f6a00d1300e011280300307640d0510b010326a4030071081200c00600403140054201450402076000c41c400458016024203d4006440c4903652241c10b2a4440c15100e0050034a543d81c4413000c4c980340c411100c031a801034800c00c1d051810b050410495100701d24a101c1d009103603c5007075000c40d007240d01913500b400303040030a580d895031030303050190a0300c58510404e14070b18445840183c0328010600310750642540a01283c02c0035051541000111750000d0130041107650074040d00c01040c040502c4140030300c15071241e00313a006080202d1410207180c241c02030740c0a00c18125584100d03494900032541111003a90740007c03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 896333021 1250 896331771 896331773
    0xf04030c170303160c0605070807180b0412020310020a0305010f1409010b030a0603020301050408091f0c0609110913050c061e0d061206020309060109050618060f06040b030103020a0b25 81
    0x5d003050711800050b01036450300081120240e040710040d400b03a2070646800001c84100300f100c150002c01c40c00f5541000d034080c170040218050154469142e41d10040c252041c540001c1c11036000c0303822180058000940310f000400c0019100c000910240803a05050396081c10490080341986034184036613121a48004005a40802507501213805076600030000e100324203150500342c5081c0c1100b40060304c40c0d1107049500c4418a64070301e6030242c15003d42c40740403505640741c2b070b03d0009000099056070440c034000d62202d1913a9402208500c103038551130704c266141c941170410300d01e40004c02d005140a40780400501017041a2107800c95005a1400c4441b99100990896039024201c0e40e88109500b00c6800002801c02001d41c0195204040450031100307107a03a0384c10b80c00305039030341074a242e0b40100400c0180000426400044e951091010b130802000114400c0415402d0b0b01650007003460260200061045142c0580d4080007440c2e00d4880303030b0400d00000d90446401030b06892116401200042e428 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 896334271 1250 896333021 896333027
    0xa05041404020f04020f0d09060f0501120b0405010207170c100209010927060e09010c17010302040515060c010608070803030f0c03040c050303030403050a02152403120f04030c17030316 81
    0x10101d00c1c82440c01920341247c07110010140c540404100c6015040003d2101c0721482c40c41f45038100d84218003484069881130721800301003000600255140d540800030840895017140204001c06c440b80049582d40a900254904084850040d01e00c0280104990000d0b6070388002810f0a82e10440060407001c071081454607403500c1401059801c10f070804200050010381c40702d09601c20300c440b0b4001d1140b8081c2a000312810703411020002035542c0520010b20250905511044c0c4c1b0030400740030001140344030310004603541c2041c0458421603444620038800300c0030512403a0300509003c00150f04606081041003005c440080040d94420008400601806651401000105030140581e070b03070390030541401000da6100b41c0c1da1a01600c00c08100303001200301c603840305100e941011940414290030844200400403806e120320760500c545604002662200340007070000c0b5120540003940c807441c615207003101990548c0204506281c01d81001c481210100c100c1e0b42c400d000f40d413071020b50851403c083d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 896335521 1250 896334271 896334277
    0x150d050304262401080613030509010512090d020708070e04033f0605060c0d030b030f1005010e0601050406090e2e030c140604090e07031406060a05041404020f0402 72
    0x65201441807014910700c48004009980ca03410158030307031083c1030b0388410b40756079203e00070b079080e0b15a01d00f01c030354400100c0c0c883c01c003a04940105251052621040c00e010200101003a1200050380c1c200b00003490304540c0420640c0001d01400c030180603550300d000e405820300c4800030700140502c90403218514983e0041200d03510300344503c5c000390701c03541d00035001100c90307080348900d000c506482d040303020a8510b46001500d280e107004100074044a0b00c01c48044001e03000d05801c05406100d0750b4010700d140c81085c40a400d1041809900291540c0b42c13004250181d070703010704160f060100410040c884554000451030030340307800c290a100310307881c0e48204000c0c1c1429002400c0110202d80703a101c0200200c0c150880440340252004a2081c0d01d071600c1c1c1e03c00d00140303010198440300400080150003116046240e031145801d0079208600d942c1e86990000808014509549030000c10801c1070030b16180400101815041d0340070050080e00c82000b11303c448000c0d10180c4a18545c1a1607082907441744c0403 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 896336771 1250 896335521 896335589
    0xf15120c1009080f0d0906210914030406050c070914010306200307020a030810050f1e0d0c03060c0806060304060f0b10090e15100f03020f040e150d050304 68
    0x1c540d0700c0010040e2540d105c2200c02140740001301c61030700004040c0d02ca800031230804543c0d07000a6000700d0b1144001c1c8020260098221004012041e8007466140c00740040c20051805441c2c1d25542e0071006d9410f824040705070001380d00c41e0720f42603410380e4075006042d039a410741c1d0b0302180c00901d00100700b00340443c00003035911410360b01030000304102d446513000c134414000c144203455211140e102e03080d1551560a580c040c450304201d200407ca20b00785000003180c3d03031001d6802004941c03c01c906002c00e07403e00c060030081c0c0d41c01c00391003020010403900d441140700404d00e6103441c5500b400c0c9480001d1061201800c06030140c3e031034a4105a200c2c201d5480001840001840303500104005030340585100354038806d04000380034040001d0f0041303000041c1d0300512400107100503a141e12407201641c07107950340c1c641d003020503a00348242182c1c81760040091003d4502c141e4412a5841e00046034860b04142e008110701420010b02c81d500015400400c0c1d80545600405031300d1102c4140780c0290794582c048078 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 896338021 1250 896336771 896336773
    0x80a1b060504140d0221210f04230a031d180106020f0601080319210b0f100e040507270501090506040f090203040c030501050f15120c100908 62
    0x802d01007046119140385880000e803509030b07580011900d80507a100c660b04108103c1d00141099582240d20120004154a60000c103004840020002c564080300c4411180c81603622060000e00c014048030044400c1038030300000d0450f9141c085400619102e010106008061104510040a02850790380302034071141c101419805c3c00011040c00001c80800038401d01d0054015154103403500900410700c00d0607502c0d418011440d1034a40301042540034240400e51080107007450301501c0481c000003200100807409400854840726403c10091000e1000400c05c1c8207140c02240180225000540c00300c400c10704603000900780d500c240c41552585004e072614110510000602001210144019000d80d8420390f40c0c48140d68441041c0012441680295034800d01103071020030000419400455201d4030560691a506e0360740e9403800c1c20b68400795481400d81541c5001c20440e10f030588815240c0784170071941405040060035115880d0440960407070f00500307c2c859010030395405008d8910040c19500 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 896339271 1250 896338021 896338031
    0x30040504140420030307152a14030f0f0901021e2713020c01110406080a15150302090607020a06020a0b060d121d040e010603020a12080a1b06 62
    0xe60759000c1e045080b1030855190403502c022089140b02c0607142141a00040d0003945005000d07192101c52000c2e5110302a4400d8403842ca0003940341c001c84200c078044a20b006103c4810981d000c0141802807100003000454006008200c24064103260450b04800110561813241d180e14800501a03c44e00c6490092404040511488405104020070b10000410302c401c0c034903001d8060200408085030360882e0b12882c0b0b100110005e41c0c50390700818401c40041c000051a00503050742070b450760040e51007400420011010401102e031140150b100a03e00c03a02d0140b102401d10380c800c2c0004014400140070980d01042e4084284c0b5003030100c54140c0e4000707080b8442d6550360840207690b5440007408940955000300401c034282042420504900d9100803a030229110b0131104441c54030005820300c403d092101020803107034807640718001d00c403200000007149550450040c80001401603009004202442c1e41c03c00208a808040d1800301c2d4142c540505101d5105946030f646025032540039103100d10f42 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 896340521 1250 896339271 896339291
    0x1e070302070911040815070807050c16090203070e040605030d0f180f1a0703020a020114070f03030e010e0a0b040f0c0b0f0409051503070b09010504030507170c0330040504 75
    0xa001810444071300c181210712031906070500e130b805040c059070000c0c08100684c0c00709270f1660040020f41950b041c840f00b2104910507e0440700e50410302c940c0114000c640c00001d1040071644a05480560803003a6000e0100c2d03440d000101e07a5030f2642d41480b03010400080c60060b03280e0301c1100c1404c1d01f0306040b036030040010740b6008034003880707000361154035502c01c031954107042401044029202280e4142c0c0103810404011703001540d0195200544c0c0309844010825500010640520140c00c3c6000b541d0020724041010092400c54034000420885580030641da00d000070140b504281d40300754420800366601d165480c00606009494000007a8000003140280d103003c002d40c040c0003118070b9060144100c2d01e40d6141c1042806202044580613001040c1c24070044174444001c202c48030040c94a20304d171658984446041c068aa04406400101560107025a4004214546400204401506d042003204400348070106403a11044c00d00b40865040c2180709031a0020380b0005d0070080d2060001c0e07010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 896341771 1250 896340521 896340551
    0x80606120421020105091002031509151f0c1205040b0304030206071812140c120616030b0603280221070314190f020c0c1207050105071e12180b1e0703020709 69
    0xc900d803003078041c14035480c800c402034131500c42c40500c5903115260518036071410f1312196104a28fd502c0b140610004120020300d00c8100c9005520a90081e03015026900745403000401140c203880e40142003028203c01404074513401882d0307107405c541c407143d0034006c1d1280c02030300b5080110f8460300a60101800700310460050b030104e081881114803100020b84400d4a14040c1d040710042100d5940000c800c1c0000b41c0c00408051402810740405005140c41050b240c2c64001640d014070141246441c2c15460044105480102a41c00a409040c1885440082640680b44410003008018080b10418442d0b0460000c3d41c4001701c0e0110301780c0d040d965040c2c49200709565405c1080018009ea001d24003540e0114008503212046e20300580d101332500505031a20f03811219820100075455003001030400c006400b505c2011003a04650320f4a1002e8030b28020a561b2803c001da01c01c00c44000304100180c2e4a810300e104824243d400880038648030b035035a040407880c054094000300d1015152034425003440b51 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 896343021 1250 896341771 896341801
    0x20315090d09051525080301090c090b070203211c02040509070e100f14161e0f03110102072a1e06080606120421020105091002031509 59
    0x8400d85842419940c0c5106004c0ca03698541008130f95424240400356440c501d050440160302d1480601c814007540c2519090104d034800c0e4440c032040341c0ea84020648094000c400c0000501e100060681010b0003500801d40f200744828200807506686c1031000d910414081c00d42c0c9003c00d4642d012135010400359081c00096000d0f000d02c0388510150313000515854880c030b11803100d00c0800307482c1e08070140c0c80d00025180b034201d00d0700f440148004003058442a0000a0160401e40b000303440e84596100c2070300300741c00d5203596882c11030100e0f000300c4407440101e401604a0002c440c1e00d480c0c0945200c060042890084c0600e100c000d01c03210310750f0304030070b03aa005000d40e8071040308004d111946400d9462080180361070703040e84400703100c91160030100841406506203950120307010340400e15004011f00c050342d5a01c0d0440e03049456007004001540e0030509042d19142500c4d050008000f582001034040d070303803020713054002d0f5006500003000404070485070a800300c03030b100050308610840c2400564418401 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 896344271 1250 896343021 896343043
    0xd0605040605061c020f04080109080406030605060f070b060103020c100c09080d02060604020702240a0e0d321905150609010b0901140a05090a050906100c02031509 72
    0x9007000c202140d14a0000e04549402e61900445246008445071580c065081390040041c0d5080c01c0c44009045038083c0148401e041c4600c0405a0396070500310007908590050700501d01482c800d20075201c1840c00c9a04852205400000e0750003181d075440012000b030700c070b0020000b28500440807101c480d41060741110508841c44d485007907200b51100640f0b651080c0317012007032005034840360202c0e8840c102f0750300800642e40040c0559004800ea08042032000c60308204000078038130b0014403544425071101d072000e8292000c407001a41ca0240751601c100301c00360340c0400164513403c8540c061a51041014490b001c06500d01a541901c1c800414226088030b42c03903007500d4a0240c04842898521840100c0707101c2e0200521039800c590910614400b20b40100b0076150501486508220480c0e1405002d051500c840350743c2d442da01c92500052103260000d583c0114001c030884001c1c020b042d5196909109410300e03602c0d00c0c1400d04214000649400003542c2c0340b00b880a058004c3c450701e100c006c11800100 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 896345521 1250 896344271 896344279
    0x5160e1306150e030c060403030309020a17072904090203070903060e010e1b0109030b070306030c0b030a0b01082707030c08031b0601030c03020618090117010e01150e040201140d0605 80
    0x10512103c2815150700c030300b10165510440810003800081c0c02944a1180381d8000b501c140d01c1541c464040e40030114400030b4040041d449690100711602c42003840e800454410080038644035005038840400707008038001d03100c5098000c00011a5103208402910040da0008024098021380c0c000b064007d1015a03980e040c107008400614004900b0500d180d10343c460107a440030b484c036256403500721002c140642484101601c0c0c0600202042064590b03c001d454200c0b4810745d05e00b0a20081c4085401c0e011480307050117900c3e0100440d40f10300020411a040c490041c05116150b40c2038810304024003908010640400034074086804c2c4000009028901c002d01c102c0c010032550800b2003139507408240300040803c80e20750400d10060800b00c010b13107070729054442001380c45000b010016900041c00d13000b40d4030580e0746002d0244048400d00404c2154800e0341c008000c0c3d180e1122a8a920610901481c00300214880128045910800d14151a2240036240700e1300c071950781003070101600086c03203441c1c45 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 896346771 1250 896345521 896345537
    0x20c1504050f06031306020a020313080106050f03150613060b180405010e01082e05130506010f0f03022809050405060a0c0e012003070b1905160e130615 67
    0x20b40c02c100381100d000d42c00c2ca00420459031569982c0d840030354420074900085000034050300c408482c07461304200103004000000314200f0b0415091011002c40045010b21075841a480380720307001c08000c0c03200d8002c08281c81c1d001441034406030307003000381c4599400000c0c032940008007640c4a100c0c441011540e88011030702032241e03981c1d40d460075420f00820300801509421141211104005001c1501103480c14015082c10390700da9015548100c4400302c501e407c0600c0c048807050101700040c448640905010510301021604080c07020050752844d00000f4020750203112081c24000d101484001502d40c030064484d40c240d15a2048005820255822141031040741e01140d0058241e0140070070b0204650340c0d803c18444000011544450b01000380d50024503d4039000c10340d030005000502040d40204d9207144d190400d590300c072884d030301005607002a16280c1014400350079864120702c6c2a034110f03454000c54205407040000c0d611184200002c15003441c041c000103040b084190310200a080075114140 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 896348021 1250 896346771 896346799
    0x3090307080c03030d020a14030708090d020f070509100308191409090606030a090b0a020714190201050a0e040204060306180507091205010608010c02010603120203070b041101020c150405 82
    0x180c1c8000015620f50315810910109107442031036030150180002920b0107030900303142552400e0b6242d20648003000000e61100c204501e04604005c0b030007100142d480140600c2c61620006600d038074960003030611505035900425540a54011003001443d00161415a940185901501821811415040030030080c0700003500ba4038408055801003030001c2e005c00015a102c108100d00c0b41e000900015189036608010408100301900381d0340320394802040184e440341d80f401c00b120b60300c1042d003103040301b544012041e15a6442010350a04102c0e4282031041c0ca40b4200c0701c1c103403404080c0b144110380061010400181c043d40c9600108100c8140010420710031075149401800c0d180304035032010202d1030440c02009495151908069514081c00c00020380c00d403107802c0d242c255449180c009006079101d40c02403090004074a0464a442e403107000031803030034007207035a2010b840d0402003004c3d184c881c51114801144e4024841007034101b038014240d8408110507000c1028640060090600420401a15032 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 896349271 1250 896348021 896348023
    0x1e181d15011e1409092104060318020f090903190f08090309030703020f0d15060e1e0f1b0a2a0c12031b1208150d0210021c020309030708 60
    0x8015500b0003043c40c10340c41004003d0120b00d1602600c210818030403050b45800382d080d5002840c40b40116070040715070f603525001e0001d041ea030500911103002e0070301c04e0341e040042e07803000c003036850540c400d985441c20360760b60400941c20f6000b21120a1a05402000051591a40000000710b01140c681340d00015840704540d1582d03038004d0112494160b400950203001520300f51640d4140000028a03c0030761044035541d00c070480000c1d90f0302081c2d480d02d0f0380c02441100b44030400780ea440f00ca058140e02042c804c188841250072b41c040d2040c126404880042506603448141440705950b039021184e035101c1016400500b84081545600304060341200307400900e03a421000d08010b43d401586902da071a0409804034900d203c10307181201403144031401c0d24922080f22505d145050301502024002000414010b05500c42c018000202c40514040074509662014032104103982c041c0d88202c01c0007034580042c1c2c6020b46802401c00400c0e1501c020320b4000d43c1c00001010b401c01c0a03402e481c1181d41d80d105031 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 896350521 1250 896349271 896349329
    0x11010507050c060f040507080d051b0f03030705090a050a030b040c060323090f011112070516080c0f011e1104080706120b15041e181d1501 61
    0x108055005030000c10a20200b492030250843d00650503647c1c4a81c1e01c004641c030b041014207661011500204a050b030f500c4a01040c4d18100305804040d0100c841180042e50726440f00500d50824403101140d10003850b1141020307040078060140001a01507160705000c1c11140086400f00c0e500761558802290842c0f01c0d0061038058010400807400c8440d010348485500c1800070314240c15440b80f80d00d503001d0704009004580c4e840389100b003215550404a518003007010780042001c1c00b807003410445808041129000c0c000b260341c22007202600d8a608504250404c0301c480f141464541c00d010050300f228080c1c0c07107078840c4840725040070042d400045254040303034041c03403080c19031030342042d003040080c18000c0360f9402800303846107400074040085000089207003820100c5000c2c080c1000c41c06003c42d01c2c00d50310005441e180ca00c840f0381c0302c41c03508601000c15003660381603007051134035001c2c0d1f02c01810352103c14000c02c640000554848600c405442e4000c60801d11600c15022005807802c80040c0e0840e00d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 896351771 1250 896350521 896350537
    0x40812030a0f1506111516020f01020a0203090d0212060711012a030504050a0f03080106080105010e150c100e0a1e11210d091502030a1b0f0807031101050705 69
    0x40f001c1507514000055400034061404090107010b6071060b03c03032100e068400903101e400440c200403010310340480020302d0a0954409850241c0c4100441d08000d44c00109a41d01d1003c210340901308070500340f003c41d4880c1d841742040f09041c440c482c184940c242d0480e0303030200c15210f40c0008100c1039541140518040da2704250501c4c101501114980500307210350407007544140140121114200d05a40f044d500504c00e640940c002024100140625170340441c05c2801000d007442c0520000007030400194154010048002c207540d400100c40c51007050034000f4215890300c0210400042c08003040d450f0b280e000103502101e0245604111030303030300385103400806041900600c82070028107001041c04210500c0c01060010308105c042ca50b03c61440c10003500c8042d0031165109980b891a09410500140a02c003510055400900c803015005511012400c130401a80c4800c0071403a115060110360440c501d54050482d01d8001800002d05d9000080c140c003e5152130300070862aa955030003103c9601604030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 896353021 1250 896351771 896351801
    0xc0c1c080c0c040b240309160602280302100509073203030418050604020f0a120506150d0b12010617060f10050d0201020f3c030a080a02040812030a0f 66
    0x3101d400c20004400a950b00074000c07c100c2d600c070490071410396030200542d4480d9005a00694080821031280c406441131003251140c120268815664042d40f00c1c4112541c11001681c2e5100107540404100005c03002001848100020340c0c182d01159508200503050b000180c00048840f03044505000046030111401d02400c3c100b0388a0390717200c020241034050302041e0b1154092001d00e40501c1e426008002c10110740e1180302c02d04102d034248409035040140824403a6410609a40307095000b00c0c2151007050600c600002d024007604000b0b040c6050401204802d980703890030200d85081011401040405000101c500c0340e924003102c128148002ca0340070141c00c050040411031810000c03000ba144510500580c3c118401e081016841c026070780c010180d808058145800b01816411140d4254006114100b0705d0030001c5501c2c0c43d580c0c07059030184801c004011001800444641c1e054a01801c111005e9441d0000040f41c81c030038680060300d440d8140740c40c00700d03405075803d05881440c40d0782003039007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 896354271 1250 896353021 896353069
    0x4030311060606030412121503060c0201060b03061003090f060926120c210114030a02060316180f1a0a0c0602030a0209090405030a02120c0c1c080c0c040b 68
    0x25450440002044144100340241c1d84464110b5401a0058a18010384c623104441c0031032450401c40d042d00c1d14140b44100b90f91500c0c0b01400f1300243c0c0300440b41d000380c0079149105d00c0780620b0703030850042c10383c8031014048185d180c04030f4040103c1d60f00010189800303903544810010001424082e90041d03160b0000808008101c102d0410050400c0305511207000f42034942402101c46104010440200c16070359005030075401030001031200f030742100000e481500108604035240d400318149200103050a600368a0316446c0034900d910a81041c8880e48061080c951521360352484409500d1090140113007041c001075172951405400010b941c44101a965140da00010035103850000394806801d401344207808019100e040c2d02d401e078106014922603001980d03a00d212040080c100048003400b01e401850404c90780c4489600080d040d20940002c549a81d209150781d00e0102d01c10300341040091403180080345910b54050301013260350340c55501ba2003e2000300002c1c410008071101c00d41030425100344070 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 896355521 1250 896354271 896354273
    0x307060b011d04110c0f1612020a030b04061e02130e06010819020408030c0c1005120a180b0708060f27103c050d061a04050c040303110606060304 64
    0x10303801038144c1520320351200f40740000e40d480007800d003208103001000070781c05806001251030f5481c07080710040c0341c41d8110300708641c015070010300078076045d00c00a452204072101182c00e220603036110a80b0032000c82e10707060000541c00710a101a402481240001c40e82c15540003d0420094070080e1081d103059480e92041d076140350103d1410382c0d04104211b4010350920020070a00010030042004207400001010500f580c80108100c80c03d0401c400700400c40180a00340c07c6e04a201420341d044410000d0201d0f00048120825017040e0007014080c149a0603002444021508014602d00030501990500d151294400c144618a4031500030000d185e071004034203d66250840e84501e40002541c141f40180c1075503034940c09410005000303c034112078000b034581d2900500d02245040c1c150402820201442d14010010762503143d0b0700c4000c2c2c410341c0c070350341e40740e101c038403089003c00b18650018410401810088505e0303c0c11f400c0360008401048042da030381100060000f90f09480743c40700800316880c650340c03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 896356771 1250 896355521 896355529
    0xe09010506060702181b0d0e1c0905010f0309020a03060504050c01111e0a12030e1c090b2101030303020301050424060521090a030f0c030c0305030c04170307060b011d 73
    0x2e140c11520806d001c00c01c448000200c3c01490540301d4000b010a001c0f00e888441401d000410310314180703103800c8003280b01d00070b5000b44146045034400d00300400c40d984941c030258044c1414500003036011441210100422000707504c042d0140303018604860715605880015640d400304041c0d4a0030300d5101802a1100c1001b0134194440c1c405004183d6801e40b4859031000c5060110b28503e0000c00e440f6111002c2c041420000c00c0c0d41651030100c400310000d031403040540980128003c490800500048414006c401c43d00b42c00000803a91a85207129a96820010002e400c2030066030701c00c5052509920034410b03e8a10030303c0c411b0a032860b24070103515000c0c09903465071028218030019510000b202010040c4100520312980100c0c000d4039034081d507460000c2041e0051540e003000e1101a659204c0481e0b4404040103a0701d40c5406c1241c2c1d2a21900e4001d1140d0066a10802c07a601c0f03805490480e000010016040300c0d403080c4e200380051002140190341c074403000700b0001e48110500b5503000c1e8501d8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 896358021 1250 896356771 896356819
    0xe09010207032628020c010203040605060901180f0e0f0c0102010b01031104050603180a061a01091d040c0f0618051206040f0303060515120709050a0b0d020c070e09010506060702 78
    0x20104013140b25468541c1d003000280d030000f413508031860f5808810401440b8450044950164003101c10000541c14401c50001c400c09106a4181c41540c3d41c80d0641600503542c48410030751405000c031000000685a1184d8a030031300c1e0f810b14015400c05c0a01d01103540240180d801140440b0140390402c3d0070720301440f400340c10040803000403a0312079900305a003420a004810086000c4c100201700e04c0500014048650303541002c01c0c0c10020780407001c00c0150080079220303001c8850fa90301c8112075111820818150402a00aa05282001329001032429005884c079900d4580154081c29041c1c0d80720708021040700c0280c000b2a0580028000500044c11420410002c40c481d080000380c06454802250301c01d5a0619440c810000005036004071044020480c4e502a02500d48941c815007040017140b00e042e00c1d0f00ca8103035012008195600b0840481d0183c1e4100c0104804407500c0c0b0382d5885141500f29021b507603181c2954a0400454218189001150070040e00504000f40203070b1100201900c1e40 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 896359271 1250 896358021 896358061
    0x1202030405120f12150901141906051b030918190504030c15090528050d0c0c06080c0306010c05150117010c03060e0f100e090102070326 60
    0x202407401ea003a0320b803071108040c00c0e450390030954681d122580b281075060300402c0501070b002c8034142d108019615030345598140303042d1a400356000d0700c00310608010030170a203040c48800b03a6030340c050b602c0814510344c49400f402000c60100905600310603100c2d10360383c1303d100b400c0c070554201c00c00c1d207403414602e041c0f03120f0b0541101005c004414901c179108020400c031001581c007100000c0507916040c09000304035080030000160300d5020040d50800d03030340302591000c80c00324440740c0d031383c0c2c201102910720950356400e1071851300601910100d00710720304001d01621028030201c0d16121030a5020a2151140080700e00c18030004854034690384a6500565402c408c210b401c032010710030005140059251010814000c2101d8000a030300303201c10440e804d0955001071086030400d0b140c01002c000c03c20703001c14241d4001c100c01d0742c146c2068603200d000d94550905a0004c034007004c0d14030280320160005500800c01039003c4d0391000000a02002c0e04d03408100300e0120480d5501e910000301d1280c0c103001026012031 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 896360521 1250 896359271 896359273
    0x51c0212040b03010608010512070e0606090a0806090f03040b0a050d1803030c030e0f07050405060118030302030c0d14030601182309092b0207170303090d08071202030405 75
    0x50640300085000d07405500100b60160010004010441e040400c4030f001d0401122800c94083c1c500302010b03a43c24652180c96441450140070882c80d88582048503c541e80c00ba040001d0103440e5100155103210030790705040148110181802e0b41600070007680d080d07910249000b03181460f91001159950040d1024203909903550420403600510481e060003410f01c01d48002c1008051100007600b260707149810814540c0120902482042c4042403110070f90300219400035154a941c0d00403280c03c0c502d2041c010840d0000c000c007206140d0000302405000c0300041c03c0b10140341120004032003c800c40e010025103004144085440b641c000d500c0f0031012903084d000c44900982d14452108045103048503080414800e103964401e608214810503445080d000081084c0d5200c101e00e0b455004c0d14810106000005d400364544840c03090016030b005155403005203030000440c00c003c81e203941c8281d50b2001c1500c078507002c45100070701481c0414800c244030384688480d808181000406588010811203207 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 896361771 1250 896360521 896360533
    0x7140304090204090b01180b04290309070905060102030a0e01211805070b131809050105041101083402010212100501110102070b0c0901021c050c01110304051c02 71
    0x328100350b20207031008081c900c001080320090400094200c800148003074035020328140007400241460412101180c0345007441d04121108402505100210034019401c0c841c070010030306c201910001440016518071201c20080c0b500c4030340c016666480f81c0c214040120701c40708105582c0398010482c0410700da42d050320103030b018032440300c0900865006140884980340f1005140083c4081044240054054003040034645840c161180020018910034000700a0b440020303040c000103150041c060030f581c0940240700310304162805882c0d02e134400c202c060000e0b41540000c1d2540190f05c4135022105401c0c0c04a03900811041103880b504590f540c1c413002599000c01499488030b43e40490548105100e4076010398450805000528501c1c9190140c01d00381c0c0140b0000c00820b031104200c580200001e04090395942034200141d00b00144503501e22820030001700350100e00c60f044001002100203a6008101e60440c1540d0201140019140034203254000a0f07100c240103985a131403001e200301401100c03c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 896363021 1250 896361771 896361779
    0x20103051e040c060905010206040c15020a050a06050415140406020d060f030c0e072c0d0812060901120308040209040c030f030201020a0e060406170a180f150b030307140304 76
    0x5000e00094070201d50f05405030008000e03540e4040d62500103441c09202404190500c2d85411a001ca15801058032010b4404040e40b0349034003c10006000c00d920100360ba0564010341000301c001c2c40203d809588031801e030072884c0d101c203000307100c1c111180c2c501440c1d43c0041c1d10759803105030094200340d0072804080c0c2da601010403000a446a14001144921076441c0081d0925559400d81e91000d80040c05100d00401007080c1010502c68030207200d0140d51003414000c85e000002a00014021741c00703002080c00155030380e031303076007000e44000c2c400d650982e404000d03030b41e0f10070103840b04e000301d040080c001692903000f15005181c410601c13600640203280e90418142c503526001ca0314111aa0100e0150713600040c0f0300034580c0c0001302d501c1043c0084440c1390030b05141c4540a1300641111300340c0d07041c41422034001484100300d540164a501f0340f035060503081140030700d0b1100c00c041002e902691400a44a00151804024010001150703c060040e501b0038010742d4039117024400c041a10155030000748400b107 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 896364271 1250 896363021 896363071
    0xb0403030b27061309020a12080417060915060d0803040609020303040e180d1b0321060f0f0605040e070e091504200318010b0d03020114012102010305 66
    0x202c0b180c690440000c4a042900811110082c03920f0001c0f905414240311a000d0b0f502e10a02100b03c40b40c0c0300381c441e807ca605d403038050024440c6420192010048100da04042c100009a091003079044808032000c04050f2800500100b2048603030b01d030b02241a04800c000280440c0266411130720400010078624003d50000b030a5070810b41001a48115520411201c1540d80340840385401401c4098441c00380903810080c1540386900080000c010300788681700405214a088013207412800c0c0c10390b0180c042452079040074040310300c04c0000441c0301c039101246201d00704580000b02c5186c0d4481c4d03840c2510f455501c04000800511500074426111150412030315006c544911482d481d60214020b20412070802040751110490415884202d20310b42c40c2001c000411282c008484a048030000030a003c502400b4201403800703241c1040c03845c40c18804060b0150445800104e400640020b5a03882c2d03441c14100c104180445d00070300d2100803c03440594060780c085500980c8503055503200b58004050f81d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 896365521 1250 896364271 896364319
    0x4050403080f010b0c030a0518030a0c090e0316020d1410051b0a020a14190c0306060b0313020f0f0618040606020f06161e090603180b0403030b 63
    0xd40100e901d807020006103a0038100ca46002d8001c101c21641421030804031a5500e001d0351f80c4a805010f00007400d988a2940044c52081c0148014103c0341c140c0d885141801000d203080c42444d620138107290040250303400120940700c01a01424121914090503020407002c0080f2a0003502c480b10141c8202140c44030500081d101c81d0302d800008101414010f80b0a8550300414a64410b802c074140000c201c5644e0100b44440c1e01030308101041540c5512111090500f88287c1204040b190803400c07140400140d80d04000840b4010718003003019654441c051505407108451fa04110521000c144005191002e007021403140064a2440c8414000000c90129801116120142d0b00200801007852400d8083c000c082c0000c1d1010703121001c108440c00d03a80d240c02610504902d610700d003c1c0d21001d0311030b024a00301c4664400f850070640402103009001014640508070010b030070f2039010712013120001518042c0a511420080e000ea9941e2412401801154443c0f41d2001d041003680d49902c80003909 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 896366771 1250 896365521 896365523
    0xf060708040f0609050402310803040306090b060108060a091a121b01140702090a0b06030f09070b0703081f03052a0a120b07052208101406040c0e040504 67
    0x31280001d04050b07000c4e00b0844580d1025200e5401086a402d02180d0403112005c40e0150794401c10055000b10465001c281490700001c08d288000318000050140d160004c3e00f420780504116607850719013500444030201c0c2280c010f40c116020b0001080403240c264000300c0383c00c0c1d051416107503007244800001d40c140443d00d241d9240394030003080b500f1090428002c4c080e0142003420804111030450300718010500420101a00c24006200011814807070382d04007030b1b10481d0003444a643ca2401045005900c4020782d0045c080744103080c0080b458419a02c111500c840c0c0544a030b1070301d03aa80401c17481400300c2ca0011071500805c18030f00000001c40811211b500c1c0c0011000d656024000d003100085200101401c503031060003c00d008014003110702c0f8030304400d01d400c401481140e0381d031042d090300e640c41900002c01401c800304614640100c21545641d00f0b03101410240d03072510080c0c44082094030580c890810100c01c13010301054261410b94001503c2d55803034200f59104010840028040341c0040f10 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 896368021 1250 896366771 896366789
    0x6040b0915070e0105090105210f07090b09040b040b0d0507090e07140f0d0f150e030910032c010c0f11030f0f090d050c01030513110f06070804 63
    0x414000d4000c0c09100d0009001c09125100e040c52900344070081075080901181e81c14890005500304459100d2000c840a491052100b41003c0c90315214403c0080300448444820041e20b801184200707100f14130030811603d084e00c10504144e80c1404000042014041c05688541e4510f040411a150440038427002405035000d010303e071389401050403e4504951002e02d1542000c0d000380180c000d02144691043d078140d80c422203c02c002000304406121451010346080b54cc108000c0401c200001c0d50505500340c1403050100e2806100d103588d490042600807036204007201181300100e4404d40c0199440154946a1814180710aa1041302044510420485039440740d15503600c0c00d400c40394070120070740c5628051682442c4817614940740d0144080d0482600c100055008c80c010780701054034040a07000308043c1003150f035803911540e07607111348400c140481c0c24800020642c4806401800c035094008180e6020740f00d400e030402c04480c8100c42d0890303000700e051090301d010800c039501a00203400c54030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 896369271 1250 896368021 896368043
    0x2010b010f09050a15091211010906090e041104330f051e040207080c01020c0d0503060a0e06150a1107300c080d09031b0b1c0204080604 60
    0x180010216004010603605005141d9000c001d0340d11402603900481e000100c03803c068900064040700c032003a241c0c0c4924404481036040c071040c406001c0981641e40e00980703075004001d6842d0015100d902c0d6a20070244090314800015000c69041c103690b00407118002d100092198100042d00c1528a89141021180b00070b11135074030340510015100c42c0506250b014440386a03140c180080d50b0300342041000c0300020303081c00d04d9910ba42c1301e580586603d2a4454407117901d500903400024003e4110b0360001503180f148407401c400d940d004204580c05010003502003042581442044d68130108060a01500189503e02a417072600a52020b03000240c429a01e100d541c0941840583c901440740d000309600300034507016100d5041e0703001d0900141751000003203c5261032850400d003504441c1984400914010345015101c69036103c810030b4181c03489240780710603201c079101420100a9680c00703000c5002204010780c99451042100300b103c40e0105c000050b240035200c5200c5410000e0584003251045026 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 896370521 1250 896369271 896369291
    0x60a020c102001060e04140a0c060518040618150905010807181b08070210090c1809170f0d0f1e0e06010501080a0908031f17071806150201 61
    0xb5852221000c0d59290082c4a180e00741042c0d00c0c20004003620080c5502006030404520002c2440902000c40e08500041411a03403104050541d9000302110b8107035200203082c00c0d91a00c0c040c426172080c0c9000307110039803004402c661142c005008a070311600f0f1008000d81d002801100e1401031074003070b02c00c81000c0e00004e0b107002d00300d160040580645060f52801d04000d181060590501d07100450828a4101055141d1540a03810b0208002a014010342043c420784240b10110440d8001c03560b50640b40381d409045400b02c2c500300c40a03a02c00a2081c00342448000e41c048922000c2c203143e07103090840e945085211001c8404903601c880300401490f40700c01ea4220102c1c40c003d9542c2c0b41c1b01095034140135518032200010307190081401841d050080c0c0e440410405030031940003400d8950301060303403070762402c4c00d01058000f090144000c80d4410b6002c000031614200020961034a01c4441005003292400c10351602d603003074940827003002d071560360310340005c0c0c401c4d206954401c048070345400019000d001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 896371771 1250 896370521 896370557
    0x30e0609010f0c05040b07080304061404111c05100b0a12060b0a050108150915210d020304030b13020f042301050301060b0a0815040e0607080702060c0702060a020c10 73
    0x10191141d4280001030208000480c1910200c54025032300c03a40d0b0550b26604d6141140061003040060700d0140b000d03804000030020f0300b540c104400c58088400146100351450720300c0401100010082280e080800048504406a0032040d0413031801026230110a4403803c01040840081109071095070300c41201d546a8189825080094002803a105103145050f40c40d1031203e4981006203402a00c0440014180b040d0300d00d0802414000208421901c0750440042040f07602104241001401800746c0c004076640008111000c90b6881a40c0c012180c1e540794607481074004000703007030717800510350b405020700c81e940c61003054001074a0300716480f15080808180d081da02c005030403260007070303140c100c050080700e00c11029100308a19903d04124a07542d009940341c2c0121890710107603041400c000c10300c54041e40c00721740140b103458959103411841d510100201da0f02d24090b10203000150b0200004009410003100501c80140a40104e0300e40005100104588207002c44043c4c0004071662006014044 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 896373021 1250 896371771 896371781
    0xd080a0b0604120f030306091b0912050712030203430b0a1a060f040302091317071a0702030a030e0705030309040e071a030f0a0911010f030e0609010f 66
    0x38080d41d40900b4a400c000007850354182c80b09000e80340503110300780c140406109400243c060703c1d0011040c045000310302064030045100e075080b4000301e4808140803400a03608072450211275000001010794034a403012290405025640640850100b00032501c0502e0300302910702d11400340217500e141e56180801c400f450740140c3d4584a1240b08920b1403405c0403401030802190480c004910000c2d0401004099035150010300200790707040340380481c0318004001ca440c041c1c4100c1e4000e9403600810381d2000c03254401084200340041c0200d041c2040342d000c0b0820f140240080c0c900c50b0308041e12440454511030402c0c070341140e45200607400000e203d000d45905000c2d40303425140d1200202480ca0a0100098407400350b00c0005001d103580d518101d21500042008400902101f00011300d54040c50711b141c12030b584201d60680e0030401d007001150041c051449180315031900458240c8010314440011200000341120030002c01d921000c405101c201d01744101d5000b2000c90000045d4041c50720f49076410b0311707 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 896374271 1250 896373021 896373041
    0xd09090f150510110f24130b060d060e0102210108120d090206070606030507080706120e03041805061c02010c11040f180b010b090102071e0b120a1d0325050d080a 71
    0x1031046e41030280150107564403021281e807180c0b00b9001030760f4001c04903218901449001d04918148450340441c1c007410340c001c010791080d0310ec100310707a0300511902d116000028030418085a01c0810b0748a10000b1003030103454038a01c040e10101c1c0c0c0038030341d4001850b83d0b00403100070345002d40e46041c2042040401c004190040030400043c15000d49480c2e0094006c20100c0b0600c40c01c2526440150004003091040300c01400e0b00320517920181860f070340c01d14000c140c1140d5107805410594014012408045584030503150305035201d4a10080036643d509000030400342c0240c005440f146030800c501c52a01410001d4400343c403280780c4600640c103000704040410b90003508825401c00c58104240d0740812888103960310107200002071556403a01d00000d82a03944030038040309012034068041950140414090030040c07070300344481030a020100740f01e80c0d101060104550320401607840351911441500001e040301c241d184100020320b4a900b400e2171f4901c0a148001039076041040141710040c1700350696a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 896375521 1250 896374271 896374333
    0x1120e0d0f1e14161a070e1f11030a0f081302030d2010090201020c0f0604060e030c0909010902180106020c06030c0c0d09090f150510110f 61
    0x1201101040100d40341c4a800104100480041031040d59140241114590292000c0c050b2025080d801c001707180c103446141c0c5814017289080030901c07251040e5210f070890710b8000c042184480b00108038001022111507158148507042d444400095002d00c0502411700054035015903113040100c0c024180c2c44010703c2c140340941402d00103000360b100002c2c184800101410180a41d10032300f504a14203e0525050340d405118016010902c07280d030380c00504540303100fa001ca80d07030340794900100040103443d40760250300080284400c0244d24400c95080710380c5000130741911640f251003004203030402d9080f610607445a440d0342a020850a22000550fa41c41030b02c4005000703541071a80c02074456140d00c3c030003849003101101058020b91038004540b10f011110b000c80f5403545426070050860302c0311303114042000e460a4114400521280120b0030500503019600100d681010f0420138203000503140f00d0208010550500c00444d0100200c0c022203a40310b005010300303981c010b1460400342c5080408480 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 896376771 1250 896375521 896375537
    0x60c0806011202070b040b2206140c0315040c050d1401060e0306012111040e07080f010e1905121201090b0411030a1a061308010609061d0601120e0d0f 66
    0x1040c6840c0344e286d04079612807110042c40d207481c29036070070000d0345000e1710b8020b90a18804204014003540300141054070003c01d98aaa0780d0128030031441d02049070300310404110a00d00c3c000c10310b01a4081044c04004c0d0600303905004c17801c14840200c9003d0300b6500c000002001c0144007154001e074048040303000440003480c843d0f041c000d420010210031352405014055900303c2004200720314000780360586018004000030700214291540c0c1d021544101c81d0785004480b182004140180103440344448004000d0440c0e41001074030003c60303802010161200d0044114480b1015076180003001210804420303242c1702d5042424038400c0f1039000c084184a1032516141c2d0340070380a81001d0343e500420b10741000507554000803803e013018408824440d0300a400080380241c031200e0202101c03c1d501e04100811215071642d40c1c1000300c4071240554400320499180091901c400c2412507984010103240900c00c00d00b9640841090310000315801425070000040449603582c003d0045d02203501d98541101c0d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 896378021 1250 896376771 896376773
    0xc05030f161413181b0503160806130606080a0b040507080109020c011b02011d0a03080c03091207030903050d0e060d0e0a02030d030506030d170a0e0a060c080601120207 74
    0x840c1d8281c56001010312000416448000b842d001d403041c0c01046016904054442c4c101e4500c80102040c0d204a2005c28004c61404d141c0c0d44510296441180d2100318540b0301181a1001d0701d175544028851a0b1241d2105809500010b042c000c20b00100703031581300d001a40c01c0160f5440103684d20392280c00d004514040c108001e003503011101c07604540c104c450069403003003101002400741c07a822440e4110f00010704118103215605601c4075181c014201080800c03101e6941945440f0600000c01600184c1c500002c60705d0041d10314010350300b2010400854068143c0115050780a400c05071003075020a42901c01002802001d2210283c82c2d0b00500d8844040d032110000280f03a40255400c0030444c0b950741c45c2d001001c03a020000948002d40080031210aa00c010341d0050103444100d68040c0a8001d85140e80c50240c0218464000002c04100a07000742ea02c0c2d0039280c00078991540c44000c00c1c802c01400601003000d91249940c1084641c1da074002500d420343c00034246d542001c00b040c40092041103100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 896379271 1250 896378021 896378027
    0x40c02011506030c05190c0b09030928140604030f0f030314060a170102090307090906060b07080901050a090509040f3305060a170106030606210605190c05030f16 71
    0xa1401c0700081b00300c1c2e201c078601c80c2041390b05041080006110510380c20901c00a110300001071301300e00d1303011214641788041102e20004192440085030340355590306c5400f800b491640380c1c0c00c1c140210000d041d81e42040d9803620b542d01d071151044415550350389210518014183e240c0503502c8195444030708941030b400c01101042070600796101e03c400303684d81307207413940c02d07144c001c1d012103440b603c00034111030026880701080070040c0345d150320484211346030150002c0c143e00003000b03030f80a05400403078060030041d1120040d00c0aa20501100341000683c50001c2490741d203039003003207010781d0045620b60719010301458490082c000d6000c802c4400b90313101d0010481e02c00d50b088a10010300800c070700405c403510752102142c41d400442e0410240c180040c0030608000c5015480102107034007c850610603155200d141c20030080c1e401c80321005840c001c40382d001c00300c0d416410680d045650b9180b908403840c2e514108104540506a80d200000d900005025a2648641d200c507004140c030f008600c0e4002c00d4030405 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 896380521 1250 896379271 896379277
    0x1e05030402010e0d050111180307140a2c04060b011d0307030f15020715060e040206030c07030903022701080303060108190f0603060501030308180309040911040c02011506030c05 78
    0x106105071560013108040000039041036840c84640300d009a112005e5442d4039000141d0f06242c0c5010f80304100000a000701d20300280c0704220703009080d804115003411000311040001c4940e0504807e8400c0c0307040407814100c5c04c4580f01d0750080b200000d03800c1c5c58a000402540c04075688080c14201a281e4080c1d076540864000d049079072006000c0c0d0040f030603150800041c601d0901c0d441e210391002c120ba9041c80262a0308004141755008100562030f00d40d0a1000c07038903400c1e036020f504804d089c800521040719010007015458003a003081810f0030394079030000c1d40c1052046d8a0009180e0b40d0048007501c0804d03002210301411a140113941907281280001341081d4004000c01c82441c0000c801c1144a070f00c41e0300601031a155a00c00788415034590038140f02602e070a00c4101c00007684d00001542c0da42c800340c00c0d814003c061501441c6131221180c2080094450100c007a103400314984060005035445100b68a0303018150340001c100124520002c0c0744014903940800240760400031145003543e81700d012 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 896381771 1250 896380521 896380547
    0x33060a0309110d0201020706210e070512120f090102010f06090e01060602030f0f161202010203011a09100503190207111513050108100b070507080606040e03030a050402010e101e0503040201 83
    0x110789181400311040308003d03a034270300ba000d42c0b864210580da09000200740f5405450b01521070304111829000400c1d640c81011008911542043c004201d011101800030801c0910502c00032810660b26200b19048a81e95800300c000c03140d40308410b2080b800280070b00802000103001444c280440c0c07034110109441001800141d00c0c1d400a10340c84021070880603c080e858002820160504e0340f087c0c068000c0d4028041c8491021004a07909202e0316002c0840b042d03207401901050403650421410ba5040d000034249849890300344c01aa00601d040b8400380080a0160f400c40761303501c3c100030900414000c42100d540c5a0b505c01c000051100154600e400e007196028a084c158565072140580c030140002d80081031216400185c0c0010310100080c603070706940d241001e44659441e800c0400c421035100104018968009000203101501d441e40207075401401810010300303294201740002d12040058a200001c2014080700da507445900d008100c54040103410040d140d8100b6400203050b440807008 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 896383021 1250 896381771 896381777
    0x6090302061e0c0a061503050c100329101803080c010603020d0501090201020c31110a090e060906060f031b0a0914030633060a0309110d0201020706 65
    0x302000107140320356044544481c0000702c2920b9550b0742c0115030321380110007000da03012410490b070300c0d90604210000700222503021000308111320014082c8044151b01c1e12101c2c0505a80d02c03101111000c1c11010f4084909800b1420042c2e10840ca00f00424000e840f9411410480841b401c4050000300046200c01e82e504180c5040e260303030100d0007060241c1195040250021183c404100030080150040c00c0c13200d10036000e8903480d401e003c007801064000c9030100092400e54008207400940310108021440518440229550300300b51501003499002d402241c00182d86218100050340005443c15003140003180c60030880e050680c0012228083c001c00011800000400f151901040060018030980b28200300c50301c41024a0f00a04544014420384d8043e44c0c0e8556050120710307010800e984681201304c10840c048d10983c40f40940304840a80e0450352a12440d0343c24a550390782d8010303104907016980c0106006400740341400c0c0c003548a144081c0112003858440e8010b0f0303000b01c0c1c0e00b02540d2581c9 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 896384271 1250 896383021 896383027
    0x609060c050a0204092d0b1602011409070602070b09060a0f0314010b21060a030b180a0b180c0a2d1205010e03030708040305030a0905160f080102040609030206 70
    0x1081c098100020880d00070342c0207190040302e8003080180106078003940c0c01801c01072003074011400c07036550b6a0320107000102500c41c080700040c1600307000308070002020b0141c400002c0310f480101205d00c0c00f078000d0b01c0c0801603501150040140702c3d41044042c1c09000400c20715414107c1400209920340100d41c080d10620640320b01000c10702e4801c2e480740d40c5000e0207180c0070480e960344111041e544d6003c162802c804032000f900f020382c4145507030a501d001d40740c0a030520f04001d01d1500d40c04890f44001d4221401200c0d4a481982198020010091140e02400c445019420500a02403c403030340c00c4800009a00080002030191b503030345103003030211042644400641e0301c1c00c00d1111040000400080e02e5000072890216410f030f85003001310407541c8104020010988046180c075601d000490712080004c5400c00040c0c0060f211b100a1a084011720324007148000b05559540d0804401c800700d000881002d0800300141010580c02800804a58008525150819100900c0d6001c1c900000e40503403000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 896385521 1250 896384271 896384273
    0x6030403030e0604060e3901020a170307031a01170a06090216050c04140c09010507290f090c150906070c240e27010617100609060c 58
    0x80d00b18007540000101a540d4501d000d19158006200784005440188140701d40003404481070b1546c01c00030307116001141e01c3c18580103940d07415240722010a504500411a05ca00000d01d03c203c110b400405081c9515201c1c682024000d08a032011b03801440307045c105030f000469590f00000c0c0a010351400b4000340c8041d55481080f07074090401c0340c0c0080086803002400d2200c0e11010301043c05003500c01c0080e600b02400140130402603070391422030441100001d0000c60900064080109080203046c1800c5090400d1074940d00804400b40c4d0301c0f41100348a07501d10314000d11958121961201040900031880e003001d40165551303c80b0500802c0c0500c60550285451803121401d4910001d001088580d898082c0e160070038840c1598030540c0034161000300301c2c4c010035100c00310700008086140d540c041e020796100c0401030900c0c1a607d1800c4ea8012101504004c54002000c95028110302e4403210340410220070b2080b4076000081403191008004813052100a40c0000001c044445a2803d006204d42d1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 896386771 1250 896385521 896385527
    0x10e040506151614060c0913060f15120e1e030403061d0d0c11040b0409141b0109120807020316080c0414070903080c01020403060f0b120a1106030403 66
    0x302a1407002e030008049042070951601d0340500010398031500b002000d0400741c04003240ea0b00419184a10b80d01810b0220780403500788200040301c02048902c02080e0a55102501200148d403500526011100c404000e900d05800110154074200702200c10416190308804040d1200c0c04aa2901d000300302c070600e07064841d80e00300705030b4001d1a04041c080244003c0380d0007100030200d401c6440083d038054946c080b040c00740201c100103103403070704412503181c1d0b800702c03900308001402c825101e1948107a82d0046003022400415411844415000c0184849562517254101d1004030301002410072000ca24240580044640c102c9000b55000024685a034818800a42495618400352100c40c0c1e80b0480007a41c1000014180c005100c241c801f000407060064091300446011604075001c20310b505420070000c0d00c00750041042a034a48001400d20303842e035840005854084827103d072030903207803c414001842c103401240404c0d0404402802000e20070b0f611090500b0320800d2062040c54084000b8040c180 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 896388021 1250 896386771 896386789
    0x1606110f16020307050108250309050a0309080601090b0d08090312130e010f0e06221a04060f050a12030c020d120f02010606140c0a0c0605041401090302010e040506 72
    0x124011040c0c442001c91040c5000301807004003644644100c4c000001d081d4003801a0b5405205900c10f458407164241d041940001070503903580c0d00705aa104841000f003031041c03101d191014429501c9411407032910000519080043e0803401d015403901c440d50401c0c0e682d9008840030a6030084295440d2640366001a01f4080511544100314400042c1540940c070040d000b0826035081501c452010790701d9003000601500d20740100940040450041401c80c6071044106100402103100014826042c41802c030554841184080308400300c0e844465031743c07805005900140c004610b03403810ac1450700c070021703454004a200b4040f00141c04a04542814480c2c8002d402058003d031942a40103503c0c50001c0c0c0c034090b0b203840600007809a0b0301400099106020768030455580760b54600c01041514500030341035004074414100d41c4541c81014000811030001100182140d4490307070b80f03880c544002103900400e0f20111a04200e1340b0502480143e8101c444543c6401d0141d40014081c0d07140320206507144 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 896389271 1250 896388021 896388037
    0xf0321150604030b01152a02030c04020a0e030613050c0d031407080912010b0a17030c0f0106061101020712030203060612040605061c0b01030f0510060b0405010305010506160611 78
    0x6070002004000e00c006400520704032410b65903142101c82c450700c81101c0c2075041700607116461032003c4116041d13401c48694108854001015140680750b003100040880c0c1c0201040008664914008440c914040c01019400161008155120302840d61015215001e00c03900d90303c40c1c0c072441400000d161140c1c04040c000c0402604003035841c07000b8100300803550010a070003072180300955010040c1040c1800b59500c0620050319601c0410708119180c682041c01c0110b0125034030090190079807142041181c0800c400785980001145801c0881c010800540500d0b440e900d0781c010080580001e031140c0038004011f59134600143c4988070040080c002e842040003240c2c404401c03030144020f100681d4011409810304803803040c0c442242089410102c641e8040141001c0d07003a2004001061540c8103081c8520b10940a417245054512740b00b07011213000741c1080c3c1c00c4c61130106007031142d960103104040c00351030121205418001030b03070114202c20b1280303080200319a840e400ea00e0481010001950540 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 896390521 1250 896389271 896389279
    0x61b0806090703240b0301050406060302070f060b03030903010203150109120b07030c090b0d050106110f0304030b04020a080a0804091103010b090118122109080604060c18030b090f032115 82
    0x842d501d100b001740a4100b0700a062156244c541c000521600900c02c40343c005078410b5031002030040c9522003100030840d00000a4041c001003141c190b02e03030b034203200441c4603185040c00c055540011200062000903680c00c8241c80944158094000c0f4610140080c1e000c2c809242c00b0506016001c011a4000019400000c030441d02050409004205401c490705a91180d5600901c0c90814400155516904592a00300b50404c00c800d101083e25001c455601600281001c0c44030fa558107003451400300d000d04190703445900414240100c00d114014a070300110406850b504650500d80300d8803d42c482c1d004078a05012000c400c0a090071560320f02c850050080b001032001401c0b035030824080c401c4051855115018005c1c101d003072074501601000060701c0b800c4004140a5032184e85000080c10308980c2e402c00d10043c420505190001981c00c5009140f007030030b54880f01d05020748054605415512400c886801c288040c956290f03a08500e002c3d100030081002060fa180c0040b100b030305411040589800c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 896391771 1250 896390521 896390591
    0x90311150f0d050a06180b040e033709060e0102071a130902030411010c110a0b0a080f0702060c0d150303050c07060305070e101209061b0806090703 65
    0x2000c48800c0507149010b54110203110a40d02d00c1002c20803901d41d400303440f013803078a074a60803501084554000703400c40d140a0300c0020b2031200c0c0441039156801c054403000c0da8110030404010111988488901e50a8038003074082c18044480c000a404e02800d80a0102080080c85420300144e208000da070005003040c1000380101140000c504856030b12003e07000c41400b81c51003000400f14114070880c0e10545d082a80c0d1440c003d0b0900c01111114907245003079070b9280c042c401e100d8096550307071034200c02003c100910075680c528212000d0800a40102181d0ba41c480100c20403202c1500800c2c4198040034520482d561001900300110003400c401c04600096011010b01000300354120004100c4c5503004800c44046942c1c50b002107080d1102110031600280862070624024103002203220100401410040700b0030b40480292400c594810000765440d98503404407210350f40b0380300303521650b2000d51324100c0f005182100100f005140081e04000401d0b9a81840300083c00130407418124030700400ea03104003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 896393021 1250 896391771 896391787
    0xa020d050c01171e0c0403051903080a150504020306040608070b03010504290d1e0c0918020d080c0c06070c0303080a0608210412150c0f09031115 64
    0x81da6944118040e404601c190702d4070002c20480001e0103200e40707250000509804100b4007080301080300546943c8454400b403002100041c07091004881c14009001c5030444d08010f410700401c40321000e04a07032480c41c903101e40c18141c41400c420100c20794005480140e60f81d00c4080100c0c0041140354031141041c02244000320340300e910301c00158100c41044a0a00c4003c406007421186c401410225020451102008030b14500f4500d1141c0f4000707015201c80044d4003000420030b80411890b00e021541034028100078400405039101da031205140d8900003401071101c0ea03001c1040e4520074580604161401318502d02c59040401000301e0020340584820b8403009185460a6130181074007040300032030305c1c150002d101c140c00c911030348040300c040b04010909049135102e030a082c0110701c20b20940ac40c108001c042a1008165210324181e0720940242c3c006842240090301282c200280720010480070104544c40e40d41c1c0081524140d9030402d4401c01404400e0b00007a001c403020b20108107440c103022030340e06 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 896394271 1250 896393021 896393023
    0x507050f040611010f1b0c060f0e060402180c22050a1e0501030b06040302011d0a150e03060c120702030904050a090605130b0a0b1c050a0c0b0909180a020d05 69
    0x3e00d100b10640024401e41c00e01105880075904015110801d0b10100f2041003001032050140090300c07401094001400c401c110104800e440640f041c00b1141c0d40480107100c11410030316044a0425a141c00146c4d8504201060000d148101c0003080a0201c0d400f2011000402c2081041c0003440300400c1d005449545064055802600c0507444050001c4002c001036254001e0043d12089800103204030301c1c0a0a40d401902c0400c0c1080740700c2c0740e4071051460065191102858400909400d49030444c90700c00c00003004142e0410500c840b0300a41100040c018500e2509003079134110220111a611241c1c0da0503412031843c0240700605074010709003024443c03810220391045c0d0710a4042c3c03200f404165038040d45050084071200e00240b000d40c400b000201440101d0344a200a0200100b088100d00303544600414075081d01c003426541070f003091030358100700704810310308000400c001d802540c00e0a0215001440303081008000c80a08020b00d288005d0325001802046c5410307034000e04c3e4060440841c2029 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 896395521 1250 896394271 896394287
    0x9090c090816031704030206091201142503110703200d091d0f06010516020a03060f180f1106070b09010506120c0603011211060406052502130507050f0406 68
    0x143c1e40499003801e141c40300b13101070301182e0a8a80150280d0f24003101001400b0340821320f000c14151075541c51b010181024451140c1502692601d2560701da02c8080720440b10488c000045140700b4145440781c1d2101c001ca19000341c882e40d5406050299104140c0380e1194011802024942d074240944008041036940000980c815240c807841440030f03d02170011035800c107110550340841c903400007400203807607980f162004181c0c050081d0410319425009a0205064019a030400c0342e610341c17900c25065001711f1a100c1d0070292001c03202214030035011622440045080302c0c070085c00050a281e40245031362181011940303032a80c03080140c900b074501104503500a04003912001e01c07607a010020100c02c1c01c00040c1809007000b00426141c80c5929002c140b40420b0740b110030031607102d807921501209540d100300250005007496150305035034086074840320410880d403e0300e49261001c0c07850b018000d40c4501c1c001c0588031102500014440e120040c09880c039000b040000000300380001004644c01e54481b0710303 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 896396771 1250 896395521 896395523
    0x11031605070504140f0411030f10230f090312040305071101020111180a0503031b06010e1632040e130209070804060b0a0303080708090d09090c09081603 67
    0x80d210780c15141c03420031056440345181e5103944807080d0b002c01c0788652604201d582082c800c40e81d00031170039020720200742000c00c40108411650402030320321003807440c2c50140c01d80302c1038205111040914184002c5201e2074015041400031105240024200601001211f40310003881d90408058602494000c016a10080302102c09040101c0c100c076495005004404146203804121401d141000a11803001c8060380c2c501507000440e5400010b4035101840101000c850601f181020300300050a0329140c142c0c1a4408110a013030513041003210500d181a04468180510304514043c01012a021001901e004012800130040c2000107902100c2d4009000701c0b580076849101540c0d030480d80c2040c0c040c0450019400080000000d0310700c603c2044e01d01e07407180c8554000a00202140e0120b040501c41e0780040740419180028040c030b554210011651110a90004020301d0842c0000280124800e1241449880d103070704030701e450103000d0b401032005040710000f22401c119410007004165120780c80 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 896398021 1250 896396771 896396773
    0x120201030c0807020c0f0d020d08041a03090c100c05070609061b050d26010909060615020a060e0a05060f0a06060f0f21050a0501081207051c11031605 66
    0x31549203450b0040c4003491180d0f4498014210500443c030501c4001c0c004100c540b0b611068919918005994070410f07075510350300609000f91a58184094032140c500001000201d4003828000c0100e51070300040c080e520f0543c19030325451032190b5403005071421505880700801ca03004501d40401c0c919800914201100c0f03403a610320541c041c0c03a244030701400c800e124024040d90002c14070300e0282c038001d1400c84030700280c41c3c000521239491032188190700002a0090f100164640000b50180038481c01680d0107031000b040d0944401035642d80281d56a0030b405d00c000d0015441e6031141240c6001030064030010358000c800d44404c2c0c90503905c205103c660845903880098035120000c61210721500c6e43d0030101e01c02d40c56100080e02142410f80b030700c5c82e44082001101020002c0280000301d61300900b13001d481c00a40c041a076506000d07440d0705140b01403101c1508000e003031000d1008660000380d030240e00c4100c074000c400d814400d0b031412119140902d01048191000060124045004e54044046c09025034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 896399271 1250 896398021 896398031
    0x90f1a060102010c032f09030d0c1209180908090409140d050a0503010314033001061b020103090816051f060312050c0705041505011b02010c030c051612020103 70
    0xd04103034201d400c02400300400a00706000d48a0041034021441070384141c46c00e8107030401300700e140040d10340f94502d21650009101c00428008200700c030b1151a0304000c12b800c103550f105040015030440100c501c42080d52030380d00c84c0605018046202c0448403441c00241c070a0201d40003500345104a000028040d49041c810850441401c6202e401511a158455520545141d00c2c68803020220700201c1d0031503d00c0d000c2041320048021803205d01100c00e0071040803140a035010010091406d40f030507440300b014018480500d200b04098503aa4080503542400d0005980e0042d0a1440e6140070346002c0c05500c2d0000e1410b042441000070304007100c0002c150034101e81e2030b00c0003000400d56401d44002850051520190703151140600c0180403200340d40d5003100d407841d41d20300008060b078505032481b2030802c0e900ca40500803560701c4004104510a00741140c0b100981310340c0003e10100a044002d030400804402c40b00400c44c0c10300065081d0b101500c1c001c0c4041d525030368521060210161700b240070a01c1c0c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 896400521 1250 896399271 896399291
    0x12030906150e13123f15060504091802090a05040203101b0c1506030309060e0102190305131212081509011502030d06090501050a0803040e0a090f1a06010201 69
    0x4202c8000c0c0c1c1a40300115500413200c0c92800e480c52130390340e0b400d500b644d030401100071072108400075040c00208104501c082407605558420003120a009801c0610246041043c80060b03002421682118401740000131055002101a41285080030740250700040707060921503110016001640124000c50540c1c00e8408007281c2e0704219240d441d00d02006c55440040c615100740108602942c141c0900502c0d5910607185114800701d613004d800450101c4c4205505000e016844110001d22039403e000030f005002c0c0c2203403901d86c400700e040d03001001c0007400101c0e0512800b00400500081c4120780215100e4100c5217480f580703040d660030708600000ca601c4000b030309188900c0203281604101400310120381c0d080410390f41000e003001c41d0710825480100195400c1000d50310a40b002004504030001d8507505113410001c1540e4694000203060b80b0900045c40410054400150010381131200010001c80c240380c02c1040e01800c0c90042c1502c9004007155010070003075910a071081c0001da00810038a020 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 896401771 1250 896400521 896400541
    0x140c030c01140709060e31092d08090a0302060d0e1212061005250c0603050933190b090c040504020d020c01050726010b030412030906150e 61
    0x2451045c580040c04042e0403481e00d060907460000200c0d00100c5038944168805040f00e40042c000701d103034426950301c00c090340034040940301d000070221910306101c51070507802c01c0500f4803008843c0f02a10101001440440c41c0c1c0d126a8503030300440d0701801042c0ca40210380080b10042103440c00c5100030307005000c0d071640310340d40000c12541d803c2c1030b42c1010710580e1038550501011a100d900c020050010401c6501d41e1011416400000a030301d0344484c40a2032800d24004407407864517130002d02814101030038081e203000c000c07030b400b000d030081d003403281d503460110726500b40080348201c11000e50075504800780039a81c1160344110b4000948048240b205c0045901400044201107074645a0144140406c1c44549400d4006024010b20030368003508010500c0412401c440003a6041804180c40e00c0c105c4545144c0300c1d01c081c002c41c8205025000540c9080804611440014001860180d59164800d83e160280e4450144190030050405c8011b8075650704107544903040c0642080200070703400088400303503 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 896402877 1106 896401771 896401787
    0xc0a110a0204060b1c05070807110a06060b0a0806010207060504050d110a1d0a15050603060301150e09100509100506130207030c110405040c0303140c030c011407 71
    0x1032907020911284001032130031031000b81006c1c00c0045854020181c0c50340031005040500c0e203021500741c400d040004aa10041110740740c1100401d03450008400b0341840d11a544500040d501c504005a0361400756200c0c440020300d04110910041c00d0070b803000800f4511803103252000540e0a0002403500c5096080300d28950150303040e901e108a14a206982c000d42c80d0070082100c0200c020315408c40c21503a0060b01d000781d4000000c100b06860941c04015146400420f09041d9038690211422080d0180c2e500c1009100c1e18409003600919485128040c2c0c907107000030940d078440203400d0030141900034240d84d4080a502d1611a10341814001022271030321942d186040c400c01c6107810401d4115140b2003c4c0100c0ca014100000140750001000550350141002c0e6859074605460420383c0c818404582a80c2c0130102c2c03485c0f040001500110902050b002018940342e071070b40d10448141c5 = true := by decide +kernel

theorem cover : BRFrame.Cov 896223021 896402877 := by
  have h0 := BRFrame.cov_init 896223021
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896223021 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 896223021 ≤ n) (h2 : n < 896402877) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
