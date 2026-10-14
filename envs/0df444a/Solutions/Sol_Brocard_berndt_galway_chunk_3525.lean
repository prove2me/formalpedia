-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3525
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:54:38.227119+00:00
-- url     : https://prove2.me/submissions/228e9dce-b1a7-4757-99d6-a71dde602f07

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 633812949 ≤ n < 633992805 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 633814199 1250 633812949 633812969
    0xa060909030f210c170a05331008100b030112080a09090e030705011802090105090a0b030a030c0201170c03061908010f020909180d05090f0907090f 65
    0x12845541c00350482d001d0500c008180141940c42d403003410011510390069800960b0144549100c1c014068a02d0b00d08101c0b0100000581001a072054014411144190740310b101c410050310780b80c20743c0032210009052120364070844842566150b190a425424071090f1541e40201d14036023050036040c005a141c104180404040004000c45000c20781c019402c60703049200f441c0d40d207015842c1039900380420381c400003035113040415076800007102002521005001c0c038001d00084040d10203103204007000c04c80003503204054100510950410030b01841d030100c0c0ca41c40c009000b0710a4000285808108003044001800b040491811035a0244203170075145001782c1907207203500745852912280d00001b020140540c07400b10a08003060300001500006081c501c0081186c281d01f030704132030081d40c0312040c840c0c06030403e0350108805101140c3d40e4048149440081c0511140c00d80c1c0c2142c1c40c0e03010351882d60784405007030b011042d0b9a654403800e6000f0601c0d034840100e224a4210310304084403550b030011901c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 633815449 1250 633814199 633814211
    0x8041a03060102060403120e070605030118051006050901141c0f090312240b09120a0f0b040c030812060102100e070b0a03020712030c12060b0d1a0d0303050a0609 71
    0x143d8001807441e03045981130a14841d00000c051111000b040c0e8850042590f120324103000541c40d0304403000314140c5400c2a41c50b8251550760071503c0613a0b5041c1c6410300c1c0303550b895408000c190320484c09000e42900503d0004e140384001510074a81e600498001c18506009180d01c10350b040d5a0700c200c00c0300d444031b040706028110042d05c0c09060342c4034a08600040c141c40349540e5215045c400001040d00303461004005c2c03a25243c0400118507045000220b0040d1392005007040c0c200380024a040c50154041c44041c41c1503855650390100350760141044401012000011000909080c00327481125005c500800162600000091815040034110a03806c4d1600030200c1ca000001300346541a00c460740c034404d030b0b560b0a0240440092280340b00182050542c1d5241481c120f51503081541d04100c5550340c1e24a041e024150101156158880c2d02c5104504014010f49200c0940041d2100c0440e02c10955034507214801044404181040c01c40000ba5200108003007006140300d103070041c0c41040410450 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 633816699 1250 633815449 633815461
    0x309060403110f010e130e032b050108191b0b1c06060809030f09030307230c060f041e030206041d0f0402010e060f040914061e060901030207140a08041a03 68
    0x141e10701c046c10408506849410306080c2d59801c20807200c990000384180c080f07207810454220b41c100682c1d201c80500505000000810250024400080b40e810a05e60a0710042613603902c0c401e8006503c011450000904001902c0c0384003c010380038400c182c04018010040c51074140e012518160407100501181f90f06000381c45900000340c805000c04180199954010341c80083d20f180110b000042c03240c2c52042e007440d62541703600d9814403a004a00204c490410140d410044280988003000c025440144030030450b642d11000c81d1159888144e120a03110f5449070041141f951090b0001e51b51900c840030301c2d203a590f505000c01a800b04440c0d011442c2c41c00e09a00007400745a280c64000e1003004041210195000c90744103d4004000c011010018416509282030164808641851181d00482c00d24200d01040f140b1101d00c428004148a103400d54040c010350094011030300c150741584501503000342d6002c00704440c00519014510881d00d440c500910104080030320300e000c0c0a1280b0034024011 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 633817949 1250 633816699 633816709
    0x6051e0c0d020a0c020a080120071e1406040819020102041a130f03060506101b0206130f0b0403050f07080c01080a0f0222080a11090403020309060403110f010e 70
    0x100e45001e4000b59544031050411288000e0101c80030b54001c16030400007483c0d42e415405130680004641c10b010380041d8075031150b0018018440041c05840691003c11082d03248001c1c010f20341c5106030300480750071041100092130100b04032000c0329000c2c000a135090841c0d40102a5000c4420f080c030003540f03424248504a50882c9800540f00c584041c04200c01340340d02501480e00002c0c214040345402035541d00c0c00d01c40040d001c2500d1440c0550081071498500300e01c01e28040803002c01e11102d1070043c800d5039080c00000c0d1b000f015100403980500b400803e40c0c1032801c000c94004d090311002282c54504509146c1c0c1841041105e40313000e503018203020005000b001c501c82080314802d08010f48165150801040580243c169410900d840024051000400481c1004a00c01e40c080980c0c0c0c03040d01c541a01e07a0b51340c0340c40ca02a240300150045a0f005207010103200d40d110340b081c41134038140300301c190100d501504590800c03120030f042d00c201c07462a424103a940000801092a2009240c8413500221f0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 633819199 1250 633817949 633817957
    0x7140f03040515030604180f0201030c0903050c09250206010314010203010315020a02030403020a09051503160504021821010c02030a05030c070c050a060905040b0a030b1603060e0406051e0c 83
    0x181c01d80f6011001030b695946981c800d0006503074402c0415280c03926440c10652200100104a01103450f0800710585288a10006000c0d23a51140082c503840b16a02d0030040d140c60b0080005000000d0182d41e0700718241102d20514550a440c0c00400155040d450260381e041c04040c81c044103a0b00c148010004100c840701401c4c2054400c1d0750042c4d50340d107604800c90551007a500040c0d0049150071002446c0403859101030300c100301c5075200d8400800b03140201070b202c0460100c10056009105401d020307604e081c1d4020701040e00f03410355079281e19680b00301141d074800c4041d10a21a6004008407030381440000e000f02082c514061010310710b0003040900107042c0d0300007d44469110440480c61034100109515540c1c003400d0014641c07682c05540b140005d184400c68040c0078025800c2c12100500c03400d01410710415241d00c20000b228503543e413070007034080c1e2904055110801d80c80d0200011400a60030009000d50301840e808600f07883e10030b4201d6a1000000141407144a00c0d108004005c20600c0940d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 633820449 1250 633819199 633819229
    0x30702011103040806010b0316090510030b01050d0608010903080c21070201090510020310060918020309100204080c0909060601120c09080304080a121d040c03020f07140f030405 78
    0x1915141d4116003078518052a048402c0341c1c0308020002c100b440f41e86015500c102c0410301c00214008468100f00c6074030117039100380c40c1c010745008260070806000c0e0f000f9403102c031410714009041c4403000684900b55211036020001907551601c02d4020705500800e80d6900c120780d19542271400780d00c00d1040c0f000c040c1042d000610070000c003020a00d268400c1d080b5001c01900030302210900604046020001c0d4010780b242c005422a10380700044e950300903030f1000f04581c8d003841030b0221850020302c280081d51005001801c035002d0078180d401c08800034800380010b010004010a00c0c44420014002c001300060706800c282e030b101e002040496a8420401600ea180c081c20200340031070175100a0fa40701902c0d4008040c18080850007207980e12000441a61080c021800c0007400280c91030b0950310342c41c039050100010450100e100da42c2e030a09400c807035007002c034034074005180c0011402500c040c3c2d003102d00100c03540e01d1000e4100740d204400f082441e100c0800b86000e0342c41c10307207441e00080c14103104181e5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 633821699 1250 633820449 633820457
    0x220f120b07031e060f0503070f0b0904090b09010902090f01180b010306050d0305130e1605130b071407060f0e091e0705040914190e01200d0b0d020303070201 69
    0x1111580300b5001030808901c1c40510f000001400c8030048090b2246000703214001c1d00400001580c0d150004013102111408801c071706010741031402c040031641c0001087d03a00f040c0c0b5440750030002820520068811503258000041c9404548100315000d03602928083c40b03d504100148841310401400008807501c0c00b0340040c84891079001078015201f540d000c01c0d40024502425801e25030450024122090360402070130386583c880c00f1805017014180e841488800300c11250020081c0a480102411447c407a46c0e104682e89d2401440c403950301c18070381140d644607415440e080c8943d0410401c0054001c82c20051004000d990005100612002d070142c8146600c0c0080ba1080c0c40c00040f14400741c6903c648940d59103030141c0060101c3e8454414030400500d0030068495604c2800c43c09030264040626a8404a1803c1c1c4038401410b10700048800759582c41c1501c005008444030071001141c20b0203400c0b44c0b00c41e08210604205c6030942c1da0075014a40c1060244010780d0040b040380d0f55603609080c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 633822949 1250 633821699 633821701
    0x20d0c03171312050a020606030109050712150227101b0809150a02061605040e091905010e15010f0b250f120c0510020d020f220f120b 59
    0x2a10704252142014003500000080ba90301d0350303103a4044c00402d90a1120703022a03200d0344542007410700322008842c0c068100c3d00100403c1c40300c07001504207005081d0052444078524801d584004080b64424619101c1b03c41100955141c40030318440501402001114405034000c501d6401070f02c0f402c0e06200d03000c00791018030b04180400c000c010a45045410107030401048900040001001e5807101424001520407500001c100074103081c82004114002d6443c2801d0510740b00e00840013500141007401d02c1d02901c0c5801c1d11100d104c1050030102409400042841d00b0000001c50800c181410b0b031118806407800184107011860710404202c40c181101c141e030319206070103214482d400700c1940c8000c0d44680b2210b07000707201c002c8100901050190a4290141d60166000d45120812902c01421500720751400ca44402c035a6015010b40104201c01602e441450010101c0c5a4440384800e0015003000c0e4100b1a140714002d02c2c2c2c80a4219046107640701401d00507030903800084401d0003001802260 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 633824199 1250 633822949 633822961
    0x9021f0210200f0703031d0d05070f0f0c090614063a0e1501030b1f05030a150e0a0f15111801020c03120433020d020d0c0317 55
    0x100030203007110a05a44141c494004140d80f00c034690091609400003400e091001c400c40c03800c07030080112180507600034400203454503410380c2c103034100080668040c21078418030000724041c412020b68091042c48200d01c050f09018202040b65029040341c12001c00f51001c0300800e407210411a207440c0e4203103842c0b0342c10001b00c281008901100152004400354043c100e4040403045412100d1105003074010f4031006295180e0b0100c40c260248005424902d100c000b165001017100c00d450907404140080c4208140c48902091411003483c0e401c95425440702c4200071020283d00c900b0200010040c05010301d154a6150b81c40c1c100016803019150084d001050b45017803415a00c024407481240b50299110084104c03240721074805071301a02d01501a1140d2410203140200308401550381d0f081555003031600b080e4644c40c440d541d10a1400500f081d11581080344040c46120b142020000e0f4000c1101107544c9400038203040510070004140520180c2c0000003039045624961014459070049a05650350 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 633825449 1250 633824199 633824231
    0x16020d0e19060513121703090a0506010b0702011b08030609090309090114130c05180d02190515030c030c030a0b0d03180b07020306060409080c010f09021f0210 70
    0x15840401d41e4003182540055241d40100140100f51410022043e200e50b4a105900006201e820001c0010100b20651034540c11548061a00040c5003021145d4441c8036544940c5440c400ba0001d5003114000b01d001400c560f4465103414100280d081002c0e00e1007200d0391808803078007020749000d120b900800d000030202641001a00c1c00d1a10040c1824800d50b954001403440035558200503000d03501c0e810a028600c006401550224405031769000d28001400030380604003450300740c2495010400c10000b10240e5101c1d00611103500786107403005540f5180900b00222010382e507042c861242030034400c01c111580908240c0764030030200288a40d40c1d0360303405010320013014a44030715030788440031a4000b414180d2003001c1e522000c81c80070b0010f01250711202114424029444025031661080c00001d500307007800c0d002114010302c500020303420226542c81650940f07080c811a00038140d40c403c01c21055191244110b181540000110303c060958004001d44030941c1d0032051860310380316249000303075241d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 633826699 1250 633825449 633825469
    0xc1306260a0f1a011d190b0303030109020c150415200a030f050c16150209061602032a010806060d240830090d08070b16020d0e 56
    0xb200d01c040c00107190300c3c5810304200301040c22903240c8210407000818410781c035114400c5002400d4410030000d40d82d25030a02001d040813900c5804442e1903010350b49650310100091740c080c0001c3e02c00503843c1c03940d130b132610391402c3d6507170b822030361006032400c117010104c0c001c01d80c60a00404600e001298030f224040301070040d56003140d084e484010000580841141d4140c1c00407810200c903c609004585540c0c018006a01951901030503d04405420500084811500c0b4102400e814009810020140002025070b04400c0089200503446500c40045141c04c1c81941403250b21150001100c03449960309201c01821a900c042c184a035180104446a48600c20b65280d030010001c14003e400c0034403171131800c540c02c1c00d41084260035442c102044592000c10401e0031546034a441c41c0301d03048c10403e070801400485804a000d103000b0000500503171a03c804140c5294050045030340e503685149041608441c004000301510301007000c1844c2c40590226209082400f03d15228506d0a2184009074002c90 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 633827949 1250 633826699 633826703
    0x120412020616060b03100c02030405041a1903060506060406051605010608030f040e0609040503030c180a0b0705100e07050111010f0f050402091f12030315080c1306260a 74
    0xc02c1103140c100040c0c1c0d00160710103c01036050310603030155640c100013510303444031036100540c006110030302c141e040c00c0e4842031440b0080c1d401010781111007008034440b0f8940b071401c5043c520800500b0720a00002d40200351300918240c4d5514505440c21100500c035010f0707201c1800d095220349000300180306007500403001920303150094035600c0031000c125141e41e5100788107906908042000007446031501884441c490b607040805503242d90f8a440205d6803550040070050a030505041103107943c0c1d110305507810f02501d40c603203156a5641d0781c0e040552500340b4810031800100d040c4a940754048202291700c078102d41007070900d24100f140c0000d800d405410403a40e1440ca06251240e03200700f480c2d01e0303003005024500a844190316616608100002c0d941e05c1d00d0010800d4141c0801003000e0b5400324031059140e40241707400150300301c940031000820b104943c4200459409044ca071103840c074051040c41d11140c1152820090140b41c1080400000103c000c07664481c03003400c44e01190380c0c005100d0803a4840e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 633829199 1250 633827949 633827977
    0x1412072418091e050405060c0322050d0305150d02150715020306010e100203030103030c030c052a0a0515090607080a0801060807110a0b0402010201060b04060e040e1204120206 77
    0x741d2280c103024020094002c4000b004204181006032540c02e500c01d842c01150070078041c0c607850b42c4918003481554800f5081c2c008840c00310b1943d011507581c6843c0c0000c034510480103840710382c0060100500b80c2e0340107410b4061045110b5800d940507554900e601a031680e05544515000303515180ca852240030b03112006d800400c4180c41021140d034585d00461280000343c8915035800010428040c150385007652000c05030340b0800051000c40d0113111501c401610070b2602d402c10101c00c0d6a40c03814101c1c200c403102c0c2044410040481d0203c4103d6030000e8000741074904910b074914050015180460710628082507034400070b030340f103841d84410040319130003500a5049643c0b0300c40b000000700420f01c24803500000423103507008154890b208a0081e4078103007600004203000308003619008546003020b04120f040d913599001c0015482e01c40c8000d48000c090381d40f43c0340740a0020b9800d00c000d0380c2d554003034191641c100d0051100d41007120f40648003590210464442c00c0300c0d161012031300c6c0f48682c4183c2035400e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 633830449 1250 633829199 633829247
    0x50307030804030c080102041a070c120f0c050906061b070f06090603050f0610081e0a091b1d090109061b181a07020d020a14120724 58
    0x804034040080c0220303441451342c0c05410b6525a529403c0b80158010320b1160440b0002202c0c070317900b8210240031400c0c06400b02200d01507913200c0041d22428404000c03030710062124600750922541261440041900340c0d03085285242c40070002c0e14078411102040e1840300300803034080042c42c00300700240107815000000859031340c4030203000e4086021407207038a000038140400182c0e25130011448070b01492001d04003002c11420300600b981d80b5903006111007041c3d590031846402c01a0312014460203040030001c0081c44130100c0c141000003080c2d40c029442e03504518001040300803600c13072841d2800000e58080100c5522039900d228050710a510000c0d205c1030802c8581c0880c41075104410507a40610f448840444409520802040f05a8481c40b8060201014258810211038000f008070302d10040044500514950014501c006160085104504860050545406c24404010480001c90700a042051520322601e00880041d013506107801070001d00001b02c280030f462010707249580142d0b200702c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 633831699 1250 633830449 633830453
    0x6040515060f0a1b050a170403020604050d02010c0f150c170610020708010c0923030a02010509040b0306040501060e0c070c12230d09120201020a11300d0318020d03050405030703 78
    0x213101110f1209442141e010001c810b00e41481f407040710201c960180404c0d0426241400f080200004000c0580c10301203207200050000b0280650030705814450841138403008414406003041310502062001031010712990030040a02c03885c80f083e840b03001103907540c203250440c202c00c03414000c1319400f40c503003036080c10002485180c1040c0445e0586000c810500e0b801c4051003010360074515600c03191509900000c0010004d035114500070000c1b070303a010340086015000640030901e4460105c40c01d403002d035900c075002c0c40884c0221707040581192010243d01d00b0003d0f1500c1e01c0f241f14403944100115501600c0502d0100461030000558190000201d005c80c19084010207072030705503089404001800c140b10201d010500e00001481c0103070182d00070069000540e895a0590420010443d0f00100100881065101c20803060100d0000003080000c401e00301c0d01e40300d1030030702c0d450401005d041c00c0520075034841a10000d410354440d01218000018078840c00c041c0c41c3d40c030841c0c0045405018601003c01 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 633832949 1250 633831699 633831703
    0xa140609100314150c030705070308061c0f120509060406030f0b06030f04020a0602030c2104080102040602070f0f050d03120b0a0b040815010e061e1806040515060f0a1b05 75
    0x4d0341007420460081c50740e44031544e03040d00e072000301d440c2c1c008540305010700e9002c24441c0803caa0700c16801f4051541c048101e035540b00400340401000c4800400c0500c0340310411513410404960740003a428080c0c2009142d50000300180114000c2c00c04240c2c2c0c807240254401d0494000d80b04c5410007074031942d039a00300007086001000301180d0070790094600144c0011840c0c4000226a511782c1c80b10701400b849100c0034100c191043d0b8817014026014414000494120750a02c0200b0052146030010034409103000304c0a280010340b035008602003800000b0802107a01c0e40d47c04507840c96418a0010b80340d02c01041c895008000c0c10050640085a141002c103030300c030000004000f07545038101190359540041320070410500742401403a10181107035000ca00a07090400200100b00c607038030341890003d8822804980b0706c0500001404504a458007030000d1400d01d841502d400c840818080d03090a000980070410610808021903004900010340418192081d0110f8486198450740c07003000207081d0502d19 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 633834199 1250 633832949 633832963
    0x2205090a0e0c030f07090b061c020405120c060d020f130f092901050702130f150501030b030706080a0216050a02010f080f0105040207170304050a0b0a140609100314 72
    0x76181c440d01c403280086140020361840102c1c800f100500310f80342410b16542c041d00030b451600341c00200c10320011138004178080301004e250304542401600c580c9808200010718058081c00d1680c1d800200e421030701a21014121480d81c8291800560354400003602050395109480345504243d85040340031900803d01d1f10340700101ea100301800d0000450342c0c421201040c2800c03c010f03001031003086c40d85145502038000791117214001405005000000c06404c030580d05a0703080c1030200c5070384e04a609000081c00c07a04802402080c0b03010031080c01054042665100a401044240980d02c00029000c840c181c0444c0c0d900005220a00000d03030051604640d01c0c040310340b00b2800300e0620059040c3d5240f10340721030b500c68040707011212940d034603050502c0700a43c042c03402610080b800228141c00c18091000450181d48160002e02c5001414145201e0607000a0b0560744004e0900e800202100c00014040c0c0c1c01240890f25102181c0f03843c0d020a02420065000802641346a034000d05424800305202c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 633835449 1250 633834199 633834221
    0x2030304110f060a08011a0906030105270f04050d0306080c09250206040c051008070f09090e0f1203060f060906040f0b030a0605090714130f090c020f010509032205090a 74
    0x10a011f00120513041000d4010250401d41041060004001501d46110002050340754008111140d0841e018045030900044500341c10030b90542e0f0a010800034208800301c0760412514040006034104408161a03d03d4503030703840d114605180100700a1640c00c2000c0f40c1e501040d4494151040003000081c0d141c3c81c00f107900f03440039410a000090982002a40303140c1c40e0502c0d41d60a00c940c3d4070b4403815148505201b0480b01003003a102400714052401c2d10401d049069160020902c3c20001501585481415056581014014002d102c842d407210300072245050412201203865034151804554075000d590b000c00c07200c81c036505000400441c40c000450040803134240c00c0c81855100c0b8140070300c400c0140c4a0000054110f81d1a00e44000c41002901005400c107007010781d0300c0e90300c5607201c800400c2c68008040c265034840c640700d01d05804101d41443c000c0d961000b400039150002200340c0302d024004040b42e02d0800d03554080084810141540c01801c070040c81a100c904000800c50000d03c0e0310140 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 633836699 1250 633835449 633835469
    0xe18010e0d080a060f0509070905130203010806090a0c050d030c0b010603021b0601030807030c0609020904080307020708011505060c150a02071104051b0a03020d0515150301030302030304110f060a0801 88
    0x20078003c0100d4040c0070181c3d01002e103001ca21a14207020f0010340791000306441d041000c10000440d41ea690b1311130115130a03608010258895042a44150400360054020f8600303074025148000002c80384031407a0215401111000207c507150300741170781d49401c4450001c14850303120002041e0795030142c1c064081d4003201003803600c4113001d011780f256550700700f800b0181481340d042c410680000d1042d807413010002e116050104100d0340c03a5001c03415840081c0c60803140745d0741c080100807a4a90411202000345400790003802031071031480000003100c40c5800b4060085800084075044c8032001c2203280901144000c4c1e403202072410801000080d000024211840358100d80d0303a01040c5060b010302401407100740049100200c802060b007401c0c0e482054003030241038003403048507000900c910903180302e40401941c505d103500304101084150175510556401d568020300040c008240c0c0041a240e00030340c00b5094501c8194a000025190704c01d00c017455074000d50003e8800e080326408043c190494082c0c8031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 633837949 1250 633836699 633836701
    0x106050a0203040e0402040b120106031403130b0c0a05070b090102061608191e0f110a080c0d0b06030a090c050105180d020415082803090e18010e0d08 66
    0x44111024440c8035081030060340180b106000b052400c045140e086403000780001184003140c00402c030010303a400401700060f50b403407004000340511b0010000b24840007401551030f04044d54a0031000210a01490760701c0003010403900f11030002080983e41c9107400004981318590b0725041d10100c1d5105005003401802a80042030003a40100f803030402e4440c20b51500300056070f642d0740c1e45411402c03505800c2a000d84800322800e0001000c2d01085102c081300402090507030031200400c007035450050b801310040381d00f08001c0c0d504e10340c0181d1254001000582e00b956504560b80201c02801103a450b95500000010a0094100103948000040c0b8030406207400344541d1000155018014805034030b64003801d07016000b080d8074003801450b0341c1134401000003914030402000d40354031024581120a15500c504060034404c05144c080056180e003404020f8007602450394018074210a511448802990351008903442c007000b15446442d0307a4800d4020421990b41c40d4003a6500c06102402c00c0100d08104 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 633839199 1250 633837949 633837959
    0x807090b0402131206110a02280c060c050106080106060f0305070206010302030c2e0e0a090b0f04020d0f09030503061e031e0f032b090b070e03100203010e01080601 72
    0x10094030f11050107500c208400c14503190502000c50010a021209a82d581060400411b00c200243c80b10102980c01003a0340b100c071003541e031480314000d00d0304028505600c2c450b0b4001845242904250741107881d000703078807070640c0c6003460141c030f00390304561600e508000c0b000c03039000d0348491280e043da04160303424030098507400c0051361103000030301019400d50090340340000d003400c154031036243d81d00d00005c0c0c900d0365685001d034014880b401903c85000060140d00154404d182552000c000303083c180004020200701000060f8145881d0400c00b40602c1d0081010840c41c00b4603400803d1101c1440420300412956103070003415540100c403050310030071403803011035552404e84104120461014004110b0201e000074100400f070310051000c02c2074403805c040110171101c18000740040404002e0005507a490032000c4c0c0c0e80c00100c04113001001031a01c2c43c00720114900440c0d041d040140c4c1d00305054050003240101c1c1c00d00440c081e01d01c080b50b000000000d12081680105412144180c0543e0966600c40c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 633840449 1250 633839199 633839201
    0x2121140a0e0103061e090209060c06090304030b0f190908070f030903061d0a0803180a0302031e09060a0e0a1e03050c01030c08010611100e031b1f1509060807090b04 72
    0x40318945042c21881171040c0502d80075a8010515204020100350804100380c007420b103000c5c021075031010301c1d0b00007207420400c0111a04425410000514000c001e516110750103268070043e240b246418552100c0d01c40052103099400c07030b595540c00110840001c2c41c0c904000d4006c21182c80210351403450131510702a0401a001d030394008502503006030604000949036007625810103005800d0700c80c402c1001d030b10102410040d62201c07a00c65001384d41c8031320f482803403108405403e07000c1a070f0f4802e04010202c0c0f980d40d13260466045500c9400c000c43c10181c51000b00b000c600b6030f0f400000c4200507281c031043c0808000347d00c0380103d0384035404a4a02d102c00700700440c10f49071446d1180e0086440b00f00180401806000121030344c14852007228031110b130320810001503030341c2445500c4943e040002c072600041c16414035451501180001440380d02400d501e45c006507100c85141810a5a0f1000040e004030035505d22040100588030040c440143c40b0110345450394030500c12943c40c20b00d03082d64004c0c1c60401b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 633841699 1250 633840449 633840479
    0x10230109090c1b02040204093e1210090c0324050609060304081608070201020609070602100b062802060a0b0f0904050f01090c2121140a0e010306 64
    0x34581d80c031070715440088000d0030202c0e940f8004030782c813903000d000100c1d02c07051510541c0c08003d65600282c9060b10500d504050032078141002e0a500400212102a40380d0743c0c1c001c650418080a01400ca29540c5404003c00000f00c2c1c0c10400c2d406007800030b03000c20f1590540000c2c5e407042d02e44e0001c10b07884220040c07a01608841d442035607040242400b6224180c600100a580d016000d91503892030404000e000c098801c0e030300a021500203c000c544c0c071040d07580c1000b04984c469215001420281d00340407010b50b0310082d02d5121800f60341c650041014a488000942e4141e041c03241e0b44201c000c003015800304140300c00d404628010300c0344600003480b00a040c000c0d003c0c900d0000d0f1047d8131255502c4184180f00070000c00a880034480e407a13092140200034801c1840d427a018044488019007080040203128045032080403ca00100b401070000c21803030b1071820184000051280c0e1110f45007030080d03c0035041000e100020b041f01080440005820011022001ca030981c1c04001d19900c0380010241012 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 633842949 1250 633841699 633841721
    0x23161b06170a091a100e24011701030f0b01060c0209060402090301090203070b0c010507050301030f0305030604090803150103050a360c0b0306190602030a210e0c0f1f081023010909 79
    0x6410902e00c489007c16001c807008178041c50310756070310494503e04201001e000e80c4105d86131a070503081442401a80a400b90141545c0d00c2c10414100040d00059034855020300b030a44210303030014504a15540035030142031410f41c040c0546004039910100b829032070304041003003043c40d420507001400340e5201d84103e9058076400910b0490000c0d50351030466580d04000e21540c0c0040d070325014140880c1303901700510303c210604050745829003c84000107003070305d001400a40b641814042007d040303080c4039410380340200340d4000c548103100c0c65005006804042c8100501088503000003c03483c6140c81c001544a080c061782c8240c18401c103030b01e01c030804100038490070740180c00600101d15503501c070700180031080002d814000d086a04580c1e4020448200010f06203041e0b200d00310074012030405030070402115400700e8400040c141c0c454002840307420841c0c0c0d507804100090380000c0620000340034030f40180c010170341c408000e510200001202d103080e440555020a00b1188006200b10300c0d0302a04035110 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 633844199 1250 633842949 633842971
    0x30b090702010903050f031905010b0a270b2a030c060c030c07060f09020316031b0e010605070f06091a090708070623161b06170a091a100e 61
    0x1081c1c00c04000c1451f08050401e00100c81402000c0c04d004415009d0540a0f0030a504007980da07a440d207501610803d46103148880c410447d0f0031614041c07000c0b00c00320342265400d0000680d00c03080c4000c050829180d25015000100b02d1030350007840e401e4000003410001945108480c11900c0784818804a8001214142a505802c000c504005011078001d544a90b0018034082000030700307540064240740440c501c204200c110f40d0f00030024410782c106801481c03035960545030001e6041a28001846105020342e01c00d2040000388081000740c902580c0c00030325000442000500103610780800e2034001201c2d2202c01c1549000440c000701c03070200e1140d00b203070711082c01050a42e02d000c03c00d8412032401e500c01c440700c040700c03010301088091140c0244008882c881d2048580724640c07070101112005042c21808160207031b0020b100064011506000d100182c811170003680d920008403101030603107804000c0c1001400754048a00441021701e4600900b28141c51000240d214020480c25a070102e60300300000c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 633845449 1250 633844199 633844207
    0xf160b150915040e06010b19090f3c0e01060e101808063108070b150d0606030212010c081f0b03090601060f0804050a111906030b09070201090305 64
    0x603121900040032001d020307102103131440d80d04246505084d1700740c0c0041c4021200180010281d00d640031000310007460307030030102c1000c0e081c2440d0302c4101c5254058038260241c000e920484101000b010045921440c510900185900341d1032065039402621412900424020000c1075040c011902c50740d0b9001c000d041c201140158120444070407440d02440f0440341001030002c03030345e240c0070302c2074a10a00c0544201148017a8482000880281200d80c0507080e4070060310301d80018603a6421107540503004080300301a62142d503441d1454685c08c081081e400910070f07500204001e5241c025104882c02101d00c4950740540140031800c1e81d2801501c1d800048000f00090514004441d044001c010302002810a440d00da046650490b1300603101080303143d102000401003a5070045405000e80f50615101c101c904080d0f940560301c00441000800810f0030300d03400c400d192252103e080c4118036150350302c410f040d40c640001e0014490b07420700500640082d0005030f00640140503d02036154103584161070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 633846699 1250 633845449 633845461
    0x304050304121b1a0d051b0711181b0c0102040b04030b04021e060726070c24050a0c0201110714150f0306060f1603050306030d030c090501030207080f160b1509 70
    0x1400c00800441c0000b083c07c03200444400440c015040103441000c0100c4092070390400c00442d00700e2165051809880b500804c000d00c0e0703002521380e40c00c01d008007043e61100c1190b6981b90180c007540e0000c4d110510301140000501c0302074072480e402240243d901111003195061800001e00341001c500740c2107001000001d000499400d0301095000c4c0241d8203841070480012551a280e001400c156040c070314480042c066004440042040041c0c80600790800040c80c075406080c41c00745800c1c450a1000185c0a1400d6901030240f2070030582c11042a101c3c40d6440723002051408019110582c02811340c2080450040840000c603015801024510760940d551141041516400b0741c940c850483c0082c0b00044100041a0302d002aa070300c40e0720b5190b101e161840525182001c0b10508204050a00280d0b03c000e83c3c00c00814020b0303820a20b000b5aa440482c1400308061064951140100380001031100900011800701e02255104101208080d00c860780590300a010401060380e0156070500440c031 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 633847949 1250 633846699 633846701
    0x10080405012a030f09170d0f0f05190b030a030f0e040c0f020c03070513050c070b010801090b06060910120e100e07060512010506130305060a0c08061002060109020304050304121b1a0d 80
    0x87c00d14105000852901800f0b444c020503141c44086111038203854809016042c2e10b01905410320010b1040708214038040c14001176a500e69810300a01845900101c08000e1072040c19000248840031384203200d003002401004000c43d50304c62035000140198035944034030b49030114803001101e000405a0f5032200f6007000d030600505c400b501c0041c980301708000c40000624200c1e551030007000210000241a0142e06010602500080c0260b1044004001005055941c840f20002502907031030214010134051141c1401080f610401d12006d104215090b07403091800e80010804103d0708050b110207039900ca005507424003e081d003c802c0480158010310027410110040c10403500384004500300360b503032612032034145a0b050702d54450068079205012075130b90304069403e410040544e03402a182445420082d10782c5018003684088940020104051000802c29540a03280446c1003030356414540c03414440e00000341da4102d00145445800180c0c080001885154910703c4001040c688458190008 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 633849199 1250 633847949 633847957
    0xf0a090c1e14120c0702100c050601060e030a030e0f0303070501090210030623040b0a09050403110304120b0423150109150312020f0709060906050f10080405012a030f0917 75
    0xb0000d50014040c0b040940e03600501802003601c907464030410800503027001c509108050b007008041c0308000081c0846920001562404190180b405200e0005000c2c0001d609400802007903616110103da29000c0c01019885510607074401c680c026107101207080150f09503500c910030840d0084180c460303090800b00c01d604d51100201c000700000707000d041e210002401800c80d5040b00d01c10503511000c100070980c1001044054180f92001035081929100b400b030504403801c00020100b42080000c00e003080304145920b01e06a8440748041c2c1c0012121102c0d41d954103076a400e4045030111200001606c00d1360b4403d02401c103105c0540c060040d42180c0741c40ca45001c3c010f65060461040c0400100e64810500809014141c0e500c000f0074050702d000c0480e01582c0240e0080c602c284002040415903a03500b4942c4003e0310b105042c4840c0aa42e41d04002d80107140200f44d4003186460380580010032908181001011a46920704228070181c3d903900000302c0b80707001c400402d075905c042c11030b0030b031051144050 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 633850449 1250 633849199 633849211
    0x1106151c0606030803090c0411041421030c100903231b030d06091406040b120d0203030609150f1207090f0c091a03060f0a090c1e1412 59
    0x405080345503556a000300c8203150b0056030203400c00300611441100c1070111603001e040c100c8e402e01030f01c444040340d000315205902c85c0040c44424180d02034010f0310741d100a5040140c040c1c95490a0040000c81c154a070780c49110f0f08011402080c07031201000045201f900109a00340d501c0c680e8035940909040002c0a95810351004900c041c0001e401200b140e0308200101c481e03220256480d00d0411900105079401c1c0e030061601d050030582c90000b41071003c0440c66100b80d040300c0104641284c08086101e190068071451014000c01d41c02140c02900040118050312041c0c0c1c80720300c45e40c1c0380001111000e003000a001c3c0d020084078440da04c03916048041035560314100007500c1000d5034940468003190f020003100c0100d661140c441180d13181d04410307200c000305840314402c0b5480f014455030001500c001403c2d01d10440a4a901c28020b44070303c0d0000e405000004010003608600c544051312615500c2000541c007090306140c0c0004500c601c031701400321180b0103011410128a0015110506001400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 633851699 1250 633850449 633850489
    0x10f150302030705160606030506090f100b0d17130b03011211010302190c20030601060318081c110a0e13090f08030a0c0801060512060d140c01110615 66
    0x3d00352a082d2400e20464400c3d111b0040011300307d1031481c14501301000104611002d0308489104075600e1404034050b584501d035400000f84508060b07000ce04d14a0b04408054640c246400490030b185a048004056840b140040381801c903586003903601151009028170b000c40d0408140480000d040e803040328222a605040240c1428400c101c0040e0f50402003001800050302108044180501c52180081d01c0c40042c18806c1405060000b00c1d9903400184125010140e40741e100c4960320680306e00c2601d0056000129a41e0b586040a1060000c802a002100c040745080a20702d0600e9000040359000906901e4000340e0284081c10040302c0c00d50110040441c0703841c2c1c1a940001082c8098008079180300c4c0c01c1030f030744904141000800304c842004880b428003c1690040c40302c0c9800406036100540807500d011901c1e9078640115034800b003054401444081e046100f016400d80108030740098500030b0762921103833601c621005944078400d441501c2948035050184c01203040600040300340c900c0100c4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 633852949 1250 633851699 633851707
    0x3020303030a0605010e0a05010e0d080c0d050d0e15060402070f02090c07120201060b0403120210060f081908120714070507090b01020f060f130501060f0806010f150302030705 77
    0x42030a50780111a070618460741c520080c462913070007015111a5142c1030325085840b0f401d00340041c2100018500080c401c030b50f18038072402004400d07011185010641026685d01c0b0401e00400b0700075800c944c24224495040c01001e04a0017000100c0840486842e100c0070b2094840704d00340002944403800540310f1001c1c1d0b0084d0409601d0700c40c800c0c3c0c051082d20528a9940c1c1a60803c52500c6c0c00e200e6406007164108401084004c68800907a02529000380c1d41e03103a580c4646009915103640d0403480e8843d1400c0500001c0c04071229008034003100c1100c4242c03040da82155001100d41c40c001c0f07100400050b018401d4400a04558441941c802d141e82170840125060305e5010900790010a011600c59020704000d12070790b18140240301d204c080a000902c1b007117188140a9464690040c21100000c1803100000e07002d0303504156220185030000003c0100c01d45440da50b40009100707008107015803284100005046250b0480740086428560f0841607441009a040300070f940050021002c101d4244 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 633854199 1250 633852949 633852953
    0x1502010c080c210c03010311060703080403121413120e2b0812010503070905090a0f06063c03030906050705100501090c0807030c0f08090a06020712020c06040617040c03 74
    0x9040c4c054a541461036072250301d14a044250400c140f4001b600800c8284000000640c211075a1600158076052407040c50840051030001082c03560007004c81c1030301e03480034032800e0b503403074690b1002a501414042c44840c4002c80e050b244c01400402c03064000300090840d02401c4100440303030b843c4001d80300c14140d04460940b41c04089400900d1215108101c101c010883c80c82d080002e80700904003c001401180303041c402054031145501000f0b440341ca01586072a04101d075992001014021001900500351b1030b014a0342c0d10107284c6881034007512043d42140526580c42c0c003d000490358140e030b0705448030b13007080801c503070701d401a03d4215a60320a50307000c503c0d55003040c096140a04841c81e00002e80081241f001031041801030100001c3c9403500700c40108507a0700c0000c40e1000e061505003101c003501c0703050402d0700d42401c0342c0010b000c3c644003240440170003030214010314011415600300c0300c0d05032021080040f00d01c0303144903100204e0111080c41e0455040d002a0550080c040d80e82d40003034a50303075 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 633855449 1250 633854199 633854257
    0xa060c05012c2806090f0203030a030b0f03160b0a0e030618060a0b0f12030c0604050307120216090c030f060e0618010302090a0504021203070c1502010c080c 69
    0x11090184030020b8031000a00307001c2c01c00980e5000281003220741e0070f961420542d26664100a500030700000c0c1c45042c024248851104000d0043da80541182c0d51680b61a0f4001c00070524203100c58800c0701d03410900521403600143d1500c1e032070108556106a0780c58941c81003890390010b0b80d5141480002c0c002c0003055034082c440540301d0121840034403190004441491f06060340100f01600a80c907040480111383c8803040010120740081e10240c0d240e00708040440d156000d01c0f401100b080c8030b51006c00003048008005030244c9441510380c00c10007404100141d8072410f040180c0741911040c23080401151280350002e0181c1c6004e4200017441020914031903056a66641000041460500a0000f5030801d043d0504d800003004004400950659001034240300703003d81003080340d545810104065680e41c0b4402c10001062508603983c60201d454031a42c00d00c039500c40c170081180c03c502031440490042c010000d00ea201d681c6c50400c10f540d804145070305600700301030400c460721610000110500e00303 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 633856699 1250 633855449 633855491
    0x3060a24031e05190503030f1f23031902100c083906160e13051b03010f0e0a0e030318070801020d1505030d05040303030b0418060f0b010e0a060c0501 66
    0x41006d10341c1c0745000d110f4180360b40000313081013107101c07141059008120142c00399201914038142c0c0190f10303107041d1381d040002c00c0d25548606505003e00882c0c205401e024650402d80f4038400c0e540c8a0108403e0301c81600c007000c5402c00130304402e004211903c49d2880030702036800804d8000f828580c82c032036004030703d0901c019109015120f9502000c03d10100510580814081ea001858009080c10419000c56051a10000c0d188492916040461500d051010403a043d040780104c1150302ca683d100c17402446401c451180c2c1100051903408034a0800c054060048100b83c000000c610b50340720081d13134800851303601c030179101c03240600c0302c000c54155030a0004200c469443c1802150118032065a20b0106140368000740c8240c0c4442c0e9481911b54011050750101c0e50141800038041c6051741c0810054000c201003910102e0035020290108006607010084003000040d040200400c00030045d141c00046001081d444905210200300380f5100e60380d0035100f188101c001180c0e14200143c1420b512203 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 633857949 1250 633856699 633856703
    0x72102070302030a121e051806070923011407050c130e011a0315180706082a09061b0a0303060e0c180105030901090203060a24031e0519 60
    0x70002e20344800c80d1703009600d80e0681d51940820008003448491490340c18289200102a1039114070018816107007100b01050b982c1c0041090f10300701d14210200a010010307a000710344044210011049550000c0b01c0c105503a0314041c0c6030b92904091358428580207400c044400c039150720514240d038000380c950b13030703040004000d42c5180858242c04480c001c6082d160801982d1400c8010401e0409043d80c0000310444842e501200000c80ea0702c0e44c0113086005140341900d18241d02c0b40c8040022601d9100c1030b500e100c5c03840d075400d6126030110100c900c0241241142d00752200e26040c0f01c101c8840c9001c20051080f415001c1500340046150240c40c0c0c10803600d03200560200b9610300b0f0800551081610055010f40409420307490a1611078151001c5521050a181044000302c00942e4007002584a48007698004003180c4c0340b440c1c181c499601525864692109070120301c012121804500d280850940e07500c200696400302003555814489500460140e596106000c5100d16625131002142c130558 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 633859199 1250 633857949 633857953
    0x10c15021c06050301060e06090a0b011103191e21062607050102030a09091d0a12020c03030c070e0705090a03121d1c050f1006170a02010503072102070302 68
    0xb5180c5410503007101d2080d40711307034032021200701080f449940300c9007100d80c8460310110005038100e442004841d2036811031203050443c03000090042d2050710400c1068910003190b0b881c030041f9540c03489100b1141d0032000c07950010809001c1c800d04902784102c2030030410704500d940003803da0b07520111a000426103806000203444520700c1403030302d004144140c601800c02800207600c0c0207034100c401040742070a44540060b03a0759038010200785020800e07085150400840440d103246800742019082000301940c284050321906010031414100801a40c0c8240441380140c01301d20f20709510f8403403056004040c0c4040040c10031800b18680d130751121170b030003440c040c40f403010115200e410044c280d404510495800354007074241540da00c1d5a8a020541c4802c440113450502c40110305c0c103a8505500c0b40220560760090714000c50384108117500a40484007040d82014040300e02141445e11100708480182c0040c0c01040010348a03401070f2020013080394800c818000654503680204100d8203e014102c00507 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 633860449 1250 633859199 633859211
    0x9060703050910020a2d150507170c0706110d48050c1204080a0b0109110a110c03060f190515130e0706051201060905010c15021c 57
    0x2034204560883c1c02c0d1446400144074064168031010011181c0d503021b1031802d841c0414001c00401e00142c45401c00c2e03408200702a0712503244407420050700c07085404a00013014100045148280390b040180100842d15105242078041d840c0c4c2c401500783c0191540804004011841485060b403050b511704da400c000c600d000c0320150203208a10300700414121a0000b110041040f56040744078866aa45403041c02d06075030380e600817480036081c48141d400418120f000468002400d00e400300744120240c0c072420030554076a07203810985d81240e030f04000d440b42602d011700100010a02030f210b500c022070115002c4400c042e4410002078035200d000c4900b00000681c40b014490520845c07105440c280146110901481c0b8040364888003c00059004601c034100c020f030410454030181d846080c907000d400050390507864445001900940c01042404411500a03000141d61482501c804060ba0016520b000a00200e5164108403030620400c60b0000c0b5800c000c0340c1141c103c10702d0b200d0101a1b40900200300 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 633861699 1250 633860449 633860467
    0x406020f060c0d0b01120906060503010605030111030a090201020f07090c1e08061509090103121103040e04080f0d0c0309110f0a18020906030a020706050a09080d090303020906070305 80
    0x18946884451100c40d03005209020301803030400b09640c0300c1d03090302000080211010004848400212503c201080d107000c00510a0100d1030308036a040d19426030003031040c3d03596101898221406600621444202480414030f4488103412520083c2c1c0144100c07101081d0f05c50216042c420350764004603896070354450391042503400c01e0120300710300e42240441c48401602c0c40c020f1f021200090203030344a41c0c0301c90400c103404403000054031880310b0080c0c80e002c125a1685000d01140b40e00c030107d0004101d0b0b01c450b41100c0c88000049400384c490030038041c125600c41c1d50307960302c1580200d440b15407414024414203a404c0c030580b29081504101d42e40c0494010b44900344000c01e2004680158041c021031f60402d40c40e43c032040540c81c22500159490740c4009980900c0300000d00a0542e00c5900c403000100b441070b801481d4018201090050714100225100c1c80240e008441d003900d401084458203202040030702045902c0300f08140d000e810058a0010030703c0012b9500d60003d08200d0210b0404202e03611 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 633862949 1250 633861699 633861703
    0x60e07080703150302010818010f0903081f081b01031d011409210c030705190b0f040b0103200901060f02011d1f110a030203090c09040b060f0409021005040602 70
    0x160140c3d0510800c4051411600024000b1500828045200240950b240000482548009204410f42004001c215904d1400900424050305c1c021032038400103144140c2420000002c0d01101c4845000b4120f064010000c503c2511032a03c00605156440c2411585402d802181c000c03403101000c00011030091090028461410181040e00341b54880c04152600303601c0e60070500b00600303507850401e07260b101031031296141d03105e00c5500a20f64052004030121343d040c841c5594103c1b6105442407807407544c1d500303e04140c3c07440490f8003030004110a0010408202084034100789400b00c0d0300e000b00201d0310705001c110822003e0f0300c0880064081074104c00d00c143d0a209900c858045800031100703988695543c507581742090302801c0c126050004c940c01c81c00990350b0008070380d650483d521903240d0001d000064000e4100301d820f0240d5018814034094585804802c25107e03c1e484609000d09446800500102d05000b90b41d45c0c3e0000c0c1e40c0c00e0400d01580c0c0780880f031006051b40c1e9507215606c0b410424024 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 633864199 1250 633862949 633862961
    0x1b180c09090f040b0f040206091c061b020d110714130603050f010c02010e0c061605010501092c1011040b07050a0c0509040b070507080427060602160b0904060e07080703 74
    0x80d506407172103414840141d640504070360080c0e600b22003040a10182d40d60384140c0d5499020000c2506203445158032a05504081035040da0f0210b4090300d82c1040303c5a03055460350036180200c07216400002041c09191401c1007001c0c00d0060140c000075400c0e4034449141e0494110350001e9400d035102d00c20210700d1000034000c4a1003c40148000e011101e001e1302d1180ea24610320205a11554001c21608410800041c100510f960450000d01040d40d47d00007540c000d20911038055041d1440040b01c0060013080c1c0c8407000c005c1702c2d4200404428000100b40030082a101d04810b031504420400010311010381d030050014140280c0c06065051744928050381a982c00e0b601150081400d0010080031070031b0b0000c1d00ba4030039a2400c05668030241c2d89003084640c4540d412605040700c08000241c401c0c2e44040d9042d059101c0d4160805c0816114242669942c00a40b00703082000354401e82481070a4050001e081c0c10311300a800070581544402d1214000801110444c1c0014042030422401e56414010b003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 633865449 1250 633864199 633864211
    0xe0c030c060702130f0e0d0305040c0e07080a0c0509030307030905093607090e030703080a0203090309040b0301020702060f030415060311061e13081b180c09090f040b 73
    0x1e52902c482c69022588549000c0381e1203000c1a52042c0e03411a0703035515000f83c001888800140c40701c2d0120008050003d01040d1800e480807409150040749002000101c02c0c02146d041d142e40c2e1303056032024410b0014042408440c0104542403180b031146840c01c00250030f00901c41d803550340700642850180540d10000801c050000d60347c11034003298500c6c02e0b401d00014910f002c2c1d12000700c207840811043ca40100f40e8481413010b45020013450004401002a192044c42991811030644414140c0000d90000351655800b94001b000300c85074901d4103a02c02c0d4000c00707001d00007508040c050340001e2015000540380136403400d0000208070800201c1105c1070309071303062070204100407415034407024822616004483d0040308006030034407000b210080e1583d01c1d068681c0c4850342d0303595240b10b5031400c00f515101e451860f104241c49410000245040c2c2c0b0750400b030140040410140d10f01c2c00a0009401a00324100240100320640301178940c20030840c4510948480149241482e240c8595030300001801 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 633866699 1250 633865449 633865459
    0x10050114090916030207121707080907050d03030e03030f010512030c1009020607050706030b010e090f04321506030102120606130b0d0e010606081003030807050c010e0c030c 76
    0x3000c00c0c41c0e440301d9034540c00003224a07200c5030f20040c014096000388145d90015280c0180f62815005c140d911020070f150071200c100024025440c1c4d0303001600c0900d02611140c92a030403085041c080c5050120307c400000e030080c900803da100d00c0211081c01c6902c20350340150f0ba5040003005000070f060a1104403600341c400302c0154038219002e410300e501d61300801d035211801911070080b01c00799a02d140640300081d4004040c2c6040503543c1c04054000c240f01070074035002c201c01d9201513245107846000355200d0250003110396106c2d03440fa80c594059618a40e1842e00300701802ca8010154807603503081d003443e0104103008040e107003104141080d0080000342042d100b81e00411203201134800000d501034001c0c40a0714441d444411800e0000c40f0a045a0085c2402c0380f0003007010b8020102d00e82000201740346800c000c0140d242c44081c12904c540703085032138480c0b0081300c000800000e840f896100f0707802442c600d00141410b03160100381d03096840c8428010030070f520600d0090380c1c074075092201100d1804101d40c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 633867949 1250 633866699 633866707
    0x207060804120e0111010c020c0a0512070b0a090f080c040f020a0e0f031c17061c08070f080403081c0c09060302030a090b0c0408150601120504021810050114 69
    0x6a841d02d0740654503086420400314030820a09079003d02c0422031301d01d071032074020301c8090104400250f03201c001c0503940c1d101d00020140040d503400d1541c802516801180080c021700c1d81002070903201540f00c42860750070482c114100040c80389031140b8501c040e00c40790015145141160301044140c40e40b120005041910400452110075084454039891041c1958504107280445c0d0001e401c082401d842c1e1911528880f562092840e40000c0700c950444d0b89015040b01c40d01c0301800d001c07540d84803013210348880c004021202c010a8200c0d02401c5c40a06c21840241d1030a00c07540c0748012500540d0040701d88080c0441c011520255404000e8024428502d0400450f18001e200038180700044c4190005e140d800000301d401c15078150840980c05030000c5140d0b100303060035500060b03194480d01c1207070b81c24020600300700c608142080301d0390b0190340142e41e004c120380c0c1c1e00c0306484014403025000b2684036004000000039450103450700c0307119100446441d46600d1402d4005040c40c851140d40c00c00000c0100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 633869199 1250 633867949 633867953
    0x70210020901090e0a060f060f02120304050c090916030303090b16210f090302030a0801080a0b0406020a0c051f1103010e1b21010f171b012c010207060804 68
    0x450f0000403a41e003004108015101e10360003400030172040c0c100100c0e143c84600301081c581d4201da0351010506280d0300301c0383c00d40807000d002c0c5d1031808146c40007001a0020b140e1b8226074a81110520307001002c210a0392100c0807e00c00700080101d903544211301094a802061040c0043c0450a40d405004291701c10f481602c208001009207032100f00c50708003801c10055070301410f841a400903040744080c00c2c0c02c020240c0d642c00c2c041d680e07030031022400001909040001c9500d080c00b24560815a40c0420791804948980c0e49040c069006450000c08000d481151034010507410841c0351030584c4c2c910b00c02d6800107000c0181a068071410551310402060404c01040305401040580350700456607180d000b000c8004150006480c400c0c0e400c903010540d20b4100d080c1c09002c240c0c400ea4101c403280d001501806a03180400201410366002041317080d00309020ba464181110a8041c0e100300c014905440e020105104071010a80440b802d0721080710416461016540c0402a02c0082c3c40030342041c40051600e5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 633870449 1250 633869199 633869207
    0x50402150c0109020a0e01091b0c0611070b0f0109180b0a1a090c0307030605011e0e0f0d06060e070e0d03030e070b0c0607020c01030209030d0c020a0f0608070210020901 74
    0x24001000c040400141100000c1001c1d88151026a030082c48200410794070946840c2201c400c2c0640451181340400c81c3c05501c807950142d204800084d110f44c107488016454040c018040e8924010503100d00704a99000034180c0150941b180140d00d413810201d5040c0341061040b90b254500741704003810140840c4010a8070003030b100768002c08441e008030706e110201402d800c51024a821460b007101301d240034401841d080c40040c503c68000c03036404000ea01d959500460300c540c2c0082c1c082e1210900d0712809076a09100d62000e4400e50000b40140c2003c04800e80800d4000d52680c80a5449558419060001030010404c0617040406e915101c2e41034810000000c100c160801c6c0000c0070325540ea0f007441c21100040c01410700a02c1000e840a4070b07140c1d260310090300d0300c0044410380c005006e04c007d80303040e6600910903500c010401800402c02c0c1c0c42c0da0441520b5090320024141e074004a08440002d1a908c05482031010f000c09a940b0440c5007004040030b841c0003003105060200f903005003d8200c50b039900c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 633871699 1250 633870449 633870469
    0xd0204091505100c0602090a0e01030b04030f020c0603010501110111030c130f1a160b0c0301170723010909110909010b120609040303090f050c010e0108090304260a0308010f09050402 80
    0x51760042e0303242c1009000485032400c07075000706082d86201000005100902041a1080303001e030700d4082a1200f01c507012a128048141c50b25401a428001803142e940308000c1241e6000f4400000203c0035404450b86d2442c0d0001c50340070000e0700700000c9904503042c200000400400944820038522030404030182480440220a030720380240101e060101041e440c0ea4404ac10781c1c00c9980c041c0a0704142341c001c16a5030090248500c02c012002000307090031000074485084480d41c481c58910000260542c400103503034078104034100000c2180210b80c0114501c101d0b034144016848140c1d6440ca8041440030b5201c0c16444424030710030520a011844000103100c83d8030280446d80b045e4240e603649015402007424280240c10840076841c81001c00400184a281014090302d0b1039041c1174074240111510340c42151040a250004e02040056842d8028090300f0060085d1038607061040014160345407010310b00040c0d001520032001007010303004146444e0003800015a09000c18503050300030448800e0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 633872949 1250 633871699 633871703
    0xf011a0309121c09030302040e01050306090a060506040e122101080712061e1a0607080d0509070510030c080a09050d180f09020408100603170c030d0204091505100c 72
    0x12001a15203c61106041e051403c07510b03803201001181014180140250051300844801e600321000100d2140781c00180d41d44103140d0750000300342d050000e030b03240806090b01400e15030300a40c6800780000c0c0c1d001c00340300398000e1240f00030703403181c640140d1007000c4040c1a26001c0300315030070050001880500000300c0c00400740c66031000c000c0301404203450401e0041164050b50119450020f2820b84c11101710307000503c0f40070301c007002c800b201d800817000c000c1e441c0319198006250b113101300005070000c1080e8021a501200c1c5c4d1090301c071502d513100c0200b5070201d00e8a18802c0040c0d695120f0516175500402c58a03040a04804100030501c11030340c4241c3d64903003c0c00d400b018040002500c0c50255100449800605604041d445400743d0340c19649010303412500500d130322402580545a40c1c12030901c224022039401c1088250802c14808404445902808062004c0e00003003142528281342800144000c20f580c5200146541c08010004200009500301d24421203144003d1075505900000b44400c10b5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 633874199 1250 633872949 633872983
    0x30f05070305040b1c060b0f0d0902121c03060617070e0a03080f300414151311010c0c06030f0b04050106020d090b0a0903080a050903060f011a0309 65
    0x160315060940d080c0c0210791040c84041c0303000840560011062048581ca112503140034004981c4680940fa00c5000308203040601038000d00c00f00c5030083c1c03280c2204083d00d00142c4030910010120f04a142080085101c01130180380e681000c0c20319560512400b40100410f1400d0201c1d18800c1011207130701c90002e000030040040d50a00c596141d03460444400c001c0d907000101c90b641e1034141d850381d80706403c070400740c84407403041000307022012504030346155441c16081c0c1ca507061550f440c3d4510711751590071082d00c1c2c418402e0201192810204188640c0070349004d00038948008018030381403a024041420840c10465001402400115140000c1080d612a4240403404e06080c1481c5c80052025414190303101c0d040000010b0101d401158807414040640d840741070301c42d01e50f080d501586c803858002d4000100c1d001c030200045140300d4050643c9410f075107040341c038203159400020701d8050103503481150000f0080042080e00c6607448017580440c42da01035a03065280c5aa1203a4444441c801003504407 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 633875449 1250 633874199 633874207
    0x10050d060b04140f070f1b080a0512271b01031d01050c0c011b0509090a02040308280906080117210316171b09040f020c010b01030504030f05 62
    0x103a640f604221002d030b07050016650b007440c00814079603400c8015500c0f0000b040c0c60440c400f0b0103d2140030b49070440c5c2c0d1411148200040d143c0c0c4e40c03504a5021504400130880c007809142a50303011700241e540503000c80c030030714268801000000c002482000c000c0c441c80b40c0c410000240b0200241c0d041801c00c2e0001d080002e103800e0032404880c0f104060410b40e10700e81d441c09040088046c2ca2102805110303020400800040d0059000312200710303040702c000c0e000f0440902407c4c80d5840e1151401d503021303118003005800d1680d0f03070b0b9580c2c0d03550700014204503540140b00098507001c0410480d54148440c2c42c0b400f4820704c0d2074400050300810041c002c20414034440314803050785000030000000d031140b9000f2240741903540143e40742082e820554510f0802c1c0300b1659442602403007200b00d030b415120750007005081a1102100c20400655102e100825044103115004003a81d5074403920410721110603001d40c4e5441c1740c2100b10b003101d10781004641071502e1702042c0404a6441001c1c40740e06a064201140c0d1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 633876699 1250 633875449 633875471
    0x19090809030a0309090606080f0a0c0e220c030203060d080d0e15040c06020601140603070e04020d02070309080102070308041b0306060b0c0607020f0d1805030a0b090610050d06 77
    0x10322410310400d03094400d0758240402c0590000000040b1030329600c00b044616200c0100b294016410b80d41b50310b000c00080b002c500030700d810f503011030840703a144e00340761030440c5444012594000a4010702c100302c0000f80c10b4400012194040c8e141c4114072490218510b10345080016a4054558405001110040341811040e00280e002c0c04c030251010b03040f1380b11104401032111103003604850440350038071441400110ac0d400000d805041e200b0300c4041e40c900d48650380034440d141d000103140307008220400c540c403000364495100411135480c0e00c460250703840c100743c10090700400308c907408070741d940e8410410040401d90089047d9045503001000c122002541c000c900c01411403508013030045464080f0002d05182402c3c0100510402407055800c655141c003400d0344c664100f040441c07074940200040c01c4007148142100142d01000ca2031001c0502e88400129141902d542c4007201c25442038014807001030030821140b54003140c8141000707840d40c01e01010400c0003051078402400301c2c0c3c54840c040c82d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 633877949 1250 633876699 633876713
    0xa0b06191202071202100c09050d030c0f050d03060b070803040602030c04080601090902011412060f010210290913020f12010c0e010801050a0f03080304080f070804090f051909 77
    0x100601c1161010341d1218850f0070810300300c40c4d51040c01c0780036204a90120030380c41c0031402a01d50080d80380c0c803400c1285140809000f40003940140032003c010403256204005003a0b00740c0050143c2c084d100408001081c1c180140440312070381c115103032440c8144407201c009000b910031254000d40c04800540c9980314481c4c00c1617280140d4000003400c0c01014000f10354507600d0780c41040b40034000d0741c61000d4a01404a24050fa10841c2525000255038000056542c00e00342c07003036100344406104640c01c03000b60b21940300480b500d040c82d241e03004064104c01101e005460402c0e01c85403004445101250030405c1c0703030b58800c440d05800240101b8540d0058066651140b04140c02613a080c4002d00c02e00c200d85074010304007416502418041a1804000300707450801c051024183e804a01e0b22000b120b06507103a1141942004100f1995203a0410400307062f0140079024141c19441021210340311801d080c03001c01031f1586104250070451038402004000242c0c440c006c09254140080040c180e1024100781c2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 633879199 1250 633877949 633877967
    0x908100213051203030910060815061315030b0a2309031b15090d020309040504060e0f03130b0306010e2715030105010b0c0d1b17120a0b0619 62
    0x95031240049090300c103c01d03408402036100c1c40038802919a9030020000d80002c484050281013003d80c06500243c695424140b170841d005200241215485030b44181a06d050b07401c3c0d040c00c0039040e0a8240200200283c8100e41600b041031100244807011109100701400d0143c000c030b5006041442c0c000c900b52140500071141c0742141c64042144a080d21081e80e6603546220810201003107817040091443c0601151082c04103001e076000d5841c4c07015000801c809858060401d692165a0782960036140074200600f400c420325050146480f40c0080510020a000941c0b0910b0102000c00400183e683c0c003006100b0409400c9a41c440c00c0906114052000c0106030444904441080d043c03046403411811050b1066600f14001e20440e03880d1104032043d80500540d00120b5070046060351820f5002d03640a0035440007210440f04142c07490340b40c081d44110112905224807400261500c10000c006021950041c6034540502a028618020804900c110080d04048585280b582c0c1c0f50380f4456040a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 633880449 1250 633879199 633879209
    0xa0902162604030303062903070302130f0608040302100c0c08161704080f0a0818180112020a050d05072c090c19060c080a031e090302010605010908100213 68
    0x81e00e032a244c3c40c02400400c0240a502c03620414141002e4400c0e00d0030440b4006c41001c641d9040c15070300c844070164069080484140c90a41c001070340400d4520800b0b11040003885181d036000c070f15041c10b060290070080007120f141c0140d41800307010050207030000e071441146ca80c040368869840a240c440700d0f02040a4900c000e0003c130303110b0a960700c1d07a43c68030007400903646020242ca409c040c07112000d5a035640552002045503406210415203140244e22401440714040c20f0010080c2451031282503610f400d1704a074040c50000e9060350300394209aa2200c0250200742e890148116258031050b942d11414802e4140381c0011051260000720046c24030a018484e05415071542d0508281c15030300d03106d4440c68035005009070110050840750315030b650021540640c0f59035400a80e1a1503031815548546281c00900d40c1724030004c5400001131403000018002001c000601e0f01503490002d0039224aa400765040140510301440584070106851b04e40441d051801a80c44900b40000003c000381c075446 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 633881699 1250 633880449 633880523
    0x5130b030a0b0f13110910050a03050a0c0510172d09010507020c01050a0309030c17090a05090105010516020d12020d080906100510022107020a090216 66
    0x100300c0401c80345644290041543c400a90855034418010300302c5100b240d08068103050f82540d03101000e092100d029a0014252048040196210030102d440b91002c0d41c01294694000c0d024403007407207101c1e40441d000e4001121200d810904807440200204000c50b12920b0311003018001c903107101640025141c0f001414500d00243d1104055292102241282c40007582e5007400c1c000342142d403022800f500c00c203d05854150030558004404c500501041c02d0031000d0009030241c030310205001034220901540c10440b95a584d180c13a2060205050b96a440035000d81320040c010b202a03a049000d8456440401134030041e00c02040c00050a042489800a010741071a0030421035101c1d0f0103d000e0b03015030300036115042e050b202c1403005981c1d80c4040700c542e01c042d540740c2014002850304640707903402e043c03c0d4070480f202203101c4045004030750b080000c40240004001160002c508003412030000414029104500b0122091030184220799920310082070300f0580701417803900c24680078940440a03c0c0c400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 633882949 1250 633881699 633881713
    0x8060a2732070306050a02130608090a170301050117070219020a030c14120703030903081c05070e030d03060506031602030c010f06031703040f030f03060801020f09011403040c05130b03 81
    0xc003646442c001e000603a0100e0810f8001207a940d2a402103507800c03a8050301400d01146060001c4552410180c041500d0b030181c00150008104113002c01e02d0910344882100350343c2e501d000300140c4524240b0440d407802847c02c80070048025008619080b51032000700300410740030454030000c0d50b2010240c00041100301261004034841d03d010500140303404e800c3d9003a000394070b4000080d0380e48990600c0000c0014442004c1400065040000b510441204a80e900000e00700302c912582594030882350980011042d14000b4480e280410240e082c2c83c1281c1410484d40c1e041c4808a00c45220007410140c3c00b4202d481000c0f021442003044495500410008000340050804a00c0103028640700c2038408080102150151015040407a800386070300240d04800300102c2d5034165007161012012f00207150765908001000c001c03e000800c06001c3c0c11803a07659517520100050205c250403034204180b50414170400002500000c0d14405943c003c580c081a070005202c055009064003606598250254003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 633884199 1250 633882949 633883043
    0x10061815030b09131a010e0402011d040504030c0b0a020a08150303040305030d0f3902010b19091a03030d050606040b040b07140c030709111308060a27 66
    0x340d071041c01940310b40141910344045c000b17003000504c1c080c0152010910018089001580078a85596503d030a004880c0e01c04a1020001012164100d4094021805410b2841e040003050881740303034010780c103a40c02c60500e8107003003006288035001006001c1e4901c01100c654960b0342c2c2013044d030b802103900c4422a036603800c5c5104068007409031030060301c52860a160f101d40c00034111241e112031120a511800c08461484003c800d2111019a0504155503880c1e2100a82d5101d01780080501c3e0760019111213100d1400310702c0310440b004c2102d203086851150351001c409542c040122142040800c0011900c0e440b42400901c4c40c1c810781d40080b00000b40081c000408000a002401040c1d020f6070080c0c0c0b80c8441001c0d1191180b04482030141d00da00060411301c0489416840107207450704036400103082000003140d900040d20309402c08051684140100b00c4001114003480000c0141c40110071540507a8a00052911044031802840543d85900c100e0307004004001115004102400a0b50010016 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 633885449 1250 633884199 633884221
    0x108030408010f060b250605010602010b18040201050316030f0c09032001122c030405030f03040b27030111090109140607030c08070b0106030510061815030b09 70
    0xe1041c40501e5081003406040c919261041408541881285074541881a2503c0713403007004404091080562460181c000701e0010321480d0701030302c140e03000060044540400c005041c036140503510001c451040401c00182d03800340640340c02c40054400c050024408110070b8010344460f601c080c1d285403910a0556030365a0180c480e07000c0f640039070030300300c945c03a5804d0418541698901d0107a001c01d0300d40a46071600181a40030340881e00c82e550014028289548880c0e00709819000c1d03130041030748007080a0001c0d241c24007600c0340d140000c0000350700c1c00d880d01140c00901e0080d0b10104940d42d201d0010552081d0403402811202c642c000c2c001c0150301c2c840131103001030b82c200c800b42b0703400510401404200075480141c00d0b0707611a001420a03040003034541c2c0886202c55000c1003290030040c248001d04c0000c000300c203c0e070b018000c2502d010130545044401410108902d90140781000014114800592800c454000a9801c20b03514443c0c000c2d020a000e902500d2843c0c0300360341008028003044036200790 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 633886699 1250 633885449 633885457
    0x20a06111201080c0904110103060b040b040e1003050c0f2e0806010302071509020a0e1504051b031f1208090a0618060320041418092e05010803 63
    0x5681c020025a40c8500c10241e8914003240010b400c810b400c804075001c5a52840503c50a06d81450302181c590b85807520074060380c101c1da100c0c0d03a44042c04075060084c80900800700f68003041c031900803818a46540c030703040e07078462403c6e07049030041700070554803e031175260b00c044202d800c14401c29a641c4403054101c6086101645289200000c04a501081c43c83d0321a000319032016401c0603c84800c1e2103401401801081e80440c100e034409441200001c1e085030400382c00f48559100c1440700d80300d01107001800256003000b03100d04440405650704200903800c10080d25086440d84124142c00c0740e6400c01c1c1000019190040f400405400310803e04116641008201c9007030705031444003189170f036000b0940307002c0001202480c21440c00401405414401d50241040d0751510100100d289852803003811a50710540010410103403180705851582401c02c90701c0d071101c03986948400d580c81c1040c10552540e00d081000c6501040c0800003003016030000240080000c03100c1c10400c05540d550a5259403948 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 633887949 1250 633886699 633886717
    0xa020105010602161e05120703060b010305040c090e010f0f0c02120a0c08160c0f0312111903021c03050105031606050a0e121005060f1f0807020a0611 66
    0x2003004004229107101041c8100e0b04001081c4000310503003070034031060403030000310740075101c2141c0b81e5800100d0340d44039250b4510740445030021300700342c2d4114103008090302c030503400043c14142480c0501c030004400340c5101085407400c2d000040c610400d9403080c1d02400a044031840000d0501c039012442c01b41c55482404910401d070201c80d010542c07510650b00c0c40c01661442404182e40f00c82000c049200d900040085c445403101d0070403420b030203179914420000c41d078100001102000100b4070820401103110746070440c40b0f0400c91110b603031500340141d0740d91078a10310901c10100307030740120100341c0200824141484403441032411040042002401008240301e024405c2c464100352401e1915892149000d03240e42e0364a0620b002d59a0409a0f1440c110014054026a5030f54503005507040601c120b0840c032200c0107001c86c160400404009100d03082c0d8040714450303404070b20b0014148501c1070b0341c0e0606140d141411101595004410303410305040f00006001f0906101c010b518031500c141c01054840 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 633889199 1250 633887949 633887951
    0x10306020c0c2202030402150706050f0a02191b0c030f060606081e3d05011416080702090f06010206180d110102042102130509031602030109080f0a0201 67
    0x845010000c4007503288401111501002c10080000340f9650000e5503c03e00140500c582001e504240342c40d554444c0c00281e40b605c0d07564040c812040c0c2070114107500f20112a00075400c1c25a011449109180c0c5044400b0a1007946a0420301000e00c40d07880c01d03009908820005d46250792401c1c0740002e0360480034110754140c038043d00031440b81d010304481030103030507020402c45c049200ba00e00ca4071941006495285507440781c80e07000c90080150381c05440c844a090810780d84a2880000c527000c0f1a540c2d80286040c001d5900741401032000b5903081e0b64140c0002d8441c40d9400c2d1a81c104800688030b01d00010750041c40e440200804020110720240c000c007401c0e404c903400c5175200640c0e29804581010103042c140c101903580e00c26580326054841d030311000c0000041c0740541d1129411145110200d81c003483c0700030000480103510301500e4982e682c2c44000b000340f00c84e10f0b001a41d5071b1a4070500610420700c280e050b1241c1c055480950000d0301d82984031480541d030f099060407203071068000201540040d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 633890449 1250 633889199 633889213
    0xa0b0a080c0306010e1003121b0609060b1c080f0c0d0804151406010c02120f0109020319050303010e0c040914010e451209091008060c07050102070b010306020c 70
    0x60450041c4562090041b1908041c4241c00c56071594600900418420104000c0d08240e60404072022154011203101e07500001c0c92000c28a4810203a0b0803243c0840d2150a5009983c0e9542c202030703034910106a031101030f036a0f944495a0340c03282035000b41d850102a500c1581c021401c02904140183d01940c042c140c01420300c5464940780d000e43d02c001c509032512003450030200c0c04550090000c046030a100410040201e0070460036140341c0140c10315103507240ea440f0001038095003802e200ca0300d9613003c000310040326011551500307030381ca1206200e801001100f050000b02d0000c1c038041035a02030043d102043c44003d404a04c40c0c1d001c0701080c06100304060548020607028600700d0780c54020403040c00074a801d40f28054281c07030710f010081c584c2421070303210424030107680601c28481c2e454401f40788800c85880750700c460140181180004c0041c44100c82c01207041c450200f00058041d8009030080c42c6a948825625115029006880e80240008003100000c030420526170083d000c040c491f00c0842e004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 633891699 1250 633890449 633890459
    0xe0c030405100e0a060f0c1407020f09071e1806050c07060813080f0a03150e0114010309080d0b03010b040908072d030c050c0405010302180a0b0a080c030601 69
    0x148820354000342154094495a012002981c1000b40410101c0007924850802034075420161034040a10380d11840d030b25858000800e4004015244801403050000d040c507035258082141707044c00c001d02d14840c044480009154500c80c5812140c0150740e1105031081154880d03026010b01044801c41c071f01c02d601c0c00f00109001d03114800340c442e200d02100081141c0c3d032a0070001c1d18160b4016104840801802c0001804a007190b0010410102204042c9540349500704008044403041204015000040711081000040c8124080e0540706900d624101030968a0f0043c2d00030084540010002c003004a030300324150780164840706440b101900244a2440c1d0082000212445c01d04000e114010a2145002040c2112031082e440300102c000991032192440c001c01c94142a0742d001c40c0011503d0340103030f041010078070444130f400909980611055045900066214142c0401100207401e000000713150407082d5040380d03941c103802800b8003100946410740b441d200c03541121720500a04c601400010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 633892949 1250 633891699 633891721
    0xc010b0306130f0b0a06051e04050a0209090403140910030b1f090608100f12170319090c03060e160f050108071805040c0c05010e0a0b1501020f070f0e 66
    0x21140c2e400703400030f00390035038541c0c0741140b44001a0040ba61240e80b080089000d482e04190030b01c6403150380078042c01900382d501c00c00c015200c2c002e10302a01140144040340d1b16460704051684c120f645401c0200c180311410155400034094104075552100c0e03192113a80d130f440e070954403c190445054410b008a401e00c2d5050326025146e0414803000220300311405c0000c40d100e41c0200d500682c8101c3e40c10341e4290303944100c401c0528190000c000078030500003a403040085a42c0ba41291f0707000100e009086103440c03c50b00e1303460fa09003882c1c02e00c2c2e1a15020040c0c10000c3c0c030140e0b200a540d1002c810000000080700256440d078984e0050356030710045103408260000000081c1f0100c0307805039035105099503100c0d0211400f08402096410350030b6072a0000c10103594034041c45d0340c001555601d1000044003410100d094079003280710300441d6004121900b01044040c00019400184020030082141000d00100c0c0781001054a00c1003074061101e0200c1e0943c2e280410004a808401e9a423801e80c4404070240 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 633894199 1250 633892949 633892981
    0x30b060f030d0e030c03150105190614092103031918171c0c12020a020a0201050310050a030501050601020d0906020309040522141606050301090513080c010b0306 71
    0x1c0d41944034a41401580b44941c1c00412080f00103000c1e10b00650b109804217140004110b40c81004043e50350060220341080c0c20b04100010501c1014910180780c0032024010701c01c91030503546162800142489642c0703408045441d844000d0580c800011507401c0e00e00d443c0c5d003080e2a403110340e04804500500c990681e00800d20049120040902201c0c1c003943e0b141400140c0c00c002070710060090100c112904142c6103400040310ba60386010031031862801d001009030700300403800c40c081441800b107088038550026113048040d0342800e204d562600e030810640c0501940d139101c0c5170b01c040021000b20401406401481c0504000c0e02122154142ca10043d20101500d00600300142d00070b011400380c0c0d1034541c00068020624889424881d8040c011101a03004120b8040d070303911807107015507404148200f2514140750788370185c04811030700303001c2c004180384018070802003090b8880c00868036442100507210101176110042c2da5482941d80c202e03502910690400d07038803e019501c001012064410404 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 633895449 1250 633894199 633894229
    0x1c0201080606120604020705010e070320060301060807140d021c1401050d0b0a06030605150328060902030712031e0906050318070506210c09030c1212030f01030b06 72
    0x2c0034640c4c5140511009400c980d40c25202c0359203404411903900300074802800514011406090080400b02041e41100034250010780103c80c00c0004000059105148582000e17030742c5848040000c0c040e0f90341e403803070080403e82c885592000903003105400d4101d405102448800c1803d002c4054401005c0001c0c4c1e000740310b4981c11030b0558004400086681040b298007200140b000140280c89884810844400f00e03140c107484019048800b84628081201d41581e5003020016200c0e071020000c1480c0402c80340d000103000544a90200c004c541d814080704016040284001e03003601aa41001401c80385000c840e0392120b4a030344c9013401124441e40c2d0401c140ca034540c4400c1c0c955100c5500061a41210651000150158102c04141a0344520080010070000c00fa10402000c65280301d050310701010b0030443c00007008200704032481d00c004c00e0309658042c0c11204e000b416901051924184103050000c1188000b0001c10411039220149645050700d0052100842c5640c80c4014000460070b40038407 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 633896699 1250 633895449 633895477
    0x30201050406120f060303090e0f010501091a07080a320301050622090c020708010b030d0804031209060c09120c03080d0209090a020711010203070c1e051c0201080606 73
    0x501585014011181620b020708000044554003140d941003110300c5c1c0e81044002440080d070401084082c3c41c8002d81088002054032038035450316002800820043c415080c03d10208030303884240f11500c0095556060300401c4190784c403801c845005140807000c4620040c0c0042d4090310103103a42407490030002241152407401d01d5070b4240703020003406410081485101001e0180380c3c1318801c00030400c0308004c1c040c050f03000c5401c0c000d03c44064140070703554019007400e030714101c0d113a2a25070700061060100c05003814061038544560404803100010021101c10b960300f400015010800182d000c440c402c241941c44c41c2c00c554884070700c10b403503d845001c003404403481da4009001054100005182114072280010f190000c1c001c08a003100e00f0803112448a503601103692814025520b4a8070400c042c248051890b1074500d54a401c90f00c507141c0500c08004054035543c409000798800c14401038080100804a800781c1d08016413451241c203074049001500000205070181880c2003626101401104 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 633897949 1250 633896699 633896707
    0x3030112051e210d0f0501300609081207050d060e060306240a1701060504020702100c020d0f080a0e0301050c0d050c040e0c03011517060d0510020a18050a03020105 72
    0x10840c0419004680890f414040410003201d075010343e44290f842506103070b1030202e44c540c5020400c504407240c0300c2c0410b251141d4044680c0d810038042c1010301046601c40b0f40000e04012505061442c3c0c059000001c11070803900050041050f0007102418124202c80c000384402030304c400040140003c29a50550554454800708080e401e2081005140000c06440c0c51245083c1500040142c036203a0300801c91f4010075000c0d025802401c2c010070000d003070b0941d421742c6030544550108594800b091074034810421407000038011580c945c101c00b01695088140b1400e415001d0a003c0368690040d041d06005c951032041103210360906008440c41034044034451824503003030245040160000900c28101e00004200100740716484c44003290040003400f1903140c6a60520707441582401e5003031007030403e0200d000024809903c00000181c3c3c009004c0d95003803103a03001c600c1e14614024162410050711800450000c00c503030b50001149120203102c0000d114000c1d5500188280c07800365000103400208100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 633899199 1250 633897949 633897973
    0xc14030a0b010512100c09080708010203010b0906070c05031f05070306060801050103020c01020c0d09060f08130f050f0d02010b0a050108060a060f140403203f03030112051e 76
    0x781040940e9450f00d4151083c10484485c07980450f4900605c1c103020a1842c1000e10050030b04205070009000380d00004c51855040c230705005d0701401050005441501c00103180b00c1040060910b0308020600a000c94007910145002d0052540f40740c06c6a280080ca07041c000784c40c0c1840b9007d81022114582c503200c5507a401c5c407004401035402240048040d64003000f0017103100e1030400510300c0156855842d04480b9040c00e000600035940d0200c00bc0400940c3d00c14480540451180401c0740c40d8050741410202d042403409031f08186078045029403500a0640603c503003501900b00e402d140c84c00305c0b0014001034a40005407000502176030070981090420b01c0501c0000d008214500d416003090a0008030040062002030440c0d101d908202d40804800b200714841601054420318442c40464070040c88400401e85642d051020f41c0741403005800c070f007000c6031644412050314010b0140810079a5030301c0d07840c0d480d02034488a244108681520a40d42c1c207003030304622140c0e59010365000c100a400703100420 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 633900449 1250 633899199 633899209
    0xe0c040f0c1211090a0e0106022e0b0a031515060c0b06060309010b0901170d0503070c030e150c030318030a0903030815041a0f01030b1c1e0c14030a0b0105 68
    0x10940034440104104141d00040d80c4045c201c00080000d0344040c0b10329810076100a0511000703000030182c0c1440b50148107000c4100c03882c08462400c00000005940800c0320000e06041110342c00a40050445407a00b405148150007046a46014401035803045503100000c860280b401500905505202400b1400340d280040c001d5400c000c0070400071404500c0e0324001103880100ba8440008007600ca00c00065584003030100c1c404004150400c40d083d40703420f40300508180d840c10130080810030603d45456490703850000340c80c080c100072800a900c448282080595aa00590700454400304d40740c8a0b050303000c13000044800d40c101d81c3e980c08112501d551303020345200030081c00d001494515174400301d0550b1213905c68440100c60b0f1100c4603e003020300b00c09011000124040180c101410030000341482d45840c010724500c01c02007844d541c07040445040c625840000c1411100303903003021922141c1880001e00b140d00070354013540124007442501c0c00c01c06946c0c0540540081c1000b10442c010081ca10f40 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 633901699 1250 633900449 633900461
    0xa02040b12030a030203100509160305011d0105191e03030306080304050105090d1505070302070212160b160501020a0302031906050a03060902060721090504140a0b0607060e0c040f0c12 81
    0x30a40038034908d03120000204901d00445060403409015840c80442ea40d04d802410300410200c4400104400040300b0825644014000c02e400b402007400c180b0f103050380c44100440208030490b0385803480d28030340d445407914030080c0c4001e0700002d0800501003500351020080701c003241d0b4142c4419144c0001031042c0080b029900c141543c41010200303541c25103007218082e0510428072070340c0c0141d035148244100035107201c2104c11803120b507001511220508502844850039149034110b82d41c3c68601d06100911000d54030503004041d9400411901281134043d0050750280960703d0a0002c034810350b0350b0000032070b0b54502c034003a404680c0002c104041480c030341c456042c4500203003040c4e250003a26194034403080051002601d9188489001808040d4886071090207810101d82c2440701c000e03000d01c81c8003e10005081d84051a0341e980240d5403644c1c6803022150502e0b440340050001c4003107001c86607110310310785039058003540c2009148140000c05100da15031040d070588810308003800030f200c0a002009 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 633902949 1250 633901699 633901711
    0x40b04120c03060c081902030603060f1b1306020c01050a0c0209041104140115051201051002160e01061202070b040f020a170a050f01090b010b090102120c0a02040b12030a030203 78
    0xa044000c0b000c64154003480c6500c3e21152511001c60070714100c1114015102020070000d5481032003401030f103990100e412034002800300101082c82d01d484200d00340000207410001014000020024001c2444840f510b0440d16641c082d290300d110b840005468510401c201100001c80e0548420010301d0010007054015000c0c14060480f00080c001141c202d500740501401a2032246004100320722080c180e180301a120340c6442c50810141084524050741d040c0916441008201100441d142c4200a4080001c15030641d4400c41603441e402d10003108801c1c010310b4009048414000710b00d10050007141d0f0f1160307202241ca4450b036a9038440980c1d20f076800100b20381c062600000000c2c8422142400c034501c0b03403980054180c1040c189490341c40c084080040010320b03414181c490b40807654492590b81110400c0700130595404484e40101c1c1031842c10700c5d806641c1d0f60f010458001103907001544000051080d61b0411101a06104214a1903c6e0304204071321075100700110f00c134840c401d4000e1900701c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 633904199 1250 633902949 633902963
    0x1c1d03060c16030513121101140d181205040303110d091701110a020f21070b1f030308040b0703050f0a09020a03020423100302010203040e071b1101090902040b0412 72
    0x101401e0080d20254185500885081204160340c0d1b041c4480380301010038403e02400e01c02100b1402100c020410b00036101d141006070303950800080d15103600a2000c134401d82c01490440c1031808088081d001d80c1160106400081d15600380c500681000288d042c00b10b41c081d00d40341d4915142c01c580c1d0f52640528020741d01155203c04c004a04295640050400c042c455009050381c203110100003131070100c82001c2e40c1c0900c001d10054a076080542000c8903c0340b604503204010381c1c0d44003102079055241100002c0a441c51840d8000241940544d92074004ca1107048001a907841d18003080f01500d2098540c00424002c2a002c03825100c0765510011146101030442c0344440c6da2500000c1c1251851140d190890b00c618400700781c070109240c806a4401e00b07a0090008090840d00005e40e0303400380d4040c241c000c10b00300e40400c2c0c100340039400c030713600c9000071400c84181d80d429413915100041e66090500d0114014110100d9000a81d00907602968155081305080c580303007102c4105003180d05132060b5412 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 633905449 1250 633904199 633904207
    0x115031b032111121e0f34050c01080c090108160c020a030b0718060c060207020402090402070f020f0303091c061e0504020f0402040b030708091c1d03060c160305 71
    0x11800748241a4444100807855840301c1e05500031201194080c1446401c05c1c00400c6980800401001600e0740d40e519101d5003040301456000300c44054611a02d841510194450840108140010381e06401c0b41d00303070f03507941c010703240c10707801c00e4103030058840003801b01e280403001900904202d04c40c40030003515480c1010545940e50086000103c0d550001d82e5080c94038420000c10700e40080c10a01e008004584801d0114a0040700822010740120005c1095400080c003406664844c0c06507000b0b240d000740304541d10b21942c42c0080010034a9003040b4014030086081e030f016850040195610400c024040c00d00c4e0300c41c003606482c08a2000c40c4200d40540d0355030081c5103400301d03e0a2403000c0c00c07080c2200040608181c010014a504020002481140100018440300404005603500314800e814040140d1305d4103502c860403c000388030001c00da0081c031084502c0c000d0340f0420564a20b010501303c04a803a000506268880000b00c442000d0000204500030a44422000c0e50351940e020346021414 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 633906699 1250 633905449 633905477
    0x1d09040510290d080d02030703020706020409050907061107060c0807050102040303090806010e04030f03092609010e0a0b09010f021c09080f0609071401030605030115031b0321 77
    0x2c588502c03048540d4800c481d41e44004003100340b410401080c004039504001480c15a8403c21217204502c9006400d03500400450221406038040d00c14055014806640381c3d91078209100040c2001c54100c6120b02c203030782c0c00240361401078600300c0328000508080d0981e182020300c00e441810102a088030020820032500c004100e0038805000514402d41d070340c00d0103510341441e0700d1034002c0c1a0401060380c1c251000340000640c000a85c00d541c0c100360304004c15076003420300302002411000c0f4614041849034090303103405107401c003008005600d000d0300c1d007600d10034041050050350082d502401d000e002b02006002081d6000e010a921100d00320b104070303204003207441d41198032440010842404200b81c0441441040024040d001540500784010f010b20303e818008942d0303078a0f035480340180040c0c5100240380141d01c6908224082c05010f0020700008500d4a02c3c002d10044612045e1100d1a03d0500b8015011288108034100d0342c20485014900107180001211003440c0301c1081c00303000c80c1300c2c1c10001c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 633907949 1250 633906699 633906701
    0x312150409120c02031002041415031003020111190b011701020405031b1306060c030e010e0109030308060112141806090a08031302030604030201050910060b0708070507080a0606090c1d09040510 85
    0x274000541c0d00e1040b0110600603c8000a0154200c201c0e00c00d00b4000c002c0c2d00e0140c045800304403502441c00e401e21000e03c44030582044424960b150303002c801c1e510260280440510310074100c2c1c8044401c40c54aa10495255080b8001c50180780d13899045109540c0311b401390481d25032648180144032000725814540712004581c0c01c1d078003c1010460f0300000c4018580c1182c10340c44948030a00340910b1260544000030403650f01800014207110603c008a00c0a9220b00300640c00d4906c044d80810441281c2458080b0410080300d0100584a10180741126420040f41043c001d8000074002c00c480c00856484190a40000b40100c0310302c0140140240541da04200e501e0059009400001e00d030f06021902c0d9003084040d1202209440c2005401c01c000c0e41c121046510380364103c00519141c168a1130b100c2d04080b52175004200034443e03031078107406029442c0c1c4008101c8500e1542004000d84c040401d8880c034072140f4001c10028100042c0f0002d5007001d80e0066070062050701a55000d1841402c500 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 633909199 1250 633907949 633907957
    0xc1005031923070f2d050c0f0c030c0121050603121c0f020310060c02040906050c04230a0611070e010909050105060315071b050312150409120c02031002 67
    0x340c0700c03141c2d58080c021070f290000300040091495240001c0c6400f0128010068000084141c0001d000c2c0c960001d01e0322445442552024075540050304c04d00004100d140307580f01c0700110300500c00c1c094542007900075070196042030140085805990041910700d034040c80240001815150140141c4a0790080e01301400000c00300d40b8121607003100b009610b19002c0080780d15106403288800c1c41007050103a000e41d0125080b003183c54600d0010360306101480031038050003c0c51402455141000148880100c1e10b80180055500000180342c0800802024000c40882000b203e03130402c50b0311206200d0140f08041035980110500e0484001a80e034403200c12001d03600764451001241d075280c0203400c201d400e00601e608040101e00070303c0341400090100b0b484090180c003800c240720240101030000b0b4844405410b00c143c005c01944c2d04c0d0b40d071405000c6076004040f1080254402c0c0b041511240d03103043c0c460408150780051142210400911080c0c40c0c0c8083c0e104241d03414032074100218117880c6280010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 633910449 1250 633909199 633909251
    0xe040f0c0b0a0f020a0507050d020f0303030a1407020102071703060d0c0806011d15062d07020906091b030703060e090a0605090a0f0f030302040503030c0105090c10050319 75
    0x1d5500c02c080d0500600501014a0082c215001182c074000810070010b411000d403101182c801d00c0c02d05451001640f89900650001d40501007c0100164141c2071703882010107011010a21140785e59403a022803c07032066480003021a848599284030708a000c602035035000c0006441c8a0000080d0344815130400900d0b4821241e41e84443d005002c50401d40004400607003112170181224207061149060083c0000300c158040d500124000382c3c100e20000d9100c5c2c000351502046210781e80045030450b06603105480c01d03801070a000021070344a0a013498014400d1052a0b0b10509803400190364040a520280a0703904054aa41c4041581c01c681e0040d14001e151043c024101c60b08070b85000c0013600c200900e60305103600f1980002011403101460950456880440c2005110984c507090380240900e030002d642601c07002c1810f0311024015032009016098080403140d01d45c12290800007110111200c0c140010307010702c04a46c0c0444042c1c16060706084001010078540c805d6010384203002d50349926 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 633911699 1250 633910449 633910469
    0xb0d020c10090c0506180f19080c01030b061801083c091911041116020a08010b01020d03020918040305070b0609060109050d0c0f0b090301240e040f0c 66
    0x10140800241d02c0d0345038001c140c05e0390176034204664138106c400180c540111140c001c00d11894415071341e607a0905a41080c00203000c031442c00030786407181c0940c0e80121042407404071f468150300310340501e0454140c641003c42490f00c604090141c80045803911809800d505800045441c010f000cd10002c0c000c0040b403a1044001c200010002d8004a2850002c0c08a81c0180c10008500108124420007081419000b0380f000d8603100d04200030a00401c3c0d00c210b12400c402021819004880d0384a00c03104195000300d03803e841054480d9840703801c888810b050345000d64070103160202c16078000d030090803080380e0051003000700140e0111100d907000c1084508400241e000946d403400c00950400c050340058054a0700c990616000d000038143d80c90074042c152250700022026001c200c14801c1e10000780c5420070921b00b5096880b041c0b000d450704501c010070b200e54205030840d41d40c1d418244900c42e00c200d650b200040d0302031a24110034880040508240d400425002d601801b040800040d84010840800 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 633912949 1250 633911699 633911711
    0xd14070623040501020607080c0d0f0903031401050a050d06020d020d1b030c050403030c050f0d0f0906080f06040b0d0b0f15100f030f06180207050c09010806010b0d020c10 75
    0x103040031000041c000c201c2100350030700041c005642d0000d8070950001e06400c044209490350341601415000c0e05400072000d40c240368443c044510300e074000801c01442034178207103c500220300800d10441002d015142e00105150000c1000f4680441c2c1c82c04198041c1400601d004014201c0c2400e0340c1c80b0309184208940c035288134140003002c401492060f4992450b007002110b40b074490040440c4510b10001d0100700000444605001080c05854800c4000c101142c5030078402c81e101a1055840007031600100d130350580b0018800303010300407040c030403d980301080b1a941c3e00d401c10000102054014541c110454600305000644240030050050503510b07010420740c034000f0441680038040301c243c81e006510122015005682089000b88200050b0402284004000c00b25500130003140d40301401a0700c1c40f441c2031000401030b07801444090301404c103a4080c10309007002d210141900384141c442580c010b10041040f20081f001074a400645c0c5240580340c028440f40b410310749148921500c040030740d904 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 633914199 1250 633912949 633912977
    0x7170909010b0c0703060203180d0e030106080c0109050d1703010612110901021c030e070b070507083d021b1b010509040e03040503011b030f0b0607020d140706 70
    0x1200d05004094924205241c844000c501c2034071183c861000512607500031012455182002010052148100c4119013540c0482800100a09640304489000c0e518103007011420309408100121991010f840b130031050fa00c4c280074001300445244056038800100d4081200344046000150b00030309003561160129007400c20260110b030441c48a83e242080c2c200030f00100c507600443c81034292407580c40d0280c0c00098070707035040d0054180c0030500055802100004a8040c040b40c0c0a40f03190b50041c03045403112510341c0c1920380c0c1d40480c3c0d19070350300f2101d5002d0b541c101105600035143c2d40c0d8507401143c288204045501800f81e03000030380e585140035908410000c03030031010041100e190080c040300004203c003850001c0c5c1980f14000130f1501654032000341e90174042082003224010440940200a0307403100c0038110700c990b503002030311100003802d10300681200440ca001d88407c04100a24030361402d85190f0810203c580700b800d080b600035400b4500043d0701882884042e00900b1242c8425415800071 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 633915449 1250 633914199 633914209
    0x26030108061b0306101b0b01060f08060a030b0f0a06080109080a030c2f0a1a04051227031908031f08070302101e0905101e03050c071709 60
    0x81e01000b01c0d120000d00402c14180d485d01040070b07000d189410300d0624042030441c00403000071001d0014045076558400014025844000c0070416030742c903600c801498980c03a080004010030f40c800a03050b0000c580210b000071030222403440d04102c16150001d031465641c0035403401e4906d040c3d0203541040010641d240707502d40502030014488050f00d029401c540c400c0300040a440b50741c082283d440411202c03443c02d107500c1040550942500213031340091044c681d074290450301200303c400b12241d000d1000e6403034a0200d89410340d410b4806183d841100148030b001d2806945102d00000d551500c100818a805668640d5a09030003500500009a881c5807003510190b00481c080824100ca007584034013000703010740200710769090780e0b41103c40b0f02028680d6181281c80da0480c0c000054400100d148003091140c001280c18211201500c81c0310a84400700350540c4d000300b5070780c010070102c04415022540980f007988503d900440d042c920703505185441e100d0305600290041c644806403000207040301d0501d00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 633916699 1250 633915449 633915481
    0x30406081602070303120b0919180b04061a063114060c01020f0408010603020907030b100804020316090b1c031e0915032406020a2603010806 62
    0x100804070800d80c600c10025510102d51002500b04540c10220441060003a0440b8174038420003001d00f0035600741030b02c0c8000105561240408007510b1300d03891540040c10b90060f0303c0625004104001961f607a515008040e00002c005580c0708040f05800c228030346d5400d000780c10b151000c0d1441d04006088140702003803108002d110031103da44604801c00003c0c00240352032040c54800d490054442d20b240d4082c5001e030003500f00340d0003001404070b80490350762015400070742164001c646203202074a807002c0503030854030320b2801c880d0810414034010007082e0240d1592a00148041c0c04c0b5800f89000b0140401058807641040c41403c1d00c42102040c03a140c245030f044400c00c0d0300b5201004050183d40c0c05840c00e143c0314002d054906200440301400742c09000b140c002403045500145403e003200300018014115000c0d00036000075010000d141f64141c0181200c15509a60010f040442a503260920181d001c810002241e44a83c080d0f101e0800350b1002640c002d01c60580100043d040580b06140c45110b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 633917949 1250 633916699 633916711
    0x1e12070c0302100e0a1502040b03130b013017030705090a0b04080601060f0219081c0908040b07080c01091407061e0c0302010212010305030a0e0319060e0f070803040608 74
    0xb06000350040540c1001c00d01700c03c001da20210f5a020001001d0b000b401078015540210792211001c01042070741035039013110380d0945100c2d540c90341c0241c2c0c80704040e98881c005400c41d0380685090860005e62481c0c01085140324600a44c07002101c40f40f08030403a00b46a0045815a00140006c622008a4207082072103034040c0101502c128185030402c0c8100b50f8034041480b0704410400e003206141140c074005c1c05844d02500c00c00c40700c807200c030b19503080c400c11541c048004c0e102500310000e10b00031100503611545080d03580c84a0a80e24051030803004540c140c014140680d071070703601000f1100c44200c00344149080c0501c600040c2100c8184802071b1414078605500000510a908a41080c810480b890010411f621400d2030000e81e480360030124028054480084650250039002109101001024100c03554455803009003070395140040c140c85414645480c54540344042c12940000d01540000100301001401c4403103042c100d4941c170341707815202d07401403010384c10000e02070001c03961024225900034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 633919199 1250 633917949 633917951
    0x120b27031801021c121802030316020a150810050603090c010305060f0d0606050a0e040309050d0305042312030c0a020607031107030309090b06040608132901081e031e12070c030210 79
    0x9001e50300429264401c030407a04001141400090045544a0003110b02370014042c5080c1d03901210080905451b03400d42e43c445180034904800601841c042040340d20170707440000600b803403000800056018001c0a4445540b005910740d4481e02c641710b440001414902500d00850028030341024403e859405421110040100c4000c00c00400c4d001000c50741118030989103000860024101210540100c0c6c00c40b5860208400d54089034415440382307404a020129400813520030f00385c8640d6668400c01200d07418a8100214410161609401030703c411402420021039045883c0481400c3c0b404540080300070941150b070902124400e40704e0907048082c01c0d00c0041c5040d05004000d05188001841203083c46040074009042204041d0740d80c907441582c07442401d04d062620202d001e501c1c001d00a612843c41003685000c02d80b842c1c4110031a4055982002d186822038640c03001d21482c00c00083e00c65001810040c0074a104c20700f04c0103d01c21101c90b51510781c81082445e00900305620324200301121 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 633920449 1250 633919199 633919241
    0xa33031d030d11070b18071814010506090d140319050c01060504180b0601020c04181a010308121e01140415051302090307120b27031801021c12 63
    0x509444c440c5d64001c1c03000320b281622100c440c40c11070b25007165a0003031fa055030381203407a030450041c2c1604051046150f8a151610076a240e0080c068580a56010160300c0540e00180070049403400c000480703994050015240707400e5440c4900b816412403d029200081d0700041c9104d50702400b0b00c40c2c04041e10040b141800450b401e01e0001038480060b84020b00300300781003800300b945a0f0007000440c5807800c001d402407022148003425251203060412042e11640c0c0360707000c0c19107061519245141a00e501c920780e0390900b803412000d1031002000512001c64003003500c0076000c030302039000070080c0208881d41c0082820015030051009480b10310a402c0b0311681c01480c10701c41030781d44000100f030030307181c803500161115250b10000e8a080040d500079005102c030074015900b80705120031a40d04ca8250030fa00d064030880745030a8801019803c40408031203070401e002910410710720007030140e00340f48140304903401c01001c144288602d40720b540b80301011400d0300710700f007007001103502421119840001100802e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 633921699 1250 633920449 633920453
    0xf0303020f0706020c0d03271401020712120c02060708030903030a062405090406050409050f1212010303080406060305100b1005160b060604150e0a33031d030d1107 72
    0x9528110000c1c10311861030b09154421346001848600308006640c6500300310f94172450110f05c000c3d21449c90f4014014644041007410309950311100c00f0340c1c4802d4981c0140d51449040f038810b19a4030003241c1c40b0004101c040c02145076140076501415800c0007440e513905004461004491059020540501a0160420000038000f590340d07040c0c0824180f060390b0f00029400900180003a40045904c14030f00001802400400650400b4185054080724984000321030301081d1401489802c000c8031040da001803000a110300b00b082d400c0303489681b01003520703510380e5202400e008606030700742c2c05180d130340301c00c00c52514054140b907800e4512800c0851812000d440304c5c1000401c107400190004540c14007140e00c80d1244801c607001412140c414000d86c401e81c880040603940fa411301184111800c09002c581036038026520710604002d0442841350107031041e51002000341c22505c21090581e100c2c1c802c1480d99044100500500306040a103a4611482032190116081040046c0380c441040c068480 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 633922949 1250 633921699 633921709
    0xe030705010b010207150c060b03010615030501140609030a06020c100501231e06091c1a0903120109090c03120908060f09030403240f090501050609060112150f0303020f0706020c 78
    0x4002d8101c0750228800c4880300c0400e003d0b13301e0f0307880f14810049a807200038050350f05a01c21030688004410010549804904000c110300520007201d5242e000010111300007a00c2c2e50080040d80f40b81401e0b12114190b12040c0021220240c2c803030280405030f04d010780030820388040002c65904048a041c042c030388019010000344000100824021617001501982d1a5541c41100940c4d81030548004158030051074007065804000328181d0311181000042490484080300f61041c05401c0395002d141030386049041009012152416140c0041241010021610300202e1200a224036200c000c01d0500c0c255a443c5070450041101e0f40321b00100b02401040580401220b0440b5000852166040c00d052100100807030700d03080c410215480d06441101104951300842601d5004074000c002d80e5964200303210072080c084a100740016111181b094480485602c1078542c1501120402e500f580c898081070446400d58200b039025a2202d94070010014040004902602d21840603200c1082d00c403000c64 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 633924199 1250 633922949 633922967
    0x40c05030c12031e1e04060807030605060d0203070302070c0f210b0601270f03150c0e090a1d1c211a03011d0f03040f03060f0e030705010b01020715 65
    0xa005683d00b404c0c900c1d418001c2c03c150340d2510751044280604401c0c94130480d01ca80d02610540d0003107404400060400c50203840340104445028102516010141c3c0b2103100a61000b0300c0302042c150f0070b000708008036900b040c001e0080c00501807c1806c0c9070418400305a241401c810054060308207018080000c2d80640e80150002d07000c1c240040c0443c408803140d01c080111202041d00c907000100002840708140d035450080760300803043e00031820a08102ca00c02d40d4580f5480714003250382c0710111800e508080d2038060f030124002000203034001050080f03616800d5055070b9405658016580400b141c0803144080c0f020b00501d041c103807104d08044103940d03608a0203102c03100d000ea030344070103d007803564200c25242110800100200320842d400102d120f0000c82800702d03807041e4032070140203401c500300c00001c8405941c80c4a0030f4061882c81c0d903503040c0c003400daa0700c1c821b15041e4450015903541c1c1400c10190069510510012500c908013600080c5001c209510218405940e903030f00040c0c0c01e401c100b0a03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 633925449 1250 633924199 633924217
    0x5031009020f1206040b010f06052a0a11180610050306040b0d0812070306230609030303181014044d04050103050c061809040c05030c1203 61
    0x1140c044414000120700c0140b0704003141c3c01c0200c402e460314548401040040c0301d18803c4241d1111642c0350807501685103001c0c082c03400450b90070080d881d007035403412017803501c0e82c03c0344407050070100880081141000060782c0102c403001a42c00c807002461801c00d55640003494446c20003e00741c94008005118003000d4085d40082c803100201251403902c0380e41101c07030511806840780741080c41d507142c03000d030b254404403041d10502c0e19200894451846030044004407014141140c103c2d200c84250501c3c141c0005803030581c418000c0000740042d80b070a001171803140d41228041c4d10031007484d030415400c0c03200706410740258504c0e241030560750761300040c4203541098200941c000850480280150f124555201c810300c04143c81a151407125842c0e007540b041c91842c1c0e00b900c5d000c03400e0b24084c441919028003000785103800541c620449414100041c0022250401d4400c0e07004072040d01281c00175a05881c1904e507410300541c1884142020005000281e00c03e88445100b00e4003501066143d002d20585 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 633926699 1250 633925449 633925451
    0x140604021306200a0b0402040c022a01020a0c06050306010f03150e0a0b04060e1608090a080f0f030403050a09081b040b0a0801020d02031e09030a031512030305060102100204050310 79
    0x1110007400c1c4205981c0c90500c0c0300004545181c0c40e1820000341700d0004542c1207204a0034103001e072016500c040b4440d18408806107968280300c82c040016020402e5020007641107114401c913541c00700d1b0880c8000001410251a00341c0c0c0c03400c01750001480c5031903031440038043c5400c01092184040c2d2022240045550040d0342e141c483c6c40e5259040040d001c80c035116680b00d0b04040d00445c3c802000c40905008a0f0502d48141c01e904a10390207036a0390404503109001c41c0c00450400c00403886034001800e026180c0700000f890030719a42032030740715604103440c2640014804521010703100e4003c0b1950300a410488002d0051109019907200c0844903160510300890300c851a050075038865820740d2001e00007040c02551100e0701c14044000a4000b1100f0240500384041072900002c2642100c42c01b855010001c0d44c0761462084c010740180c03c08410300c24041c4602c1d0310010f81c0302d0101310b150140901c295404a05418100002403a28001c07a62141500d481000b0800a56400080d04031502e041810 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 633927949 1250 633926699 633926717
    0xd05100b0109030b04060c1107080303010e040303021b06040b0f06030307030311090d0b0f1006020307030509030a210f020c03100e010b0d1211010b0a030b042301140604021306 77
    0x101e42d000c1c0240d03c001c2c0442407140900c4108000c64002e0300e000000d40d2354210250000e00302c11580d4403034501c21408107800801c0103008000c00035a203264828001d050140ca41480d04d0181414500842e003121010b400030002d020070011000c40042d04490f103001d060195061010000f5240d214030070005086c0750781c6013020405094850159941c06a0040008500300741c6070500b07061101003101d070b14141d0488400021080640e4546a60039110103038000d5080c50115035042d01d4070b600c188100c1ea8180f0910500e80006105a0030034408807141900100360319019503000f41c81180340048800c04e41d044030b00600c40716100050540030b00d011030032000c6441d0101c20303800d500404c40c5045c02c42e0407035a4107400e441841065040d0000510b881d689081d00c4501c1010000c0c2250304007518980e12161264007000412a1840c42a03003140c020313080d6498141090035001c968081e4038050b14004c1e5140c841a1a0381608221016404030303042c2d60551421007131b2501c030b2029024034004c440512545903 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 633929199 1250 633927949 633927971
    0x31b0e0904030908010c0c030210090b010e0a0207020a140f0307080606010315080706020304060f0c030e09090c12100c08010b030f18240112020a030b13020303041409060d0510 77
    0x10403140200812402084600d20006000b007071500710010650241c441d101e0007480010b020301c2010303180c034cc010301c0c1488180d00700002c040d04414041c22800e1000d0f0248110760150f503c09134184010304244211041000c1240c09101249880549181c030a4000315000c02c255403010403280c2e40801c091900168007408001c185200d20130710f810400c01445450340200344680c001004005507a01c0740c0f241c3c18040c05880045a4820104030001c0c000f59650082d1200750030610a0107400c1004c02003911030000000000c01e0a00e0020101a9800e80c41304440c03000c12803081c892600c13120f85616000b4003039070600310140d0f00f40c44050941c0340f0350381d40b800002e20588031000400c0181c421070b400b45c034501c001d450846041140a40003613554046420000206000c90000802113540e0250044014a07d151154840b0010042c17000c0410703d003041c07050340181c0d4280300070300143c1001950580143c11034002c6c862a0b0000900d01405210081424008100d0001e20550321003850301c004541c24510f4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 633930449 1250 633929199 633929207
    0x3050609190e16030c051f0c06020702060c030a0c0c060f2a02060403080304031701240509040905060f0108030333060408031c020a140315030a05030a031b0e090403 72
    0x43d005640811a0380640841001185098041140d5040b19401c101e60180c0700e450041010419807400800c141c60203d0000070046d8000d02640e0780010501c07030412184469440c11640001010b8000440901802d41000b14030031504c00039040500d02106594000e50000e8407005900b282e500034a8402070240d13403038583c05819002c840e94013510442d1115130f41d15101c0d505420075241140456000d0b02003845c1d03008055041412246810740501e15044a0100c42078801d264250150401c1020000c02000b600da9002d0303c0c000c00e00c250300400451a044030818940c00042e005028650400c000b840b58180d04050000800b013448807000f040b020b60700e40e84480191000c481c0c80e03001080820005010800400a44980920503015400e204601c010603012480340c2240e080110f0401c0204c0015100c48801a603031110301c0310f150440d20150200064a8107507003000803902070b480095064161b950600500c110343c140c80804030000408007001801040030b80e00c05500440001000405141c42 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 633931699 1250 633930449 633930463
    0x1090905092a040c050c0d0e060706020a1e020a1401060e1902040806100e07080403050f09060705030c0607200309040e10050a27050c0f0321090103050609190e 70
    0x43c01041501600c42018040e80c105031044002030080880e007815040c01078603515544100208114a4500c80c0c0e552000290071a030480c1c410044d14140400f42030004600814005036a90000e0145088030320301071071546140091100141d0600c2070801451032507050b1203400039245090140c0854903504c0306002401035500150f0b02d8850042440324141c0030006220550304140f010f8140383e40c0d801c1083d03401c0081502e001703000a100300300902c24558100c018040041d8000d161514182841d11421301c1c58001c2001e0071160f8201e03d05104400e90030007004060030b007010743e0301c1514082d00103103542c1340c1c0501500385004e40c1e01c0c1e102e991a07944040c40403441c1d14684110810581c1480f0540100070304031290401000304401088a0200d840710100b1007406912400074160b1007481010301031710103010061240c151051201c04480c000c07004d100c03c043d089031809450340300c03484003000400f6603002500d11801040800309114031072038025214101c1407140000843c022a01d510b0040c9010071b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 633932949 1250 633931699 633931783
    0x60f01020321150d0b0705160b2d091f230403080a14040210020f030403030e0102060114030d08101503020c0606011718070b030f060109090509 63
    0x103441c41d4039642d11540d007080c0c80c0903000c40c3c00006024850141801066181d02201074031801c0800c0014910500c5a0014240c8413400440f690a20406690380340906078183d8a046e5000120b004500040c03c00c00b40e411015440d8070418030050400140507904da0780d03241040144102c03000302e281108019030b001444907040f0b0081c0031003c0500005400d921002c1038034120b0002b80401e0201d003a680b41c6006100c0320310954441104d050320b50b81e00700b0085050140c80300040d0301900d10441d21000007800904001e60081e101d0040d8400d1020009007418070582284005458001c1402200c0e200028055203440c10780c1007450303550b03d80c900c030300c40401c4413503012000c0072292812030445c40341d054018082581d0711104507482c41cac617400010b644015001400c90399468020000450540100d250b0000d807030004001e0310300d4180c030340f0603d8120340d0007280c005c070448410300203010140d43c0c030001c2c8100070070a00c10301b0006801c000c0e9900c0c3d00c980980d0b40440c0c0032130041a0040141d60040324152801c1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 633934199 1250 633932949 633932977
    0x6061b051903120507020106210f2a15120b010905030f0a03200316240c11060c04060e18090115081f050915071206090b09060f010203 59
    0x2401c5450003e10072440d01c46891809418040070620745401402050203982a07401011520150031150701c00c000340021007030720741d200742501c4800458040c0070390b10210401307400c00d80540048202c00007024101039200a46a03801744e10348401d2560300100720b60202540140201e5160350307070741c01292110040c1d04100d515004003601002c224800141d000300c10b0348281c40340300103c1413100d182ca000d0b5059081c2c49555400800034000b690540140344103410b842804c1200d00c80c20080c40c2c101c0c0480d203a0013103141141d03640005142c6150000241c400110980b0001c0446180506080b081401640300d0b079820702001c1d220b005915502d68428801200200500300300e01d181035480d09020b0102583c0f00010751020020102da0740901049080c4038001e20600414050050131541c4020071000345050014000d051103451203a015401541c0908001d950700c0c046001c00b03160039003c582c0241d0011302203514150081055883d041070059004d4000c9071401c0340882c40c44010b034254030607040407104c18 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 633935449 1250 633934199 633934243
    0x612070f06020d030203131103100f020a08060906032107020301020706050a0b030318210d020a051207050c060c0312010f090f0911040b0f060a0215060406061b05 71
    0x1100c50036a4012100c00b5800c680d54801c4035002a41240300c02d0b00d90029050f042070960300803401c00701244a032100003400b1268400168030b84101194a6141d0054070160001f490603400d0383c0c00500c1c3c1c2d0300400d040f80c81082038200900043d5446c2001c40c07500030712105458030b41a20151500a454106030060002d40da21400c503e0000e009141c100c0b040c0401c07600d02892089282030000588003035121420070602000907003c2044a07018a05075514000b03141300c20050707014442407044c9004141c643d0001c01d8400c4c40d5141c820b0611107401000f881d0304405000c0d05011500c00540d004024400380d4465554811b00c500c0740e401c5201d1607030700140e04900003000259090008583c6000c40300e04100800450640340b0b43d420540d0047d19024081000380000100d042c42e141d8888541c9040c001e100c102e0133104c010100304190000c10340d110150b0001c0424440a0102c14491a0711041c126010442c1c681405000f030010101d5082c9030075103a0350100c40c1402c0000030024050841451010f400344 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 633936699 1250 633935449 633935459
    0xf0216050705040e0606010804060534080a020c070b0c0a020a030b01060809011109010e0d0b0712180f08030702070e04210201140118090804030606030506010e06010507060203061207 80
    0x40e5401da4420b4038041ca10307000c2442081040810101d008060503955181651181c0d21aa40070f008050702c4e4007034440c048440400049003003001c00e9800121001200710001034100042c1485400401c2016082d004000f410050240418110150780200000075110800c07003140e94035059104100035000340f00c01030702200b0b010040a140303040720100d1391000f40c103994034070140f03090341c2484510070300140c01800715803100d60243e54100401d0801030000d540240c0903460700b183c561810b5a003100418801060a510040d03203005000c104880311441001c01c41b8695a50813420052070400b404e00c41c1c012001c542181d10900822000381080c42d060992030900e41840303a0700c01c0d54458003c1027505a2592580300c5801030080d0a105a120540940c55a290070713803100082e508178100c0141603540d1140c8400042020780604081c43c010b00300000e40d90701f1842d10354500801138102d46400c074031700b1007000100d81c0d02c03d0881f401a40d104401684035203070800818240c4c40520030604440c001c800c00892 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 633937949 1250 633936699 633936703
    0x5040906090212091507110c0409150b010e030c0609060c0a0602271516080409060906081203060f04090b150f010c08040b03040515010b0414220f021605 67
    0x108003800300903c002c8039102d4a548907910804255460060100d40e000180000d02492002c040c0c6403040b0251401c850f11078002a0032a1651401103801030004041d114821440e40316104464000b824a1525000d008000030b588101c4920710b0f41c420031740080c102d44251103d200384d0b002c000c040000c0307421803805854080b0203034000c8514107144600c0f400d42c0b07035000b25240d81f00010b003100103021501010410784008c043c0c2c2c1d00550114149120400041001920a07802007008042c1c00303900080c41420616010309440c0c5541c042401e65000c114140208465030f0101c0c2d420003011a806502440041e000c10040c0c80f246202410803800c1304100511b000300c0b801c01d0f80c11450100d403901460b0105100645030601a00000f0f081110b06010501c0380445103c010b50300603020340e0842d40308044016541c00c2c681400d0b001180326034008201004a15010f01034070864540880301050040c0343d502c000710080003480340d1101ca040c0c4410000c24007509544c104c400c8008080c04d0111403640f242480d60b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 633939199 1250 633937949 633937957
    0x1205060d15062903060d170406020f0f03040b0f030406141311100203040923041b080c13021804060605040e060916050c07080604061e05070504090c050409060902 71
    0x240b400f041d14122010341038032110900c41030011121605540783c280500002c030004107000c59440d11050090751a2440b6040900014150355006103204880001101d007058154582c00d45070340e00134441401403101c010113036141580c0d2011714545a588504200e40546220607a03101891030640034404a07c1c0c25010000300540030780703d040111a800d005001c0c450002619400c01600140b205220003000c030b4000d5240010b019054004403915503c2c0c1c0121224103031402c540c0d0342480c03031412510b0307460303043e0550040090001811000e203ca0010035515409081804821a80050707544c01c42080480c0b12a4a2500500100310054458901a00c036901074000ca14003800d1200004a0525200f04828804d444241c2440b6046841e10400c2e030382904a0090f07074941d400b6019021170841801c00c4100d102e40c4c01900041980600400c090281084050624404078101400c0018468000c4212400c0756035030400000c21000c0228112400d00031a008040c41c2801c2243c0003a1460054004e4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 633940449 1250 633939199 633939209
    0x3021227030f10180b0c07150504020a050108091f0b0f1c030c150e01020d2304031101140c0414060403030c06021303080c0d021605011205060d1506 65
    0xa404a009110406560342210000084150f000216501900f119070b008000ca12010b0003c00b15400ea1310745d82c11402000444130000e40c0300300498007c00b440f2041d000b680302902c220320200b015040caa00400c8490b54180075582c140030005010a00d080002c01484c400d00c1d07100409a002d0305441e010b500c015200034800203216410800c5520341926201094604480300c062240f161050b45c1e90b01070300c607160780740e5042d6a4100d034001500b80c00d0003a4082c2c030301c1070790f40131000503900c0790795441000440d040c1d50012801e800390300204640c403400b103850b40c41e013058040c10300101d07501072100b2190240c103456024810703e003105418001b51207203100251041c0c801089140c0062a4290103029040c0910300c409000902c002d1807040220b20144d00410040600400c02560591070381c48204e61540b04c04100304880c0c9c00b12603d1442c50b58140400310016103031100d451032141c0340c240024903010598040301943d80d6074001103105551819901c8900351b40c480030000041c0711880d006002040c1c18451 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 633941699 1250 633940449 633940507
    0x1020c06010e0a1a0409030309150203040b15010203030402090a0e1204080601090e1f0227191d1005090108060403080903030408121b040f09060504090503070f030212 73
    0x480c010f080140550922100c04103165030030044281d0420001e441c0c0008160241580c603030460703012651b030790340d1070b407004e640e170342026039242060324200410b02d1006084045135044103844400aa0380403040340d801c50f404a401030356170340300c0c081480010000b4080c1e6a80c1442400d510380448a481c01c0508120358554080d03807000da036a0034400041d10b4a8142010781c9410105027594504c0b40440c0040051224036030050502c5200407146502c0c2e6046112841141d000c124a000c1900c0d0548044400040c0440407885844c504140003411440e0960075081b611640741c0025001d03c00110001d0060000525540d080e581d910f407d1038441806840c242d00098550b40001c450640c0081260f0103030b5030000c0203910380400408003410120000e4000900c00082101d840000010700000d40094030b0107540d212141031500344407034100d41550348003030700550806003141c000c0743d808019103000e40d800182030307130f8071340b449140c200d003071613000504008083e10100e803a054a0040900b46412060b00c40d02e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 633942949 1250 633941699 633941701
    0xd050f030f0612161d091903020a052b0e091b12160206100305070312030f0908130f0f030206130806070f090617070f022806051b09010c1401020c06010e 67
    0x1040c64405001206c0c0505c442e030040740080c3c803061300605001c000600910542d4018400d0303035541400c02180b40c441e81620121080140c0c1c028800b0807840ea03280700c00e4102140703104c09000204044500c01040140865440700800e400c0c0081d20081340c5241103441e18600ca545012100586400d9041b01c5580c0144181c80005d00021065084242179941100040c0401450369039102e401c805c0784100141015260800740c02402101d00801554511800c02c05445580c0d00e001d030310030915035900c00e80b06403c070800204001001c00540d0700a0729011348a06990741002072001c4130b1610144d0040005126803010070004030b912480c0e04c8a225031541e0317060700d650343e6188229a010186c02c0c0d5411528542e00116211900403c00700100280c18019103203445000100710390710912080d24a01c8a01102802e88200308180c410a0f51240c041c88224580d2a0141404003050146203030003418009180740c00c205000c40700c42041c1c0e10700016802596501d0304208001c2e00d411081c46140d0308194060 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 633944199 1250 633942949 633942989
    0xb040e040b010f0f14060c0f0601050405100e15041401090f11190f021905150a05092523040b03010b0d031b020d030503090d050f030f061216 62
    0x20140500300e0745101c9408010500740b0800d170413401900e403803043c2c1c030080400035501100c0c428040150311004070f0001e04071301d61505003400103035407000309007001c40144100305008824100b0003951300b005580f20151810b45200300824014403c7c2540d8151000f41034000060009842c0c20407100304d22500c40c2444030440b0015101c1c074500403c5010f50140100741140e40b840f0384030307820088a0010078811a00d28907034188030810102d00c0030800343d070240c22406081c54200d030541d070700300e4101c0c0e001301c1c04100c10301d000c0350f03082e4031580b5104683e841c103500158040c2e00306040c910080c0c09800e201300c11540720740441c41d15187c03084501c000b4a0240b8201040c10400e40341c1841440d5601f4005050b040244017a44d400b00ea00c60030301112110142e00170103501c80542c440400c0000c10a109480c3c1c039940b0300b8001940e914010a0007044020460108081e9a48810041c00d8907048599800d00340c03842e45800c0d002032800c0d103192059003000c0c03050091045d038030304046000f0300031200031040c4482841d800e0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 633945449 1250 633944199 633944219
    0x60403020d090e070e1801080a0605011d070f021f1a030c06040513110703050703021207020d080904020717130605090d142404021518190b040e040b01 66
    0x900c58030a600000b100082e4604c1e00803d40c0024082d0001c110b001e5582d010a40c21100e65003e80003114503502007040341741002500d01c9968090700c0c808507212000c044a04803140d807031100401ca4400c0200d0301043d100c1040c020094121240043c0b0031090040b504007003001c00400d401c25961140c15880c48400701e480c00d011501100502000e04007518050510090000d0750034204003e0030f000d03650f51002e458010920b00030f494250b00c01d40c1c0d80c60740c407111810001d26180a0300210b0100010801c007000043e031701c503141561115845410280c580303202c800018001d0080810140400c3c0d201000745081d648010010311aa09480b91903000707154441e08111001d004007000903800c420084101c201046000042610761486130045918207860b41c1c5c0c072140d01c0b9920b0034000003c05841002c0c4803c61808440048856122a20ba18204070320740144949101403400306034081c6007030302000c079030344610000344030080c000000502e0350b0780765103040741e821a0804540585034403d00c9000418110f0403 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 633946699 1250 633945449 633945467
    0x90307120b2e06030c090f1d070206070527030d030608010f020c1e0109020d110103060e130f1e081305040605011d060d110c0d03050912030c040305010e060403020d 72
    0xb00101055603908043c3c0680041489104880910050901c0021008150000d10014103240410320300c42600c072201c00c00b2901400f626600039500900304001c44203030701c0400d0343d000f6000e00c0c00c0500040402c04028807030520860140d601402584074903110182c16800003c03c03611217000801ca0082d5a0301034030100e01414070304450360b800098640030454500340203108038180400c000a403103902a40013480703141c02c980d030484441ea9000072106007580c02d445040f00501e41e40c041c021840c41c2c590000c08002442e54002410907100e07180701c03001d0200c5070400440d40018034044410140450030020529005000c0c90a100300f807440010621741001d00510084070410f8441e461985000084100303082004d404298200c502400120741c0010b4501070078441c6c54007910180c0ea2101406040c03410804082000b009060a00d018007030384440005501002d02414404640c40782c403140000c0d0fa5500c195800030b04103608081c001000020081510b602507031090f0202c69034004040800c1d00c01c1c1d11 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 633947949 1250 633946699 633946771
    0xa06081b0706291f0c06051e0403110606010801060912050c09151c0302070e22030309151401230a0e0702160e0a0506030c0307090203180303160302090307120b 70
    0x5010311740e07040018144e81115030000841864214041260b402a0b088220100c0b82a0002602034000c0b0030300c0d40c001c0c06440c7d04800c0078038001407198148000501010b500d1b03c105d01c43d04488a10000a010003840700300b128580007001000c45d030805282d10410880e412440601c902c0c0401074203e111007a24110000003940340d00500704082c50a140d82c462010018a1442c440001e00c0c01c44601780d500105a5210900c682c400054014407420486810320b0201d4065004501d00807004188019400e0b40d00e0440b0300340c014652594200034483c0300754415000340d0503000300d030041e00811000404e107280c52044540b50300700d40c2d0710010070404540c00303001c2d0b12814524940c9100811211003076a001194022000ba0840d81d80702c00c6400440d2400c84241e000002e499808414030146440d40b20310307104a00460b0000394114200403070124100038518004e2030506500141140c06600c060088000400e52500d81940d10052801d0070006030404903103c540310b07030700860b00402010400ea240442c0c01703 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 633949199 1250 633947949 633947957
    0x8031b04051302031e0f040309080a0f060c030b04020408010b011e09050f0a05030d091503021c050a0e03070309031e0f0312290a06081b0706291f 64
    0x202e030400342c0b88025030000e0281d00b43d5425801c1d80c8010110140380d4a8041e00b045c1400054916250030002d200c010f4640040e036a50708000b05a03800704140d10f40902203150000750000300598014000d400824050005940180c004140020700c40810b40c040d007e205001e07261103040d8024040030030740b02000c503125000800c0030b8620038002c50800f804800040c85000e440c1c240c0203510b600c0020325044000e9005000288801c00030300c0741d01c0c07061020b0755649003076040541c10700c080b2070002813141842d801c100a11507078640010301405581e8002c1c030780b1144484152a503400c0c003414000d141d940c10b4042a44c444074224042c0b108420820000300c90b00303801c079110400050282d507003160080c44c07401c2102800d54172080c11503144210340c82d24100d04c10411000340c0c00c01701c1d02406d2002520655005c081800f26043c10043d408508a040400031980c005225a88e0616403801a005040c505d05800c1c2001002880c2042c11411120f4800c845004442a00750f40c00b64a960207041884249014002 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 633950449 1250 633949199 633949219
    0x9030d020a020603180c060f0a0e0609030a1704030807120f170106050c151018051b1b0307030f20030414011e0519090f1206020c0a08031b0405 63
    0x80780c88401e1403038500035540540d4114000c42d0000389070f50f008010900c130088c10004030501c10316007001d455030000d10191042170520701d0b00030021340c070382c81d041402800c2c00c03949819021b0924016000c980c040c650002c981501c0f15284e0a004011000700c00c00c03980421111071006030258010800842650028000d100d51603080501c202c449800c144d040540601c582c480f00305074524848003003841690722450300c9038075600c0d1040405050b21482040c1c041030b464002801142c41d04841882e256184405009039030f0501641602c00701800c000c2c010780390740000320b4640101540001172050784403030390b50744806400109040302245687c41c040e284041c0c0c17003040104101012600c003040107a1050401d4045180c0b0821400080701801c107400300016400100280e4020107140c070301403010010b18100043c10304001130785060400301d0040303070440c524030100d200030400103070100c40000800398207456038001280f501c1c01c0c80d50010b0720041405901141c80c00031940400065900b115001051113020f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 633951699 1250 633950449 633950461
    0x130b0408070b0921210304020604140d050105241f120612061d031201180f0c0305060102210919051011060610080402122109030d020a020603 62
    0x403603025414281c0c0200d503c0410201142c1c00ca4000e1a21001c0200a0010021741050207604003400003020090010240284070250722154141d0382a5500c0070114605241080009420444413003401440c41d800cac4000c00246070251070360038100800f550b16500c48004c0707903010046a101d9440144024049841041c6900e9100319940c0ca1010054000028030b161190880c01880c41c030104141c50260300c030340305950610502c16602259840c0322020350f0170590b03480320840c40210113100385011411400032789000d84140d9440390b2050f20184004018171101d0071805030240600301c0d60302e8054020071b4064400d84020500369010111030455887c58181703018100190304070081324402c6e0304060705001040ea07480e8164603405402041d01e40b0034404170902c00d19840c02c00000c105602560b032507032160f0f102e90340100c4c4484c2c115a040b1400c25001c0c42c884031007032070500c5005486500e954841e103041100e810001c020203042d0b1040c1d040d207803006001c0344160303950322845500a4010100f000082c007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 633952949 1250 633951699 633951719
    0x130e0c07060c050c010f0204080c060f030a020d02190e030c040c0e010c1506080a06051b0a0c0f0519030215090303061009150806030f0708030a030911060a05130b040807 74
    0x414052542400790620139036031001800c641341d20208111040e4006410303c032036030b01000403645052007101c0c11890b01401d07041030b0301d00d0700001d09540419500030400f0b00341c0d2501031f010785120200b41c00c00c5050107441641b00800054000c18140d000780a030000380012800d00b0700803081001aa51280c4200c642040300454180482e92000c0d01e00380c001201000c110555070003202c005100030300c0102004881c50038542c084038405011303405542d8864040c1034000781c00c2000c0d602005424207158941003083c1c10031985484c0e0010004002d800341754400f40b482030034801d950009501a90031124503007482e0f00c0303414000070140d4041b4844c0d0b0040c03000803903925008000324000748240c40c059184558514900da20000c0744003403c0041084507003044100d003800c020042d5502000c400810302e1798a04890981c581c4201c0c5880703010161a401d090051000140004850542c040d181c0756964004547c01450390300311440c03091064020040016401d140309d4240c0e0161014170740640809450988602 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 633954199 1250 633952949 633952961
    0xf08160e0d0203070902090306130201020d031112090d120b0f0609150301080a14010b0a0b031005130b04061205070e04060605030a05010b01030c0906050315180c130e0c0706 76
    0xc1d44010300155500c01a1014003142c4010103a110700980c40c1c035010820541080d800a20b9000c0385e003404a428030250b80c0c002450040140303907050000d210140d01508540a1244582003001d80c05210305201e10124002041803503a000c1f03686210ba1201841503240586001c0000386900880d00c0c90038128601e4060014856030b10014107580c0f11400f203883d054050340090740211003e81291082c00244028400150103018120000700640c80c6d04000041c1800d406000700340b10130f030010001aa86000c00d100c0b540262400070508120100003440210107402e204450901460a10400007250805d00c07004501d000d5206010341005400c2c80f401514810300203000391409601c0d0b00e000135083d2818019881c00d540100c0010482d110000005400e0700c40c0d6101c070008108010904200762984401a03d400c001034000d850450030700d000000d0107800c101d4078004000b00c00c1c0e000b40300320400080014244201400b800790141603890300403480d1a041240c085800c21020050b00f4000382040e4080 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 633955449 1250 633954199 633954227
    0x1210512091c03030b09060103110d050a180f1403031303030b061612021612030e040b03030a05181c08030403020a0c080a0c0b18060a0306030206120105010f0816 71
    0x200c02d0300a0180c01c2184140d1900a041e00426070b1002c0c81e10580c1004400203a124400f828144162140d00d02c6002d190711460041010550b40c4a010403500855a001803003080780141d0084110000d0307060546035883c00c40400c645040c1c0b80b59201142401c0441542d104400d41d4001e022618915103058001d04101489594030850410400481d0308040080c4001580281c0e64180d001403081e001174540243d910044002c4540042c0c100b056110400c0700300324140c0d05140110141c20b000c00800e02a00e03c100039a689030001080c04241d90b030340306000e0402480b1741c11610611021203000d00c005241513450102c8a4900744000501040c003880065800500c60f10480303504400755100ea500c1030000d9008042c3c25002401d03290b080c02150002e041c0030706404c000700c51804a001c442c015030f200da21481d95002e8040030882d420002d00903806200299000f0386482c2d500c800701080c80740710350000d014103404580354101a014040c41030515921644141d801c1300500703e05501e05403000181500c3c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 633956699 1250 633955449 633955459
    0x301050d1103010609020903150603061515121609031505040f0c0602060603010c020705090f07111b10021f0b0303091c050c09070c0b070302070210080121051209 71
    0x20508868500340f24403030003805c4044006858200c1801058103050803480d8940c50811084140b11503075401080c01500005244000e80200d90280d001c42d0000009003940703214148049042100d150780a2411449020011411031707040107642d009882034402c50002404a400e070249107031903000d859100d41e030041d000700020091004540d4403014011150741041d00180c05c0001449040d081c24080c824042d10140013515100c1d0520000c1080c0e40720007844c50714664400f1002c52400c80c058030a9042d04200c1c04150340d412020800c503074480703400042e0400d001e00711004180d00402d1011600d1a0207680c200500c10000410301d4820300908004081d20398140020800303401d142da02d028110038903480c0e03905484418505410720300c3c1404040c4201c0b50042c1c24003c10030a0995011000c802d100303501c06065490354031440d000700c0090040d400f00030740002075a040042e0194000203080c1c100c40050010403100686c21102101d108604180180164482d280035446041d808025010003c0003400e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 633957949 1250 633956699 633956723
    0x3170c0d0504140f10060510020a020411090904030503091005090c0103110906070f060507030212370510170706050c0a020405130506160c240c030c020708120301050d 73
    0x1d800f9080880c02004035030154018996075054045034040c9400030001203840b02d0100c0e0008201039112101a40024801c5030340b440c072814000b080c20155100c41202034002a55890640303070140181d40182d80c096200d2007102c0d8010008211030292602c00d402d400c01400d42481d084005402508034100c00042d0600c043c0f0202c146504d400024003041400b07803650126032001da080107011034402800105c02c15004225021004006022030380d080034100781d000c001c41054070f40d1a15449031443c901002d154049031400c60400c250b07001240580701d84c946114409a5401c0c0c1f1a040c48148040001250850201002064004d0780941002115a019240307100714030b5000804440c011190030092003031190705407060040c10410745034045100129040480c81d03161010f00f0340c4480c20401805420700919200694030b91400c6000a0f10a81c0818008403851310f00241c05413604c40c050000621400000241000000a640800d00c10140d480352941c0d0900080c0000480321080985034489204 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 633959199 1250 633957949 633957983
    0x180f120207081f15031106070c08070b07020423011203092d060e06090409020315070509120303010b19090f03030e090c13090b0103090b04060903170c0d0504 69
    0x2200d1049840ba000060005401c4441800d408031819545040c10036076a4407005d00c00108100380082e1403940445174039864001c58500b040540705540c004281d90f0095200028580204c0c0b070141800718801c55080c03240010500b1200c0700140110481c0680e03541c0480104050034605e900014043e0080ca410300c480c9448860a003401107082c0030716410828007482c0d03480c2064120288002404080c82c1c0103900243c00c00000f107682c09801c0e8198401c9583d0840002196401c000c4180e09400c468a614514503207404c0280841e0811080c150040003541c00603a0005c2c0e000c011a410b84d13501e480124100f81414185409030600007154006000d140309020581501680c14080118840e65030701002038400001d04c030300c4407400340c2080d00031032040c40750318030424180c04c0e9901540e1268000007140308404004070040e010924025100c1104141408140003854220f50f8216000b41c41c0c000840c0511200d80c50042070803114580f01810600950803009100d400480d005401010403a800103001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 633960449 1250 633959199 633959203
    0x507020f010603050303160908030910090302031e100b0915010e060409050405070e011d0a020d11030406050c0726130e060907020f3a0210180f12020708 67
    0x20b0300b00384e40c071703910100801040d000b81f0b000840c1000c0b001e15140c03c02c2860940b03915500d0090410203403141158282c0c02c0280c0b44540b000000442d0020304440c506600c4281d2000d007040c5404041015006005003541d1001040c0036000c00001b014005d800f4555580c282d00304043d0744451914100144003d555880d9500e200c00780015141080c80010701c0c2c00c0a140491a12591791b01c074000800b01600104007490302c642c459018011281c0c1e900c112a90f03880850402840f82d984000341c007916002c0c0c3c403130000f00c100024521941c0f180d5000c00c541d4486002e0000c0c0381c000c0d110700a2480b405685080242e5101e60001c10005003851701032803d100d010341c0d20700441403168001c2a01c0500b00d07400c1200903d4901400e54102c0058005000d0304098a16144d0310b964605a0000040610785210003e00d404a14140d14131008901c06c0c02c0040c0344283c0c025160f00460003640c3e0040d04004045065a003407412110070194002c10020b5800d00b00e03654052004204600d03070041d4080d0201c001820082 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 633961699 1250 633960449 633960461
    0x60f0c0f060f0901050705030f1906080309011404030b0c0f0405130e01051303020607180302041a1e09070e03032208070608040b0a0209031c03060f120c0303030507020f01 75
    0x20300001e400e107450404065031a02c5001403203034116038105400d2204140d0070108070390708500650035103144c6070303074044000300c900880302e001d00c102d44d1428100150206011015120500302665220040b001d4003807030444502075804060090010b400109010204800040050710300d00030f900d506156031000050604444040c0d20013400b074072080d5603a03c405c028030506500c0941c80003400c182113544c1d280255580002040e80d014002101c143d5260100001138407001140c2c0100240b0046114084017200e1902a40b0500d0040c00b5001c0020070312101c0c0ca4200380c940c03502a140c88287e40d034012085400b4400300d0f440300e400d40410000c44402c0f100c2203200d804d40b0444101c21841551a10482d2454131003183d01030b5003000594014400018440119103812155208016850350300800010381480858540d0317a05000800c2c80140d402078154221104a40c4403028441c407460351400018150403e000f00140740c04035603041407001901990201ba000400c2c1e02c104d0f444509103c4180303003181c0c8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 633962949 1250 633961699 633961723
    0x807090917040b03041103010c02060f0a091e06050f0c070f0f0f1208010b0c0307062d0f06090b01020d1808010c030615180b09180a0b04140601020705060f0c 69
    0x30f0004100018003030075140346a507070308003a030003080a001c002000a44030310b005410841c50039444008680002c0c1560040c10750240c01c6200e00342c030620b04402c0540702c2c144024003121194201b00004000e01c4a83d031f81c0302d00c605e182c03c02c41d81c50481c161707941c860032003643d403000c48298001030b000c000450b6011740c000038071622030056203100114800c0c0141c800103059002c078442050030403501c1040032010003a100c0d050740c0000b003c60042021030b0060407601d06803417425080000c600f403105140400780c0240030340b103080710010051f064840c80d540d07080e035801c101c00b0360140e80000149941d0510990400c00c8401070700e40c070722040d1919441e215095804160020001a454540c184072244901c15410800700c06418883c001c00315820891002483d1403150412580011543c0c1d03003d510364462990f81041c4e002d030403007521300d412005900109652070b19503000f60301d80164904100da414584500600e0142c0080800034684010012658001440840c03000c00074003500e00c51080030800708030800703 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 633964199 1250 633962949 633962969
    0xc0207032d0602120c090d06020906040530070303052203120f030b06040e061003090203161712040b0f040b0c07052d04020a020a021f031104080709091704 68
    0x11103807840742c41003c005403428081c17883c01c2200c2176056540041c11000d41b540118090f0301c0e00100c200080250043e58041500175150305131803100c8805003882114004ca0f1000100306206001c45066600c0d019800f004002c604208a604801c40842886000710900744040c043c8964030382e80d600d10707440001c0301c540010a402d4140c0d0301060360180941d0b45196010384146052a140c005100102800070f0030340d50150941ca82e480000e9403281d0808401d941e005021615010b04c1d404186030618a980314a9009804080019440100114030904010514181d2605042c00d2250002d4142c4c411088072102d18402c010001e034091155010b42129440140134104442c03425007405842100c110000c0e1a08601e01408c41d0a510040c01480d0003c03026100140c07607511128099140c06c466003006076020000d00100006410020b070386044040d00e0303550500c115034180c00000386c1c2c2d01441c0181c0d0400d81100d0801d002c03801d0580e100c581102d001703050203103031400e031103ca038291644a50020000c0c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 633965449 1250 633964199 633964207
    0xc08091c06060f06020c100c1514040314090f1210090803090124090902010e040e010501060e0a0303090311190f141002030d0509100e01020310090c0207032d0602 71
    0x200c0c0b00e000601006084c41d0000d005008403000000e0a03001585d0700200a010740000b205041c04541410415480c400c03034400c000d10390f44042c1c16411100c003110b0480000f2502902e085800c0f94400c19610407401c003420828200c01e00108128000d88603020078202032103000001d280406450080185150003855429500e003404680c0b00d0a6500440c2a10030301181c051200e20400645612030b011a02e04000c009240c0d0602c1c0b0048070b8500c103c0200c280e01509000d1560141030065100c0e078100e440903282c00300340041150912a41440603c8041c2c08142882020008203081e100d0a141a0034010302042020401800e000715400654100c0003108000813001d00031804510400e4820200440c3e503100c50300043e0200035035a01c99900000c106940f9100441c2c1003990070448101c400000c0f5006010b61031940303c02a00035001129043d030489000381f40003582e062907218a0380005131543c09401090700f582c0700c0300d07848a08940b00b40c0e0482130282e41c48500c0a4050f481e05183c61003140c001da61 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 633966699 1250 633965449 633965459
    0xa18060510050108012313140f060901081b040b04090b0f070207030c0501030f0917070c0b0f03070507080702031603060515100c02031009030302030103120503070c08091c0606 77
    0x500c01070741c1100f814095020018842d01c0b013030442104008184000c0b840700d680c40c00c07012903c003904954001c56940e00303002c40c00e01d21443c0214540d106810740c00c0c1c2c600b0301d07654138000c01942030400c1c8561480c03600103000030480c6000c0014014440c03070010740089040d0002c200400c08861003080140d554600e102c081c4145c140b88080c52540040b460320041440702d05544030104a003900e40301c1c0302d0600d581d4003181e4200a840340c024540c4a07030404800c0400c500c944512940590200300e08039140c40901601041200e61740060b24040c030b50201c001070441da140c2006407911380c4210401d8444070424018240142d40800100b442c04612030003201c0100d15501e010b8051b120007070031103400c54a1090001405071130780e000c105440b26081c0750a0440e100d90780046414842c0306844480081d0800e10030704145500b46c0c000f58100d901c1030304401805c400c003001c200c0707060000b5500103000514a0060700c01142c070543c060801c01c1c000034060b039071200c0d240c82450118601680c003158426112074003000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 633967949 1250 633966699 633966721
    0x1021b0706110f03161a0906060a0b04030b1b2b0f05061e011412180a0519080c01050a050702010e0a170f040f06020f070510080f0a180605 61
    0x1030119542e4008000c0c103450020200d0700c90042c2c26642100e40c0042c1040c401b4404981001c144182c050709030728006081c00f41906848040854039580150340c411800100140079000f114110303a0040d42001668590000c3c499004602c003025410045003449814100c1c49001c100301c41010712084005c40d003a00350079108080d1400118140011868035081180c2c6498103c1c00d00c1084c00c028a0030b003502824140140c4d0441181c05081d03445131008100f800002091460f4140100c0310714104a0500100164103503031a03440a50040032900b18441005943d0450700301c11030302c0d503c250002c03410b05a2841085086070003c580341c1d0740d22511401070002d91f80e021300ca01031a2246403c05401014502d403a00700e40e0700b0740a880501c131ba103000070307120441c07148450564000d450040f86605d0380d81d690342002580c030f007000c0480300d0081c024808006001e1810711521007901000f070f1100042983c0700c030a0043c2081d0000c00c0010803a884030900802c14410450250542e031040704000340038200449071030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 633969199 1250 633967949 633967967
    0x2040f0f090f09020319080c0106080609120a091401020a0b040308100e060a06271502060106031806230a021b0607080c071b12030206060a0302101101021b0706 70
    0x100749080d910380c2c0941c130046000055200c6003043c1900040b1b45103040c0c0b20030b11603480462410352070400c02007440030001c61005e005143c0c003000c9500103025401010220f10550180c140400d401c4c00c002c0040004007000e0050b1030350140141c1d40c041603280c41e400f502840c106d0301100028080010446d91034101800c480252040705501e842c0c070315050012628040d83c40c0240ca0a00c284015135503199801c0300303408075401502141c480c4800c0c0d500c864503801c10040c00300703000150144c0000031130403034802d116215003c504441c03241011b07821515403600a0907907014115610034030403040b0000b50102031010340540c4e004180140c2d100d642c204071411101c41c0511400c003d800000c1404900f69001001e960070445c1d091041e40c0c0e8443c246031466504a20240a12607141081c80004131541d00300c0c1d448981a0083d001e45030741eaa98507080000c840e1190100035407109030a00b5020032644138600c4420182e91034000145003400380305a090700b400c00d0340c0e043c800c1c50344014028080140d000c4161 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 633970449 1250 633969199 633969221
    0x405010819050c0c3007061805010203071b030206190e060c13060e090103030e030709050405010b1e0d1202011508010606030608030a08040f030c0f05010f050106020a0503070b0a02040f0f09 83
    0xa84002c90104c0341240c00c401c04039071652503800340810100203003c002d900c01c0d20030b04492032300250000341e545841d034081d400458140b00440c540d00800c0a40d01c400701528030f0000e030f040d800760030903a8407541010503800035001c044220640d10740c0a240d460740c082113042d004031303085070966840e01034140100740d100909420281c1000310280c05034140c1d880b81c880032419a0f6240c14540506480035002c03e150280b180e014808640c201401c2c0700030310006600c400c50a8009a81c0c002041c0300c01244010041c2d400010b01d50080b0004400b280030952007400840710500d81c3c40045640f4540b50580b030030004494000c140141d645203001c0200682520070580244036401c0558100b03508544003030060310000700080c29990901880c2e6080611a80005c82480c0c0c0c40407900308112680e0034058001d000030040f0206480c5802e00201c0d009000150110301c0c558400700552501e5010f0361450401e01e0040c0a9429454003808040340040e80d1184010150070300048840c80c8618060016040c0c48020703000b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 633971699 1250 633970449 633970483
    0x70f1a0406061509030b0610050f12010302090a1a010e04150e061e03030a050f040317030f010819031101060b041503060501140f0a0e04020d021309110405010819050c0c 74
    0x10030000390071400441d8440811a40071480d1b28000c0300a44c3d41e44541c800102b4043c3d800294100152000b83c0d000b07050343d0096500806680c1e0f0760309100c00b00c3d089561010350101c3c50280724003a079803080341303c01120034001c2e2010850058200000c40581d00e00d41141c0381600e0341404102c242d00b01042c09402043c1c400d10450f030000704020219860348036614070070f81004400502e03c0d220b0310480c0101c50007168000c0c1c4015000c108103002c100250030a58203800307000c0d0900300006108000003410145050120840c001c078100d581d9065810108100c90800c3c9075403210400038120742ca18000d4001050210401c205503030500a0041c12503415410640c1031082d00500c00d880340c00c1e01c0050300c6c0320040b01c2011a540307056540082d2000030382d0020895005000152100700d8915a8010f4510482c8030450400d500c0e0701c0304840303010344d0010520100708140070f020410040d8411018140c001204030152400103010a01030f00599504039404c9083c4000050500c204d90403c0011070b49550701200 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 633972949 1250 633971699 633971717
    0xf10230301240b03070207360905071403010e0d030b09090d0f2d030c121e0c1e0206011d1003061a0a080c010206071103070f1a04060615 60
    0x3804600401d160f00402848660200014403481c2c001c011401c0a0010015559100d0042e05191b8295150700a090504645221500c194603400e502071810142e600c070000e44082ca050046082100c00905d04859056495540200c0483c0c4280328800d224079107540e010603840d03520301c284504035501911402c003980c400c1600d280e40d1540700e181001c1c100141e25240300e184940d01d40c172403102c00140d40e524070f40303c44032802d000b81103805030f03c807900400300c039103038000c01c41e140001c240c08980e00784a600060852080d6412803000b07599020654603203140c1412a92070750343c2031078074540c220b150000b00302503031048005012864074410000a200c1d4076070b405105a1400c1041680900240e00c4010100c1e600e03490780702d20ba802c81c018587e180c144060070f0341c6001a42c3d40e42c1560788440f4862424051300612004c6042c0d0b9201d103150303c0d00700c0313071000040d0b241c429507954032001d80e544200181e6604d45031141401d080020001040d0080303003d480701195540c00c1c002240d940d840701409030310a1041c0c0230 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 633974199 1250 633972949 633973001
    0x9061406040f05010c0303020d180605072d020a0c0b04030605061e0409020a0b0c070e0714040e04020f060c010e1b10030b03070b07150c090e0f10230301 67
    0x2c0200001d0795020f1030001c240c5038480c6000ea01234041c500b000441d146c200400b001001d5488012489102d000300004c1c80503881d00d680c00c0d6500301086400e00001c16160102810a20141103020225002c610455480000607111505843c41c03d17040f110300000c0014080040c820980900c076044201181d202c0d143e40c45038420000030709890000d0318080ca8036a4040c0c2c0541d40e400d103948008102103268039545031008800d15480700130601521076011107590104094030721681260032040c1c0c200c1d010a180c5070501c40b5092075840300034822603001c0600c44040301d15880740700c0a01000c80c00000041500070100c4025420300f000b480040c01046014060342ca1b480c0d88040300d514082c001410006104030f40080401e04040e41504201d0b00344030000380a00c1001021604100c41001c01002040100010102201c0da501d19204241514105002203090040030940c21900040b11810088405544600e00c4c25008401c0148102c103000340746504815040070300036050189418400301c960f5003410 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 633975449 1250 633974199 633974219
    0x1a0304050f0c0a03030305190221101203080a060f0b070b2a07080c030f031609050a0306050601020a05012d0908070b070c06021801140a0e0402030705130906140604 72
    0x94403018040541f0741c0c2c04102c540f02d0029545007900f120280a6540b584980f648220611950030410a140310740d000140262451241d404161420807500c000c0003507450310200c84182c00a0b00b002c6c581a5a080300240441c624444180100708d0083c10503144c20712420b103020241da0051044010070341070044241c030805498403200320030701041e2040362122101e0401040c90301a50f41d00c4c01c00361000040541c24804000003540c402c0e00c0c0e600016030304214980d400c4412070035520440c0d0300b04800020500c00600d0a40090b40d2120061040318200c0ca426224036007503d0031210a80c1c1200d0001015800400040c01d01843d10f840b640c10502c40024035944424103842082000303020036007900081100603110b4082200303410b1300124159100e6060010200950704c1c08100a070108114440144506028100703884600f1230644900549121060a11029500003043e10081280801c040b01d94855050800d030050700c03a1900000c3c00c5802c11741d80c1564030300340a00b01c034407491090104004d02510 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 633976699 1250 633975449 633975469
    0x901031502070506270a1101120e0a0c060e030d0221040e04202d120d052212060207111e150c0703030e03071a0304050f0c 54
    0x1105140c5400c562400e00e104009029100004007540107000c2402014822940c400c0e24103124800c4101e14101e542c1c4030941c0c4d8001204000700907400e9007984654960056540f5a0034034084000440c54104103500d0504000340300301c046070031100d040307002d00c0290b03840001032035203090650080280c0c3c200740308080c0d13965400031000402044d1200184450211700415200100019030703440305182800c2c44c0288018800c620f800e038070008100d100e007103546404101c081c4004c0c16680104040c0e00c5a08207100d4549000720880d81000d0415142c494095040043d407103c107015a03a8652280c011044100304883d100d079030a00140304024050040045e51032107004d0840d444040103035600c80c1480c1c07021140c00c0d6055000d0b48002d0840c400b200780d00c0a4000c1629100081f40e410010010440d9880f4182c0201980300d074942d8071201d01031000070301810490720703e084020210390b50141d0b00c001c201c510285a450020b1010b00c080244030802c041080b402c0710a02c0300300f019040060701c181c0801e9610340 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 633977949 1250 633976699 633976703
    0x10e06010b0f210c041404050105090c070c0b0a0207030b0108150f070c0c0b1908010f05040b0d05010f090b010b1206010e0402092805060301030c03111c05070312030209090103 77
    0x150018440340044201c8aa0706811182c080b4880031a01d480200e0300744c544c009200b0201e4001d44a800341c01c03d0328003445807505880c401000300d0603540b20b49c401050140c00180040755248000100804c00789070341ea0150484992590040040a0840c5484d00c1d400340103074031540444d40203480c010107001500d49020b03400403000003002010394a03481c0c00c480368800c1340710182079150301060224100101c0c500410586204502d0301e9101086000200c4038214240300fa0517944100c44001e204526158003d4002244000d1034031302d5041840e118142111030642e000204150341d48405020080e280030200e0040c03d04619003801c01d00300d0786006203a503e005000d207040140454450005640c1e6034140e480300d8501602042d24002600074410590401e5048400c0340101440f00090914014084034180c0c0c0d404400c040042d4916036400c82402d0300030308450380c806c00440201c0103000c60008040b0b01710b8012002001e034580341d801c1504402000d81c0c840002c06004004603546a01c610790076030f044035 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 633979199 1250 633977949 633977977
    0x1020c0c01030b03070e04080703080610021e240709081c0f090e0a0b0f0409083004030801140a030b0f040203030d0f0516020c1806030106030204020d0e010e06010b 72
    0xc03d010740024240306150b04401d00c42c1120f94180014801010080c00b0410f20a0311140011703160305007041100c0f00051201030040c9e010300400003805010008241d40e40002c1d00445051541030301480d803000f000d0015120045200300308101c50650700c580001c00410b6018082e126101c0d910030803007884440300d10300341d042c080500e20f0440c0c0070f840341c003c0d0002030145100d020401d0402003024005810701680071440303041c03c1c07510707020140f400e446504102036202070107503e00003070316540c901a0313080020701030b0541071038403940d4048416a49005104a120740d5600d0f400b58140340228401403052440107000700c00500060000038a0302401d00e82104843c9080d1600d03070707901c1c03000070b140d8402c5251060b5034a081440c4240d202c011504030900403038240d90407550b0b6070016203040f80d03200714a41c003180c1c0c0003d01031000940c605545c0c51603030b00500098008140ca80d200c1d0085070999012130420840d0590311240030754001c41c28070441c00a4400b10b4081c08165142114001e010f0150340d00b00c1c03141e2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 633980449 1250 633979199 633979211
    0x60a020f180120030702010305070926070f0608102403051b13030201080105030615010c060f02040e01030b061806062805040806010806060109090c0309020d0b090f01020c0c0103 78
    0x280c0c0c05100c1040f4003403070340700640d5868624200404d0f125081805d00300c2c080307800c0c0700c08520315500034a2184181c50035086188600c000070148807410b242d84121081030b03070182450105128a00e120000e010b4402ca4450840340c0c00c1c04103803011151010b41c40130700c40d115800003448900ca12200c2c51202c150b00c510f4041002d44852842c24074504540c11090103031400000c01c641038043c10740451040780c0c001d03210744885070b907a078090548030304048403030b458880481648840a07600440500d91100c0c09190006815080e800101c000c03030388180c11400000d03c1c543c004100300a40140c0d2554445c90070303540c030280ca08001c00800f07007032f400c06801240300e80004188020124090004810b00000f07181c0f4445c2c402444220240c4581e10a01031030086000d210004038400b00e0014856001e83c806035145004d0701e141c500c0600046c014103620b4410161101104400741c0e5400c0c1e00c8680250245c0c1ca1190b4500b060401c0916210302d003900388107140d0044c481d16032811400f00c0c241c02d800d07800307007000300712 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 633981699 1250 633980449 633980497
    0x230705010c0326010e071202030606030103060507050f0307031e02070c06080a0e0114091204080c06031305010f1b0c0314070807050717100905060402220e0f060a020f 73
    0x1c0203d0300110781c40010b0140000541c0aa40b07041c0140502c0f11030301c0710782030b100e25100c034442a031000725007007600074000300010000540e01d03078044e584c0b01140d40b43c8641402c4809640003100d0340180caa400c002601c0b00c1c1030310f01d0162024007280e04205009011458035640395140d000040341807181100380414040040d81540d501e4200f004403140d440d008014884031849103a4001205a440c20312501c5a21070b85c2c408001c90b24100c400352241072008141c2c46410800304807140cac0c4000d03c4440d0310b0044038010000107009020740d80c0030120295010030301c9800d03d448050b020640b0120301c0c08122200300d50034042500b2110100d031640c0f09098569540642e801e0411152051260040061142c01c10008006007000300c4000b46144807410b8800f065054030640041e60b43c000c1002d0156040840840c3c01803410219850400d516600d1a400f4445d0104042c0c080703604c014405062500000130402d49190288007580d8050240002142403805804861005008500c1082000333140d100260070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 633982949 1250 633981699 633981737
    0x50a020613150e010209031204031a0903070602090d020409050d08060a1802030c1303030804060506040902060f030601030f0e0f1e0d0c030201060302040f1e0504170a1803230705010c03 81
    0x8446c014003260118420300c280c040550340148420b841114417240d42d0301d070f0804641c0708039016007085801107050a907551904030081d4400d260b06030380642c02c07a0b0749000584450044518050081c8083c1c00700002074000580480e00c01003d1500c242030100091100302982c1001c9a030300d4044003030050f182c0d83c03100114001d0b48550181092040d185200c000b0805910030030301845540320b14414030480d01e81c1420b0009075808103400030b6000000340041140034048001031a40030314149801704900f203050301d00b5070848144118450694000ca9030156042004000840744000c1c1044240e00c1400302e952050346a03038518480404000c8012226414107100350044e0000e190010f1041209040c40c0070540000d00000c075003402c00540303c010381c5001044034858039101d540c02800c07421291000700c0085445510005000c3e0070b008080c07a04890303042c4082c50b84c0000d0362190000c0c00c0c801c00355081d124800020303100c0c100516807040c2c00c10300850743e010b20702c22852949400d000b45c1088203001404 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 633984199 1250 633982949 633982957
    0x6030c21070b0f03060a0f1505450a2328030201030b01020610050f0301110706050a1515140912011410030b04020f0103090210050a020613150e0102 65
    0x1400720007001c643c21080389a01401180100c0702110600302c2d082d900d81c5001d001c20b565100d500100d5861580450107a40550010510910000344120580144401400c044004503010880d0014003540c40309196019800003a80d084045903058522407030034127919016800c00707044144150305403801141585803400445016090300540c210400d80c0c06100d481e44a40600c001c0c1d0000741000c00380e40d165400450418003800741d503200312480310705100500519142071031907240c1565039850030701002e0304ea01c000381031854031806000c1a1420540e0000c815148014100b404100d4000000c1100e80c04001c041d074060052810300c200060f402c0e0400100303074040d01c00c034550071900c00a6902041c2c1810741c0041e03c2c04041c40103005843e128000b00000c3c00031180401003641c3c0040c400308016241010007000c0b0114149000702d201a5554040f80041940790303044004a0030202d441040e0315014041c1c90fa0103d4030f50101c1d107082d803c0c0e0300d502d41d081c80b0f4540024149941c0720558000e5001c00c0d0102c0e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 633985449 1250 633984199 633984209
    0x20906151207170a05240114070809090130020d0f21030c1211041203230702010509060702150c030a08180703140307021503010e06030c2107 62
    0x81c1032500d84800342042c26001d1024146001c2200025044500c51107400d005a450014003c02e0384128801e5140800710b882d01035051000b861600000c0e160510002d050302072040b03c0443d1660002001d111002c001030300328000f0001851014030390700c50030403071228407a518500c00c044200e100c1d00100c0c2c2044c080315009004042014162800c2c803520007200300c18118070800c6441105440d0008604444604080b200010760366410f481400100c6e41182c4450103071000320038135040c1d44000300700a40c0c2051740d0031000314100041c800c15411a8010761200e00200156403441d295041d40000c000d84690002144a0b1001041010035511102c080c003c1c0712840c1c0141565458240d01038981c0d0b900320115450005400307a000507098441005011150840040200381280c2580c1e0f0350014131030507400750403540c8400e028003400b580e22100064040c90710082c801e9078032b505003001c0c0308104500030700a0b4001d0b03000038415189500c8000e242b0000444844d0815103014103910071070b04001d40e540c08 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 633986699 1250 633985449 633985477
    0x60c0a0314040309060816080c0a09090e07080d090815040f050d020f100b030a0303020c030f0a090e070c020d0b090f12090a0e0106081b09030d020c031902090615 71
    0x2000100350300038240c8802d4170a01e031261043da568040160908820000184001900c01004a406e40101002504110240341090040152164218011280812006030082c0d00c00d21040001060a000440c02000c161501e6a2564201701a07169614205c02405100e0110f4600250902100d8010031405640c8182580c45030580030394020350b07846010f141d03121240281030700754071000c9170b601c900c924031040900030b0040c1c802d00b5203040d002500146c030417110b50700080216031103850704e141c020041100c1c181c881042c0d842c1404603072001440014000d4042c4502d026000c400740e0358501500000d90f0b0b022803014099075950144908240480140e00030500c10b5441c841100d40b1444013410010780241c45061003c1c1e40e81c21200d4a5180070710a040204440c4004100c1c03c801d104038201803041d000c0b00c00c0e0724150401003c245022038840f1a9001078201c103640c0d851038030b03061241a0300c40c028070044603090421900014400ca402401403485420380c4804059246102c8050301c801c0c2c034100ca1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 633987949 1250 633986699 633986701
    0xb13050301020d0606030b03010606021b0402040e181005130f03020721020306092a011704060c110c060409050901060e130506070f1d01142217060c0a0314 68
    0x35052004e0011400b6040100342070019031501d80c00c05108010446180794020818007446030807185800705c030303400300c5030704250200408110703221404609409001804522150041005c4245007040843ca1091400600700001d00c9002c152400b04000e100350411103101011160307186c00d03450842540e000b10380c00c00c0c0e113902c0b00a104d007122480c07030001d0b4000e81c00d54500d503440c2641161075854503072a607c9251513000f001c4000c000d651a00c958260340604004420641810b190030030440100c0f001c813030b100c1d1281000b0808580c003100c01d03c0b04a284000401c075034002640040c41900907405008000d9a66800003582c4e81d409400c41e000409010390056018244600c401c081ea8119078010348443c424000844d494030702c83d29040344c00c0c40f02e81d035900142001150100c06200e442040742c80c1081026180c4043c0000f140000304000703c0100142d50907066001050741d80b00c83e4607402006205442d4000148a4034042031896201d02d0b0302900b50303134a046100059000304582001a4880d4446070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 633989199 1250 633987949 633987967
    0x70512070201050f07111f0b03010b0a030506190e100f0c020a021c150c0e011412010e25050d18020307060f020a06150e010b0c0d11190605010303091e0b1305030102 72
    0x292192088e01001e40080c440000b440c0140080b858aa10000b0199402980001d09540e18222190010069840e0109000d41d40e40b0321240b0304403150540e0049103a490307010001240451099003040100341c0090805c200203500010b002c59098080c141e02025414100410032038070015154a500300081300300b14051902c240100340c03000b01904580414140400904d045104405032010b441d010071010480d6802c010b40307507502d03c1003c0d1030302115000c94a034000054128000c10b822006a680d24a521107231150030319803d6601d4044000b003460744414410015032004a10802600c2803803d040503840300101c0b0882c5441121500070340020710701608088140507518641e02110315594483d070b2540d80310340500206200340281030066501071070711842c416010389040c0c00201450340503501c8010402000032540d503c2e4420440d09a0750300d0005104154015900300044d0451740c403a1208806148034600b107445443c060801d07070000c042005502c0241080044001c0d040140080d500e625241c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 633990449 1250 633989199 633989201
    0x109090531020a0e0f04084021060222060305070207051203070f0206041e1a031003111504080c0a0503120d0b0414070512070201050f07111f 62
    0x440c03049108004520700081c5080e00701c440c09009003002c039403000381d0744c071641c1c2c0d180829070103e4204402c0c2c0d6050755100300f0030301c0064a65004a40d81220123419038074280383c8140c9011082c0c103d0004810144541040c081d5101d00c0ea0704a564480c1d0016a503d080c0001c859440c4a025640da100d01404030010809580c9900100d00614041e002c84900540f01c5040111240c0840c00034441c552040c05004041340308610341c000c6c034a0000d0a000d24007900c4009034500c01610032048100f0041e0a07404003c00580e40600b074543e013000300002420350524010311982c824241c8005000000d44082502c4540c2d00c5203011003040d030f44802e80c140d490b5920820b603519180c0c0403014600c0f6404041c0d00246604010603940104482000b107a85011040c0c0e02510081140040842e00903580c4c43d4200c04140c0380e83d02c20350103403040f0348a541d144e59001d015210780c2603000f0440700469041c00140101840f1265029401c030040782845001480040007a80c0341825070645101c641c03a803414140c69216003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 633991699 1250 633990449 633990541
    0x15050108030d0513080307260106091806050a0e070e0303070b04050c0d080d0e03090406032a0806011802130f0614030906130f06020703090e130201090905 68
    0x310081030290340d50710151601300f41072409000e44024010400103041921400d00001400c412000c035041042c1d0ba92905544a9402d8000310081281d8603020301c40580c1c3c0d06022249800c910070180292800d10000c1546000c0c1880380f8003030070112601180c007650103203c07001c14481018040345d4640340340d402c007181042c000307583c141c0d90303401010141c00c1241080f802c030b452015080111280344c0071b04451040000e110b03c0d0840005400b0030300040c0c020755114007540e1700441c0920b503018004204040b0b49604d0380c40000028168540741c2108000702070020644604482202c0e2509142031120214000607200b0b6034150040d05644100100c1c885500170302b641c007a1000c1c0c2d5204007940307044080740446844240c032500c40a6012400044d10300c0b45112602800901c0384482880400fa281d891106980200c407049011411541060088581001c1c040b5071150000030131541d000301c0c1e60000f805500850140b00d0071140c441c4001104103280c09000b0480b000043d030104018080410903408a942c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 633992805 1106 633991699 633991717
    0x50918071d0d0c0305010603350310091b0f050a0e09040219060806011803020f100504050607061d010b2223040317160503041505010803 60
    0x59540c0303e9002148114000301e83d56040d894045025021a1642041624200c0080c1e40c0500b0140708424003214044640b0750300d48511043c000302c03c1c026001a12200d003404040d45031342c10080880c085000550795440160403e81c0c4040341c1c00c3c42400080c1000407041c034401c0c42140b802401154021748004d10306490780c110075000c1d02d00600e81d5400f941c046520401008025600b00d462080c9291101d041c4483c0241580d000540a8100350040c90280015020580d0a9030190040790003800d00145402e8545c102860540b0141040d02c1750a06000c3c24800740706800c00f4140196502124010039410b0030750310b101e40c02c13619220302c00c450750812600c07907000344a00f0800110140e02d0800703800700605c4a2a05040180480c210003961b440d0003100c000c1004002000d0a0104074405081d1030240e9032a251030528030f1400d8a10443c24400030320b40000011250300010041007110 = true := by decide +kernel

theorem cover : BRFrame.Cov 633812949 633992805 := by
  have h0 := BRFrame.cov_init 633812949
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 633812949 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 633812949 ≤ n) (h2 : n < 633992805) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
