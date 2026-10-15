-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3899
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:00:09.675002+00:00
-- url     : https://prove2.me/submissions/60b399c5-ed5a-4f72-b2b8-94ef05bb6ad8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 701079136 ≤ n < 701258992 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 701080386 1250 701079136 701079139
    0x915040308041e0621020d0501060e0a0e060303070609051c0e090703092301090212010e070f1404020a0509130c270e180a051506010f050a0311040504020c0606 70
    0x80f03a804101010394082d40031184507460740708024021000c0740b920003903099a0b11004590901030304004c04a40e02c00c0601074007241c0c8038101003913a41d07410082c005d4450b9204d08000301442d81000301c80c0d1004003e8030340d110b502420200f2204543d160850801c00002d111a8681114000d40b031546548586c566900f00429036601c1c089440e004400c40980743d0b20140a4410225044122a40000396021011002d203001c00060460481e80c00903007006a5188981002ea448081d001c00c20801400140000d100e01210040e5071860004205a60a208010f480c4104c0d80402d5400109000c0c0c003c5408403070009060510401501d00e0420007040f13002c03544000966515610035481007031900840130841c401c00c125020524054000c04401001004407017000340041c848009400100603070f5401500c120090440350f01c0b5200e0b502e52600380201058100004003510b18002d40c7c1240469492555510b004210030603000c02c43d410601c99580410b402503c0000c2d507512000002c140315009650 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 701081636 1250 701080386 701080409
    0x8060703150f060c111504080f0715090b030403140706090c0f120204050c0c0a050307140a0308070f090f082109360f0603060612030f091504030804 65
    0x8982c801d6603001c140a004902c0429007041d101c1c8042155101d488601031002080b141c0c0310f01d4100503624a50700150b008010710740c00700030300741604402880b110020306888558802c0c0c1411002d801816001c151044841070318000011805140c80780300c008905950f00264503580f1030f01c2c0e1801c8401010480d5041d1492501c009010a5610445543d442140c00f480305515010100c0c1e002c000090401826403521003100700314503040c0510074401102c0d8240640003951f110000340c240301c0c02007403806040340c00d203400401307402c00000d0f08400900e0300000c1b5880e101941300e64519040d200d4a0302900320540c1e40c5801d0341d00003400305002540d0880e80c1c2901d040c0c1418035403d1a40480b4502071860201d51040d428800f00c40e500c0303184070480d0000f8030003040c2c8041e5441001454051b036079060302d08096800072034040044c1410108201074201c801078410104c8807405a0725292a40110644044260400035143e8483e981c0c810b82c4403040c2c034240a0141e030703547d903034a050f85107070303006e0320a0408800 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 701082886 1250 701081636 701081639
    0x1090605040312151a0a0c02040f0506150c060a02070f0506090102040f050d0519081b0303070e0f0a030b0711011109090108071d0a020f030a0507030f09170903070806070315 76
    0x40c0c4d0101d028048030411014a04810542058940b076904000c019404000c000da006801581e91805855030402035184c0004242c2004818450a41103400340000e4610042242020900000580540c04003c400d070058640d00d162030710110000720120041c00d10300c5414103104a8420660084c401c41e00380ba0b40070b00700c0744d903148144403101c00d2042c00640107412403140180c441e02d810510400040c0309008503441e2071105082d4036403043c61004400c15a2b4000b104205549410001d800800c01c01103410110750030b42e2000190540102c3d0000400c02e10300c0c0e4001c100e1076401f80236290482501c20b402441428112401d039065a0014080c4603c40d29480300000b540720000310750740040c0c840504503414100400340d9503e030340c6940a0322a0311201d508006a511841660000d10301940c1c1c110004221b905004400809581c15080d99103650340c90044200300041407284044440180c84840540362100640001d040180b0795000401b00d000f010100405645d150780032000300c500d007001c40c06101c3d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 701084136 1250 701082886 701082911
    0x30b090a06060903062c4806041703190f080f06010203090618010906090807030f0510140912030c0d020d09050d0f0311280201090605040312 62
    0x10380301842014040f8401400520200301543c01102c036442800001c52515030406105000a0000020807045600424040e400b514610442c2d000c20410011040c0b000071400400005518104c0f03800c0510203810314100c1040b5184ea80aa034001e104c4016020b44004a0086281d12a485219421008182c40041004c042c0c094440c1c074100191503903545000740d4441c4040010640e014149505603c070501402d88655525001400800c900c0300d0100001c80c52800003400b07101064100e181072118a10b030500451800241c1c00c8103c0382c103c440d416102070b41d401d00c06c2c105030450b8160840142410000e8140e01c45203450140262044000c90704400032256030300005d4002034030b001f0b4402404201801c0483d5940d00581320b082c2c0102800030780300c100c0e651150b04d0503101c0c1e010b500104003240352000023180c040c41446030014915014519044000200b1401d110920001c18a952011a003000f8000d100b5403024940603400501000760381031500b00540900603110090308070303a00701461191203 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 701085386 1250 701084136 701084141
    0xa0306051203031b1803030325020d140a0302040f080c0306090c0901060804020105090a060f1b0f020405041407030b0f06060c0c061b07090f110406080402040f09060507030b090a 78
    0x1031111419400b0f00c040c06003030f1303840343c070742c0f00703078807030442600710240090301d594050004502540340d2140e030100e04200009490100b4980c1181001075402c0703510b000e08082c0d042000c0c1980681d0051885d1355404141d8410b4009000b07941069440c485410700c0030503100f40020700504202011422252565a080003090b0b0b1940c1004100b03130400100f000400c0014040c454064021f84141429030500713071510007284104120313a000000089252140d54007031508200001002036869110780035038105a00d0385042c01811107402402190740d000054140041c42c10030080041d8140f0698268070794074100b4590106094400326090507030f420100711145080421540b1034a41314010340b00c2824104200101508a80132809a06042c001060b10040f0280a004050003012100003000c0c03003051040412114100c2640e00b10070703000c2109100c816005000b1a80c0b240d41240d01081e14080d14920f000604520036004051900304070910002c01d801d50408841500e00b030307804c0300540c4e6a10348050203 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 701086636 1250 701085386 701085391
    0x51309060f0f6f080c031b07150606080105030c040e01110a02010e06060102010c09230603041515050a0902250807031805011407020f060a030605120303 67
    0xf0680021004044059826101d0030041e0070307004224a070103103001c094580300711040c20380585692030f203151444244080303000010312600c103d2107400002e1a140c10140c51a80050081503c44030040001813031400354801440c50303101a03400c41502c07400ca80c540080820790301410341308154204000414480d100780840fa041300d00040080420040e0311040c40300810070200c03901c100b55210620300f43d040341094002c06202c0b070030761f00000c1c1048851040301d0401802a24050469041c5415a00219400110758040e221503004589452000040032120100490881508007101008000911410324000140d407410b1910500101401c040f072034200c0140e90140c607a0284e8480b0041c480d6064503809020064108240111264112031160780d00d04807a94084900810004000c400c06034000d0049031810340c0070851010381e07030070400040e21644034001041204800403900f40155030b11481082600b5001801302965100f80301402000740c1701600a4901030600070764814054400081100e2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 701087886 1250 701086636 701086649
    0x809010b06160507051e0f03010e030712050d0c17061002190804091406130603020d1205120f1b03060a0311031f0f0501060e0a090c051309060f0f 64
    0x20310303051010a18002c10b00088000b9903403882803080c00315282e2500603603c01ca40b00d4505250411024840410483c1440400c842d07000340d05003c2c40000d0750704004291140554040c90058181325544400c6501740100201c000095003484900340030681c208501020301c041038405ea610301d40d02c80c002c0c420141c600160300c2c40164410440b249240c807040210140803803007401013074503140d40c0301042401d41c0c1ea0f606103a94841c3c1250148241c524110500d003030b6800c084c440c14000030b8695000901d58411006014001e800c02c0d00100000b81d116038111810038001c0c01041c031550401d0f002c2088101011614000b041809401040807000c1e07040a2302d102d07035401040c0e0280d142c1581c1c3c0e55500c120051040b50342600c90b44e04141c85024043c10703450684440508006020020b0082036003e481041e0300203000d1104481d800c0b00d07a9103070703000410280c40c1c2019000c1100102d004049402d0b1055126182c003807841c017440401d0f40b075030300d40240048031300101110790599155902805422018410030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 701089136 1250 701087886 701087899
    0xd0219020c0d0b07020109020612150121020d020c011803080622020706020909010308071b031a040819020f010f060b1624051021031d030f0d0809010b 66
    0x43d18a0304829800b80c0c0520003c10800705581c0490f840341c10128004802120010810180318482201c003a060038003403034642007129200400b4003883ca503030101e601e03405030001480d03003c1c140c0d15012100c0030b04c1481c00800c01c42c400505030300c0000d01006000c031f0005200d20302050084c5004410030b9148240300207080703011401540080001d510110085031a55001d020802075075a650800038004c40c083c0325040d680301030620b041d050007070210880d030740c19413113000041c0302041900342d035104082e50980b80340b0b40680399414214400d000307000300e4032030420860302d1640300142c6c0411021034220040000f8411080640f450205850003030044047c034840512488044030500150302e80700764019a11410b0f5240c1d20005048500e5a0305401c000395910f6409005540c285c0302241c2c0010711351000b2802c042e0b0889040710b0703000840481c018082240d9058440340301510300004400c080401412558000440c0300300310348071200307030b400d4402281000300010300003441030080700e04160700142003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 701090386 1250 701089136 701089159
    0x10504051203070522080a120f03020a0806220c0f080f13171c020418060302150c0c0a06080708090d05040510020f010c0914040b0a0506031b0d0219020c 67
    0x32045943c5600401c24081c000000010f0b850301c05108900c2010700903401c4131698088d2090141801100c13203103900030035104110340004180d005004a03000041103991a0140042c4064507041c041c808407490301c0303185010300702041c43d90400e40c0022101d010f0749070542076070798071010391719001403c66002400005c02d81480c0c0009600410750040b4000c0014140d003415a46580d0b00c180c8e01e12003010700061980000d0038000c210365047c0310304030038008c02004d110180c02d55010035580105130303141b140d050030080740c0300c5074004051260050f52400600030490305a50344900030301c201000c0d548440810042d070003181600c0004181c00e2600c00003511500d00d854907080601c00c0d10800b0b01403040450007140d1990807101820701460b04480d1403540e40c9980c1c1c0d41050840c6402d4600304068030f2145181540114458542071069011142c044820703503140d64854060340e80141005a01c109001c02c0000d08808480c89a80680500c490b5005c1000e0345400c4110306a80e035031800500c0c2503008140c2c902 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 701091636 1250 701090386 701090407
    0x12131706060f0d06060602070e09030307021203091011042105030a2a0f030f020f0703020d032f1504020f10020111070320070609060f031d0105040512030705 69
    0xc0a91508003501008154072281c5454049805c90f401000040e000301c00e007000384080c0e0b0300f8000d40110350800a5480d40c1401c0318003950b511485072940c0b507181d00c0480043c182072818000c284007003a280c042031014007403071329075203c13150301602800b800d041500460401c01085040c1e004201640100110b240224150060702c0d8401110030441000403c006141c0400842e101203a01c0c0c2031040c20f89999030245803a02034460744031a4045402c541c8903400d0901c1c0014001091001c69030141c070401940c90050904540040041085901140c102800382c4001c80c828045030054601c5941520440022050441d008860588000e50305c07060800407680f003890554104a103048190000143d0004111103c48131504a441c040d4003040312201001030b5003000c001c205027100b0303c0f04082c040103800c00d0405050000d0901403a4100220a080c031003007540240d00204c2c80c0d000c0351085038141c0032107c45082c0a80421203086031607001e00380708030192070b9076030302131b00c0c010442a00d94a003070103040384 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 701092886 1250 701091636 701091649
    0x6130204090f1112010c090608040c0f0f060e030102090a03081b011109010206100807062604060b042d092603060901081911060c1213170606 62
    0x180d902a603907490400010340101c0e0300c0d0b00602e2080d80800740a11401041041c0c4142c2e42542590b0340e41400c0740411041d41c084d00342e8007900c00e00d080400301c40d21182046404101ca41c1c20182c0030464108c40403031540c0f01c140000781241c2c3c1da80e5500c40c031016144181420b03406030080b01500145e100700c0920002d1100c2014056941c00c0090032032910480100503425912600c034140c003c0c560001d080c41ca0b070759040c4806a4041e42c0107400e40680e078a000051a0340b0030284c480c1d0020800d0001e40c1c8815500780040400c0c03410b5034151440824142820510020042e84600d144903a140c9001d800346a00d142100c044c1c1c05940176419541450b030140994050407241a0448500d4254800d2000c0140c1595000300c0c4500d0303501c4220746a18040c003d0002182060300b1104443d8420700c081c41010420040803513000c0d900102442c0c004d10103402141490181203101c0300030b8098030038580d40d404115005015000650403c0401c1541d5442c80c00d0345422014045595a03004040018984d05110 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 701094136 1250 701092886 701092921
    0x6060a09020f030f040f060603061d01090507090b010507120906111516020a060203010e0f06060304110d0201261506070f021e060f0a030c030203060102100905100e010212090a020306 80
    0x10301d003250118206d996600104c81d580d81045546d166a1580b280400030f00550f20349014800e00001c1001070302d161541c56551031035102d14017400d070f01ca01691146034840e41c1550b2400f540000d03400070b1654440c0010b8081e58250040700c0003d83d00300e20100101500217200004c0f50700d032042803006038455800010710302400c609103030f0651242c416000000346103440214000e0403070600c00800c5045c021952811230f540548154410b800070300a00000c50710818480400003011122a520641c03d4030050321131198010194001061446a80f54142c03401d20049104407810042c3c00f4840f44400708211042c011070700060320300480700c4900401424004800300c001c40c1952010072010340c03c000020070a030b1117451103094006001c1604004981c060081140c40826810705505510f02040000c1d5220749000787c586540c0d0b101c9002c0c9082c00070501204108104004050004103a206240d0740070394802c052500341c0f610583c0c0010302c61480890b44152640c1c0c005c1c083d21403900c400c03000c4441e40845 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 701095386 1250 701094136 701094143
    0x209010e0a060804300305061801030302100b300c03060c040504020c0705090106020a030801232e050a09080f0322090c0e0405240607080f070506060a09020f030f04 72
    0x24030b005c10418400040301d09050141c0d9010405141c03440600c07440001c141c200348054000c0304c2c010310000c0d40101d0504a040c1000c03400090303200c407a00c001240d150700010480d00425603191007803072154103e2800c19150440000712210401d140f02071541e6107100f261004003108082c0014802d80c900f6400500b910f43c00a003c540703150b521800041c2c40341c2030a81c86900075038440d00501c001c05030030003111801814110911560483c1c0704141d0142a41c58040302d510950b80400b078010390b00d802da40c190781d41c50000851508080480b00010306154000380e40140806e80c00000051000c178001100504a40e02c00c000d58140203124a000b64042c0e08101c851009036184030001c1000c0b2507138401c020b82c14129503102c000c040c4034902800300301d0ba00605010101504600303545000b01d44030550035001300307003a40c055580e07404600303084200340600d02c0c40c0c0c58060f00000cbd42130140700001505030b0141d2002c652101d51a031340d8050034001c900c500c1d041400441c2d0140700080b450f503000c03144241d02c00d00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 701096636 1250 701095386 701095433
    0xa0e03031b0d08010f0e06040e0a0c170c0909281e0b07081605211f0e041e0804052701150e060d09150209010e0a060804 53
    0x40d0100e5644084140c1945164089400c800903641e00080241c01020005940000c0703c6c10480c1030403420500400840c01591200c03500c61891000300080c604543d048901d040039951504542c211031100b202000b14107200d015242c02007442d040c242e00340121202401003561109030b0348409288070324590002c0002d039540050300f01080d954249060820401c0030b040126032a00e05e403090403034101a0604007040850000c0054413000c2a601d100c44510750305255071500c1700d24203020202810002c01003035410007030080c09807500b10844849083d840080350780c0c98054440b000c102030000c089030003030050980d00c40b003000701459490300320300d045000e49842072805481c2c3c0041550300340b01f04074813840e05400c0741c0c0c100c0d6080900394481d805003010350340f0b11021040f81e0380e000b0041240364080f18821400000c45840d10036030b41d80440842684410708076261a4164102c0d002500034504003800b1410f200c2d074059071031a1800d1410160342c1e29468010080d00ca0740ca032900c490f200d4030760002e81a00c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 701097886 1250 701096636 701096647
    0xf0408070506010605030f1509040318081e120f0d02071e050d021203072705040c171320040b03010e070501090b0406091203020313061d090402060a0e0303 68
    0x1d20030b010301c0e4041c0ca802d840c1c0c55170300e0500c0c0c0324072500c0c268010898004450386018803180b50755071340c42e02904a5090310b000584400060070050044001e07034800451481418403248040c41210041e070058013211080c0e0b40d070b14008416002e002d00c5080001c103980042000001d4060601d5405042021300172161100c6045208808200295081e00309507081c0d841448050345155040100114a4500303443d11411070038103060144c075185482100d20552000503981c0c8044891109040d0001c007002441404000d120350b6000d000c103031803407d02102c012000c1e80042c924807048503c00d0501c6a2142d200080c6001d00403e1400b11000a46e18a91054a819060b039880e54240100c40e401a0608083c1500e14640070015140341481c1e40640903120050208011554100312004201c0e000c1080c15860b1081310325007281180305089007248040da81090101d40c0d0341d404542d4a08100d00100030080041d41d140402050442c12a002584484100b2640991a101d64a41901d48001504807800c22 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 701099136 1250 701097886 701097893
    0x80c010c031d0604030f050c030a0b1501020c060d05161803081c320c070f0c0e0705120c090a05010e010311042d08250312180510080f040807 62
    0xa0b8045c0d44141c038500b614050758002c0c05002d101d40b02800d41d044000345020240355542d00034054008224020600e000f41c0c0007126a402840003035800c0c20b0080c50a55205444000b40000300b00540e001080d004003854200c482c00d0041e2080b01c800c440c01c40210008618641d100030381a0b10440d4520124003500340500034400c440d00035400c407038181581c3c00c035182c3d9024006512071005074201c070503845c40d58024030005900d120212134039290444217000310369000e07040c4070911600395841025524580000c04c05456803040c0588441031f0600080f01d500c0d2901c21420140d40510030b8001c1d40642c07040380030441503000d0001300390301079410b05012800c00d1140c00c81034a00d4016600048130700c0964034002908100000902002d0459210408a01c80c2001d01c40c66840c034541c1d5170341009420043e500c1c0524070f503840500c2e0007954403100b00a1403100c4484014610110190b10012030304040d5000708031486e0040d2306143c2c04030301d60b981d507000c5c2d0380716400c4206045020304107131a00802003240f503020 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 701100386 1250 701099136 701099149
    0x110c1e04021308100b0d0b0402030f030712030b15191b080903070b0c030406030c020a0803091c2a0c090908133311071e080c010c031d 59
    0x2011003840b4a1a02c1d5450005110305050524020040152401000951680d16101d007000e2594000480005540c1c1c1c1e48040380c0351400b042c0307144210f0300c408501d0404004805042c080888010740c0c080c44507038524800e02c40c015180360a0034003840014069540c00c03410140b054840200303203140a030740f80d000e543c6100c010420b03004000e5a960000082c91030b0030742004c02c0360300d00800c4000c24a80c548500e1031030040c4c0b41e0042e4000d4130700f015160300000341c110b4030802c5441036080c0c101000e16520b0810521190745d52080700c9505900c00f00c00c407040011540509840503010700300350965a012a40e1071090041001e1040742103600702e010200204905200d0306c5000001440380641950715030000b824003002a61951140c403403002c0b103142800700c051a510720100d6a0021129030406207140e60403c1c1c6103280341441884103881039004c009121251001e038800b8941010b0040c610f041e031201320058a5159480119010078149040100000d04c542684482403400d811a0806a10103400040f00d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 701101636 1250 701100386 701100397
    0x9010e060a0207030c0e10230402040905010801140601080115180305060906090106140907030b1306060e010309020a050d031101051f080303070c03050c07090504061506110c1e0402 79
    0x40c0c3c40030364140108204802c0c1880507105079410600d0b01e24203c010030344500030f60f004d8654000c41c880d60109040101c0302c10030400020007001036485a0311a51702038002c001c01d2146952700d40c00c20b01f042c0c001d0506090018000d00042c3d607907142030fa00b041c0c507101c400f541040b0100100004202100001c41450060700d000d544500c000e4451401c00c41d040301d18000c4040c260034002c0e498a001080000710740c000e4040c1541c02a10751140d02e81c0e4200307080c2c0080c246564030942182200000c0304e60395883d40c0c071400540b82d8544070038401c81c020304011822240c86000c029080442d6440912030f5241007450141424428030b00400900e104000c1e01d825a4030503a2402201107203141a47d070503100b0079179941e01828070b8000640c107520342a00e000b000d40c64800c0c406018050001602c1455500500c441e501419071003d06000c98100742c50a1402050a030007101c000124006021a9440c0702c0c04d81304100400d418004d0807924191000c02422180b502d000d0454100480c54000d100c0e15580003506 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 701102886 1250 701101636 701101657
    0x180a08040305070506040806040605150d030f300905010e0d03060303140705031623031e0406050711030703020a080303160203040513330305102009010e06 68
    0x944891031803600510f460390640240e40308280620041c0401180091010b038805c2d0080b50118658407003003c075652880964244a0708171640f03280c1e00b420b01d6082940303414030034400d988a19802c884c181d280301c41c01c8010703515030300c18180e074001141c3c404070950010000c07940a8070001034442507640d80300d072410804100250102c0d0320f4800800905410503803802000c01c2603a00c0a2800b01c07540d40c0c040d10781c810008901a8440d0446980701800a0285e60180c191200b01c5014100030780b03090110303600d802070f10340d1000c03080d940d0740500140b811b0740341990120b03203454031402d040c041140c0c1d407580d0b0303984000b162540610400a0000159035611100001007045a000c0c6503242492034494141d2810490300d141554020401080300d81c90319400c40345440cbc84030000141203540502125441c1000071096100800c0c0190104005140c040190703003120f100d501143c030240848131042040c2c1e0450312034420140440c0c6641ca000f026048000d1a0640c0140341c00031031240024005509900040b2644 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 701104136 1250 701102886 701102903
    0x40506090f15160b011a1b0a0b0703021b0c0307030b0a09050d05090f010206010e1807090204060201020c071d040809061c0b030f2b1b11040b0906011403180a 69
    0x2d405201c05012050701401b140003120140d0b000c18000d0a505208081c047c1c010b100300d02d10ba516254505020b800080740c0d0043c203030f41043c00c0c41000140a500a20686e04d5680c0070a9032141170b0344000555041500c5010300a0805140f0319203844050040007403012100302d84400011001920510501d420504540c4581e5100d15034003003448030b01c040c03181c0040e0642d4010f10040c0407103c082141980c0c02000300e0120f01480410703150b154200005640071444190020401045094042d0043d09402c1d5141c411242283ea4501c0c3e4581d4018015040081018100000c070340030901c400001c140000f4041c241c00c3c13410610300314882c50aa00c2c1e668010429560741025142c615041c4000350107440814010714140070070102c0c0c4901c404c00090269224600c0051210390300f80038045014007114402d041100d0790714681085030078805003000c2284194640084c0c0c4400c1c0c030b0720084c150300500040c0d50724519600e540e900c0c6030003540003a0480c074241100300c002000c94041000b103246118400c4002 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 701105386 1250 701104136 701104177
    0x1128063e0709142d1914130506130c09051b0705011e061a0903160308090339040e0304030606080c03061b0d0605150705060903040506090f15 62
    0x50450948513290075044462138100350000100f000145035081202d60345a4582811100070103401441250426001c2c099034804200605c46851040700e400c1e03000e007054406658848810916040942c00002c140304001001401120015070206902c161340b250350741101d001e01c0d80c0f03190b0260040300d4121002ea4442c51901900310546032125000c42401009010060070300312940e00c021140170b941c410410021034002c0541e6410003181c00b10701c0c2007a010b51345c1c098070f03410311001903480103404038041c0c46a100844e0f04548030310030150500403d14001070340304109402c4140e41034404101258001d88a171086221148240000c0005610908000071990719094521382441c01c01110030303220350440700410800340c0a074a070480c000346040b601e03142e40300303151030090005098540040c1d4020080480404c3d0511040c00107120300fa0140e02121669038800d08450381e01d00c40c60042c1600501d040c400012503041946c0d0780c09038a070000341414690700c03441c0040c0b826034000710350302c495500c0702c0d200 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 701106636 1250 701105386 701105401
    0x20901150e0303090d0321020a050d180c1412010c0f030608030702090f1b0d020d1404031407240c11060606071128063e070914 56
    0x1003032003022000c2d0041c5041c107003113000080d003014500d50b018050060303491081004001c0d5213000c101089140408540381c03d0303030720001011070300540308181095152864005c00030305039601c4ca080e004d41c050070b00442e15042071009a003070307942d101038290001c01608010413005c000b80120144d140301036480c0015042e0030340008058a01e03c0e440351000d50030402220300981c441034106d60f480550264407142135203c10065102400d140604011810000b045011103540c0a400600001c22442010311004003032010040f22001d040d03c00034045892034290000c41f200c0040030700620b501440c4038240134070070b20b44c04e1040b09800120700c0483d90303558003a0740a81904501c100590b032a04200400540c41c04802003a60747c412550f01034002040c06460741c007290b88070002078803075401e03281e803080030008203460851400109001d0031001c5040004005292042c04100340c402100000c0070f940c418105401580f84140900140035090040c0301e4041034001881c000d081e00080001084595458803c8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 701107886 1250 701106636 701106647
    0x6040e2a1005030103050d051308100207030e0405130210030914160602060f0601200d08040209130f020402030601030e0d090305011109030a1502090a08150603060402030a06090c0302090115 83
    0x84070050000074401400402d02c0019101c006940c1814040e9640100025820b5000350b540c0c0b024650f072103080c103c12140203240d0040c1404603c42e84034281c040700e803081000f058940446618800c440e080b0b440c80051710303081110400407515402c0c0014104510344840c0356150b016449116194001c0c4170450341080c1c0030340720130b004100607c094545400c002845c1c00d0102c801a0180e410030421600e91a240d0030181d203072440c01d5a2600844054034041c810280529500f1141a885064100009500c01051000360f0b00560380c030020361440680103a0801000b500080d0034941016620420003030215400c000380780851500e43c643c41040e501e1450401d09440c0d0070003103400c0114081c4428041341e10000b60380c03843c460f0b00680d0800c2202c81c45a181c0f009010342450141c2c00800301e00c00040890000c2505a00400c0c0055070b0074160307403000d06041d5035042c15030300250540d0010010b1030100b01c4c5684010b0800784503000c0302a51540d02d030001109800c080c3c000c00c1d504403091200c28095900309 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 701109136 1250 701107886 701107909
    0x50f060c0c070308091801080f0f2e09020a03300507030f0314010b12010b2a01090602030408120f07121a042d0e0606040e2a 55
    0x1105441d1074244a01d10054071410684030042400c900814444c0350b590711036141c25800e01c030780e02c0d03115071569666a51960300e60f11800407010340e00800104240c0114041035140b10b0103030344a42d201c603041c038425040d9011440d407101d9a4106548103500001a581c0e5590b200c02103024074000c40590749124450200003944010011602c0c0c01344141e07590040d04102510101a01b508004000106442054015054041c1c5040d1582d03104800030454040c0c090207403802c03000c0c0f4a406500707a0b0b20341c80107030050310440400c841c1c0c0c54801c0d0394a41d850f070a28680514960180400401c080800b42d07102401c0e070704140c5041741c6000012503150750031490b1200346603104510394080a160b00f4400c5d406014080390098003078096072164111413160800c0b050700c2c0c5030900064400c00003810419040d800b25101c841014006c0d072207580668408a15a004201020503e07001070b020a0300c81070100070003405042e149980501804401d4030100840e004c00103d08080c18030711003181d50100c0208001440361 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 701110386 1250 701109136 701109151
    0xb06011e090e070c0c03030f09060201060503030d09083f0402090f130803040c140907050f0a0903021201050603060a15031709131b1d010e040b0409050f06 68
    0x180d035a0302069104000d0400c6400500c12403085072245203080350701d8000440b0251404024640002c20103921080810420a07103680f8460320549820049090740e003e4400c842d810b5000348801e42e1002190352081507003d00c030301e800d14981403503645005480c02c001c900c015000e0105204c0c9440d4a016802ca108140e004841c003642c0c00c2c90182d0014030050300142c01e40e5054100480003400740e40d102104000c03400e8204800f181c5034038291501c8594210140078910440c0c0c0090304110f80d40c01e001140a0294000b070315401d0034400890a2440940c1103a041e0b0010001090070000c00760f25071114690760a41d112001060b41d18044081c18034221000d094041c0f400e00d003034481c07040c0949500ca004152580507000c000b4545815140c1c030203600a0039000c4c0d03448803103858800c10340900341e80550101240030811030f4504640f41000c2d55402c14100c4030003004841e5415200d0107601c1440210001d240c0140700080d00c1c1442c00c0401c1c1140c200700800c540560101c0030144007418108200d035030044d0b0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 701111636 1250 701110386 701110427
    0x9050406060f05030d12290415030f030c050102040504060b070b0c1e0c03071b090e0d050a030e0a050102160b0c03010308041715040f140d050a0f110a0b0601 69
    0x41d00e008241d1740c40d0300035400c1d020080030841c2500522107e8220148034050005032035810302c0000d201c0c8450030242854940700d2803410358035094001056001c24100c2c0d4000c0c44291400046e500c0a65011191940455007550300b00404100c0f56076a10654000c0c0c0071405600e501c0c0d1b8410729184004400c041d2060040708014450340f41000f241020303541139482d41d10502501c404100c0500d40c03460040c22801402c9601500b843c0c1010070202c41000d048030154034060110445800d4182d480b070700302000d2000059820000200c2e207502907040602c502d226035007100d150309007030b450306400c903004121054003200b0040008000c0c4401c9041460b00910303103d1403a031840d4903513501c5040c50710071445988900707106015030440d41c81c0184060144c80340807004e07140940c90320749003105070000d20034000c8580f085075209011a01100182d0101c4110707503074844500e0700903010426244622070112403020040420f84010340c800080c0a0340400c18800c980c02c1011741000c200251803504903902e05014180c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 701112886 1250 701111636 701111639
    0x2003120a031d100b04020d0903050903100204030f080a1704060213080606060a08061804050c10080f07110a061406121c121415010201050702160b2209050406060f 71
    0x740041510f0350101c601810020b81042040b0114010780130b040c1110100320b00c1d0401e0381c424036801c1402008030740700032003c1c3c41825000b621400101c2c0960700001c1c1401c1c003030f6400000058105002030001c000c0c6c60810003144610720b11101d51040003103400b100c2040c1c001c503018144028507a28071000c1c04d594400341c56185455804116107024480c41d886c2003011f00c002164045c1c803912140c004641c0e448001841074a030a04065545088107615903000302c690700c0c40395282c14842c10300c0703c3c081c500004120b40c1985801c0304c02c4031860305070020000070b80580210100010028856640d109215807074004891034500300300100100d41d0864000c058001c0c1d089286000007030212041c407442e0764106006003103c180e15120003020030320320611008940720140526080c0015100d02a038600368001d101641c0c0303018080f0386600b95401c0c01c040300740500e0010312880e00050041c00715844900d0759102103510012040c803481d40d01c4da008102d40c0382d941c81808180031003400703080090b00441c03102c902101d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 701114136 1250 701112886 701112941
    0x30501091404060504061b030c1b0b0a05040302030409021b0607050903071707150206040c140d0809040e2505100518120111090108100b072003120a03 66
    0x500240b00504480e69440050108032156002d1800e608034450341c40300c0c1680c56400a8010100c8042c10030108081d81a803410201c000700d82c04090f65888411078206881d008007070400341c40c02820440a43c00700b4000030031301d8030091028200d01401e0b6559043c030021048205802c11788080c240c80c040040811142440780c0300012184100c454044248420200701c2c4011424841031f0f802042009d84480b11005070b444c0c1c00a0800c4c0a5801018191010fa6491200f00341c1041440c1026400c0024400c11002007803800000e05803000003d0b01c00f04070740c03824a803200d0403c0610b8034002e5166110400c4001d0900d0407640302e50260109075010a950814100040c045004e1204505a9070b200c58071407600c00d4a6820790f443d00c054a42d00284503094402080d46080e8111248050014102000007021090340d02c007110219103401003050f280101985485802c650750742e070658044a40501001039544013001028010352020304440d440d40e400c0c80c001001c0d2440c0000140903040721700001d0580 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 701115386 1250 701114136 701114171
    0x60603010e060607030311040e150409020f040e12040e04121704020f0112110a0f05041503020f190903061b08070e030a2102070b030c040302010503040f0602180103050109 75
    0x200608803800c3e07407209a0b501d82140a00040d601151a0890201d000a000d20a540d0124040d0b50f01805e498020b031440404c2c4001c0300e00b220ba029501141040a90515081c188d0102d13040010071030550f0062000000c1012466002d91322a0b000103244d03c0401c002d01c85400750a40b280b072443e29140b139541e403082c0100c036062140078201034405c0035000b0b01100c681e070280410f500000c0e0724402c1030203110041d00300300380c16401c0480d800300400c0d05c410140d00c169119504075030603540392000200980c805c209048000b900070381c0c0f07010503400d001c01008070310940b0761144440034405692103d40c0c45080d4a4203400365000f036040100c20181c80008031034255084a00c59500c100c16144c45401c00d104400001e1030a141c0d0790003d081c51002d0b00820850941d5401e01c2601e8003401d40884007150340e00c60044034644401c40d1040d000913010700c402d000540c410401990042c0c090154100c0c42e02458440400304c1e40320030140c110782c10219840c1401c80d40c0502a01c0d00414600358100070841d444e403041c054 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 701116636 1250 701115386 701115391
    0xc0301051b03160c02030615010f020c0a140301060f0906060909061805071b05060f0105010206010602030d200d0203150609100513032117070c020d06090213020d05060603010e 77
    0x341110100c8241143c907128006a4408036001030844a0900340669512100016000c100f0300107922103442001d01400000e80d580142d40240c148002c65140a040402c0d860481d0b159a515540701d12001a29942446485026103004640000c04a00e0114050100c603226400622a80d040c05000c02c4140400400c0d50000c84032201c0104143c0d40354542115039103014180d29401c15440c042460501c80000344140c13054081401c106540d03625480160fa86a400744034000050340f00f003000c00a901c003690080100c2d002054260070095038401281c94450b0042d500140c00164040200008800080c29100350400d0070360300c851601e041100425581c5800342e2550060000008a0002144444c10108029600306428800b80900c41030790700c00c545150000100006ea40741041c0e070000d4403e150260051600381c550000d4a005542806004604190141c8906988005110240e1101500318182030910480181c1d118014040034080380e40140a81d0301401040c0010711000011855854 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 701117886 1250 701116636 701116651
    0x10f0605100522090b010908010b0603040f0809180a1a0901050d020a090606110f0f19020612071e08010e0609090f070902070213140a1d010e0c0301051b03 68
    0x2683c50101050310035549000043d4020a69550300c000506503440358441e111074102661480c02250f40c80e04014245c88100701c10f103610020030800304001455504101610500c81e101d85802c041c14a400280d070039601280000c1da000120003007044001303080c4a10200801000740074040e0141d101c002c1414040140a002e000342c1c81d49004000b595110710444006100c4074032706006a688880c002004255251591a003a2081c240042e1034000e020039011036400000d001002c0040800030f004e1031400c1300c48810b0b81c100000f0801c45682e64141e580d111310ac2c203600e4407681c07001c10002c45a40700100c1c0c01c2d4841010800c2c940014845500c0d440405900514200c03407021441e2034400c1524104007625507161910b2184020000f0200c04607005848020b0003165842c80e4901510755102c2642c0c2808520070340116028005001c0c4a5141c1c00781e0300504040c280c00102c8050009200d0864401442a000640c82507010440500d807d008180e441982e02c2c00d000c8021a121031a054640801f80110 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 701119136 1250 701117886 701117897
    0x7020d0921050106080c2103030f0408071202071401090303020606090403030e071206110f0712020717150109021e0d111c0b09011d0a0e0a030809010f060510 69
    0x500805200e07600c000641e541180003040510764400700f140d078030a91642c3c01400b40c0b40d24040301010018002c44c2546500c66007001c0c0d0320f195a90b01d224800014000c001b10b40320b44003407001c9804a006e036101d10400005a4006080484c1400700a03613485000200e01c0d810401200300500000c0d501148464000c02c0c00d0fa00c1da002c0c2d403140d00c1c094003d00b020b4844021a4810040002903a00d02007501a600f0b500410081001e000602c0c1024118820302c0ca07d200c0b0081c7c20014080001c0341002e070307188810300d07902c16506103544070303074a25080c03450300c00c0044440d40c402d198000e075080c881e002080c01006c40e00c0045103005072050b4030001d5141c2e0101c03280c074280d8006c240100b81405940181c03284080411019030b41d062400303d03081181107148040030800c1d151074a98880380c146040e01074140c44c0c2c0814070500daa192080840811040140303000c0846445400f52b1a01d26030130016081c941e8400d45a071380c410325001c505d05007111248107c4201c1181085800c00c200d4454000010002c0050b00d4034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 701120386 1250 701119136 701119169
    0x816050108150301022a01020a0801060807180803040e090304030b040b0c0712080106110c0603010513090515040515010312030f15030309050a0e040b0126030a090e07020d09 76
    0x41c00c4460451206054065000044c0e10115006d0000c4400040400022040ca42031082d81d02608074007901c0c4141011840d00801409000c1c000d140300d5500032098039142e10f107201e90390b100e042041d2030395001c050b10b0341c070202341070249024003100d40f0b41c08513109008504140c603680300d0b24107c41c00a000a0428000760010800603580201200c003505e410014945071f03084034400040200200344a0300c00060041065021019400300b10059145c5000301540d044d64200000c00c261003d5640114000703954030061030001070020b020f68105903443e01c04501b060b180500308181002c0042c0700c101540780701ea2006200184100c01c00031842781451070700080f0072100c40e5482d0010101c08a5020241000c407070300004246c0d210288501f41e42007074070700c0c40780950b4408596003205001d4030002d01c0c403041080184040320700c040f2620f0007501e40321054010041d602480321704644c0216041d00000e00300400c2030005010303002c1030a4010501c0d00c0108214820308400400200d400e005400c4560001c40c82d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 701121636 1250 701120386 701120401
    0x100f020f0607020c1206100504020d02090d0c060e12150606040e0f1009110d02090d0c1206050c0406021510150201020309060c0703090e07021006120506010816050108 73
    0x30100a400008219055810890000b81d03840c03c3e0000740c01c0c8a802d0100440d020070b0b4011070018055401e4042040d2824280710800000c0d4000e0228581016424400008195035003003000840038040d101c00e040e07903410520000c1c80e419182e04418007648480b205200410170004034070020b80b00e05100310009803240e45c0000c110b84250f40c050780c2000010703001c0c070188d9135076603040718040e08030401d44500c00e036a0750a500d007e03103440030341c0d0690000c420f01200c80c40641c10340050000c40030003009800c0142483d910104142c00c0c980041211440304901c4d20108042c40c032526820045480026013401e107085402941c0d0312a003400a42c2c031501820200341d04c00307405c4040d83c0140c040a40c04150010300203100a000f50812285a6204d12441021407220141e0f00100c072080c90300750b03407403014081c10100180c511000107402d560440c400e8aa0781c564149103880b403080a000c0c00c0140f8031680845003002c0b850490180c12000080d000302244600d448003d03030380c0700d049401c20b00b403a500030740e2280d1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 701122886 1250 701121636 701121643
    0x20a0b040c0e04030206090610050109050105031f080f010c1b020f0a09020d020d061a0a1808070303051c050601200712110a08030c10020d150b0a0f030209100f02 71
    0x184100b0040c0a02401e0108240d00481c01d280f1179a4038070200c40d40c5039100e9020140d422013501c102808598061402e100c95403164008560007411f050744d00022401b594001d010001c6207070701254a0741c2003986030051400084c001c454001c281c91405206034001e44148005c0885800c0b0024800e100460340400f00b900c0f0741c0682002060712050842d280c5440000c070310041d40c8041c6000070803030320b0054045214a40e410500c0d080076241d000385410280d2140c4141d9104c220598050300314000100e0002d0b0010782000401e018620a540e29500c910380310400220003a00011402920390030720b42009400e91713111000c0846400f0621070541d000082d00445801c1584ca500181c44000f02210010140300403081c1201484600351041500d2036a140c8816889028601c000076280d0000680c0f148064074a4004d051804120000041e00c0c01c0401c1c115007600000b68010070401e08003141d803101c07007900101c650003032008908081d0306e0510030f8800500020208030a21003030060040310710708254400c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 701124136 1250 701122886 701122889
    0x1030e0d080a0b030102070803010e2a04031415061512010914070804030c030e0a1d040606050102030a0c151e0207021e132a1706010f020a0b040c 64
    0x100261500303040d6190005140d403904032042c1d400503041c030440321241e050500c21500959003104805007582d0030020034140580001d010f40b0707029405945102400c41d08560003070400c0301e0000207240c0e641c1c55883c20281c8561118000e68444d04000b000e25000e404980400e54000d4040784c00c004410708086800e1124010f00c0500d682c2d100414001040c010910390044490b41000800c00c1044d82d00c0305800c581c04001100c0081c0083c2d800c091400009019495190103031900400b41c07280a9221183d00b25072241003a4001c1c1d10507504008d001c24860360748100c401801d07080c03000d5031400c18030748800307003c1c03035118800102032220003541c00c0e41c9482c0950000d0b00d41c0011000082e181c0c5001d0340f166029400040050344241c0340b541320b00c404112800246422180c0160034501d0740fa1a20b45010010007111851520394582c40030201040241203050f20004041a21100c01030840c001c4611000750f0b004160701d0610002000030980c031f40d000200000e070554000311038105941d9601d808020403505 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 701125386 1250 701124136 701124161
    0x10c082109010b03012d020f0d0f0e01111b03040801091b09063221061b070b0919080306010e04060f060309080c03130f080a0c0608060103 61
    0x2038009a601602548a032580a100392038000d000d590300c214101400c0741c00948551b8000c1c43e0b540104011042869189003900c4940840141084c41d002c69122955010029002070981e0b00c00d140090607a1911922001d045400d00030012003e42c800561018400d03842c0d511006140b0401d00d545004042003120040d0051600901040e429407411842a81d140f1015001903d4554004038007031580e40300311000c440b1601724803544204003003845803c88070503510343d0403121074000c007043c1e075605d6110b8075010000390445d42124a000c0595601e09085016202c0c220340e8000c80c25a0007008066801e85103001d27003103a404601d0b41ca5401c2100e241c071108100c500ea01da02e100d103147d0180400e0201441c410310b0700b070b242c14400c140c03c4c40401044400034050170041080114092000d41c2c80381d80100c0b9040d1041056a00e8140c0d031241441c0355822405108403072a622003001c0c410b4502002d07130200201405401000100725686e0b0396802c42c50280199800c00c0284c0d0300251745a0300c641c00915828070b2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 701126636 1250 701125386 701125417
    0x140f010b040618030606062d0c02011d0316050a1202060927011805180a24090b070e01020f070608070905040c0f080705070302060a020f0f0408010204260c010c08 71
    0xd4404000e0f15914015490b001400c0c802e4034004000000d903025238502a20942d80e008040a41c1c0e40103580b2a072840d0341d502c4410540688140303540c0c5041180c000b10742c2e03006218000482c5000c0420070f4410a503008411181c808d101d60300016210700055610b03103801168a9000c21940441e03810461284030007160040100200010300001140011900f50b6071210b014841940d46c42d210b5210700000080080c0560f00400c00d06020640e650102d0600c0d1104010014201045810400c1940c1d420801039030014850418072841d02e800805007007074540c1c280081c010700c3c41e10fa1007550b00e41485104140600416600045000c0e11405181001e400c0080c0100900c122003400106002c42c00252140483c441902242e044c81c0100f09696801e03034154000d04a940d41c0029080280d040b038100c16101000511101c103d040846c0c001d80003501c078000005848510b00047c68a41d041400034200d521900032a11803a41000410a070680303103001e0a000c1070076000c0340350411551156154020300507d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 701127886 1250 701126636 701126639
    0xe01090201050904021803030a1e1106040f050c041e0608300409020f0c01051b1b07090603031121090f030c04020d0606230910090306050a140f010b040618030606 71
    0x4d070404809420101100b07030030200004071400036a40d0b4548449502c40a50cc80c20000300000c401001141103188140143d400500420000c20300351041035085040e44218007050401444407845004018200c2400800c0507801141003520464208605021407500444c0d468145082007403c81d402418072007001c665640c2c040507629810f81103544d5030601542040046124064002c02e03590301c81c09083304141c5008444218645010390000140e441400355600010340f40c00107114002c001c60003500c0c0c8482101000010340e091810b1110142940000407940745030f40c0e03480d40305492010708250703580c034240c20700c01d0002883d101e0040166a80180001060721820b5180d801c0f031403ca546030740b580390103030794078840104541460b004840700c0b41406001c2440a4034001e405043c46203104e04150700c2980c0c8030b45500c000ea4804850760010943c48a1880301701d1441603035155030020036088422031550510101d604203101d03a00c0765404015100c0e45c0743d860070a050940c10000d5030300820822966 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 701129136 1250 701127886 701127907
    0x3060616150f0c0201090302120d06170f0d050c0d030f0216050c01121e09020d080409020405010818060109050c0417071d040c05090a0e01050a06090e0109020105090402180303 77
    0x140b4400502003140d50a198041802c98014028048015419009000640c04801c19007415401035001d03441c0c0759488002c00205c445070350140d0b05240c04002c0207000d031200c0c00c1e01d403140303400404400700d002c2240400c00540d241001041500402102d450085812500390703252401a000707a00725019402040d02220081090000d9504048602030300c3c0c4100c1c0782e00601d400001c80d0581c09200042c1e0180d0030b0528040103e5a100040440c0300500d003044850194983c4070b142d0f0001d070040e540d41c9a00040600ca20340e0000d19007684042c80e0303070f854150031141095041d12100c044c072491b4001c645440104040d20084001c0c3c90140515072070f04841000c000d405203540c2c0780903100d0110300d02c40c7d00c0c8500700c080c820400814442c0d50850029481c051808051249003003008040d406200d940751410856a40203000f800c0c0240100c56002c103441c1e061030150340c126404042203281c1c81c4c0c5001440710050341c00200307850601104840068580303580715101810190700d1142c00360301d4000003400c0d030b540 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 701130386 1250 701129136 701129141
    0xd081f08190c060c08030a0504030302040806040f02090c0306031510231503040b22080703030e0d0932030607080406150b030a0c0215090c0102120901050306061615 72
    0x4881c01145000110b5654000607a030805810701c02804a8000b00700050550480750029038202d403103407800500d030503590700340181441700a035421111400040301c01015860700b41841ca8001e4003484036140b45041c00000695244012064042c0003030039070300040e00000518042c240101045955451201104d5a000d80200401e42e0701a100d0f02d40d03242c040303114029400c1902d21035584417881160a844901c42802600e0404043d0070401241d650b1090004011002609001e442510003152103004000c9441c141030f07e003071040041101d441010001100505503001c121147d0b010000c44041840e2514826410300009140d058401c800074070410607440f10044c0c1c810350103450104080c3c2e00082ca51191082c0c036225140c0b1103607060000c50400c0003d03503c98000403249004640600e10f00c0301c0c101d0203a02d8100c4229540d9000012201110750f01170112140c01000418018580081100023a15900001d812030f8003814003c11140710441e00170b21700e4082c181d004118402e034540071a110002 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 701131636 1250 701130386 701130433
    0xa0311070b071a0114330d02071a01081905010b040f2a02371112070303050d050604090c090b031203131e05070902071e020108040b09030417030309010606020d081f08 73
    0x50003292b4031010a08404060003a42c1130341c09040161a01598421035894034a07251102030340c10355030307030b1a0f5546907035154030410401500030400428044a40c0700000103800d84126a051105034040c5041d00d5142d001c00d240300781100d521100580040201d00ea9003e003581046a500c40e044800071031000e0000c9204030562404080f01c020895941d01c02d2019180d008510000b000b060b421b102c1c0708600f440d103810007940540060000544220561a0b20000c0300440d80840c5041740d8921220925040611080c21140003400c082d501d94200070364142040701c00382502070840c551071540e5018030b000e03082404d00182e4000d02102c006079103940d0884020f60003060101c83d0002ca20042294600741c698203004d83d40e805858160040e5590740719042a42c0d07006110000c18042000007040c4c6484200b0010700490b0301c40029610303032500c040000d084409540280301954840d0040e8150140d0010a40d54450b88404110702d0038410844200d1f0301000c40c0e000304005014181e811a01d00411404128 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 701132886 1250 701131636 701131643
    0x40506030c09030d02121e07050a060c08070311041815080f061305060708061c030c06050906240102010b0a080a120e01020a0311070b071a0114330d0207 67
    0x20b01d1000c5220b1309913a42c1c41c5075400100081001d22205907000100c07050407856206400465207001c50075500c13142010902501103606980d00d948412100d940400b00036070100050404002054503128820302600407441115040342c5048104a0a01c007039030021000710240002c0304090f07a880c1c496141e1a00b84603481d01c12244913070400150319051100e0694141e5801002501050729007583c21641c40b90001c010310341005041044150f054046821a0a40d034026602c0b551840300c2850300b48190f5030050989403460344100207100818985036403500c5920441c41088031041c5003440180e000d070201c510304c50b0b0700c91400500065039180200b14502e0b010b11501d4901c101c0c5860440988086241c01a81401617012080f4000000d0152102d800c1c0000701100f00c488040e40c0701455a07141c0e20003401102c4d100e208040038011054025050b90241842030300602c0c080c0c903480c021407101c9100e441400710140020205146171901014801c2e0301e80e0301c582c00e84d581c4013440310941001c0e500040048 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 701134136 1250 701132886 701132893
    0x4090204150b1213081206030703080f09010e0d0c05010c0c0305030304200108010f06110307080c0c0102070b0901050a05180411032d0406020f0c010203190c0302030f0c030c040506030c0903 83
    0x7048004c04d41c0da0009181d5009064a061101d400948a10034a000300480d402d482410f2010001c220030a01070424400210081c0d562840d00340001441c109003101c02c0d038010070300002c0c1200001c1c42020018180d4500307180240309400181400a400d41b1540e10241c4240000002d00051045180102199030b80120042e00200406d10044031019424450000090105602400064458100040c04e000101c080342c2c208066500c40500e10340c000c200d00348641d4841301003d600d0356018481c5170010080701e40821700380038845001a00300d11580e0705e01b000300000040d010300f5840341003110895068002e0000c005641200d190302045510580f0320341194003080f0b11102003070825202a089098a56640b154282c90b40d070b23901c0029402224840042000602601400503000d101643c480d11920a00243c0d10004a00105c1100c20241a01e0101401041040040500031781440d40100c08400400d640b07942d81d2130000d00c140503540106a100000000307102000c007a210190042d02011001d6 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 701135386 1250 701134136 701134141
    0x2e27060c09060804050a030e0609030118122d0908010509010603021e0d1104140f011a04051e0406050406060503160305010e0c09010e09071d010306050f04090204150b12 74
    0x143c4010308100c5004003e03620406030403000911602d12060341c40c0004c0c2c1103500348800c0f800024291000750300c0403030080b50304550440c20b00101d00c10f071000100302400e00301a42c0707910007500c211070400d01c107071801010b81e0302c0c192201e000d12400303840c070050550900070441400c225001034003a00592106034890440003d400071080900d2204810b9184010182c880f4403840c0d5171804583e44c00c0d5108903034496a2005d00041d01046001190300c25044030304030750003e6050042529414806006455007214240828002070b01d6540b1004c10141107802210203008000000a010b480d60f6048503401034100000001c0440e00100618051f9a0a00400c0420b00410b901103046501c05d100c0e01a413200c84401081c0001195002002c0c00081807401013614400007001c01c944801c10398600c2c001401c54074041c03c0f224124150703042020001d20b001d02c000352802d0005680b0400350995a0701c40c55450428008654503903206040d2061a801400d11082d51080d8403695500710708210000204007000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 701136636 1250 701135386 701135399
    0x702010614010912060b090408071b030b190608072603120613110313030807210c020f0d09030302060907030209010b090f130c022e27060c09 62
    0xc11000410f9640145103031514500d000400901807065400c5a607403030381c690b1103890300501544540d0251401d03d0341d034109490050004005008003d410701e410501c14400a0404048541c103e01e401d03c100b9000b081e5003240c08020103095002c07040038428a580000e24004002c0e549110728a90040118541d20041d00fa0307480f4414000806030b80c0480c00005610342c0b0b813217202c2079651403006800041c06180d40a210203541e10566040d002c8a140b8040d000825600c0380e5075907400001803502c654440ac1845003241514844c0704101d03840c5d0344a103841707500107100b0000b0001d00c442c0001215075042413078901800303c0d000e0b070000382d005000740d500052221000095070411070341d0150181503103a2034140c040712150807241e14981d00c0180c151440c60341e40d07150f22205002d90581d100018640711403800207846c2010710354040e6901c6000e1959004404420b9621010052400c2c202180d0b21603038501e001e500d41c048910b04610788041414040a01c2070740d41c42094402402d403510010301c0d8440b103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 701137886 1250 701136636 701136659
    0x30c01050c060606031003080d0501030b1f0e07180b090109080715051c021c0605010e010e06221e0605070809010c06060506070602071509020a1a090d060507020106 72
    0x100380a0307036403003030011a440f8103210740119031003015001c10441403a1039035610001c07540103010745000140c40304018800d1280c41c103013243e0000809036145c07200490004115040075010f04c20440260b03052000a04103601445070315401903120041c05100030349134140080f10341c0220b560103002601404000c41d1800e80001c221042c3c2e06a00b1a000a054001c0c02c11035117079020314080202203044040410301d1411a00290842d40240905075160310305501c0400c080350095840541000a104150030700c0740d820806540b41110266040340d44c4003c13104250800350b000c0303298682055a00305001a6551000c415504004c1d0300c081200c049a9440e101142d05000d81080270304265420040100c096000e00d10203805c0318404d80000c20515901c40014089030400041502c00c15000200d4600b0028000c0001140005e141c1c01008a0300042d0049102c4000318040d07540c146a0b480103600c80c0c6030140c4203440b003880008055000ea43c005240c60400380c4000d5540501560804001040300076160 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 701139136 1250 701137886 701137897
    0x506010801121101170108060a0b030c130510050907050c0609070303120f0e03040b130f0f03020907120912020c0f1f26041203060b09040209010210090b0105030c0105 73
    0x10040c10b20440b00580b41c40700c06282c000e50080c10300c42c00c011545441641180400e00034101c083c040c19462410564102c25542c1302d6035114481e8000801400c0d20f51349504000f400141c0002000805036924052440300d420300c0c0c1c0029610015030010040640d03801002045900c0152081d5840e944450000d980e8424490000038040b400380ea43c0441d6403100d0758060041c0b0f40c1e000d07401040d4a00a8101141940c0c080d41000011500006203040000003490b0708000504103c01c120f42120310f0700c1c603d221060501d00000b881040103401103055507105601a8141d81180e980030401c142e01440c2c14860355200c035403201d001d8090075558074040d24145417000100b0b080a0030f84103034001c6041900d1219411240d88500b0f020a494240050b1380f011204200f130a00303200d42e005100e0420382000400f00742c03e00410b408050a02109006079104102031b50b181503000d07540544c4035110313000142c2c01d03c560b80b407001c00c50a180540034401d0002440f811412140c4c11780613201081c054100440c3c907482607 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 701140386 1250 701139136 701139149
    0x13050303070f15090302030f0d0f06060513140307050d0f06150f0b090112200d02030a1514040906060915090b010c080712050405091e0a0204270b06040b0d0506010801 73
    0x74060823120003a01c10042016000844d00054200d641c4070b100c40468044d60400c40000d0b0b800315034804000c0320603003031130007502e4000c01d00e91524031007400103584c820b0345008050103645440340c0c04080200c540e182081056100806201c8000303e9060100c42c5c40c0c9912540e500380400210010b03000703c43c801202c41c0351006a50394820044103098040240c036019182c64003c440780c40100014100300000341c0f8060701406805030740e07401c1c80304034102903070014508207441e1441803000304003940004608a08581003514045102c080a0400c0001000b0703e501030500581080b00b898480388486d21a030081d01c841c0001008440c0341302004481e515581c0c14004d06c21541080142e001c5820f030303824160051154603100c1d2a040e1070748049508804292010f0300c1c0000c62011003000c030f00c0c1e4a20b0342a030106010904508013407600c1013400224501000d40d071861080d0b4000002c840c03441e41c008600312100503040703d584541c1ca001e03000d403c1d0301c4601d54000ca40e203400c2c041003141d8882d0302130034125003e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 701141636 1250 701140386 701140393
    0x41e05010f0503130c0906060804020405060f0307032904120906031a040b0d1704030b0108150408130512030c010b0409020a1a28020d0206010b040b13050303070f15090302 75
    0x107840c810840c13806840d070701c00e503600e04080100150032030710b50160002030032242c1d442c034181c1d08207481071000307492024007850300c1071000c51112400c0d52000104030040b2900b154644148480a140c401420680880c0c8200c40032104410002440030927614120781c118990f0b941e004240d0341b800120200c50300114202c03c90000351036104040d10703241e0001d1455920080129044410590781c020310500e0044c070201c005400890104280500192060b00500810b4050080110741303001c01c3d0741004004100038100d50010940494041d0142ca41d040500b1001d040001d4000d4100381c80390740c0e03811442003001103608007034400802c0d0600c0c0c01030580065014083c1c481c0c641c2007210100e0350b100020181014070400b4000d4000304062203008480c848481c0d111201401c2d468a002030030586610309507403c0d0b40c4954010030100d002e038400c80c0c0841d81c0d000010b9840750340c4401a281000c02551000350f1620010410006000140c00302c5140c82d44286030011000080c1804901070f1421928040c0c003682 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 701142886 1250 701141636 701141641
    0x30f0f03020f06010f0620030403032601080327131e0b031203221109010b07020a1401090e090309121b090a020f070506010915030b18030708041e05010f0503 69
    0x1070050860303079409040700000347c81c0e901c0e60010192458005074001e4000586030807240a000c0c08640e17104040c8414204040081d6042902c02d59680c07054482c07001110310302d0502002070501051800110000003050030b400f00c1520301d0710402900c0e07801c2c1c81351620440c01031089001010707885108201d0001401808031281c0d500300c00358151700003e024440340c6c42000c148a01c00b0f11001c2409200c00e1190b0300140400c2ca000c818000c8000e0140c01045051070700700400800350340c401705800300b02d4076a000c00c81e0303401c1c44460040361114500c0e848072840c0e80d28001400350010012003c2c0c004624240e400d0881d80041000d1a60b070b1b0113143c1e51103070b43c509100081c09082e0818542d82d5072b10014074080036207881000311080400c0d43c000304082d16a604811300500004160b40540c420014420343c81c2407103035086850310b05200d580a0600a494440500d41544d10320052050350030070758100144070f132aa1f0342c5030051020690080c08111b0881685440841c0f0396000d0408400c80300c0300340c1d81c0c0d542580d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 701144136 1250 701142886 701142899
    0x10207050d080115020c0d050f071e0b0304031209031e02011d03040e0109050c1306020303060a0e1603021602060301151b080f092b0c050609010c031206030f0f03020f06010f 76
    0x7e03250b9a080e0b034907001d0602c510354a041c0803c0500018940c84090080c82c04c003d00310440341d04001d801c0400084401c00030701010070b80c0701d07000a07a00030030410b0008908000d454151608401e080b21020170414240761581c400d034040d0710541410500540b29200c4a50074039441da00d81c8078500480400d182c103080140171120141c0d0200e58442070703d0400394030f445051407501030207400030f030710030801644000100142c904140340f8000c0141154954140301d42010b80d5001d20302c40040c480e00d0109075010030380008040908800000c000d402400c101e940c2d5840c0c244d50b03c8510560803610700411540e000c803408203072083c62040c251a8220341c0c0142400700d00000841283c2c819460a0b601800c150071004511038090352003c81c1000c02c41c4d0100b10040c00346022051a0010781c801481510140134001880e43c210240c110390b50780c90728007a000402e190032900300510040e000034182402a50301201003001c10001c5490b4140207400b213411802542c40210369480007401340a4103e1003400040184 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 701145386 1250 701144136 701144149
    0x61107080d081906080307080a17150d030e09010803030412021f1107061505120102041d0709090905150901091106030703240f060525080705010207050d080115020c 72
    0x1202d08101d404100641d0f6817640a1070b5810040c0141e80045c0000f44000c012134202c1c1c0c982140021111b0041c0080c50700c00b04018441c2000c2c0c40b0340d801060140404e00c201441140349203880c440007410001c4079615803216607070b80d800407100ac0381d0150069030f084080c2ea000049449048022662011406120085c0040946a1555204200b62040c0280c20000c0c455000e2a0900580303200f22064140c0b4220410074161750701c400d08001c692041206001c4400303680703004d88100b24110011850303a2180c0f0401c4030b40181ca81d2102039101d1a1a4900040120204621080c03104808035a00d0b070b81c0310724501a080315000d40006090040c0c5181d4191242040c1001e154480c52500300012200004c007410b05003420001000c4040c2121444140014021100c48502501803844c10380d0802030850428080011040c51240035481003207440420480d401040b508500d44c03242c002e6490320b141d4070303109948400e42d1021502160700c5a002140c0009603504071524044264014141034070740d141403104 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 701146636 1250 701145386 701145421
    0xf06020a0b0115030b06070302010b0406170604110d1b0810051e070201110c0a05060109111602060d1103060901050301020307090311120601030b040501051f03060e16061107080d08 79
    0x6054032080380c1c4c800c0d955146d0152005901903000403d0803207000d400c000458030540c204201441880c4442070b0140800184541d100303900019200b80300c01007400146142c44030322401041c1c610518102d000140200304c6040846400500312061000940b4404064801c11150005076182e44030005048a00903080c183c0c1105c0171340000511007a1300e9140341d60652003243c06d41050350207141236000308402007125034014504050100300c031180e07840445000b8031030f408900703880c1220640d0030425941c0d80f8040394080f0240400810114202020049039038004a940b18840d4011a000003164201802145c4c480c1085548100c0a5420b695880903013220320904940c008100c50045000c03050100000c074041c0d40107400c4100f1030300d0305240007400c0d01c5004019008080c80c49240c0e0602c81e510200e10700a0b285c0c000808078a40102c8403c4528002c040c54840040c0b82e41c100c00054410341240b03841d00d071100c44505841d0181d031207070381080d582e1104100e04800200110009a075a0010352110039 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 701147886 1250 701146636 701146679
    0x11b091a0f22030b0c130803091f0e0402030708060306100501050f0f070209040303050415140c0c0f06010b09030c010801080307020909030c071508130c0b0a03060503160f06020a0b01 80
    0x180c40c0c2d034907501c84c0c40d15507000700c0d602d001c511000111507602c8a140f504035801041000d00440c03400001c3c6002c1155204094405001c0c0c9200d80940000d049c003440d00c0c6400288094801c648902e0700c14401072003060250f9160307019004034408550f002c815901414141c5070182c50701c40c07030125082d420045a03031060000c84c80c000341c18080b2000698802c00f589000c0c90081da004151401c2038100400a00c002c02ea000300c1d85450983d2000c0500850074210b035010101d100001e0700c55a01e100100e00300960341480c42114000d04001043d40c0355881c0c0034000482003074081b20342c001454001500c03013801c00c9c09085055407040c480c0b200103250180c5007540c00407600040e070741000700c803904041c03074000b0b40d404c241f0440080081d401581540051074079072180000c030000106045640b074031811506903018829041d80e000483c26490b43c0a600500c000304409401c4400486c0030a407043c0a00d881802041a030b64034801d000601c6520004860030826041401000103910300349103445111a80d100a4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 701149136 1250 701147886 701147947
    0x30f0509060d02030901061e030f02040906090605011401090612050705090907080613060308120603010204121110021507050c100906020c060601090b070212011b091a0f 74
    0x5034154540304054480308030440e90244c1c403030500c000c90b43e0940f00b80d600018080c90214010b000305400a20b12a01240e0f08242d1000e4840440d001107800f40c01000c0c00504482c1c01c06180354100451680400e048076469114081d08040b07403401116040b105206080002c1c2c1d034050000d0807180f0342d07071010750000c0280c1815440d10200c100802c41c1c10301d0458810000c20a2442002414240300001e1f451405920100f00103850465544d0547c5000c0c0d250080300b90a40d0000203580da841c254120740103481000d42440c461030181c03a20701401c211105503203000300044002c4490302030001400c03070941c4500d4501c150782a0740d0314000322029040b071394480321a44207802c1891542803280c1b14a0380014010000035030350703481250744541350640150030349040003a482d208100d10030684094034020303681150f0346110100d00000040c050040001200c003150281c4032008000b64100541c2c1c02250031581c03000500c02180c520b0400742e4005c0c406000c8110b1400c00040583c0e25022400c05540a44482403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 701150386 1250 701149136 701149147
    0x108060a05010e030a060e06160c02090109050601090e13021518100c0615080d08090714490f030c03120f0b040e03030606090f03100e1516020a030f05 66
    0x407401520341d03407c2d548203647c02c0768090204104140e105903521004e68208080c0c54107040d404030380600414414001110703030311400300351240e01c140c08010040c00603250500413403c208190180c10602c440b000c1b4030070808000051080d2420600399031180220360710b0342001d40912030911811542036003540c03040202d0340c42d410000848500c16240891840e03c0c0001c05c1c58180602c662400d00c4860b240d1080c01860020000b50b03100004448007624000f032030301d68001541fa0041040300c01c115058480c10201e003030116041c404046038804880d80d030081c0194003c00130090364070040302459406880144070250002c01300740150b0445902c0c1c2d1103854120746500f0004065412114a40b140c1c00c5059104c500139406803815005002014191070080d6181d81070400000d8114070809001a000b1075000400740e403140c0d0240540842c2d080c136801c0034442d00c103045001036114980720b100c81e00780007280c40105100a099142d0004c4503111a0018030700740c0c13210340701924090300c608070990800104000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 701151636 1250 701150386 701150393
    0x905070506300f0a1407112b0305180d0516051920010507060f090b0406060510090308090d110604030c030b0903030403020a030f02070506030408180108060a05010e030a 74
    0x2120010242d2510703150045080419001c1490304000d043c803560181050342024107060418600d540010301820035001c4100421402070401d01070f0807440100d01e00c0c03000e5110503808014640302004105590400455490640003200341d03445880443c0140c0c0800d01c42c0e140503006000400d4003034072054096940d801107a54080c1780042c1c0c0350084412004409640c1c1c10001080e50341d00c50240309038040d14130900a000020402c2c041c2c0d0501414560715120180c1014101344e01c02e0070750030340101400010f803400d420400054a00d038443c05014021410100740030520640101040d680d02c500414a4810011700b0041c881e12103000c250b508062121304400c2c3e5545410050000310f2081124140c0c03181b8609201982c440d004003640780d2500304004020000b41c1c00300d80c0d0400180d060500036100a060740007203181c007102d500901e07080200007050006204041c405000c0c0e2003100c12001c1e442c0d1030340400440e81c450040d40c102d500841202c600b0320240d8001c08100b49060307070250403a107900f01c494a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 701152886 1250 701151636 701151697
    0x902030109020d05070914010c080c070b03041502040b03010603020d0609180c09090c060c0c08060106110d0e060d0908070210030c0801060203070510180c0b1c0905070506 75
    0x81c0080151940098000d882040c64081c250f0b11000c00d041a150340c925000042040e4203e580005042080268030402041000030a480c24402d180b01280c400c2500c65941200a61041d60241c811a81643c2e0b05102e0a055008480550303402240c41b80c03c5900c0c1031001d801035004940e58650140d210b420208251440d8400c14144d560112201140001c2509102e9540350080c0c000518040c1000384480101c0c2c1d0241400d02110290318180400301400d00b00718484003400e402c4014980100800050310641c0203100035009c0302d4007070607541078008691090b40c2600090b140705130031a20602403800c0d0004950301c030503003550054a503180750208a0b0300148207042c2e0030109001281d603500c604845154040c00280c050005400150310702410780e2945a40c4248180301d0302c1d220764858842c20008a500319403c13100c1c07540005860f100540300c0c58a10442d4000c00c8245550044071b60307107202244480d028a510454001c00504051400c14003408541c0d40704000c48141640c030308004194616225 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 701154136 1250 701152886 701152889
    0x11072405152b15060b1215030703061e05011d060f01030b090406020d11040b181c12231c02041e030201030c080c0909060a0b0f0c0f0f07031101050409020301 69
    0xf240c001c1c140c500b502030741400f140c0d2107402104e02c0960610041e94500000040c95411000c8120700019640c040c00c0041c0ca080b00c10b800042000e805c0120458030355481d940e89004411559105101c07981e2968584401c100344a01034400700da0054012a80c5400c0c207050180700240c040c580402d480c7e9240002c0b4508480a460845410358000360000503420b0500c148a400740c00b0301e00041c90140f5090540308580a032a4a010114841d0050104180e540d0320039000511075085080d4095040c2d41000303011140003410480110300c44601c800c08500c2200c5001e4490500d1410003420141010071070044002c504a44c2d42d52594200404a60030701d8040e00c403034034050510151980641944001000d50340104450010b11040000780548040401c6c01d5646140050341d20401e6541c0781d07000030b810301d26154454280d001d40042c1c80c031401c100d030348018400141108126010183c1c010340c940d40d1640706807507041a5412a600520016031134552f03d2090040516002e410301d030700da40c2c0d00f1089a000303 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 701155386 1250 701154136 701154143
    0x11b030c32030319090f03052505010b09060411121504060807230f0f0d060c0f0221040e070e180603160503061911072405152b 56
    0x3200f04242c094100c2a60041102001300500007600180c1c0c8070a004a26880000e0501c08040781d03070559a804101000410801c0d02ca8a842d070290b1410218002d260a0325800c0c021488200051072608090040482440c0401c680130311704818020001c0080c039020b000c000429020b41c100c03140b143d8a40c00b580018003903400143c10154a8001c60181e200183e20b2400c401c00c1c8100c10703000095450000c2c2404401c003e0381c1d281d2000ca5240002691a004841d00401031840e05011031030f03443e4000f085818180640e0201c2d1341c040c03400c1c441000c00801000c028500300000b00400c0c48000f840c00c0340c00303800148600740100520030313440010b60090280d030303999103035000d02d2800c101152404200008000905000f0307001c1140c01c00c0c0c04aa200e00004000400710303941d070300d9100490500340d803000e05070113144080d07143ca4070301a14050120000c078031030005c02c00b03034409040300182400f446040d000d0400048442501d00d90300f0280011000d000ca0341c400c400000ba900000882c1c6200c0b004140c0070720 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 701156636 1250 701155386 701155393
    0x12020609031b0108010603060521030910050301170c152209020a1d10080c0706090c090b030d020c091e0a0c020d2102030c0910050405011b030c32 64
    0x804001812202c0582c40360040500701a4100420340f1644150110940003040900c181c07082a0312b40c91441c4642d84040344c10109090b410725045600001541c140c40c0c4284031138000000c071032603446c1d55034000c034420350b8002183c10034601130000f07420081c512017901c0003286010700d6034607000080604181e480140c1c07690300012480400350740125415110303c40ca41d58004028042e03c003080354141e200203203200b4050a24085042c42204e4420b503a12507501110500c840c202c02d1800d1207000300548a0000c1c104e003070900128040c607000ca2001107110b0340c0c1d4002c19070444404100040e00c070015240e103042444c1303449540c10320b00d003441000f4440c0d485808041600c410300c2d60000e1815001100301020009080034010100c03907800d0300d00041515400c00582c681d00c5296003082240306480340389034016001c00d840741c80309400c480503000320340b4249c80c0d007045032200c0014441c840300c01800050008030b00e1804140000c0410f604020031750b1186030070341010340c240807200d0810b00d40c002e90095261b1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 701157886 1250 701156636 701156683
    0x61203040503120d09020d0506090c09130b0c090d060f05060402070b2404020d0e07051c14010e03070f11190603090311060a1d030a080f0702032101091b02071202060903 74
    0x5010440041048030339503100d4101d2402903982800303464052001400390314044081400240400e09462510340d000b041c120703000c119803510074014840c0054400aa60030540010f0443c070b054030a80d00d016070000100c1c41c0035940c0c101c440d070200208a1000c40d00c203402422040300380c4c80307601c01b41c00c0c50100c50380b00060014506400c0c6251600c1c550016220396902240c0d03020700f007410720f00000960361110340c0d80080319035180043e015204451480c1c066120105940b000e22071000038400300300e8050145108a941d401c011700c4510b0502c02d58051000601042c104112440b9902038108203000c1d10705081c4007030500f03100c0303814000141ca5158050740c076440f00d01d810854000c2104050800080154038007210500082c25180c4001d0a81a0390380c01180068a01802402180e035901d030440d4404c4140702140d914171400000038011410f1061904600000344a1a2203c040c02c1400640007041e03c14030301044408070400c1c0c03801c00c0360411400d2041040c10b4030f08000c4c8d00700c10319004c1020031100d0f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 701159136 1250 701157886 701157901
    0x30203061510050a1b03021c0f0207030311031c0f06170c010c02031203040605160e011e090513020306010807180302270f061203040503120d09020d0506 67
    0x2412041190248248803522a40c441d6901c2e0480a16400c1103a00c078204140c050f13a0381400142021a0b001c0c00030302090816034081280c51402c07414890b242d880d4002514211072500f80621808050f80c4041310030300201c0e015069100440c038000b01240d00d015441210400c15428002000e59101d4641150002210300c5000f0a0090941c1040002c0e0301740c44c2e5042d5a9955030642d4005050207820340c0120b056440503c80d10100d03150310b18540b5078905161600c10000c2c5011130301000b0302c1c84400c1c10b00c081e480c850304480b0101403050359010030301c116251020380166a12000c0310240414141c000803207454182014043c1c0811802c01030326440c1a02c001741840741d006000c070081144852143c080e000903980000160b0b41c0655a000400100700c0c00c8ca802c110503544d0b40400c1c100310360104403281799140045072044900f510044002e14080c0e003c5a546e00590050755415000700381e404450080b05406440d6004092130082151140d68000c0f07103061645c02010380d2950014010803815 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 701160386 1250 701159136 701159143
    0x11180307050d02090f090f030a0903020405070801060512090f011a04050124050307021f0903090504060b1b0a02040c0518240a021e1005100f03020d0602041806030203 73
    0x744800da40c2d00d00d0b982c80503030002d90415802807200340700141c14804261034450070401c00720724508080c1201ea992100c00710140813483c0c5444200c2c406c5083c140080d00d0f46105560460407609541c07666801c101624140101490340140343c519188107074075101e02e44000902400e11917240c511441507400c9240820f01081d01c230140c009400d07103c120041250702c0303016001c1c1681d40c141c252030800d07160385072034038124201896059680c2c0b9000901d08c6692000c0130b141e10483c0c40510a40710b1581c0702c1d40c0d0b0010310059641714402c07850034080600903100c0085494851079406044041034400059a5900060458044190003c00100b020880201c0030313090300b140303964600c01240d803001e2003403821041400401c0c207809003003142e100101c2c02d510203600030040b91100c0c5565803044079009903e840001e03606c400a1031100e0f6820b080001080210081951080c2600c1e00e10b0040d0f05c405041d5021b2041c2c000c445442120015403c010021381b103804a502402120220900420032a20f03500401d40f4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 701161636 1250 701160386 701160389
    0x1707120f060302150f070b0f010617060306130201091e2d060509060d110a0210140402010e0303120a020703121436011d070e0103030c0611180307 64
    0x40c914505041400942d4440c81081d0b52034015407080c0da0790307080311201040107000b080704c0100981c0a0034248840a110300032118142e440f15038a010000d018081d405d6200602501d049425411040116442c0d641070000001301500605111652694940441e800c800504859440c01c485841c07052155000000c1d000340c002c201004000d02c1414a440410320700360551050358140b10002400c04055101e00c400d4600c0d200081e0804c00140402c00d00ba01440e41c0441e1904006014060030b030400e460251056101c94205088404c00d155074641c010b5030b01074040214554148400d1000e24072110508103494861259000c0240e1a501c143c03034060007196108a03e40d0b0201d05146209164001d0b46003069880445040d40c01040d100701c0210080303480441003c4514840c0c15840b1840c2030005402040c6e01520031004599504040188952580110f01428121004c42d00c01000030034070038141a00c215011700000903400f0041c0c80303a030301c1c654441000008a880a466500c0f01840c05011020 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 701162886 1250 701161636 701161661
    0x5041202071503020d1b09091808041a0714011505011d0d1403310b07060507050d050702060a05090708030f0d0902060417120909060402030403170712 66
    0x440035050001c2050032000c0c0b2801601059030100d03000b164010182c100170114100c20a014107103071030442d8005d00b10612409005205402c080c0000460701c507024230f145405810118803405c150030944000703e406c00200d0100c094480502040000c184003500e8200c560002e4030002071855094011050509215172007d4140280d589691074401083e5001514208040b2600d1000f041e070303031800a1140500c108403220901c00440c0002e621900d0041036100c10344c2c240382403500e03104000655101c0b6191401540e4100100b840140000f500d213400858006145042041c208050301581900b01d410071180507005034801e40502c407007250a0700c00c29401000f034030040c280b9241070240b410303941e1290040c8014040e00016940120100a5200880302d90b8001d100b03a561315610340c40c014064491a004c4403490041408481d21040c0b002c08440140d800a0038a0780c0e1a9a1207007000000d400080c810303002d001c8801c039010701d01454051542d114100a88802450090b14403201017203c01420103079 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 701164136 1250 701162886 701162893
    0x30703030e011503060506150408070e0a02160305130b070803150108061f03060e01060201020403120f080606091305070201021b0a1e05030d090606172d0c0306090105041202 76
    0xd50003d0810042001c0e260800c0010403580c84400c0480e4650b0108020000910070114000c10030010105e0080c0442e80d107014504500d0b00c40c4c5003403e0407840303140c80043c08403a654014000013400754029000c2c0003841040f2100543c1d0700c1a1100b120ba000480441c0e01c16800410847e201140700408440c2c208280b038034910760b140c80c0e80415148508665070618080d142410055641d01c2a0040e10240c104241c01c2690307035950703440c0039020350080c0c0412501c8954101c0c0c0340f0345461080440f91380342482586d800340b00c3c4c0c60f008240081640300c443c049030040d8024048504460060080e18000d101950005039141c0750018805400244c9840c14203003900300402c0c1201048280c00d0341c41604e141c03a16283c0c1c100b0054501549036104540d800f008072824070781400c0500440350f10081c00c884d0b4101505003000e200790309031a200c0719080101e603442c2c1100c50705101011f40a113000c0703155045010032034980c1090030300024a060b1041310304100036034492040200300600a0f165a2a151060000303 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 701165386 1250 701164136 701164151
    0x603050a230604150b0409060b0f0607030203120a02090907091814041b031e0204061505030a09060608070905180109081207031416080123011103090a08030703030e01 73
    0x40c0d9445100c050405010f10074940308445483c1142c0e80b096170ba920000b03000300304420184c0f9010001d80385842c0c420b0b110f16040c05804400d404c2c0041103444540e855809076184c210400c080c040c40300d40c0644284100341e4280000c031156120104030500484030b5441d002d0089140c110303c10008001100a22401418520318207601d5061042c01038000381d01c101d004005481c28683d6142d9030107aa403015090985c4014803040c00d00c00c940000c0d200310300a40b0240862602e44103e0350b00380c500e400c5110009501040021007851540c0d000c420810305c90000403030b810381c2d0b40c90010700c1c0c449290440c288095441e002d104a074003055800a0b50b696600c0c00034030000020b510303007021340c0c0030b1405000118404040003401030340c441d80c00b190b000500600c0c1200d80d070030602c01e40f42c05240c4a801c00d9001c28041c100100d600d1441c0451107410340000400003c414000a004586412080444d00c0c3c6902c02031000c200561b0b62107039000080c00340c6500941d21180381e41401800d8980600c0c40b200135034904104d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 701166636 1250 701165386 701165453
    0x8160503092137080904050c0a0f1713050a0803090c03011802010f052511030606030a08220503071d1302010909020703051908010f1d22060603050a 65
    0x114140001500070483c001e1441c1070004042c4280b008042d40309103004200314102c0c11200c054050032400e50b44a14a241108205170340003180e40d0102002d04004c1c1000401403075207443d000464a00c1a4103984410065a9619210750015545071510340c0041c24400c0080c2004d1040820400490840c8480d0460540001e04181c1c980000d4008020001420a4140d040781c010305080384c0541a01d4022007182c1e0810009441880800030b10a00030400031805601c1d000484e510f08640250455240c01c840000014050807000c2c00e007035044211150005540c0d900703011100080030481002c0e1f4409641800341c11084500800e01200f080f00f4204540160340c0c015a0a0103844d46e003000165901e000b81010b80321805237880e00481c42d6481504001140ea10a520504960401105405082d1203451640b0714140d9040144050313481d400006000c01180700401075540e8000140010000f650307103542040e40c245800544955202c003950004006034206004101207034010b41900e907140d20364 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 701167886 1250 701166636 701166703
    0x15030f070809030708040b0403030314060918070305061501030e1504080d090219050306010902040602031602040e0a0c3003111f06031e081605030921 66
    0x20486810061100c0002d001e00004104a0b640140c1180d6501d8490340c0d14000a1100c5d405130004500203401c215001d6454aa0800d490b406228001d00b9412250344420304da040c5844101c4030b0f40000d02c0380b003078000045102482000d000c3c1540c00d40e80c407a01c1c1301c48400941a221920700041c03c95010200189015403564640d50704a81e00030481e42d502c2d040f03080000041d00d50f003503010b50700802003c41c2215040005141000f210b80940564116030707a200081d200300d0165100d10000750b00100300d40952035802820790020139100400c00030319003040d9840d451a001518504558801c0d40f600d090204090032140d080103204000c200340801205540b000f0401c806801c401824810130003801c0640070010300c8400c04898003010301746120140030700c101000d405544004d5a407451001c48a4801200416076070241540041c1314510b0101c030024001d5041d00d00440580d05400140f01e03004040c1c0d50b40f21203c5000c0214006040012517209045044c440d10b4503600d91a40700f141240505102c040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 701169136 1250 701167886 701167891
    0x41512060506280b0901090e0a050604150b0913020c0102040e150f1c2303120604020403170c0a050a080414180703021b030406020708211602010c0203010c0e15030f 72
    0x10070202e80b00c10800b0011f8070780400702e420010341680064104111120382d5884248500750459090050f50800444020301c81046e010b0402040005c102c1000c9504200c9011040061514001468a03102002050880c0c2161b003081001080c24018444101c1d14600903021102e0129000c001c000008030000d0007610f00c03044002810141d803a101d80c18402200300400c2207059844241c40c2444a4024250700c175440550f144409000500c0031030598145842580c0540c0da01254220081d80c0140d24458150013050400140380706000a5400040f03041c8032020043d40300300c02ca60389450600c1580401f29503801500ca020313504086c000000004444500c9412542074200141d039208859030080b0030b20041d440000f1f151200040c0041d09030f6001a0907002c41c0c2d848010b03685400d0743d090031007510341c20b09804004500c0040c03081d40003403019030010030403503841410f2004c02d20810758042400d40b001e90f4406d40126807102e1000d80b840c20401c10200303c000c00c03108102d10750702d090741c2c00c02004e1030003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 701170386 1250 701169136 701169149
    0x801022503020c1e0103111215060c1636050619030503030906010b0a0e10170411030f01090201021005060316030c1a160204151206050628 61
    0x8200d05050600a2181c83e511810107440c10100e00305030001c103034100300c0000030280000d1a010b5552049a955001c0d6a00301c1280c02e603113001078840301c0d4041c00e12903003c00201d500038420003481030610000c10107407010440b03031007521400078504804190300c2c44032030006240e04503c04044090501c002c960104900b800d030b1000003090b48641c40420591005d85952441114100c07a0102c14040000701035480f0310181c0c412200300340c1c1c841d400c1c00d016000301c0c0d06100101d80c2441e03c0520701e01e400044212040818a800c03041d0610305100c0036150081698103840000084030004036a041c2440503000f04034031180207100544190740000d641e6905609030803811652a4041140c9980c1403118a81e2000c1c0e03a102c8032000c5480e030030014048601803083c442501030444a259060444005a03800c1c211607800c4084550060740070300c0040c3c141030502090341891900c010034500348425a2030307101802540300058034945001401820180042c0d0041c170061814800700c00f800c0360300302e0304094645 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 701171636 1250 701170386 701170447
    0x7080d0509010f020c03070c060e03150703020930070605070807080918010e010501081026160905100308070f06020c010c0f0e0118090b010c0605010609050a080102 72
    0x12140381c000d006201c03510401000030700010b00303900c403040000041c00400d40076449158640b9500c44050b00e5801140140d0f90701a0426000e0340c44d500440c1c01070640c40441414054a4007815500246410034515019404040355000c003000f1203254151480400542c94000c0081a080c084041d2581c0102900108a4500050348101300081c09064034003295028010203083c5840b080d011041c0c650900030f4a0003003180300000500c40d07114001060180c2000001039140906249218074810b0048243d805006040c001e40d82189101b04000b450620361201505500e030308041000b4242ca501410600c182d5210880600c0407400030801c6070036281c0c1c442100048002070f460464081e000c0c16641c04119440d102d1803208960b0481a502c182d01d03c2a48c0d1215070b80c00d044015205400e88040001c0c070000307070117000d1000f0140ea500c0558540d2050421066081083d6244030035200260080c40000359050420096810010208005010154000e47c1454100c02c003401984084c044010700e0000d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 701172886 1250 701171636 701171641
    0x408100605060f160206181e0603070c0201174b1906150f0c03020601051207090e1005010b070f02010e040f2906090a050d05030f0a08091207080d05 65
    0x4400c482002c0c40c640c0a0403c9403034060821f11204c84504a00344240504614000030360f6056940b94101c2d2a80c50041c010760943d01d03042012601e88540d164100c6c184070740c40f22110400d080300741d00e50b8030840b01d50100c5080e00240c46500700f8420040c0395103103c03801080f008030132210760f208224402c000d000c200503101541c0f44401c600103010702200030780400f0314125000c15034140c02d40c002207135000ca68a9400040e1002403040b02c6030800b0b041301400680200c1d0040c407142c0b501c0c1e80e404003028821001c440f90349840d52100d404449203d4a01e4507198040e10b00c60058203d1401514010702c0c0c448085420301e64103403180e00140203000c90003410042c04107540419580d2702ea00103100580250404c100280c03218281400d0b400030030b02044001c2128941c1c45c070340d03450315408489251310040e14181e007e80c070302024000c08171080d14045895000c24070040c0701c064851406010b00800b070303031341e50501420400103450402298080038031003190300304030b800c007c50001c41c1110054a051840044c195 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 701174136 1250 701172886 701172907
    0x80c0a0216120303050f010509041511130806060102030712030507020a0606031203052a3010080304150e031e0714090f011809170408100605060f 64
    0x4003040220580048244040b46002941040301e001903c207440412031601d80c07000c1514903507070074800c04d503010303049100103800211101150742584c001c8610204194801c0740b0500b80c1c540140c041d044501c50030300010006040d08211854100c0390a0025500d0820070741c9601410003402400f827403d0544075400f150805108100a03580b00c0e80280040080a8481c030b44020440c100400f214006070401011404248060800501e1007480403145048400000040d54040e003081421034080e40040703400300900d42e8070503402c102e00f2285015880c03142c070701402043c2443d0250741200c1c0f6142d00030700c428488035540607036421009115051004129a038400041d113420140740c0b6845180682c03c1803011828400124041a14083c070400d580e401e00c91000e00c41c16680403500c1e141d241c82400010011f0080440391118007071030801020440801070b484941031100303061901554140700003010004903a00307000039001214541428056180750000140e032074042c4801c40d114080c4005002c000d00c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 701175386 1250 701174136 701174143
    0x31909050907081609060504060c050c04050906092104031719020106092406030507090f030507030b070f090b1615090c050121020306120a060e1c080c0a02 68
    0xa10300105000303994a88020010060002034942d180d010600110032100b441c06003201c1d10680760150f070340e2801c00346030400031a44008030800130780d2580a9080111200d8a0700d0280c203219401c507400408450400368038151800070080b1410360344491243d504241010b040301168100c980004504801c1c080c0090012880d229240303d0100080140e40704001558064004070100c5070a08010010041c2c1d82c0c0b100d5041111004000e0064143d001e010320850380240d02c0301d90403461624000300003503141d5940e0807509009402c2600c0b0781d40314410400401c0341c2e14603071651203143c0b407030203d00204a407500581030507064000c5405410000c624820941d00c440c120059282e0000201c002d03c1601c00d541400600350914244d4842e82802c00200e11340d4001d51440300c1110120880c400d40c001400300f06030003904054007165014015800c04201c550041004a506c00c0c0200000584824800f5081c0e140069410b80c00341a0780c510b8400c00740079a04100040d6210119184d007a65601803a00103d06 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 701176636 1250 701175386 701175389
    0x1b0c1a060103062c010b0702090103080d110a020114010f050d020d1506031b0b0307091404090b07050a0e0306100603050a0207050a12170c090f12011112060a08031909 73
    0x70100c88000c501c0d100b03041e44540404410f1144e40105003a6281d209001e0707503108050000e50000c0c0184010400035168100900110210314800280245222000c0041d07034068001000180e4450003036803003010102c00b02600408926908252076454840814040c0088071030281c400d10200c070514042c014880840141c2e8507180404200054481c5002c1411400a20120080200304000802c4100a50f004c83c0c3c010306a40e01c13a4200c1d2880d1040030744080c03003070320078054000d6291007042002598060710039000326869260705841d0603004400508610490788410f2099000e5000c0c41060003541c0c4600007900c07814500422290344248490300a4801e001d0020035130f100381620388061200c4040d040042d40010b90380d0365000e074000009102e001c01d0640382c003e8049001c00071507480c2d10b4003000c01c03500c0e502c014103d03c1130701007030405142c01c41d8050100c84400c603400048103c541c0e84141c045a0b400b560465490108070b0406803400d55a0040b44010b103101c0c0d480c104885160380c000c281403030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 701177886 1250 701176636 701176649
    0x309031d0f061b1218092212030b03152e0303080103020319030e0d0320100e010e03040608040c0e07050a030501170d05030a0f020d1b0c1a06010306 65
    0x2541c410f940d5150102c500100c07140c020310390050102000060200c00c08540d028684003a01894050103201042100b15001d0f18502d08211410107038212144010501d0046600900e54103040469505018003616070101035076110707821403c090401410f0318039159412116440100c0041d5281d02e0030340702c003c06588985d00d0300001039000001015400f65007681607920179811740d03030010081c003030180760072030749000040104080d8003044246040c04080c81300390a000780307002c0e8501000d03c84840c410a08080003003420360841c2050300d84004090080402d00ac1c0500b00800c21043c6440d9130300e4580c0280e01038a01040001c1d00483c085c000170107c0312010b4440d0304000840740c1800d8201800c40c0d031109030f00c200400d05040000494152285100a8114601e0090484814010b500321016132008240552141e51000403d4681c000d81c0701401110701c0d103c40001d0a040c103c0d807189110100e080c0b1020801419031301c04800140d921032184240004505080f03501e48503480140c01400e465000344 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 701179136 1250 701177886 701177899
    0x804170c1b041404050a061a1305090d0f090e040314030901050a0605090405030904271b09060b0a0e04060506031f0501261e1006020601060309031d0f 66
    0x240c03401100e051500000d04402c0741c003001460991000301c052001e04490140c030316001044083c010402c290461881170308211009481d986400e00040d100341b8601c080038180c00d50b01e00800c040d8240400032949407181c14107010404602c5650000c11140c05406a0401d070800c85000c9400c01d406a180c0d02e00c4041c03140d903041d0326440c00400720350007403108690242869060420005207400c1146d2032500483c1c000015602d00000d0b0703414040540601000703040c02c450740000f0b0503044008002404061032050460080000b1044202610384429401c0340800503e4540300b0400380e0001d00031280c41c800d01d418181004080c11000900400455203c80e41000001080042e0040140f0700070480100c0b0300380b04441e4903182c0303004664843c1d01d85440d0720042c500a69028404a039480c405500015400c505c540112501c050b041803044181e1748030b603050f0b4006005004283e01800403034013400741c92904018200c01600c00400003054520618800d10000c070210006468010b141d241490019016 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 701180386 1250 701179136 701179153
    0x51b0901111e16091109040b0d050609010b150c071502010e0d0306060f030605092e08240c0301050607080904050c0405011b0209161209050c010e0108070804170c 71
    0x101a211100c0c00c1d5070303091500043c1c80204081d002442040c42405140440d54241449001408000d0030340c404169480b0480801160000d241007010b01d200d50508000424142c8021050020b080304045030700302000c0c014400141940c00010f0f88408170b50080032044d40220307201400381d0040150070219006400358603000d426964154011030f007107039402e5a07203070854030084208800f01c41d914010103030300030b02d010041507401080c0080d907101d00da0503d401d5a241c80600009068901d40da500507035258004800508030b8003440c10b81071903902804d05110030a0302d4080b01d09401840140a01d9108140c045400b0060000610980b0710071440a8000c01c42410801b41d54526034200d0f03c221400141000243c0b014020b00c00f6503000c50307070ba0103400d450203500c460a214101c000e500c603a003c1005140049000c805980e4000c8146003402903016003001040d0340001404ca00c100c16002d0705006000090000e9903a021610f50340c4142c011700c0c0c1c0002100f00c3c9200a54510a0b4600b046142c0f05c0c5121 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 701181636 1250 701180386 701180443
    0x5070c060c02010e06070c2d0e010f0f060c030f0509030105090606120d1224060503010302031203070e0409051905060a050a0b030d030203090a0204050112030201051b090111 76
    0x52246400d4004d80307500d00c040d00e0450801c507541c0305140000b8034046c468801007200e052184141c510f410170300841041d0303100c50300415145058007a400340c4034207011280104000d03404181544064154040c800300c80c2820a007010740103401c8800001d0400001030500400315104605035502d40c07400400a1246040038441a940d42d4801d42da454407600c280280c2e602800d60005d02107400718025290307681011040c84040d0018005141c000c482e0f005d149041d02c81c6454822410b1020740441c0e00e81d56200d506600615240130354044084007110420800c3c84a03180e009250444540011540802d44401c60300d030650400295901d404000032070f40c0c0da407104204000c68940e00c07503038002d00e081210b55541d9a501081e90011011603405802c80701c40210090301c249c0003141c3c0021054200e801e91070807079021a0459101360301c5003442d410050710380010544d0a018403900702050000768041c000003c1480c400600c0707110116070520440c41840e190480c81400b0350b40b41001c000c40d0660b20b501c400103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 701182886 1250 701181636 701181647
    0x70c0b0f041d16030606021b0312040803030a06060f0e040b1207060201240f1e0e04030509010206070c08040b071a180f0601080a080a020a050708010f060905040f0201050a05070c06 79
    0x20741c0075a85501841d4101c00c440e2003417056000311410340e80241004440328442e40b002d500120005c0c0c1e0140580c0d91182501105903000300001e088a100456503460011100003c65809400010412818a81c48064264004051410401d01f201c1c0052405007801c0001d500c0203030b49280000500a1000000e0000d8041d48813840e900492614003600501e42044514555228019022503a840c030714140082c4010540c25445042c80d41c141c1503985881b6181810055402c407411070000354006110507140d40e042c400550002440d040c507102042280e511940c150080e0f0181d00d401c45004610042801800c4108160b1581038036901129401d00314640102202d0035200420107200e02542450140c0002035041d04071a070303042c00307840300000c1c50b0388001465015040103c11440340c4004240410002c4c003800008000140c0000303070003040c0200c0c00c0309450942d40600702c5140f4000403c0003082240a00540d02a424a400c41e9146400c100c00d031001c2c065407c000e00151880880841c072a908079 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 701184136 1250 701182886 701182891
    0x90b2103220503030406030b060c01090c1d06130c030213031505060111060a020703030605060307021e0d0c0f0c120b04050712030c020906120f060114030102070c0b0f041d 75
    0x1080c901a5500290000c1c0c101004684280c03901540104420003100c1d21039030248201040c01005c8510f458a840d146901307440170701c042682e0558400381c040101242c0c00d00c41503699054410b84508600d00003000500910304002c03d50605921055000c00c182e04c030758101c03081d00d582c203142203a181d40c50b4108804c6034001c04e200300c185c50f450040480ea0030340c0175081c092012001c1000400080e03a812140e480a9004107500b20185511408081742c0c81e607502024600c59041a4001c0c407840410b2080c0d0341ea0040140011607040d001050310101c2981d012801c000c280340c21051001c1040d00740d180c20700341082d090748000000c9140810300c9003003001c0320607036a001d03900420844045030303142e4240002d460170070a002408030700c00341108001810f102d061940c2c80040140000b540c00042e103001400c03c001451059070341c0d00440c006210084a001e181d803080542a4021400e0042e20340e81c20542404501070302d0101d510100d094000302d010700d405c0720058043c00000d040c0242e0b22202824030610305 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 701185386 1250 701184136 701184157
    0xe040c1d01090b2a030c03072409110420070303091403070507090e03090109050d0f0b090d02061f06120b0406030803090c09040b01091e0504030f020d030213090b2103 73
    0x1a0058101513000002c280c4400401c0e80000c0d514003559955403514a8418010340100f9102481c55400d080b280d42c819101268003503101e0448440c001404c0100301c4070f1055080f0f0b070303078607400804400b80c118150680b032a6540c10709000480d200c02d030400500ca0320042c07190440310320000440380b0410001040101c101c0f00c01c14030500c00784050040c055164099010000d00180704184e04012500c0c2540f1955040d038003070300300c1443c680d42903280c8091192080742d540300d0903409801d02c40345640d410131049512141c440300f114401108003919154045580c400e07081000b003910101c01c220001d0740d000c40c81032000100108001552840d11840940040300c3e102a0760290070101112070a104841302e21465100702d070390b82e180e800c10300c0e40780003490f500c64824440c42042e0400b0507641c90f00d02c00d4038051400fa450302401c070904890020b150910886403002014010f00102d0342d40306003184074509075411200c000ca150a2201c0105144a1404a4a96405807070400080080e0400300061180303441 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 701186636 1250 701185386 701185447
    0x1e0c06050c0a090b0406050313030c0605040b151507060905250e010b0c1e030706060803180d03091a1c0501060305010b040509060d06020c06070f0e040c1d01090b 71
    0x11307202a01a0315005520404001c18001c05c006498011032000091406c7d20904000b00300a07070948540b821200201c80407a05614981d051080300f000a440324240301d24200c507007450300140c4000480c0180203c1d000100203d84030360b101c004001c1c2c00e0020510072a940440c44c910700c04002c0318180d2032102842222080388030203001090200d4036000300c0d407200c480f0400408002c90b091288100e4117524850300c04040c08140140e0000032114040e010041c0380701401961203450500d100780d5016444824a03200340f041c3d0307402d000042e401c5850362040700d11080c582d00203c030050805c1d0b6214421007550b001400c8a01e0490400d40402da0f1007141a1143c42e80c041003e03a89507030071001544a94061198042000c000082d003a2030320316051800f140c40f580c0c025081c219500c08140c64000e050340d03450007064040c2d11441040e61710441c40046500112001d0106207044140580b91400310f074801074011024a2001d00241d0180e85024003c02442c1e0000741c0d1140c0b0402c04085800102c0d00d1516090f1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 701187886 1250 701186636 701186639
    0x7030906150e0f09120a020102120603240c07140f0c01020d05120c040306180b070503010f0b09030c060a02070e01090c0509130b0d110f0405071e0c06050c0a09 70
    0x5810141c03407041e03803003001c1040240d4483c0c06400030201c5004081d0203c0784503a900031800c3d0302c0e415018142c84d52441c0c00240e00c45c29a50712840e40f00350010305084c000c1c0d1110440a88840c001a84401e0750881030300000340989842100441d14400d9890140841003403a1200c03a07558030000d600c54020900c4826a0005c030364040049884020380d83d0308000040c3c042c400390002c1182d180645410a044001e030034603040d1340c0c1e51040d050b9400c0344807000c182c9555042e0082404040b80340294016040d10f001e41c595030402661040442c200e01601c0a0084d0225041d181510100445022407000400968494042e0740c002942c41e091401004404458000006007442083c0100ca102041c540c40702c50509045100b4800704811300c50b44120000e840d071011100350744400400403401c82c0504807240c3c2e50711105003401a000c0e0514010342c0240d00c2c2408001440740c0c80601c0c45092162100071000680784d606044448503201040602840d142c82c050009215010005009041c440d071500c14516 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 701189136 1250 701187886 701187911
    0x5070e0c0414101d040605191703090a0e06040b19052d010c052e05090312010603020901110304120201021501060f201009110301020408211207030906 66
    0xf07000001500c08244d400070f40a00ca0704203460090316410307000e440041c8060b03031400004e04c0300c3d40c450105180e488188409205500b14241c5c00040007039910f008601d081c4100300454040386180c81341c00c0e00c0c4051800440c006645039004040171480043c0b0014410104040c5148282e80c68801c040c070680c0140c254002001000c002d06041010880f841c2c9920442070340150b50b00c4034955000c486500500036042001a959409180d51640c0c0d1512803107800409251141101c1015251b00d070940e0061045060941210503e103040d50541d10f005a2907005110040e50107500d850f140d8072083c00040f0b400b0401500d65013480702c0440c001d900f00c5070302044040b039100403c0da0038010703100000d100e056082c41c0680203c022400c015826400c0f00c08403403444003181d0424000712081518030b07880c0c40c00241489800c0402842100d4120001c6141602d08420306a8980c422403680d00380c024203030412441506200d09907001074028404680d220310701900028020f084042e0211440d0b8030381445064407 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 701190386 1250 701189136 701189149
    0x20d0f02011e0f060b070302010b040c0c0503030a112106031027030c060207201906031a0303030c03010905090601151125061101180f05070e0c0414 65
    0x500400301d003080180000d426400d02810600303061518583c0c66940c0019086442001800087d00940c0001001d280071003c101c00d8032610f01407002000408542c07000415030102c2100d801004004000641c08405044c809180c0a8100c441180324410000c0104000c06107a5003485064202e0507202c2c140c0803401038000711132600040302c8413040c464071003001010141c200860824003a0500c9401080c0943c0c0385000da0703011000440d10001442c01030029281c0700010011000e00445800c0114099420307c540440082d12610081680300c0c0220071903103201850924910780041c068130750320314002112241c00c3e03000b0300c2984e80192900b0001109000085240c0d03060b540900542442443c00c00d0044803010860900b4503100c0c000c030f852001c00c0d42406200a4407140c040744070111514903000c4082e10189100e119605940d0508103a040c05d40c140f1201455090b600114882c07160b0715505005e460f12040e5044254242400818070200c032105602900c201e8815448644502040c4400d01c46c8 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 701191636 1250 701190386 701190401
    0x6080106092f0d060b09040f2f0d050f07022a091905010f05030d091208030709150e1e2b0203060a050f0919120e03060403020d0f0201 59
    0x68100072204002d02c1085200351281110403108207041c202515600e184045a0590b40031075aa00000591088070382070034080d81c0540040c2c0c0070304000c015250b00d01080b031030068076040b20340c03244003c15822990410034243d9416003105d5000f0040c07841d20044015403c102503039800c0241c8a4450084082400c03a4991031405028620603d1540c49000622180c810041e02c07407201d0810710008545400c00314071440e4020b20102c06c0b0a9041403902c03060504220040301000c5c108011441c041c030060807183c0e2584102540319070f40b01da0300ea4514004982041c0590000440280036846a400d03003a0300c080e0401c202d40301125008002250f00303c51843d041860a043c6820442164010b0220000310400e000a041d11103142462500c240d0300181c01e10303400312035031301201e0355a90038007400880580300c00e80e0003401070004010080122120850001010714001c003840139840d61038203510700c02c0388110103450f03026003166a50b050514000e503c1c1d60400c24071800140103640c3d44610141b0501480c003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 701192886 1250 701191636 701191661
    0x10f0b041a03270d03150807170309030601030308040c090212070c0602130e0411060a020a140c0405010b07030f05090a060c02030c0d151a060909280608010609 70
    0x41da101000d0148031125040200540450660f10b0381100c0441060070740b00b003024103180098042d946803064060210340135000a0280c618801c101407024810000d000400d482046d8440d00b4010140c280007032651080324201c680601440340000105908003802d50700852242c0c80302c941d1541c90b2200341d0100d001c1c103885400810120004904454021605c21900b11b00403035000d0300c0c00f071010a111503084041c0c1d2003070030082c0c0d0740000c0100740402840e010311982d0088402a00d0101c0c1c445009564030001c51000e0702c41d8021f50340f01c543c3c01c00100020011004098002c0c08190394440c183c18035504402016408104440c0700c040f00b15106c0d4013141e001c51001401c03410a40c1c00c0c043c0844a40c407007080102c4e014422582324680c03d60b03c01d81c1c00d0b16110301c600104080150380f4010ba00c15a4404152400a09070b146507140d20350341c0f28800d4550040c0d007540c403441c80742c3e04c10001340c044c1c2c00c00c561b4103d21096002c1c544040c0b231840e0b40080302a550704d44001d01c0860340d1015100103c989000020 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 701194136 1250 701192886 701192909
    0x90b01230a050907020a0c140102100603050a150902032e050f16030f14011a0702100804051009121706033412030305160e0f060705030c010203010f0b04 67
    0x10b0000d4a010b60f58a50070855601c100c0700c0e0b0141a94a555001000380c10180d0051f02181224aa560341000004d0404404038020b00002d07240d80e030760aa075440f0700600200861220141d25203c1d0820f54040031042341c00408136448401000250340030714024100340e0650b00103420024000c000785000d0507020310740c01034804802c0e64448050b00080c200c443c5551041649500394400e94244a005181c0d00b0311010500f1036841d454a2200f580b00003400003856400b0206001e940c3c09a90383d10146e241460071424458210f5031686082818003001c200c1039200f20303180000c10004c1c003109200030000c201d0903840d000042d00e01c2014143c0c41f00002c5071941da00d40d11105400550f01808020600c40d500d903416103c8448403082c4500c0c3c0701e201c040c0c01450ba00400b22103034006060785409400c3d00510548050803c032818864014104054007020901917543e41180c1880b0352500801c039254650482c0c1600e071136a42544965010794005c1c42140001a0032a0000c1421031421080b1000c5400c1092503 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 701195386 1250 701194136 701194139
    0x1d030a1d0f0d08090d021905180403270810060504050c041a0d06150c051b01021b0109081204031a1e04231f050c0f070213090b01230a 59
    0x902c0da513580309800d00780d0000c810003841310068440a100100b0951148080b202036400d000c24070040c40d0005402a801406034820b010100ba0010340b29031220b10400e00c1d00408611050300807000005560014605201d11104841c2054513588000d0135100c2c1118240001d440710301c0c60020030b0080d4050104468184242030058100340c4004240c000c0301c1d00ca0100d05160703520800c1d210800b4149100f4080740f102c2c41c1880401006003d058078101140d6040c00070070740c541c00004c1d51a803c2d0308011410141c2410840401d81c01803510b0702c0281220400c80f09505181c040003203050304184001c0303460588015400007211005202da5228019071085030750224203d5040303048520b0060030a650f80354190f980701c454540d4072551070440018480007040b507803000c1510300d80401907c0b00d000c140a440d2106102d00700c80d40c24221066504021502e176160441c50000070690303d20555032000b03151902c0400b00400804e20781c403904860708540300c1d0740300c502d094048d07414101070071450a9100090900 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 701196636 1250 701195386 701195393
    0x60405090406090609080c0f16030b07030608010e0703020a080601050303030f150904031106070c02090a090302030d02031614180904061805060108012a031d030a1d0f0d 74
    0x50030380c482c0c050300e0b000c00c2020168643c2d40440781d070404165081440018520340c1218100700103144a100203009140000610030120110099400020300d95038184d00070541e80f03482074116602170032006008000c0035141c4004203545026620040f405041030910004840313401042081c100e55000d00a9842c0d41d40300d0251010101c80144240d91002c061850442162140035481e84180d12948400800850283c4424a17054001741030000304440d65880a0050305c2d190000c917003000c4c80c51400f01d4003640514040c0d080d800f401814004151020040105001c0106180c000d00c40050701c1c3d00c40310304128250441644110003082e00c402500384004407807070a010380100d509c2030041c540041c0d54030485620183c6000074810070791f61540040c0040c040d015080c070030f001c04070030104028603591100312035002c20340c1c003240314810600d90341d03852950395015808140c030704102e101c000340ca03940c2e500b610300540740a2408560031034004800c19810340301d080012005ca010340c2c004201440e101c96980c4d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 701197886 1250 701196636 701196649
    0x114090f0a08030409020405010306080604020a15230d110310270923010605030606040207110315040605011203020a0209041b0305150c09060d1109210f0c060405 71
    0x10581500320007840c038005402c200501c040c00c040c220b241c2016a0300d43c40c0c0350005082d148a6041140250030920500c4010382d0380e01014012614483c9048c1e120751969202650400007070840307021041c07100031101c100c0000b85c0c00100644d84440c841044002041c0d48540b2050008950420b180764686500b4400a0f880001c1050080e8a01c5540003c02d00071032549819501c070380c0ea085414000c051404c0001003c15500c0402c40b51200c8000c004451500001035524000600f520780942e90004140c01030010902e8205404a00070701110405a24401c614004a41c00c0b174041c5c403414600030020545000222401da80980c055000f0981d00c030003a001c0041c0800042c01c101c822516101281161044c1d004a0000a600500140c90101c550054040c50b040c00100326401d000d60400001403030780e40e0340702038448225280100003620602800701095a11038804103540c0b00303001104620ba1640400103210b00c0039481001d03170745080706800c00d55590300f0b400640585d2140003400b01348814204070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 701199136 1250 701197886 701197909
    0x301031e032003071a0a060e060d08030916180b0a030308010b0307120f020706110a05031902090603100305010b15030c0a0c0f0804080d080417030402011116050f011409 74
    0xd0b0700303032840c0280aa070799002c0c40358030310b218106051900d42040480051031040c40002d1018810702d516070300e8a0400190342001041c03004140c08804804900c070070108000304243c2c1300b0390109216615480788402e0040d0545e0140d08250103062444038016420000101c100700c0741d140d102c4000503400c01d000c41c030f11508000c04003c208510945496036900c030a0054690300d034450940142d8032400382c2004025105c45d03035074290700c00708200030b03c01146522404595101c80d41d403001c2810f0317280400100010713100d1400c0141d070101020080c401c06038014034120045038841e030000c100c00c591480500500c01f82401c1e601805000070700018201c42c148600501d80007a040c50404045a502d03940e004141c2c00c07079103003505c0c0c590340814184a4041d0070030170f1301000301090030000c5080c40c00d690b800c01010008594000050404030106d070441e4020761a1104d50f081e644103030307011140e0300c1300031400c845903920a241c4981c001c0803418135154011441800c00b070048810701440c0c182d03140140290132455 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 701200386 1250 701199136 701199197
    0xa1b02010216060801081b03060714040806070315050f0f0f011b08040e011e06032007050a0c0603021315170a0c0807090b090f010e06040b0301031e03 66
    0x7402c180c0703800512a400020003408560301c85030b0303865040c030307501030302e440303e045455000000c5241c5c184070035940001c0c0c03180d800600ca1820002410080f00301c54814040e82e07200e101103200e410280100315405400041660302e2400310016030aa480040096549030394501c2c0380c11040d00b00b142401800c244402e44054241030405c42950291810400b000c444080c1c8155103554010905000448010a88500401e808400902e000e0b494914005c280c1c001d0344102e4041c1640c500158880c8002e00488502c0e14207460369407a01d42e5118246251103480315001261200200d903004a0800c0c02842555041030312640a40401410f100d0741c00c00300c3c000c4980400a1221500000d00030001090413207115062450022415164801c000f07050420701411241c140700c882d030340501c800e05c1003200340d85482c0f50450321800303400208001a207607241c62002040c0c020200140210f05888040c004504032403041407132005180c0c410303082c8120308180340002000948441e0002e08011030b0500a440b000e6103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 701201636 1250 701200386 701200393
    0x1b150902240c010b0111030d150f15090902130b07020a0e0c21060916030608030408012f040b0c0309030303040c0503101b030f090b1f0b0a1b020102 65
    0x90414440181c03881e0a080d0440c0403001a190040000c00c0c0580c42507035400782000c0c0d0300180b00e03103c0d403926400340020074110300da55403880c25859642d81c01203000070300042c00521080780d110f6102030f403030041031a84500450207801c800a400c800328404c8440000078415100d44035410012000100e0f40300d01c2c801d0764084081c1c14081008a070320680c090040001c0203100e5951700c0c442c0c0c80b0142c94000c40c0c0c58840340d85002020000e89807501040558400f80100d60300540742c003801415002405181c100ea0583e120106000c1140141540b1101c421112040c48164441c034484c000103400b0380b0516000c11b0a030041c04204481c562103000781581e03140701d01c06d4904103480000030910f1070b042140d05031290300310303a64201f02c0390509008404406580b41d0051200700e240341500c131072002c48499080c0416035180d032a40c102100ca82d0210b00c0d000e43c07044000100317003488005101030022a4007803800f40e420521000440540000032a10307540025120351000d03e04207185c504525003a40c0703003a8190b00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 701202886 1250 701201636 701201659
    0x50f060c0c042c0c09060f030f06010801152103050307051611130c090e06030709050a05010504050601260c07120801060206060109050a05060f040b0a050a1b150902 72
    0x241d90f40603a20300c0b0910207080041e202400c800141d0108085400d0310019000741e00030baa020344034111400c0e48900c0a80d1980900552980440c0c41c1101624400d052030003140b00120b14000c040d044230a866084800d400d48090311101902c0d0141a5809144107150640e066000007a000d8405142e0020a5051a500340b109190310400400385469044401da02a40b40340059480e00000703c0040c85144081007100a02410740030381800b0890250300d0344051400005142682d00700600d2001d0141200c0030b0009052026044010300030a0043c1d908c1a0304110000310154860020034000009020311048034168120324034144503005040e070982c00008000c0305004c41c0b4030000b8110b0a40455076000f0107903140041c002c0c00c001015148a0400524003001c0000d5625512404203550044230325540e079142043c140034041c8129030105500410101c1e14141603504079014000311030180c2c0b140f558801000001403419102c101000f000403801c405001070400d0940d21403807005201414013903400303 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 701204136 1250 701202886 701202889
    0x120215161208010e24040f0c020106030b1f03060c030902100f030f021908060d02030105070903050f24070207172b020a0201050c07031a0a15050f060c0c 67
    0x14103806415140420707400d2a081403a40d1200c80d4034010140a15402c001c0d041c0901312405456010041800340c8034106022001a41c40d42d0040c44200c041070b80c1044200c0407028040d01810b140d101c00c0d2000b00c6d00c1c400266044168000d040003900b030000040003c2415603440c42c00400f0600c000c202050f50b03801d40880182c032940440c5080b00c005440c0e2032031f8240003000040584100307241c101c132000c1c014880f001c0b444514495940030618a8103040503da941c003004106104607990b8040c0d455802d0600b03224020b6040314481050701c1c00381c010391340a18086049203560300b03103c80059861010b80c0c2e14007090301c0480407040350010183e02c19144000d98544000391040000e180f01c05c041e4100032210b4801c03c40208010380d0b540107040320135529003c0c461002e500d80c1e10040380a41440000954240110020b00411014580c004084040c400300c030303100109980400c0390840d160350f2a001039040b03850000103480c412140e0041c840c2c1d90030403200040c02001d420440700c508092040b142c003a50b05 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 701205386 1250 701204136 701204167
    0x2091909061a040b221802071e020105040909020f040f0b2106010e040f02031203060a060c0c1202010908030720011d0f010507170a020705010512060915040e0c030c010306120215 78
    0x1402d04c2c008050703168480707400d0080950010327040424101c071000440c140141d80000c10340d4211000030b07600003100c1c47c00340007040703040d460010499031040c034051045151180701d5100c050f00720b40689001c0f65480e0f500301da5841d05205502c003940e00c0e501030390040100b1400b503800b0a9003d0300c45c07029075028400f80da020074a00600784900140801c0003000304850342c10020307030350320041906180411184034140c959840d800514000c0640031007074000c82d10156401a40104001d29130881144d54442142c2061407418002c14030400c5118412944920103610452041d5002c4c032032010181418040c0d80d080100600340b042c0100d0600a00f4000d440200c4c0c0c1d00440703509104014400543d507000850390007400d103415500101d051084c28046406008110b0444550042060b6150741c0d4a07117039030440f40a81e10802d42d0b000c1d80b1a0030100030500c45107010625100241d810740c2150900b0441c1401541921241c0c000c5948040300c83d480f60025242400040102c1d0070b490003240c0c504040403620100c0d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 701206636 1250 701205386 701205419
    0x30c020d09030b0a0209040903080a050c07210318050f070b0c062a0a090329070c0501110c031305030106060c020405100f0b03090f06070903030302091909061a040b22 73
    0x82b41d800010030041c1842801750b541d0002c01e12820501d031108070381e82c409540480303a5002c442407002c460208805802a4804911081d00c40b02609024442d4a080d69840c0380200800c001c5000d8204001148503c0400791a040d03a00b207400f4010903510525021844040c904003144c101c00c05902c400505815400200a001400d945840215055040900501241760485000e0000024442c40c44e0350300001350580040039031078103004106c1070341040d0340544482040c105d12200e001aa940b9460000001840d80c4140c2130f03035003620244d4403001c140c00ca0f00313280f0402002c18108482680189801d61085522000d0003001c0c2d940c260322a080803000003070603000000d0030040001440030b005020452050001020001419903143c4160001c00145641c03000906068010403580119940e5024803d40c20360400a10710301c895440302140c020f40f0036845018141c0201d1110907040711070b02c408481c180e80c2d04084051074402d164445500110044840c0364a1141085012800050720001c000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 701207886 1250 701206636 701206643
    0x30c0204061211030c01020c010f05070c0b030f1510050d060803030c0432010c020d061103010f080601030506010e04081213020f0108072309090a0903030c020d09030b0a02090409 78
    0xa24a501c00e2a0018070b0843c2030004511075845040148005d80e800035010340168420f203024480150788032406c4e5094020000000c001036850f10012030001002c2c00903510a0b4011440f1240c42c1d1a904802019126480a0103800c04000403031100054010001014065085d000c0011901d613651101c40c1550020b80e6a4804800000f4041211030f4413141300c41d0541101c078030340b10411000f1004800c810f0242c8401d0f00e050101041d43c0c6025982d50160b100a410313002841406144007030304502c0955402402044000c41c0032070004204554006507042c10380707600200600c61b41e400c120038a203500e00010800c95100208219561100c51156001400b0700d420541010f0380c0102c0b441089013103164030b89079504000c0008200308540390301c444044880100900701891891200c24a4061885032302c030b2a5811003c01c2080c4a0101201c0e48a00800350080ea8100300094504008984400e51900610b0000d0151442440031030700381422980c100080c1c50303006103400405000300d010780d0b100300000e0b03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 701209136 1250 701207886 701207909
    0x60e060f0408150106111f020c0a11120f060f0408040f030b0a0605040c08060d05030d0e060a0c1701030809011205010b070c080c030a151d07030311010b1c030c020406 73
    0x507581e01914440f80b40035080c1828120a2202118042c90703440300c00c0d0303135211100d060b00e901d002510010303581110034040f030701015909840510309014044e20079a072a03640c09203c1403141c4044481c408144d4134032501e040c10144c061501d440002000213034016005498080040000080e080499201000114801d003500000c81c46c0013401c10044501c02e601590046003080c100d0014a54032520281d481141119860540c1c0007d04150303103180200760320021064502100305002c1240025414418000301d00184007003c1030380402c603003d40c0c5024098007103608440c01400055407000c0a051509130624000740c442005034103050984000380e020340b80010740003408100784110700003040058202e0b00001c00c0fa020b02c0c0404261f0b1590b00002c01303886d80481900d5502c5040480c4c21607001d1030314810640c100d045039080700e15101c07000d510045010901c420003c004106042c050445450b41c000d0810205030300850311080141c00102c011001c00071851020001a6143d00c0703054054841c0d8440f0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 701210386 1250 701209136 701209153
    0x10e0d0f0504094b0b06040e070c02040f0b0405060d050a0206030403140a120b030a0209150609060706140a1a010302280e040c050301030c0b0a02030c010f05040611090901060e060f0408 81
    0x1310340d411100b40c003d100420b09020380340c400e6869103400c517822981c462146130066503440d041180d01e5200c05a0096200741002c958401c0c51416810248040008580410164955038204849000e00c014010480d810400144000d45050009150b000c3c0c044c0c1000c0c00904004007170180e10394040003480f00800e503084030f400c1080e1114030440010308002d4004100c5080da5400180c50300400030001c818981c1540d02c0168161103074015210b03c000044c000e184c070b41400d0328190700901041ea080300003440f02180000c0300d11455005405a0751644c4e01ca861079148008011006540b2006c1c41b1200101c5401480c01d0b201c0c50001c1d110740d1405259940c0c058010000100070645040d8103a60040000900c01030021440c050740710400c952010b004140d807694140416811030140c4401101d0952a1445041c210801500140c0c4030342d200d820104100c030b2a030318100d00320740a4220090f802c010713880014083c00f4050321803541e00040041031142003038101c85c00082d580d401904010026013013080d5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 701211636 1250 701210386 701210501
    0xf061506050304170d02091e0126041506120c050907020f1207020424031a0106051b3a021f05070c0b09010e0d0f050409 53
    0x1901009003040749480351440c01c194031214008082031203041031010f40060003500700a642e42c1100d0100001034810072420481e5040110030b41000343c0401e000c1a96080e5401c1725500c10ba420704021540d075040d2603000d80b627a86507040105c050514002c5507640c1c072900402d1000c1c103c03240350542889080704500140c1000d05102d52400c0190010003998130442e04d5040e40310000c103c0c03d2122040c102d0302c1c2d803a2811800000e01414070f00610241e5440d0b50a00c0341031802c1d001003c00e05883c094008000d0b2005ea586100041c20003d20400c0e0000390140012030342c002d02c500700301804e82441002c49442540c9620814030701e20310301844200c1486003200d076001e00031004054407204002400545101c01204070840d0103c030081c441d810007140d0f103600040169011300031815441e5000900c1050074502104003e008001241d0310240301e105504c16446000d2140c43c102002043c0c42d6200b60500340750100305000b8220145070244801e14103002004000c03101c4002120385c11070906d641c04025007544 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 701212886 1250 701211636 701211671
    0x1204060507120501050d02060c121c110405090114180702010c021605150a11070b181e040e1c02010204150503060117220b15090402090c03070c0f06 65
    0x20b44924000b8140b4004014568030781c2c0034040da0a070152081c40c1d907891040321890070300010a08114207802c010a0301404002c10f0080c0c0204100404c108011030540140d4980e441c0c080c600c00d0988c0300035144010720032204984d8034030405900281c2000c407a2080712000010014045500c030300141c0d55104034141e229410405001c030f441c126151304110300d0800b0080f0b26003800c2000c103808800d0001030300544551103401050031381070300e10060383c05280d00c4004030f0700254842400e08512000c0c1c2001c0311080d1a0030100c0032100b40c80d0b204401c0503680d0b02014400a40800744584180e40584208a0003030408a03810b82c040032940d90005a656084c850038091803d121b038084403c21070203108202090740c01030341580610100b0240c1d800c0d195a8003032100b0004041da128841d00400c035468241c100921960800c1c002c0c0c0c03420003603c20b01b2960702d080c0824580e0171180030350300030101000b24040c401d581c2c0013590412103e250140807600140c5400500e4800030804407015503460342105800000314 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 701214136 1250 701212886 701212907
    0xc0d0e120a12150e040f0c033e281403011512020103020d0e0a0b0103060c02031e0309120c0d02071410030b01020c0d06020c07090908030106141204060507 68
    0x20350811042c0088110210904101e000b91203c650300074001c1000d001d101886881d01c0c41e80150a000c1f5581c41e46418800596100030780130250207280f03000312044d4080e4007190000a803c181e00d0060240baa1b0411038a412108401c2050b029070400c010201d90902c0081e4002c1e01134040c001e000c010149090508503182410032026680301c0786014094000e65220208050b82c0918000d40c8072128a0320070700040c0110741240005101e443c91600c100011442584d04880c0104810840300c04580030590b1648034000c182126404440200e9142c00c00c640007458100e1720300d070111a100c416805600496510100300020194821802d2a1840303a041111102a28032002d034990301203c0c0901141c08440b00d4006036003410f4907500c401450341d1003004248000c1c07100414901100750b02e828010029031202041003554001d074040490428400d0285002803a0300640c21031450b0300c0e000341124041654900385140c2d100030009800d0081d801103c80e409140117071000599030400510150054002 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 701215386 1250 701214136 701214167
    0x1d04020a050d0203030315040f1d0d030e1203090f03030c0705010605150d0c022a090c040501020303270d111902100c0809100c0c0603060803030c0d0e120a 68
    0x1642e0220060310044141c03900207c0c05000c025100c02c03850002805003d80910501965103064480a20181107441500303910004005840c5507040c40308088007038403800f541c000d215070302c4454034a103008080350055a00480040586065051054145007190700540c0c200e0042d00d8040382d1036003484002e21681000300710444003100031588040d40344966004004540c1d41c40c81d0b585100d1800c07240240940310340c40c1d00b25076228004100a43c03071040740080c105240c40c01014540c00040495104c00210b82c01c2c2d4105800a40c259568001c2c5900340f07032500d0301c51001d02a201c100d0426008000c22400c080e2013201c1e11120640032050141615156906901c0010380142140510142c0c0b90b60040300c000708144d2030101040d4140c1e0620403a203108292030307030790440c2c9003000c0d0340511076110000240c0c05105050b2000c1c001d550743d00072070654155000c1c0342015002080419807002d41d50004001c003ca0800c0085003413000c83e0b02d810b060003110280300c04a0030f00081c0310714035290311888403041100e1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 701216636 1250 701215386 701215399
    0x140307030212060414010c020c011b020d0311010b0306061305090a1208041202010209010c03081b0c0f0c100203032d09010501140d1104020a05040503061918050d0e01091d04020a05 79
    0x4421f000b0742e20403d60702c03164180004402200072503020111500080e540150030000068880c2c500240110141d40000e02d00c0e52800c0a841a030b80390110f82580140b000a01004a40e40300d401c50390010900034200000b103201c1d04c9000380000d2207421041e0f01481d1282c41e800000e15240c04e10904112100c0404011640b0400040d80541c1e085062004050f81500c1c1003903060b41c030303114240791100a2700005828410042401054444009071401e034800718042512561340e8060305000ca841080c08001c809a04184001084103140c00a01102c0340d07444a00040030704600e08200850070302c10f545000161751208010b0000c0c040032803400039406030942c1d0980c00f0758055103501d4003c0c208043c0291086400041142c21644a41c0c280c401070300c0c000781641c1003030412003031038400c40020b03c241c482c076a400c150036a40c4e44100949203040d0703190810082d0040e5a041c000031a0032105443c1080c0c1840728010340403450340c0c0c8003107a00f248041800251000c5041c203004210004d8400c0e4000c901c1030b807 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 701217886 1250 701216636 701216651
    0x40f02040e070e1e09130507092a02070501140901050906070b04020f15180303091908011a0a060e01030f0509160503240a0b190e090a03080114030703021206041401 72
    0x3112100e05c954400200000d03100406520300d482400c1070f11940c0300005450518841020300142000c1d9440d4071180c0302440d001061080740d05a886501c980b0440c1d0201d081d5041c1c80041e100094001c03e503004051614a181c00800000217100f0740100c401543e81460880c100400c5041003c20311149900c100c4000001807604c46080c072107807040c201030f02024120614103401da61010003d83c1c440c40d41c0101300082084600c2020701d6030300401d2052841540c02c290300700505074a13503444032401c400040d00105034541404000d860001e0031620160406a903111a60820310461044501848200014202e00d03004040f404d199035180344c00c0a0b119401060540c3c200d15850242c5030b40c00814000c54003800d0795810003031001800038205003504420002483e03001a407940424000b502d810301c68031007040d00d80e16400c075640c1c00c0e08a0001c000c02e40060042c04211054801311841c0200201203070940703a282d03404150070801c03079002100c042c0e11070303018032041101204903009019810b200800019 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 701219136 1250 701217886 701217889
    0x6150f05040509150c1b06040605040b0106050a090e0705090405040c0501030c080f06011b05010204081606051e160203070f0510050a0f051c0509161401020705040f02040e070e1e 78
    0x715000b03054003905e03410010b491494080200d55510404182005461403031900f8100b02020b4001101d086468200c1d0f4000496600d00660030f880541600c1c1e921445164146801d2000e854800b82298080c41400d000346030060751540110352081d44a4441c98600700e2034100090244e507003030040401840914010004481100000c5170381c01203013440e080c401c1400c4104040c0c8500852140903105500010340810342030760010b00d40f448115860001d01200e82e8441c41200ea070300400b040c11002000100385920300c400d10b60301a00700c40c81d500c0c0982d1084186036001a01c1c0c400d0f9036001081c91601e0880801c02440c01450101141d030890521070318140c2d205d100100350300031004d11074080c068042038030034005051000100c410b41c0003034400c10040c2060040c165076040340140403039028011540104407109951002c42c021380c8180c0003044101e0030310003084080c000c052502d10485a007400005a21280c0301c2e00a4081e04094540c0100c084d200003e114002c0c072210007044003001443c0410229 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 701220386 1250 701219136 701219173
    0x11100f0e12090f0a0810060e010614070611160309150305061003110d0509060f0912120a02250c0503120414190815010f2106150f05040509 61
    0x10000490303003542458120400580e111584d40c2100c001031080382d4801c0e4002900f81d201c1000e548454410041300c0e030380c5100c12540c0000303044400006003410302c28440010740a810050f120149211080c1c100440840c00781d031070503c0200d0681c005001804c080000713000d009141c00c1d03554014a024001890010007144030410940103040c101990348070620b101d10030300426940c1c150310a4074180141d041c542d040e143e6605003510503000040c210b030081000c42e20000350185038900f5280c0700c2401e0070401c4654001001c401450303555200d4081042206c8005000b011500c50b00390003024403001d06107810310f010340324015004180139a200080c403502180d1508103880c21100da006241404124240c04034102e10700707001d1038030721003594244045407241010a450400a00d840c04100c030684c1d9510709141003e01ca4810314110809c04030140c0c903500280100c03144045d000f40b00200d4110101c956190101641e0342c0683c1c1c82c5d891300d6100b0720032880c25006243d00489424018060a229020002c0c0d8 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 701221636 1250 701220386 701220397
    0x203090d0f030605040f09300c050c09042f150703031503030f030b01050909010506070f0b0a0207020a08030712050c010b130515010903051c11100f0e12 67
    0x780034040205241461194004401034403000c2d00a2200c1c4180710f000c8800740090341b004648095081c500c002d811003014240c020914018103500c40c400300e00302003c0c0e0700d48004182c1941c1074003507161115910f480b4044081c0c025485009103605a4a030403d0001c0c0f0035004a070702d107901101c02d480610a581c3c0c2d51501d00d50070581010306a80d10806860141c00900d2001111520400803810001c281500802c82c90b00306182520180b1444042e0001103034184220b202d01d5600c4400031006004a06140015103080d602c680080d6128a5440c0caa0200d88007080f141e062180350006003040031400c0c0b02c920b200041403018010340c1468040d640d900031002d00c6040500400c040411100d070600d000b500286071a010140c49202000ca41c0f05e24007000c5c16086941d1400c16180c50821115940708415290440c1d8001d80074010511600510f841c4aa840b40106010080f1210080e42e008905000d8100d040b1000070000a4000b8940505000d4511300300c80803542c2d82041101100401145007104c8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 701222886 1250 701221636 701221663
    0x118050318040902180a0c030b060f030612072309190c050d09060204051e1f09031403090312030105030a0611040807030b010f0b04061d2818020309 65
    0x284141d090011030010020403070301a522074256110f41010f0140400d9890243c59070301400d10070034901c0c40c0d0503010398031200314068100b2410009425410301600141d0782213800200019455544030700494907141064014190000c50340c4014a00a20541c0c40003460510070f50380b6241d07a2030701d000012211180781708880c402c192209404000c0500c980e0840d00481490801001501c10505081d00203400c40c0c050795000e075900d050000000c440304944500500d0000300701161052000d40141083c210104c1008180705542c2e00210002e8442562110f641b6203003c0216102ca030890101482e10702c0701d01d00302a900200f00014000c80e02c0c04283c80040c0c0750041404242d44001b64107940c00c80c490b80e41b254010b4003450001104001000110301c1c1260300e10a206850b00c0d8a82e9110803584c811031003007030042015802e030140d07510702c161108020420024104656180e503132030502000c4603482c00d004001083c01609000c030710310260f014454a20354010440c107502d00100010354440342d2002c9031 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 701224136 1250 701222886 701222917
    0x717071a0906190b18090c130204030c032d080a1704050c280801020304030f0914040509210d060602150a021c060605090a080d0c080a030209030303130501180503 71
    0x81d61a080042c6101400030440e00a07640390411b4159111001c0020152180b00c01b080029000c0159000b03540541b60046240002140745039031340c445000003012440140031a00c400d040700c0c103c8184040304201d000b1103c280c0d0360a0008402054900c050b0301421006010f02c00740400300d000010300340d0040e013043e1024120200403140ca10024040520f81407a0044a0f4101180720041900694012071094640b80d40141a100c13054480c082c00d406850180714106107640c2892400350006600702041800303840c0c084405040762a0640180411400110400950603035010400c5c46150b0003030500f803001c0c0101c1d460800e001030f00c07010054190b070314058010420f42c07050164400c4001203040c2c40c55040010941e00e0001400f29046498064465160b1000008031540081112107000086584050441007180c1d9268000d8000a46100815a003801482e1242d107040000314069124880a5000040c3d00c0c039182c1c1c2542c10b0440d01c1801e5000700c1900e800025800001c1e1818840d190030f46 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 701225386 1250 701224136 701224151
    0x1514010e0306100e06220f02041502011401050f090c03040c05120a05010507080c030a0f0e030d0609060501140d05070c0210050a0801060504050f0103020717071a090619 74
    0x485060408050041e894041c0c24140110000c400191604541c1112040c400a0313445d00100890040c6406001c42c109140380610410303408181e006400b5180354031130050405484440c03102d80c01e000c10700d0600141c0c0d0741d040d00010149481e56120f0040c0340480380d106803603038410040755021070003030700c00c464007500031010034100101010004060000030f401c5c070800842889070940e9825900b4415502c6501c0c00d0007040c0da043c4105051b5200f1000102c10b00d2454031140140390081c20030346450048955103483d000b018803000d00c020240940a0007012902e9400d28203c1c00c00c5031165489203040c80102d8540f1a0880b80001c241c800814010900182964940c00d059880c4900098029031009021421090b2641c101029010175a0b00d903480d90b00c207a803901c3c070917142440b80780103c6600401070b00e20700e0006d601c00d4009190765446580418500d421903070b8182d074680c00c041030442e00d440328070700b0000c112031480286c41c1c2c0c03048018004000c681005003c15141d9980c0039040380c041070f1a0b110 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 701226636 1250 701225386 701225389
    0x1807030206070c0b0a120b0a06140c0709110d0e060708180a0501020d1413051906141305160605030f090f0f06060f010e10052b0b0906041514 62
    0x1c0b11801450402c42c040d07928446108020403014202c1c46d20341d062840e06000070800d00313041c0c001c0c005603000d0741c450510308000c2d251052a40e801054144500e4800c095021842884c1c0d405402050182420250344070741c1403418003025607031226105400d5920100401c415242e02c00c0c01e00d5040502403034006840310a00071070714241030242802410641c00042d47c000100001d61020140140e4031a0003412a00e481d0a541c10796100c40c0005425a404420201c203c00b4003100032000040c80358034005080a042900502c0980342203d01e104030802204078401402000c1c004641d2803201824502005428100003030041d000240404508040c0c0d44001903031103204004044d2120841400c684444e82e101c40282d41d25101100d03118020340c81c0040580095008102c19601040e0080030040c09009030501154542c0021001c240f901d1047e040480d0700c0000890005545a03020502103a403512440903c40010320140800740580d1a0841d0841a6042c180d425800d0307902d42042483c4080c2c5040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 701227886 1250 701226636 701226653
    0x50411150c03030f1b07020f010302030c0909010f05091b2713090530220605030a0c090605161506090506030706020c060415020a0f030314180703020607 67
    0x503000796500c80001841200c00c10290203074403032801d04c20012403120000d0342c58074060290a40082d0000700120482046600076006107900807901c00886060140702000681001000ea00c2803504440300d1006000c3d504140030070a9114101c802040e690700c1c00d89102d044107108088600300420351010442540d00c00300048031441031801003550181c40c504010180003400c1005080382c0303510031341310180c0100f4000200000c60460b0203101ca0b06840500c0044041540300c95482d0f07424150300141600c0000019030200c0142059903074142d240c0ca0f02c1265681203d49962a03103050190410080114a60100484501088025440300c20740036629007281c4079910062002d0045013402c0000ca0a1015a48018442c40085003115030059541d0320036a00c0b0b903400e101254200c3d00801c02440b101140c5180c0e5401c204040c41203030b2211403541c50b0402c0c105e00c23020342200081d496100480580c0c5139180c9480d08040c3d59000340703402100c10110366903121590704c00203001d4507010944900340500138 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 701229136 1250 701227886 701227897
    0x50c03160c06150e2e090f020405030303010e070809070308032a16020109120b1308071709030d02070501091802070804030f15050f010b0c0a02030706030e0d0305041115 74
    0x401030742c2081c3c4075001c010013180e0807928092000c1526601c218000f02c103000c000d070000705c10180c25030703010700705003900f00580003e20324142840e40030040041c003030314100002d50091540505441ca40e0418000092005e10040c2010b09a644100410710205000c2d0b02101e030844d072021060241c080d0102c00524036825144070034800d40c00c000c19003840f0603a805804400c0d0604c00d9032560304503500c80e000440807050315400917040c00c11903000030b810a004250001e100500030b02d8404e00303103801a51080610107034901d180e154010003007803207240c80c2010070100c0c40d40071080c0054034106003418002000750380c051080b054400d02204040c040d54160380d0450380300540045034555510384a0408000141c84201d04486170000c203240782c28040304034892035008107480321600072107904c0c101c8950201e400010061802d0f0144100400c0103950400c00a0003d00d5103480c0416500010548a810180007101c501c00f0f240c189030030000007a2010318001140c0004072500307100da84040c403034150707103002c0e6 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 701230386 1250 701229136 701229161
    0x80703050303180a060c080117012703020a170403120503070e011215080d080c0a0e09070909021c18020901032612061003090506071d1e04050c03160c06 67
    0x5003103000c6d08065202c0750311070694078125150000c040c0010005403c840301400f03440d005181c0460700720341e440000300d0140d0016009104032080754400d600d50b980e2003100b511007464200400607003001003055050090300ca40c00d0030304102d411807504920281640b0700707155505040225003000000080402e601000c415561048400c55080c0c941c690180c0da00300300041400810110000100300301e2604040705c040020340da41d48003800240b2010b2110529019000c40305110fa0000003007841318203031002d0000e074099010002200d514181c140d0302200d07031191290040e150780c0110100941c64502d00e40d811a54486406001d80c402564800305100c0e2480c0b040640010001d21a80c541c80840f007582e000b01d00c00c0f5142002c4510240080d01100c040c3e07603000b09650130548c00a6003c501960505102001400400001020b00e000082c01030111030041110304030907400118283c2494410603900002d02d80c0303520320318140306041c14031070600603031410304020104007840704022658021010302c0c4030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 701231636 1250 701230386 701230391
    0x3042303070b0910091a0403030605090a0c0801050f010c0f0503190203120c0310060e0a03020402040605070501060b0c030f0c10092a030c05191e0f080703050303180a06 74
    0x480d49000280b0304802e5848030f10328810201a0240580c2d03034803035210050b90009070744544c04050b800d04c102c1c00500501c180d0905a8a440002d625141c690f000c0c3d01c1080c0c12600000d002100040103050307010181c00c110300079950082c3c9030300142d8000340b120b00c0300b13900110050408152454114a140b140e108124040c0001c955903082c4180c00002070b118003814242442c40f20780d00c504c442c00c03450108903484449215009800c0000c64084c10214107003a00282c00038140580703c0d0041026680306500c103000061000848000303009080c401e500141c20095403a61620040c2c151040d0f8034020140300c05441d08000440420640041260054020f00e01800303001c010018107103c2c0300c0224646100c108414040904c20b0350700307000074045042d80e600911b4420014100700510400345400003030050301c0003103072502244031b81412603d0803204072a01208441035040c04842110403242ea8040f1401d41d00c0b4040c1440000e101000b0780390712030805d03a108410404158080c501d0059100c101500251 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 701232886 1250 701231636 701231647
    0x1201c021206120105090604031d03071e0f030203030409111201080307120201020a0903060b0a050d050304061b052802060703020109060507090f172811060307020303042303 76
    0x801c1092030300d02c128012510100d6036440303201d8003030170380d03d0848140c02d540d009040000d0001e4028440d0403201c00c1e800c008009132442503404a0b107170a4164100743e92686681c56000500717110222040081c0204d580c03101c0301240380d940880e0b5203002c0d600a004000341c039805601e20504400f01a82e032002511200140c144d41d607000301c1916a07100b0078007918800303d454001c1108a0050003110303842241076031181112071039034455600800b8000306e0141d10001d00b4000060956070040d008645174091006181e41c1e40c90503031b0242c03a0500c1106040c0000d021043c440002c50b070007103070700310015481114948424014040550081c0c84150000750700200100710003050650550104031058800c1c01d04100d2a01d440b40141e0700400c080c410b1024940210300c3c103000390524283c4801d0300c094580101c500100180010040b01d9041076103010201e0b030f044403803105128a403683c80d0b0550a065031031503d10300b00034400946034400104080d05255920349403203040001300740d1010307002e030b100c3e0305072030303d48 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 701234136 1250 701232886 701232907
    0x509190b0a06140c210a021204050d230f031908040305070b060105040306020406031a0108011a160227010b12071d04020301080a06050603010c0801032d0308060102010e01201c02 78
    0x61b0014603942c2d006125000c501c420f844a110101c030151400101030668521466945842070500e1803030144040410694811040030100300141d000e00700f1001541c0c441e10080000300307002c3e030a02410010049041d0074400425001812a50b002c0d0f00003409840d00e80d21540182d4592149500c0140f001c0d10008001401c2030745548100200042c0000604481c0c40010044038600c0d028019184203501d029140245105004000c025143c40d151754013025005540028490414800f034113130400e0014001882c01d4541209114098480540700d94101007a0000422003444000c14075401e01c00c0c40ca941d054140642c0007010b540201c0200155600e46c0c64404054981c213201004440315070030a400b042003440c043c040d113034074001c09079079110142c0c0c6940c5540c0c42040c0403448200006560140c280348081d540703c010090075002c0d45a501d09814000002401c42d071141c0100b408a9142034469400465584a01070030403411080c45501c40814150f200c0c2040c0110345030300342c468030011740300703008 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 701235386 1250 701234136 701234203
    0x60f04140c06040e1e0403020c1306030f06020c070803070317091c030204050a0f080d0e18070306031a0f061201150801050403030b01080906010e100509190b0a06140c 73
    0x1964181207001290054403170528000d80c09650060240e04044158242802c0101c4202107500c01082c0100c1d03841d03641c0d10b136105000303507680c42500c407540c000450504046040019900130485407004624056070341d00e00401e0414501c3c480502c840441c404680c0c0408100141d03040541c0c0f003892590900100c0b040075000b58010b103d00c0c2c1c003914044100140446042910200301c40784c02028146d5149071100484071000d00040707840e8000503011800040c1d102100c48103100f40c0254400123040390a40c18460300003800c0151280000d014201080305032982c19a0054215100781e44000c40000b1482c0c120b40513110a407242c01002110324030000300407505410060245000f51070401482c1d4044004481019089409500c0340c1e00541c01084144000c0020545c80504555a0710300c00d03441c3c10001d1242001a951280011341c070700c03001e001c0c40c882442003a0040c00c007121442d00b440c1ca0110050a402c1168048041d900380108011007401404e000034143c041202550904844814030003180c03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 701236636 1250 701235386 701235391
    0x2091005040b060c150a090512030403020115140d02010311070c050f060f0a0507060f0629190c141c030f11030103080c01110f0912060f04140c06040e 66
    0xc1182080044649070810b003080300c102c190b20b00301401c01c1181050300014022001b425122a05030303204250000305034280042d4546583c0c801e0078076030b64102801c2c000d080d03400480076a1194005410104450003072211a902600020b440e603021390b2445000680c01070014403103401d02c0c800000b40d0b034810022103814000950300115420080308a01100388a8640070300d241e00076049108202c2000704900a9000d00201481100c0101d42241c00c5986601510050752143e0240c50300b40501c0c0c2e411034030382060b491010400c08040c5040c11002440b02c40c0070001015800c0074000d4190b40003003406403e440c600074030540e5600300c17640f01a503110700081011414250400091820158110908030741c0110300072010001700603415a421516804511390143c0002035583d961280c8024050802030043d080c003521184055448510300320070f0000d02c1e25031085401c00c94000c03134200500100c0300080c81c2c1c1c200f5040f103818400303010010b44882c40d00c46018025a8004da02090028040320f070034040b1031 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 701237886 1250 701236636 701236639
    0x140c19090f2912040f05070506040b0a0206160212090111010212040b090109020a170f0d0305010503010b0a15030b13020c0d1e0c0210030f1b1e0504090209010c02091005 74
    0x162144400c0b82d002d030307403030140125420700151880013040109680700381032034049000d2015214090340c2c0c0c000091a55110364818000d01c0d00100300340007815014820903500260f0f01003e102019070444000b0746401402541040d100408958480302b6481000790380100002540210b60b035401c0064908803d441c21034045440d10b01c810001002d40c0c406014034000d0607800341c400c240b1541000340303400e91500c0340d0141d2480c0d0310802031042c08a0004000c40000500d03292000201941001d0505095922001c80b031ba02502c84148204084800090109503203800c82c074002400a042d100010f001000070040750034024008a105403d5200126510150800325254440d026500400e00c2031202d001d4081d207404607003402d6807500035042c100001038100010389030020b41d94803029212400c03588041010313002800c002c07184800362508a60454070b243c0ba11603502d9100005010000e01030310590040d880050740218941c0d115900036008503642c41d80c020700740c844915001c004103551030518032415 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 701239136 1250 701237886 701237939
    0xc090906150e070e0105190306080601062102030603070509010e010e340908011e060605030603061503010212070804110a1503020c0a0203030705070306140c19090f 72
    0x1540041c1201d450200320307201c5080000c203039078840c2c0c01034410300300607001d440c14800104203100501540c110303240c01d11000c544000500318200207007103143c128140c0020341400003003100384404008044514640162100c0d0269403030b0350b60f80201b4140142640500d4022321010004141c0c100d80d801903905940980c030418942d40e444d07001140d090408000151140c000f5420040d010380c5582004414a00e25400c040418603038583c03189003100c00c03420302c0c426141c003010f0300e02c40c0700d40142c0a202d0090042c0c0c0740540c21070400100003921800702404d050010404292640180d441c2034045e01c0c081d03031103605280001c0c60410800b0701444070448085405085c140405152450304884000075109d80b00841191804180c41c1a030080d4445d071007440d4284544807004c1c006036010801001101d201303102400c4183d28500c1c0500903601d90000d84400b00a4403070800910802440607a80440703280c2864192060ba00729060340d15200d50341020074416903030200441d520f058100002c905a0340010386 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 701240386 1250 701239136 701239151
    0xa0305090703020913020f15040816030201090b13150c02040c0f05030a18061a180103030503060d111005180301050c0714030c010c0e0f0f090a15030c090906 69
    0x4a0300c9507414000203600040550115405c20303100c0f524038030782a1001e0b062951000100c400900d085030344015803401050002010b100300c2c00c05122108154180512500d1610b05541c0003030b100c040e00d4046c40c9084840440c445103000b14039090400104000103034094200d03d6200010841d41c02e210059004504181c842e0b0282481139105504903552651240d003162100304007480506500352900182c0c03483c909101c13000c07035002d1007009507aa9003500794840c1504040c040c0a942c1041300404240348203208010804690402d084980c403880449068100b580c5d6403402d00c164034606100c07240c02408000c000180913030004000d05c00b04244d2558441118444810103082c1e92045802c0040140d00744254000581ca0320f078001d02c0e0484000580342410310b02c01030302e0308403184071a44800064011600c904139062401800c40504815903000e0394003000c00c80401c019002c00341403241c04640d203c402118412842c481003003e942e00029844082e541e586039007004e0210028160f903e075150005 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 701241636 1250 701240386 701240401
    0x501060801060c030e010f020703021804020120070e0c0412030c020310020c1e031c02030f0f0c070b060f060a050706050106081006030c05040909060507140c2503050a080a0305 77
    0x4183c80c642c10ba0381d62104034802e400450f02c1b80300e15602c180561294103c0030006039102d0b0071102240c11104250515450301c2d000050074070044501d1030703851040c00070302e08107400004186042529089103000c0c04035118090b0b20011881180d00036408940d51400e81410540d10040c0c901c42640214115241402415000d00c1280f045164608080d440b4550074420300d2400c1d0124a0000c1400c0140c90074105103206842c00301c85806030384401241c1c004100b0103042060b1440355004542a0500105450460b01d088140c0c41202000f0740503421400000d511f581d01c2444200103c02d01905a9444c0e0219171409409a04205401c854890505e0000701e01c4a03c40c0c020300b40705140e900784036120545003a8040d0020080c4002ea4410070500b0803011480c500f0238003440d52618030400b000911032170007031700090200161114400c001a0100032180d03403603600041d4104c2c0c11068170712000e2110200c5c0f484a0401d0010781c00108a8081d45441d00103000070100a850400e140e524148030b00e0381e83c0c45 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 701242886 1250 701241636 701241647
    0x3080c073509031e030705060106090317120705030a0608030c100e06070507020108040804120c1509050f0609010306170303160819050c0c3025051c0201050106080106 73
    0x4180f50903602891040350700d04840b02400050904003010f491030041035440e0941050000d810010100e500d1003070810400c010314100310b01ea02c001070041424424400480c014828010b0300c6803040000101c0802c0e01880154040f0b8001c0c10b080044a43e2403100c2e401841d280c00c0d6110103042e019180a0000e2a40e201c003041907442800255030b080c1c80d00300075600550b000d42c00a0001c0c4c4030560140b101007024006021851b4517140142c1100d081c00e0310b041494521460100038043c108920044200881c1d10707822a154040d003000c4500984401030000124001c05a5501c01603c81c15424206014008c000c00194050040c8000d0901d00d60024002543c030700d44190760005108010b0350b483d000840080d80480d402c0080d496545d89031229400515180660f0456110406600b010035010ba0404050311266070b0800c0e81030b500d013030020f641c682e421034004511813924031841c1c0107d010b007000014086a0005512140701800002c02c91000030f000304024042c4034085101c0c14008140140100c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 701244136 1250 701242886 701242897
    0x9060b1e03030301051228061b02060406110f0301030c05040606020d12050a0b09270a1509020303040e01080106030209010e06030a1403090402310308030403080c0735 73
    0x2a000b54516441c01050010041c1610040481030181c80c0041c0300300e078608005044003000e014000c418111060910a0490304032102d103501801000c607441225640200305030758030540000c00012828030070b03804a412442882801c80606600000200820091062490648070152810084142c840300103036560985004010302281241e0440101c0b6040c941003a40d205504480100350503000c0d102051070203d0a84500491665074030688504e0000c020b01105442c269000814120b0072a4940094460302e41c3c800e462501d0301d528104055450420445008025150181ca141c0d80d552807011300810850108038131618075a40001041604403140d17a0042d24010b01a01e007000060361946644c0c0410800200c0303d0100f40311140c10b541d00c40c4082d141c800b410f0860780f54010101c0085098408641141c0802d00020f10824004210282d0940e81e0080d85810282e4403a1100e1405010500810100420ba02880040e44000700200300161800082c5010b1000820300354014034034450040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 701245386 1250 701244136 701244139
    0x10305240a02090a1203211503082a0a050c0102120d05341107060206040b0c0d02040b2d161109090604121e050a02010e0109060b1e 58
    0x14000451400600756004006141000f014858a0742c1c4d20f800c8103083d000b61440a401003051030403d03070380c0c00c0a40302500040720200d01081050702016540e924101d4a1400301600d4080042111030811240c40e03440940c1e01c40f1012004103400a035440c990f60340c4050641142d150264a5030308056500014440241c460940c0e1902d0a1400d142c0100d00245401400c1c40b90000d0b5040c102103050100c8469000d100e40042c25100080d400144c001c0c1802e11003407080c101e01d90042c001004110750218103141c105500c204080841d0b03c5861210400d4080c541e06140c0c074510024000560f1006140207000005240c0040045601ca82141c484060b442c2061620626020400211070455014031130034a07034440c12111202c45001c0b0046404080c0803100442d443d4400001d10003130103000c141491320040d962500f541d0300740c0301c461162085941c0310052810700c4404a60190303002c2c000c1d00080c5141e0f8003000200988203c5090800141501b02c1543d4040c3d503881c0410400d060081280100b103800 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 701246636 1250 701245386 701245453
    0x216080304090b042c01060506030f070e01090312120b0102010b0d0b07020109081201060318110904031101050708060111010b010e1509101116081c120f05010305 71
    0x1c2c0030002c070003500200345034540c06030b41c1c0d400000c0000c0400c1c41000d0000d04008040c250780c2d59444815085444d01c0c8c228510410040c030410002c505141c0c0f46983c44002460b12015803144400140c44140c1c681c0c0006240d454003000c11145280d000c04102400101120b0a00800c40408016402c0300c05a81c00b040c0c000064000400200300c01d60b038525007143c810320001515030785a880300e02c01da0b081b603124610350001981c01000041c2c0d1601500300010b404081d014503103e900c6da103031800c640f203158001d40034000b2180090141030194000d03140803c4820000d124038600320100901340c1d6412502035000c03c001001003074046405116000e03400304107849011440c413000c4100721820b901488440020701c1c1c03c1010000648a00d8262038048403251a104101c0039040d9509013040c0b0141d4000030030300d60010302004441000181500105183c24031003038013410a5404461000580045040c2542410940d20415070140e00040c100d85c0100242d80551801c0e0501448074403070441c3c2c0001c8901c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 701247886 1250 701246636 701246639
    0xc0e010512091204060e101404121106120708010b031e0a0204031704091416050d090c060c0507090e1e030705010504060207060f092001020a0501050907060216080304 73
    0x8440c07040035034018507a50103c0d0890380d00c2001004480d401500014009211502d601ca81400c240f084080c4404e03050400e41584001c000da80e0025008511441c6480d034105e802c004240803040103d0141c42c0e6000d045a0f5403600790410000120f40142c80c4940060003600c00041c1c80420201640d01480d02c100200c0300402040c07040400b40341d00a0002d002c81542003000000042c1b214403500c2d420706d0902c11a9840d0783c6484902c1c030072200c7c007582d01d4040080c40010030942c020350460310400449203040c56521003282c2400740c002445903260051040101c010082581500480062034a5200380304481140f61508090410344640c001c104180d6417241070031205079146801c0ca0f81035a80141c3c200c0742800b006885180c00e42d9026a41612816400142c400502040c1d004052400e50001000d120080c1d1941c1d40c241c0b40824014a601080003144031429941e10900ca084101508440240b041c0e007800741c10707661240e5003880340501602c01d0700720040c1602c54620005086814000180d070506 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 701249136 1250 701247886 701247907
    0x30a0b0621100b0f030a050601030b0a0c0c030302030705160b0105040e010908091c0b160f05090a06031e0504050c090601170f06040e0f0d18080a1719050c010c0e0105 73
    0x104541051213030b218290401c2000561410004403c500f40942c5c02010075501d5800e04000c81440075240f090b84a04080c81506040d4004040b0f030b00da1070741351074010f90b00e41c1e0b20034045910b03004501d0f6040d0354208060200040c0185200f40c10705071031040f1002c100e50304020140d6800c843e400036004240181c02e0002d80d400e441c3c4100109a1810103a1840011111940c2c800301c2c2060212000f03001140c5006016204960090f51102c03100101d00f0700074a044103103000103800302c03a284101002c040d19041080303a103501d0801d40ca080311408040c00c1c0001d0800c0d241043c0c4603001455071034040c0321843c0010b800f66109410031502103c0300300207444c403903c5035100c400c485c04000308030340e13000354a64a400c15468010028072643c0c40c00b80018001d00084090000c1000f80c80d10000c0c44601003c550900941c000412101401a400514044200207074103084031a4012500c03030507904404a4070404259400c42c0040000c0c03100c1200800000c0703282c4c402a00c030112005c08041c0002c005000c11100b4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 701250386 1250 701249136 701249141
    0x504020702010c1b08150f0f0a0e03070b06090a060f030b0606070c08150c030c1803190302070906080102030f0a020d140c04031a060114070809030a0b062110 69
    0x1581c01031512203403005035516440500b010f03404240c0340d84c8500c40c1040001c00d03003d01c0300310840a007200d210401d504107030110b01315a0744041c1c0081503121600001c240a0607003940a004036800c540181e80d00d070500c81c285150313603040440d0f100380200c4280c1d0010b601008030780300708001e441541e100c090a0340d00703585030710f0030003240100b080c0d800010400111010a80c05a800d02c001c4c05040c00400042451004101d04050058844c95000900748280601d40c0300d20070650741c2101030f640d064928050300d100024075040c16000c801c40081030180603d0189507000c108041510051701c018060142d40350b2245080380300480b24034050780c01410100d1140d1440b50014140020565008144000d684022860705501070301d4494103810002010410011202054580d40701c0c601c0c007055041c0b80500000e411068404090040c44000080220400818105403020483c01a04a4110502070b00e0080300c00801606e0302441010403030402180c103402501c10010420035080a072050180b5081718101 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 701251636 1250 701250386 701250397
    0x3070303050d0917030405190c140a0b040602010c09120302120d1b030b0f060c060402061e04090b0f0405190e030d18060e0d0804080307030605030a0507061e09050402 73
    0x8007585914081001c1482da05514131501020803000b07035281001d103481032034010580c0030304943c80b00078001c51010440346902c50084808510000b401ea400c2040002e18028142d08400340540c1c000c1008102d9950550003136020390002d1321346100c081d0310780c50313014411414120000d0060340202110303c10b200c05c0c100540003400808402150f18424240d031700f111040038040150009aa44403000c405150800b00c40d10006016142c2c20b1500b41c5c3c400c616612100d000b800607000344400900d102000c044102c40321002c03031501000035110f686451103c009400710400040c890100c0700b09040152400c2e2017014014241000b1001d120710030300da507403c060a50012a0070007030005101d00c00c3e00141ca4000d101c0d2141b245107000300031010034a000c8040310b400322049c0c0c00561051700b88000f0700c0e400c1540a80c20a402c41c00d000d460b82d6862008902030074550304815018010024290304000b0001010741c00d840890300c4000b03001304a881035650a600d03800c25a4001030403c4810045418564000c04 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 701252886 1250 701251636 701251657
    0x20d14060d0c0320100e09010f12060207020607020a080105061f0f0f021905150f07080c03151005211006110c040c091401030209360a0603110405060307030305 70
    0x41c02c104480b0005030503030001d0401c10b020917500c1110981d149800c1900d1405456061034800127141081f10f0010f094010840080102c2e60000f00c21040d5038540054628159008100c02e1038503444075000d40c042c0000b5940300e8042d18454407006681c444161510a008900d0394401c03004e441c83c20011100007020303541c87c20550241e0031800c82c1461b084000080710900941c01000e0007003442a21a03c81c140c010103066104031182c06205505a000e1221500401d11600c041d8507030311001704d01003151f10140c0d0002e9001402070a001003040d04100076105020ba0b5102c580380814003e01040d1112204850303055082074090000c0c07003001d00440b000075100000d18129101841600c020030308440340c440410020949180b020411484500ea16501012080c60158105030800001c01c4045484120840031805da0b002c110402140c03981c1050602c0000e05230b030210504001c600c0e03a0003403070640000d8603002c2d4040c030508102c4c01c0c14040c260007001c014008155041c90340cac50031540c40d0806400c20 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 701254136 1250 701252886 701252933
    0x2030906161401050c04210503070201050a031506090602010b0907020715030603061103100602070311040b040f050406020c01150803030c0c030f27040b13020a03020904020d14060d0c03 81
    0x41c40b102c8001d00c00d207880740042610190391181003900135084c01102d2406103010403103010364800080c40201c150340c00e0300c0e0b080c24000d841c0d00009070281e0180498800320103010070050030005010b588108030804503001a002000b0070190072051000518007210441d015034000301c401c001c1c401050403026007111403860f00240b85600d1b80c0d078440c103582041902204004d404814003a84c0340d59010807400428960000341540343c510303a035058001e0303e416020340c07240350796110280480e11603400081c000306a40e04101300c10300c0d00b494104000d4214040b0500039600e4200c0784051b0409000514003900c00b29801113082d513481c00042c4419604c00550317000d0760700041c1b21000c00803001001070490084c81582e40021400d5050030350201d00b007500b1049120340d0501c0441c15158403061207400b07a8110524002d41c1e01c8280c1201034020b44159449a900940700250080155483d42c1c8407501030045510444501d0b1a0903040004400d1456070183c00800068000c0000808401076000c0c5103c07800c20700b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 701255386 1250 701254136 701254163
    0x190311060d0212041a090d03021309020a0306090b060703020a0206130e09030d051b22150c171c180209090a030207050102070f2304060b0d06060203090616 68
    0x10a000c0e40c01c0b00201030148000e640510080244604042c9100d000e840050b0034035280801b0846e641e010903001001c240365002807a070364072400031440030f0040c1908050130b56903001c0c13034480100148464840c0c001014a0082c00d11141d2500318201d65291341c1550003400009101c0e005c104a9903c03001d00301c4084d440c410400216038000d00310541c4104000c0d00a5500d07400c56541d1507095030b900500224030320201c1011110360354803880c29500c08030007001c50301074076041c0801400f07105030081d000076000403021f40882e00f40310352001494825620480c038200030320000c2119100d16009a6842e1960a00c01c560500b5400c0025032080c0011440d03004441070400c480c1d000300b41002010f0740c020200350411042c00341031640410a43e00240703070030310090481c2d80c0740166543c0380800c41d0141c280c0491136640d0b04400002481064000310000030001c02c03480307981d034450388050323840300e020710300241c1c00c3c45000241070380040140d90401501400141ca80f00f00110b00c80001b0040c0002269030f030301040d40 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 701256636 1250 701255386 701255407
    0x40b0a0504110a02011b09150228020f09070e0105031b03010e2202010f050d020d060603020a18060e04090f05010f0b010e1c080c072102040b19031106 66
    0x462401c0000d070b40000e0b0b038036010030341e0003420f540b500748000e2500c100c0310b245542442c0c0c4c80100c0070102c070300b1610342141556030f140040b828410440c6c0041d5505401c54480201c90701e5450388106103510880b1000d0303421003050140804a542182c001700802d150045004d42c030f5000c0c030001d580c001c0b10b031100035000996444e049006a0002c0e004901c040a2800410103a040d07540350308140600e580410a40843c41507000803c21152251201c0030070102080304900282c06406039000040d12220600c4110744524004000b904050810300c0041c41940054850781e41390304000080d2002640c4072454512004d003884080c0c105084121805001c002050020075030a00c510714010180d5030b40480c4580105000400350082000f5036881381e001100e140c181c0d00b00030030500001c1d580c454a1a600e42610707140312030030b15546911a0041d251414420003002c0d072110500300d0950b10031a42005024508000c3c01080030084619100b401c0c403a0005002040710200440b00d0340c1c0c4020691841c004c0ca845 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 701257886 1250 701256636 701256641
    0x7021e06061002120a0207140618060d18050c1005040e041709060d05090f0309011223090f10020f0904150519090f050c12060118081c110705040b0a0504 67
    0x131072400142c111007c00e0102014500107205200400c503016400c260544d180d100c10344030500700035441400300054664138406075070410f0140c80c04814441d82d4452040c10300684415a401c074081c8a061003070301560300c170741c0903c0c01d44040d00c07016030340c000c900c1e50b0343e0307a585030007001d80c4050308924801488101c41aa07074403002018115803031a404180344c03c245500501d4450507019600e02c0b03800610060303ca40c0d074841c1d0445481c0012400125600b401c0d03d8404079080e41c0d000302030082600030f0003046507c040000c2d095044407039103400c946805030350000742d20032409030049811894204001c050b05038609500003840f202e84030051000c2481e03465000400010282102c85c2d034000714000200106203092081549401c020389003030096240c0344500b0b00240c4540d81001e5254502000402c645034401d030340c0c4941c503054242c4050b4030162244600c41d0b98000fa08810212207181c440c07a51400c070f201da03c0400d187d10181d00240030450030b1804100150107800e4200e40c100500c5140007801e5510760 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 701258992 1106 701257886 701257897
    0x30d03020c0c2b0b190b06041509170c03060a050708040803090c1005121602030a12090210081617060d06091202010507021e0606100212 60
    0x210900480d000c1a01c01006101c803e014510704101d40c24502c00c1c000c0a40c08615002d109214580d0707429654007085d242c0d007250b010300040140720a914114100705040e401d0208e0290344903d600071104000401d01e06c070b40da00c201d503803400d517003814030150303820681098061000341b600380b00141a45001600040001c5030001c00910a0b10007030007101c2e099031008001803041040644002c0490b0044101401d4000c820b0000c01d080e03c81000248441121075000f0b14103104916000b40c400205500c2010ba001da02d9000400050303940140c1c83d840c201032601c0d0001c0900b88030000910340a41c40300c4000a006001d4190b544566410800360303880b540c100d40000b50181249884e40152100f4000140b404560b491200141c5806401c298441c0c07800f6800c9032a0002d000a0511140c61440c038810207503000f02c000b29500d41400c90700f814016a0f0340c012249910351204006001d45e201 = true := by decide +kernel

theorem cover : BRFrame.Cov 701079136 701258992 := by
  have h0 := BRFrame.cov_init 701079136
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701079136 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 701079136 ≤ n) (h2 : n < 701258992) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
