-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5121
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:48:56.28975+00:00
-- url     : https://prove2.me/submissions/a93c331e-81e0-404f-a32f-df1f2644c5ee

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 920863309 ≤ n < 921043165 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 920864559 1250 920863309 920863357
    0x30e010c111009180e0a02060c16060801030203010f0b010c0f0c0b071b0b0403030503041511030a150e060d020108061507050f010c0c0804090902030a1407050306090c0a0b 75
    0x116a14142c4030903480c0c035203030142015200c80c0f80381512003210300e00c542402e84141003141c001c500c1a40c4103034103695003034a0340702d00104541801c081c9402c404a42052101c001141a8000d2400341264000e800801002d11070010308410342d800d4035184d0f4042403030314404800180350207c076000d040b801442240c150170340380d400040d0647e00a80c025201c08044458100c00021020103140c0208110240743c3d01e040d15542d0301409500000700060407180b000c100d1010307108455040605115819041c2550780e141900b401c3c402003040c0c01d000d60411055007070204546000b005104c0c007410700103041140014055004444d0400024019038008080c0c80c614560085100080d02500e4802c070040c1c01d80084007002103084440b00100300c000c2110100301036010680348801c940a07178003004004280032019001091800f421003000510607221071481d0402030b170b000f047d403070165041241035074070fa03403642600c40d90359042c04a1007c0d0b0102c0000400c1000204c804000c082807025512582d4642c1100 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 920865809 1250 920864559 920864569
    0x5100807091a0a09141c080c0105010303120b0f03060a0c200c01270504020304050a1b0f081204060302090a09020a050405043b010b06040f060905060403030e010c11 72
    0xc210b401c81030a0001c1144448140c000b0040d80181c44039145c07a01089420a00084101c0c00c030003000c00d204048441840140486001152080f00300c40f002070220356560701d40140200c3c410503602810038038001422100b4604850795010b181e038000d000b014591200d8000600404480b51200f050100511020074460a4061701c4035502040360043d207000b06105d4005001e1480c2c51030005100b000049903000d0489102d05240c00740c40b01500c0058580ea260302d4814904580300070050400695600d99031541e0002415541c01d0b40c004092114405685049040c0d031120110b8000e580004144018442d01340b02ea406060744410043c40b40c131410f40d680c1d0f11700040f40c0c8080c40c00000a03000140501c8682400e006030110b0303040d83c82c80d103800359480040254018080c030101d110081c10001400003e04403d41000c140c008004100ca940d039650346444620b141080c0c41210003040c0c000e034000810f03103443d000760f40840b601030322040c01d681303280d0300112045a40c1440894842c2800c90121035a40c850b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 920867059 1250 920865809 920865839
    0x20a0311030c1e37030e04090b06030c040b01080411010e0901030b04030906050f19090b0f09100c080a18090e0c0a150e0103110c010c1707090510080709 67
    0xd040ca00b804010100031800f41404844041940004c90071800c90240d010000280b4003480103000028403600d945107002c4440d040e0440780e07035511605045c4103c05011552070801d0080000300c084400340e8807550300340400d4980300c0480e81d020509440004010a4a44580c0c000440051409601c02912080011540402a00701f0b65950301054100300130550440860005840e0508016042103e81d1803140076511645850083c1a052140b2413810640144518000350040490b039517290740c1500e5800e1415000366034540d200350640c10354103101c2406160780b803401c25042100a40740080d07c0009a5a204005407400e0410341403220006c2c8a040d20712810114403000d02c042c3c02c11020b101d041240000d100d4201e800b502e0032560252180d1a08405040c210079000e0902048400422032522828000c603c5561340315402c18030300f444060303402041c02140a0100903001000c4d2600708003156040d2047c0541c90704a06290311014005004e0614a03901403001d160240c500741e1288003007840419 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 920868309 1250 920867059 920867083
    0xf05090d031a0603072f0312130807080304051903030c020c01080f01170a021509100306050303120910150807050d0503250c0602160e07020a0311030c 66
    0x31a10600d6060190386031011101141d02035010615001500e40d1001401d180c09104005070891010121900c41c1214420b241c3c680c01030190061080d036481e90700c50201c44150303126460003d084a0301279140347c041b00e41c10030003103420154950743d851016407001d00b058a070b61094241c3c0031540c10b00d110505010b503110743d502007449889010045c0c40c0101c0c615806060016181c00c200f0025035031402d003070440d083c980c29200350703010050032a42048004803003e50003201c0801903280030003610008041402c0c05442040a10040d40c00460031102c05024440d07160f0020480c000d201e071031002c07486402040103c291503130010000c150034204c90040350001c0c104101010100040c45041c0040c3c0000d00098a04502c001807a45c1c45980b80d128502c400d51017941c942e8528080703005031407000c45c1410f40c4800c0180d11591101d5010303580d07262001c1da07403644190001c404200307824041704007070066a080c0c004002482440c3d0b401e44141c0301c00341c08440b95100601502803036450822003405240 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 920869559 1250 920868309 920868313
    0x3061104030b100e010602010504121d12071403071404110f03040f02010e01052a0a080301090515040b060307210207030c060b01050301120b1905010e061905010c0b0a0f0509 76
    0x191400e45004e940c000160301031070541e403400e020400400c0307210800d90900d0702e00d46441c4403002c01540600f440c0c80900006c0355001032415404150101000401c001070f240704403440040352548000b01551039006000350420301005030056819814581c000c9054440ba00c002541805600380d560001a00115000c0d5090b8098846031000c0d0b51b004090040300e00828070b0014540fa0100902d84196441161440e00a46061000044c410800d01c841c0700a20707030000c1c0e01fa9a035691403940501030001514103a00c10002031042c1d40c5145014410080d0505001e41581d0030765a03820320030b44946080c8400901141c0104074054082d6010748001c114042c070035122034400b80030504100d41141c051914040c180002080180032416004180d21a41544007000f000c056550b8003001240b0044950321800450810300041ba030850b81c0d00419108207815a80d0060801401c2160105044a84100390115a01c0200100401c200d5140f086d480083e045000c0b40023144248054112107080310703804c00c55 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 920870809 1250 920869559 920869591
    0x1009090c02100203191a0a03020d05031612031a18060f1011060c041202060f220816150c08040312170a1a060304050c030f03030712050108060103061104030b 69
    0x101e0750720440940c6440382c4100c46c01c01b0741e0540411901d044500002e40f00e5640c0700c150800300310b41041100d2800d01422401c56242c142071a240781c9038407420f112400070078180b01c3c00c036858004200740d040521400400c40d0314010010502d6142d00000076024980160742000e0400241c2c0b103000000048403807607500d806036081130035400380c103000001d064500c02400810081040136100b464030764145030116540341c0d030f40d0250501d202c01e0748110140c0019099100304070100d00f0034000f1400d0f003201c0c4400182d4512500351055500c05200c54028030411120015501046074860310310180d04503ca2407c041c0f074542c803501e40e40071041d40004164001113100303182c18100fa9250101e81e410004810051280b0b00b0b90031000d002c25540c5442d4180a172001000080a00c001000715696000025069a0003400c41c0760840341c882d0b0048075001c2c0401c042103140c0d001c002d00d511500f412200e500c80a05526400c582e03580018140030424140201d00601c0003201180c088a9150b014030420a00400b003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 920872059 1250 920870809 920870851
    0xb071b03090f140a2706090c03111204060b01021f0608160f050d0309150f030b0a0503060f090703080d0c0207121208190908070c051009090c02100203 66
    0x80c081d04882407080c03441c050280c040c2c480480c0c00e011748000c000d024803d425103946003003000b400002400020340c184600080c0d0b4030165070040300c8000566409000d0800144060701c41d5211700703c042c801c41288100020003040c016840140511014810384805045000e4001e5030103e19803013002034255625401c0200e08000c001e070030f200300b030704a0b210210145040001c0d00c402a491240c1c0d40510a103200710f401301440f40f00441c0c0940400400d00908041c5001c0c020410100d401c403800210340f40c42ca5002c01450450024021110000c00900d0340340c2d10014010000040070300403041e94455800003100241c0c2903409072140e000310700d00010b0f0107010b03800000c1c90640d407030b4440f10340541188600f0001c81d10800c05030030320500e142400201c545401340c003014211250b00c1074800503881c2000d01c074100700d802e00040a44a0081707a070340318425212420041d480b00e04c418034002041c00d02408000203542a00701101c3d040c06c0d0f0041c0d84541185040d140160781c000c5400c500e02000350a03503112 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 920873309 1250 920872059 920872079
    0x207080301051825020a080a020a05060a02161106090424050103050c0306090402010e10050a0306081c080a0b180103051005060f011805030d08010302090a0e03070b071b0309 76
    0x2000000f400200315909110200381900d00388a80340500444c0240d07a0301072501c1c001c000302e82c140c0d0f50100c0c1c0707546e0342c2840f00c10081d02d603811030320100ca6901440010502c21901402034a41d6041070480083d818903240d900c8440c94580104d103640c10041c01e00540c045a6918031405020048014030250803140314071b03030504181500d42045060501d840140448400e6004c02e40c3c2e4800800c0e10362010540396400162035010f9410304403030b0301460242d525003445a1041c040c0540038000e46090001e140c5500440b0b40704d465030420441c540d00641c01800c41c161190842e80c3d0030070300c0c0303681c001042c811070004212042e00c003203028440b030413000004100304281000b0071000c4110042080040703090032800104140300003040c4038104010301c42000c4804406482034001010300070120343c000b903441e0300302400e481c2003403005a10030f2110b0000141003030103d001d040984512030000d1481c0c0952a61141242d4501904040400c07a0208086403881c400c0060300d140c542c06a100e86481e10b2600c40c03504 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 920874559 1250 920873309 920873329
    0x2071a031008120d0c0516080d1a060a0e01050705060405031225120608060f06100801181a030a06150503070602070e040809060304030c06050c0f0306130f020708030105 74
    0x38034681c400f0031802810440c05080d00c41903999070001160844421604550500801c2c95441d1900301d010034603410003919400070020b0b040d00c42c0007440f283c04030300030080b04120b42d5415941c100300c00b001904040d40c8107003c80740141c1c1050400354207115480d15070740c0c0b0b0103034201c504a07140c0d03200062040242c02c00c2c100c82030340295000180000c0550801ca80303281220f038200b5990600080000b805104000c1d504000d024080c4041203414500e04076940c0760400b0819a00a1702421100e480b60107054410048a0f0503950951038540e640c141089108004208065034091382d1500010101800d40d010b01a1500c450b00800000c0307035140c820300406030000b60316070060b8444e500400d410400c09802041100883d05031000f01c2e0a15625820a64903522034a0500c51b4400300002c200802c05801680c00c514441c020441001617903074920201b0303e01d106041d144a058501400010040c2c42c101c1400010310951090104440803544145e10590b0410784040b0341c1150040014041400e05103291 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 920875809 1250 920874559 920874569
    0x91203051918231501031703010e070e0321030f0a1e02030903070c0308031608011a07032307050613080304030c0c0b0406030504050f070317090102071a0310 69
    0x40120a502c1c04001c84400d20041e0b0041030002001c900c8101500002c0c00480c40019243c152161100c0d0090004000c03802400304031400000c030402003002c498003c0680781070740c0070320078031000c00d40314802d064070b80d1020002126414866011301e4155018041e09400705001d01c901c040b5264145003444020020300204072268203407401002d21485c1c0302c080301140f10004040d0005aa075191444464210b214810000d0098540100c00008000c4400000c51003011641401d0724000010a02110303a00c0080c400c5000b054640c2e80400c041880301d10040083d140704c0d08020700710000001203000c030210941010086800c0125800060040a001c116400b590054034490400380c00c0e9181c0b40f15000182c005010071045250074010401c030244010043d04c1c031946060b0325541e4402c001000b6040c11075085410f4010344070b0f91004184001800700583e80d020701c00300d81000126010f140700e034001030100f604600c00e404000030100e602c03602010002c0307080c6408664034a4005040c6075402d601d0740c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 920877059 1250 920875809 920875811
    0x90c0a140f0315060d060905061302090a0b090c0c011509021804020301031e0203071d1501020a0507030213060512010b0111060c2d0d14160818010912030519 69
    0x10000c00e03102c20381c3d0340302c1d8054011644044500810b00b41400100035620b001480c510696081c85414004600c90b911183d200b10740007400c9a80c0c441903001070701e5804403650380110040022641061103100075008040d0341200010300500c03122a241812281540291781482e07000681c0075200700001846070b4141800d0381d06510719407641e0ba5840d000d0030045c5040a941401d20794a20440d03505006840040042039200030b4100703488916000d45000a580100c1054824500b01c1015400400c0502c1941e07000b002602d81c1d40e2a517028002041f24059170305800581e40d820102d466911009022071498560000068210b0381800250003101030b03070b1580c00c1c0ca82c8104104a44040010300701d0301c0490a140c203001420301c10442c00401d10316000300c3c01d182c2000200c0c04121069950788503410140c1803080303200300b42d00c41020a10a0302c80c07a81c0070400091341d0400088600803424106007000008500000340e1001c2034407100844440100f4500c0001d840707805102e0038810708200343c4210b110307681c0c2c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 920878309 1250 920877059 920877073
    0xb040201020d02010e03121003050303010e01050f0a0320010e04090f1a101403011107060e1209030c0d0f0f0312060e010605040918080f040f080a0302070e090c0a140f03 74
    0x810f55500d01030950401041c7c0d40701000903004951201ca40401140c4c4103007240e0b16540c40d171428182d000c20902903e4090060100d0700002460702404180403280c00031003130009031480e4014000c015010f80041c0303040c003c40000345c414540390340c41101c0c0d00d240a40000104000c8501d00140c440b01e02241c9a14038110b071005201c003650f001c240c90340884401024010400304c8210200c0c2c0503001044140d45820004980741d01804841d4020a403100036050580d0004a100c6507099000c0c019422000e40542c02400e03c41d00500300600c003224041d00070401c00740300022640e0f41103120f5018901c00c50004600b000c00e0780c000c5890340a0078014080c0d6500b0640c866040c40002441c0b030060344aa42900da44500000e0814144000841d20031900401415a240100d80000c135007130b801885904e01188000c200000d4480d004510b410505034140c0c00b80210a107018001c0d82c042c413015200503c217003e10f0b9003140b51941c0b18509480140741d01403540700751000030800c004840f50703402007450080d00400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 920879559 1250 920878309 920878331
    0x60506031602100c090b1e0307050d0e1b040f18050c030607081e2203090503240c070c0b070605072a1b12051005070c0f150908070b040201020d0201 65
    0x10b074000301ba6040c0003142030f2582c40d100a4020400492031031030303095120000174001690342c400024140e002c103e00302802002480f80032155030b401e4405841d44407003121031002a103071925400603408101d10f03040102d010a074405000041080d00602140c40fa8031021488459007030a10001c0e61190ba0b0b130422420301c4c941822003061a00d090804c4050844006000405030740a4107140c840c0d01e1a0031442004a070503070310b0042d1000d1481c2c000d040c800d100d2003036402614000e205580c01d00c2c20112a2500c681d444100f48046580c011901c01c88038030340c1000340410205212000741400602500c4041418108480c020b42000f00400f030a4009000d03036041c8100340300d0b10b5070060554644c4a008801c0c64415080d00b00c44030111a0000614880002c10080c14032000060065030000190010011501e6120042d191010301c0c4a000f0501942c12000d4000309034a4048031800021140010800ba0704542d18100c0070307804000c048601b43c100c00c040c8400d65034100050946186640002c111900d401 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 920880809 1250 920879559 920879567
    0xc1903080a080c04120309241b02030106081506130c020c0f0a170109050c030706020d0806010203040302090c0c0105010e220c0302090c2805040902030406060506031602100c 76
    0x4607040c0c01c140510000412102c26000c0110760003411002c900361100341281c0307401041c0210034441c18907002c0c000b004400c100484581404010f86094503202c2050300c81d50f65007035000c015484241d1340340d5601d00d0006009042440403807126040741d4800101031422008020414130f004580080d624903186100c4c0c0e4036500060700f404200d03001c81d50320b0039001c0b001c1c0024603805000d4010140040260446104c040b005420042d9801c0c468401c1e80c1001c41650203240d03688a045c4901401644410320343c3c01d00714018100c2c55000035048c8180c0b0701d800e84139000310300410320030f9554900c400000a500e0300050400e109003400b40101d10041955410112000e401d01c0314000240080d0700b000e81030650420000d005540000c5a004d0075200130b0b464480e00c00103858200c1c661048403480c82c6440c4186a0408010007061154141c94403410207040080d650000d41009000303c074456036840004c00c0319a12900914800c0d1000d203014000c0b6030340f07a44020b060100013450a500d981c00c06c00c881c000c1c1a08 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 920882059 1250 920880809 920880817
    0xc070e16020114011e03060f0f0b04090218070909060617160503060f03070e0703061d040503030708070201090f080d110c060402010f181211010215010b0d0e06090c190308 75
    0x901801403803c1184c071a9840c00040540c0000c7c482460100c1107a0107400740d0308000000c0c005214100000140401480b00343c9d155400004d5104007030f43c03820412281c0e0040c60541050152074011115a01c400c03a0380c080740c0154019401180000e50340c10404200040844d0348180401c00201d5010b046880c0076003070f8000a04414421a1840100003807514108103190081c03540703585200c8203082030380c80980240614000c14030403580340006201c00600f036402d064000ea0b4072500440c40d45c0d032400000c4440a10180c0244215504d4119003000302d51004469200c2d94001c0310381560766241501684201d526202c0c141c1400c40c414800328090302004181154003c0d020f00b09461003140b0000c0403605080000b41e0503840380041c010125603119002080411743d446122201360701031054006982da50600540d042c84001d45d0b200520010491101400c1c00302c0860708082001c1c2d0948a07489c0c1001800c03103540742a40c2c029070307002800c1d1030008582541e89480840620b1a6030954880e100b81d803203 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 920883309 1250 920882059 920882069
    0x100507050a080406020c01151403061303140a030b10030606120b15030705090901031a0f060d020f030309031519141f0909110103050a06060f0e060c070e1602011401 72
    0x10380403c004205c048223400800c00349034060a010320941d1500c0c182055480c2119485000f4424100021a49006101100c0d8010341513102c03030010071100c09840d402c5900000f10007080546806070100300707441d094480340c5404075548011a40c0e50078000c3c02802030181d800c808071481d05001d01074150351121050301c0d000b10040c61800f80c0d00c3d611040c0650b4075215100900b5000204d22000005003c44584400c9454500c0510301c5007036124103180404245082d01c6080c1e0047d52800300500500e060210540e403910050182d0382401c0882e00001e0801070501c203181345041442d400c05c141c06203070a48006022908400400a2601c00800503100040003840c550a4000d00380c150381140107801c03092001020285130504c5442064a00300d4441403003004042c0c01b107800c2102245008000b4042c24050b140c2c2503865145035172103d03030100d410041e900c40c11034000504011001c42c9620520021010380094080107559050804504515424450001045902d40320800310445140704c90181114 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 920884559 1250 920883309 920883311
    0xf021201050127060b1309060b04030206121503060928030c0b0c0d0603062301030521090901060c1a010602070e060f031b04060909110607031101050702100507050a080406 75
    0x52000f50958024606038004886540003c1102080f915000316076000b41c1e40d1040d02400903a03500c1c945001140214000250300ca101802541d021002d26500150b110000345000f41c0c000d0425808a8201041030354070682c1e0f9000728543d8001d4000c1c50840342c0c450666142c0d90b0b034006016441c0107010081601004284120800106414650090507615011025001044110303561314042008003007a41c28100c00810300c5040d068884090a4000d049030f4005000c0c11a03032259220450304860b01481c0d55440c000184888500c90311140d540354060403007500d8030450b50149040505440d207290030920f9120f007005005005459000c16000c00b21242c041c01c0781c10036151007001455102d40480c1e021f40500c00c0a008600d00c0030300480521604505840401015072100000c0c0140c0d90003040140c182d44d00340100c03d4483c10160001c10026001e4034010300c10541201d041802c1d078000350340c40d00c0180e200ca2159418a8050300c226078101203181003061a1901401000d0301200000300050821 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 920885809 1250 920884559 920884619
    0x2d1514010c020315240603040c06030e15090d0201271e0503071a01050d050c0603040606080303010f0e070e10120e0106080601150212032802070f0212010501 69
    0x1900c1c1004613950380c1203a202003c4072480e000742131401807111615900c4040e04110407403101420f06004480c05075400c600e0150030340341440300540240124a000003454071030149400101c9003240c02c05400384113410080e140070f203d242c01c02802d40d0604007541c019540003503103103e01c00e070302c1400720000305904c1450041c3c94a550b007052404a06559400307011804002048010420a100b00540e000d0741d404003050700e43d8807641444070340d000421008140b94400203004649140c40740186074454807504c0003082131911078030300f2401c0d0b4000380c0c0400101855400140f210b01502401198451189e1801d02c0c03039110400d00082055450f00c034081c00380312150351002d1102c080e47c0c210666503d03074400244407042d42c820115075030300c000348240c40742c0c1440c4212106c107a40c404074050f5080d50080d02e1700ca003940c88560004e03aa0007244d12442281010400c84007003002c221340007410403a805400740510b11a03160040c090b1050112003218a1641b4080042c41590b601010f1110b1103149240400e141c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 920887059 1250 920885809 920885813
    0xa120302150403030c0906090b07030806030f03070b0a0609050c04260d1716020304051003150b071a0907090903031508030405011814040b042d1514010c 67
    0x610100012122040702190100424140c254020422000003035480e0f1855580ea00300455025000340140103070440d0400408010030322a100c03080d04444001e003524070040b0001c001340d00e1940416002c4507a6040c000c100300912095126aa00600d040ca01c14806886d01d001001010310850251240255141c00782e0814010302c610402c80c1d44951904907009540c14880281c160014400c1d81820740c803d404c0010305503021a04550742c4007642c1d40045092606120400002c0c08900002c10704250b07448680f1218101080d101030010031558030215a0366000d0b0402c0030302600d00c90100305103820b14005203d807007140024150110381d810b0b1400035814a181c542103014141c4a9841140810300f1070300800e82d410088010f004584007600e88020700360b620103000034072041d00d01c664600d0b03503000d00f06c07084da6090075002440d02d0b60b0010070000e000c1100c541d05403a0071110401030b1030054600c3d07510303840d0750909200f03038080e008035550400101c82c50010104840ca10855041d81007041c12410002 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 920888309 1250 920887059 920887063
    0x70e15130e2a0a0e0409061d0a02090a0b281a09090610090f17010b011b12170f2e120c0807060206100509040b04140c060a02030d060609050a120302 65
    0x44038113030081003400a80d441e4100500504010707030b41218816020b140c1b245c044140005c0005030307160b02030041c441e165070301640c1000400180c038003150445140301d50321040b0700464600070740309029405a142c906080030110300b01c10fa8820210043e2105c1081500c603195075040207281c1c8000100c84103110245001000c8541d0011613011a42d056101000031928007004034005152203880c400030041c0c440d08000440e030301c401404000e0741c182c0080c0d90041c0840d03403090a000d56046142001b101540a461580a02640c00c445040b2480301010038080306d81100c031039001c01e400d45490300c0a8254410320b00341e94201d51600c01e09004900d805000410881d108254000070140a01500c0c180c903034511019444040c02c17100c100c44a41d07142404511032a1a84800740202d821003007034061541d0b0f035076840c0c1e408403806240c04034a1146800c924920354904005011420351580035603100c0b69403404020a80d407103500000e041c002c0000e005d010944400c2c45203411115500d984e0007203240c040c201a4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 920889559 1250 920888309 920888327
    0x21c0801210b0f2a091005120708091603050109140106081509070302060a0804030e030703201f0e03061501050304020d1b03082d03070e15130e2a0a 65
    0x1c010f40301354541ea49880c0080942070800c010b03918a94040400481101c547c829070314000781c0000040041100940b00e00da040d58045075080484e5952031800044a80322221a407007114a603454071460b03030401c11900d0165442001100080c0020380c1811009a1194403501241c40c1c00411100040e4601404100403002542c000e40f00c296180c454a81c014a0340004413019404240c00500810043c240028244101e0360440030340100303200c42e00c292203c641da540040301e83c8407501c6600a04403141c01e40c140300c0e580c4e28603200c680305034030712506150400d01c00800c3c0c00e58843c1c102c111961103981010440e980668100c0712081e142407940b41120842c42c1c000d2804941143d0640040304100c49100103000b030302061001c0204a0a10070660381115081c1110212a544184081541d182c0190044409100020180441c0015403202d00100350403038159441c1200c0c01840c10480700752070790386064109140c1a190169124940c202c1c0c03603402810482c0000d015400103441c082540b10318541 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 920890809 1250 920889559 920889601
    0x1c1803060e030a140906071112010c050408010f0203092104030c090b01110307150e070b07080a0318030519030e06070c0209070f08011401021c0801210b0f 68
    0x42111114841805035240c000b415442c010603840b0035608480c040342e00664501703500007801d00b854000b441c0c0c0c403492004028004140c000c0c0000917140364801080c0540444081907981c0c4503140c510306400c0d40d00b5079540a0a28070781b00d104000748100160007003a40340c40001050665050501c20355a45070040c815544040d0001010502c00b2601c15125004442d00c904260b0760050030206040b0711540724410310300d009001e41040c0225200300c1210340c110700020400c1c141640e11030340d62040712040c50b40c042c0c0d100b100c0f0204001008107040740c0612030540d08106110f0031014000c01e0355005000743c411240100384c0c1080c3e02c40b04c910078902c02e8011184800701c000a450340e40c102040d016040840c2503900b244951084000584030070b1003080703114680c590b00d5030703070780ca1907442c000080c64607814440c00a411030140b1441d88400d46a510303021042e582c2c10341c0c1c03030166070762600e800602810f041c107a440754038110342c0c550000440c00300a0b0b1940c024401003005c05503a01c070340c1e10280a24100c0381701 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 920892059 1250 920890809 920890811
    0x6040b0d020d06061a0a020316051e16140102030f0313021c02130507020309060d02040e07080103060b010e0f0f0a03240506040c1b060f150305010e1c180306 69
    0x601c0c2000700c0c0d5000182100c0350454100b100a588401c842c03054018000300c6c2d4010b0303006014034000ba03094850151304481c0600c0030f8480103c5441e000046003950003500c0f0640d54841d982002041d00c0b141e07000001085070303060010f0071808510000751248582d0441c034405035800700120b00400271141e03003a03100950082040c01801401c201c0c3c0d009000c5285001d0348a03181e209400080b404050140c0e500c6007659078065803400b5680c200300080303904006003002d8030980c244004104040840c198601502c50340d100d0910a600d5890075209032200340b0030341c078100315006140306440d4640c4410160b50a0302210076100c3d011150f004180d100c109a4405001307200002408041c44c0c000c0030403102012801d15003442103585030350070305c019260700304c041c000041d503441084a407111104c128960308611030000452250180e112400070342d00c0b041050450320b0441c103010000c000091182c0c0140030380817405071005d40c00303103440c0c03020400107240e0302c40900c42c55000b2600c1030354121040d50042d660005d0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 920893309 1250 920892059 920892079
    0x17030c06072709141005090106050c1e0c1908060103030c1b09270506061215091506101e030204033008011206020d020c010e0109022706040b0d02 64
    0x120040a010210710741c0300c440198401054032061700780e100400b5500042d0201d07107264600f100458143c3d110040350700e082d01030302c2d11500781c400d2904120160046c60000816140c4001000c200302484c040d1140c81c50903030110000c00c6a60004140d081c1101c6d010b0030880c0040095050052003c1c0341c04070350315500d000c21140803508505503400301c0c40760702c5480b603070311075200e5421034142410100c8080038009501c054005052881c100305203619060300728050340c1d40b008180c2e5034800924001c2d140028583c1190040311000c170254101a1380c401030448100d20394808407039004e4020380d060121007c03080c0c0651200c8503024081d40469005541c0150b00304440032803041d06103a1000540c40704070600742c80702000200c80d44598000c5040e5103031010701611100040c0e031550000d50001c1c10101100c1d0b000d220400d10ba05003885580c1c10085001c001041001c1e00c0d02c10070201900e1341c41c0052a41110942901044a01140741c03503000740240d800086240491001408400039007000940c4882c14807 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 920894559 1250 920893309 920893319
    0x12060e07030501090b060703080112020409120f080c0f1903060503031605070501020123090109020d030c110102120702010e031002030103080a110615041d060a0617030c060727 77
    0x98840c0f412140c0044080000130500d0041262510078450054005000100140030003414800a0034410384001e00010b070602a9036106401c04400c3c14804001c0380d800301c44000c3d8141c00c42000c503801144c24952070f2a214010300e80740300501a0810100ca0201c440c0e0107007440900941c009005400c0c01402c481d2a100c83c0c4032642140360701440101e1700c034010030790300240c19401401501c07030060001c403180c59001201c0c48450411240100310007003070b41d20382d810389000d41c032a403003c41d244901a0341c600040c0c001c28209503540c0144160b01178110350046030f072480690018401e44014a60929050001201e40c00003e031901a10620a96100d48000000003c1101c103070001c1c00300c841951954021103c1c0c03040402d03141c6a049910010076110924224040d1515501c10f24210703d0344240071555880c0130300218540401101d46c0d0140c1035483c00c05101c101c1d0448190002405100c0c000d62425241500d040e40303c0c08041e280100f030210300d03050844000500c0803c0040c3e504001410b20f042e41d9a1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 920895809 1250 920894559 920894561
    0x100605030414030408031c0b010c0b2214160503190c09020c030c07151706040207200307050a08120f0f0f130509060d0327090b0f030d0f12060e0703 65
    0x4119a40607072401d082c0c7c03c0d1210240a400e0000005850b10340400004c3c2d00c0d103544014008000b503842011101c0072844000041048451a500545480807044803601c110341c0303025104118903c10004050080015030780020300c0030310301801c2100c1800307052141e14201c2895a99908501c00d0710340040391851010f0400406803940b10000304c21500fa256503541006110800d0040080004201180346032a04000300d5085420000c00b4000620300306481d203030008003000d92501c1c078051486140b292800e614003001070402911049400e2b030011850302e190140e6901d101405540e56a0300460044141d2443c5019520144480b44d034595540b04500c0071040c481e800b07007844420800c0910004640e5062014a280c40741d10090a012135203517154405842c0706001c0100c24081c118602210402d0003400102c400003000410320101f007a41c40700301005002c0301d160207060b0103a030000d902d0700c5466a1060f00521005500c2c1401945d01071903034842005403c4603080030410007050000d1004003641 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 920897059 1250 920895809 920895817
    0x90e0f070e0f0f090d1b051005061906080f091c05030a05010b0307020309010e060405120c0925030e03090406081c020d02210c0106030503040e0f10060503041403040803 74
    0x4103111030b42c00d580e4068980c0401c00141ca44074025440f610811035041d0050204600d401c240b5940c08800c0030290307036800e182902a040c01e5076841e0303d0b8400d01880782825140b407039a40402100c00c192460512000a01d4514002d149400a9000d08040707180a501800206500858000342008002c0000ca0251041d07106840700102c1030f03c1e003000000c0454400040d00d000300c400e68040d40ca4110010300440740903040c150b0a55000c80108000113072982c0b42e10800154020a4000d0b001080c911000c0180014005210030003201c20301000d011016400a6581c0c412900350800040600d001560f040c6540107840b4000e4006252540110340d504c000a0141300158044a5000c001109064226101d01d1268201c00160340800c4450001c09141c0c520070410165442ca220b062808080b42a82914000c0e8800c0da050342002505002000c0702a41c60341c0d01540d41c111545450610750503000070b20565214030f41c01c00c14040003007410070039030b42e003d03d001c155084100c980303c3d615202450740b2980 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 920898309 1250 920897059 920897071
    0x1a010c0b041505040503030f01080c0f040e070b2a01020f220317030f070929070f0303090506011a040306020f070b012705090705010e12070e0f0105040203040507090e0f070e 76
    0x108c00000040c05031800100b0014140307000d000c1482d50100e00050002a0110507541c0040c0d004206c40420001d1640c80905441005007443c400f503480000701c460038545550508810340e0340100041840d003a05081290350a41d10490045201684c01c2d0b12645840c00a8000400100c0d060400341c10901040d40510700071421031300e018506845018003501d80d1032280c420144030301810043c0c0f403441c90305100c11040340404200c11912706401942d82904019a140c0c2c2140402d0f40c81c42c0c1a07082c01000c10a440c00341c002402d801a005642d00c0c0310149a000341e100c01000f164000030303c160044805425211901d52110752540e1a503103c0d0340d440702c40740e042001300c85460b901800071040742d550350240c9401804180060a0070b1420000110b4010702d010307940a800555521034001d06141c1088641d00400340d14001c0340e40c0d0306100440c45005427040c1d020b90300ca079005005103c041340e0040b4040084840c1a100007540e050501922410101e41c07101c540707030501447c140000d0007107034016414800c0c4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 920899559 1250 920898309 920898331
    0x501050a091b180e01030803040b010501110307061a041b0318113f0c060403150506190305060405100e12071a07121a010c0b04150504050303 62
    0x1601c80000c0012580b20100c1c904101d2404a803100e9a03078024a05151207030360030501c001030983c980d003220a81880a030300486000e0800070810041c00031494045000d440c092030b1200d155022189407071380d03c1c00b601501520ba681d0359034400781444043e00c10300c0c0800c68090f009000c0a07206042d1350211900b4189154042401c1c800000110384800c00c018800a07800510910501859018403041c28005025620b103400c0c201d1240703000c015003818403034007140700000e40c81c043c0014512702070514070207600e850b00421043c841400002c00700c85045031090500d1000040135a10480003c103960340050301c1814907a5822404424001c001c00e106108900490850ba04200707000c00c0742c0c085809518035020700d5040a401c1c5111740041c500100003050242501541044042042c400e01243c25540300c400300340c405000c0d18203048580101004118601c000380020b50440c80040d150350014440180b5006070f1100050030404c583c0d581c561103400c40f035010089440c091820903503e500564078039420b1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 920900809 1250 920899559 920899579
    0xc02060a05070c080f0d140117061311041b03060801050606090a15020309061303050c030d0e0103020a120606081e06012307060908040603113a02030a050105 69
    0x294458000c46000b010190390303151a4011503102c2c20095000440402d07005d1008000c0b85810031214082d0050040420340c01d141d4551400741c0701c00103400c00c491200d1450700028100703c25046030040010005030803005082560030400c00050040203040c5000b00580461145642540c0d855440f000039500b80e01d00820194503503004204070340c010704551560090120b0030922482a03540c10460a28815004813424007240200182d000d0300803401403699500340c18000c205204040001c820980016030141c4407000307000c44001e0480709440d154605158000580c1d1003401d1154281d1400d2241501d403c2054644648008001c0c8905603001c5100c40704021305804200099a2100d0090005840e6404583c0a1001d080262002000e00404419050007090042519802001901440398510307660341d03424034401604444454041d5519090280100d4070b41e44071400c44400c9242d040010001c00d42035040c821107101011504201c2094004824400050220b42129060b62800c071100c24070 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 920902059 1250 920900809 920900821
    0x20070f08030421020a032f04020910030c11030301080f0d0f020d0305040c17010e010f021201052103040902131401020a0f1e03211107080c0106180c0206 67
    0x150b800b039406120320049500f400c0e5900c1031140e44241d141c80b031000e03120101c056500d40350f00c0844a1041706802c010070042600001c03d4482d00540c00351410300b25400c504261090300406c80d04070071901c5003018150745000341084030303010b51080c00d4080f0804041300d5a03903031101c0000d6203035041200ca210442c401c4c0c0c050b0101c081e0099a00b40312426036603000b801c0000000e10210060200588261031040400e10041820f0315407074201c07000072401400129492032a240d0702403c4461038074807440b072240305010b0b20840d000c80000090455008850098080301c803c8030310030550810100c440e90f14400010300107103100881e0041c0062800444150403080e540d510040d905505d140306060050b00903041d0000060390344030001100501868411800f1408250440e68a401c44281600401d4a1010465840d050810f5a40d0f507498204001c1c000300843c1101000c95006296000701101c07030204013000010025408940140f2201d00d24099807410000c4480007000d4096500f00140140000035071 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 920903309 1250 920902059 920902063
    0xb0a3c33081005060415031a01060306080c0f0301020d09030c0510050f0c0a020703050709020904050c070c0501120b09010e0f0a0b0919020903100506030d080601020c01050a20070f08 80
    0x100300d0301d800c805841d40844191030031004150040c14541c2c0265280080c008500300c480d000001380d8890204841400d024085401500741d0503845603080500f004c400380310901c004240c0740b0071054155190105140640c0000b400ba0055110124600740350442001c103040d40320200d43e12503802601074681d145da190f02c00c5070a4500485810341d00c0840000400c001c104010300400e0324100d648140e0309000d4903a901ca80c01c1500329403040030542d4010914400d2458a40324058002103440700031440c194080d510f010b0713100300e180702d11070511189078406440b9540c15040510035440c0200303c0c440070341c0c407040071000081c4250b070709030403500705500040c80c1042c1c0303440707a104c85000c01400c0389a00d03a20b28040c0d401865407a0015074042d03409005075561a01c003004130840201103110003151503e400030a040c0703000030841d0890100302c5100244469a6004140707035100b0364013031030040da49541021054950341681e070203100080d2201700010700c07403400128000082c0c950029010a03416640d03508a5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 920904559 1250 920903309 920903411
    0x140304050c18070c030c030c05060403050301050a12021003200a03060e061206220b01080f0c0d15050a0902060703120b10021023130b0a3c 61
    0x9008140c0500c03040000c81e00440e0b403580d4682c46848c0c0b180c8940c80b69961030f1b08042c000c0e5021004205c01000510083c54515682806070442c95551b40a9412580003d011001a04c1c4030340c1c00d06690f00c406021900124200783d000e03580520b1001d03901c420398000100206554803c0440b01421140411403514015070350f9900460418000c10440e10341501c6c000750382100144801440c120140e80c04001030701c010503c0d0003000342c2c101400c00e103005c1c26400c5d130500100c40c45d42ca114412990300d05000600345c080728100d02c1e04044000807640d880b201c1c80c500070491a80040e601c04c901055020030940d00100150f0481c05414087c080e00c0c10800920020030500808a0003603000201c40344414641c42d80980e80b0452001158260070003041541c18440740195210030084140d01e14103820701039024045500304100e2002006402c00d205900c85904c84840c03003a9000000000c0c480104080550040500f04034a0004001104000041d00d0b4140301e0081c42044081c2958004204500440422 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 920905809 1250 920904559 920904571
    0x2d1703190911040507021006031b0e0108030f0d0209060706020a11012c031905030f0108030a0806191a0705011103090a0209070c170c060a06081c140304050c18 70
    0x7400b00090b25800300405400018001000c51207080c01a00080c401406810300640c0510f019904a207491100c1548900703458002e82840d100500042191040c00011240c09a101c881119210300c1c14684241c064869640c40560012001c9081d40c1070001540c0101220f10164491444010340c0718501801d0b690042d51114a00d1003000c0000303655038585c419441e08200b6113090b86d180c08014000900305a130490005c60016802208000c4071034800000c0d035001d00092030045040905134100140180002001103012311518220441d826810072a8a400ba020840070085480c0b082d0412054a420200d425691982040100340000e18440c003100d0040340450050310300b5189940900412100140070032040264640c07800d008550308032100202d003010300c1050381e40d80090202882c42c10340050720041400303141640030040d4000c00503d418001c88050070094000b1030702c0f0f80558014009101000b14550004100010400f000c0b80701d00d50014200c0300454011103d56410a0110044481d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 920907059 1250 920905809 920905823
    0x170709030210050f0405040c090302031212041101050d110a1710060e1210020d06091e0f020c030d020d1104060504031b090e0d0e030a2d17031909 64
    0x144845603c60750041011401c0c0000140c50680d0b10700104045800c1e01404200045034448144110701c4d007030101d02c107880c0d0005945400e04442000d054600000500003c2010010040100060b40540281c603101e0b2800c0000300b212900800c3d03002101c3d0310007900d140004824101c651207405400704418000c5202e6842500e445040c060203a0390040301e043c40c0d0380d2000c103c1c3c01ea82001d0300704110800c00302e0143c03000541c480d030500f00c10406403a2550820b42140d410001c103020140c480040c0520080544000441c0d10182085114001d204a00c0c6410343c031b000c00074200c02c6104840c1c000f049051540c100800c1030904c000a04a00707030189005207400100304100400101e1011141040b0250b850500c0d03010302a9208420400c540740c0d280c089015400400440f0700e4540c0180b0340502c000c0017500607220344502d07a900c00c021260f90900c40c00c10314a1041420800c00d04002603c100e655000d440403500b411020162480c1344c004440c10b00c00c00c00c400d10324048545a03402920b03121940918 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 920908309 1250 920907059 920907079
    0xf0709060810050c040513090204110f030a1a040908070b0c090607030309030909020403060b0a0f080c040e01090221070f140405061306170f0a0c05101e1707090302 72
    0x10381c02c0240038050003441e5644014400400c450b41d810922a81280c00039000180c075907400c0c0705000507a02c0b40c0d540c5025104d814860040a4a5042e04980e80300c10150310006401f0a004030059080d1000c0c004d240d0440c5c58145060100038a80c4000c3c4a00303400707070000038102d60710a2810b02c3e4031f07c200500c66401100c24801e58001071301940000340304a10a0401c42905034440c3d0300351049810650003030302c070310b03441d50b11200281c20250a41c0c1e0107070000983d9550741604014407141d40e5401801c0840c01169240014001c96100794080a6801e500030003030702e219004011820b40000c041851b204c61030041031800141419822492000c8a050004031070071049000c2c100001003c00030811900110703490468016140c503489600d01504041900d9180c0c1101015403a140001c0c1600d002d00c40e40c015405400440c908440d454110390301110155615803507000708803454000358400a00e08642603001220690b008080712460341c0142184c480c96030f4480710108e40e80d1040b840080e400100c0c1c15 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 920909559 1250 920908309 920908333
    0xd170a110d2a061b0e0405060604051e0d081c0b100356090610210903080f1e0703061d090c0604271404050f07090608 52
    0x580c6640d800426101c0b45116826100c0c402960000c1c0d0030034019400700c00000d11402e8100b140c000714070005480401c00d03860720300042182e9100d10700500d4030907c25111009500011580c44503c030312006481e80c0403013071a5140240090300708074000342c1d03400c0301c24441e440c2c1200107109040d07096070002e0128150b105041c2c001d4000341810b0f009a10741e02024400c00321480e0b181c2c0d00d200a003038000d02e9612409440030b82c000c10950100042c0400031020314802d1070480e42e4220026800100480320807601180040c010313205200b1095141c00c103913540f0103150300324032600c4c0e000100c154040e445102c00c075038400210340c1c006c1c0d001315400c0d1501e061155103181040d41469025030b111003a400c0008030369481c0c90100174603030790702d80c2c2001070712080b00100403180e0b000f0702c0300d05c01090040c0c5502c0c0c08c060a0280014241c010510019071041c0d081c3d00701c0d0f00e50011034214040f6041003030b02249580c10281403003600d411802581071418845c1900011b040040b41c400c1c84211452038000c5c1001100c01 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 920910809 1250 920909559 920909597
    0x120d05031914010302150c030409110412110a060314071808190c080106060f030e010212010b0915090612060f041407030501080a0201080408090d170a110d 68
    0x6080108820244444800c181c00e0510071000b0031802c1c0c890700c80c020b600d148100045101000c2c0c9100b803000042c004900e1100c0300009407020745041c0500401d0345003201c02c00101c2c50140398800060301d445040040b00b03000301c0ac2e129440003a030a8030401c1c4000e4451000742c1c16620162031250303c9460b408005100684504180d1030f007496690745c0d242080356101c20842c508007000c1d03010505402c0c0107090004200b01d540d0002c000b0031440f80244030182c503110700078004041e0f504503182070507181c2ca40d00b041d1510a40c12100029000d0000c500d49585035041c00a82d40c00442d210341c018460281000b102d0030000b825103074244002802c0c1460309800704070300c094204014001a401420342611310310b0031307925402090825540070900001514240c40000c0995606a020300681d800202c0c4040c0582d900c12030301940241c2100c2100c0c0d96408800100d0100e5142140203002170740c2100e5000003040e00e08009200500481d41c1d5248401070000c074954480048500300c101103107102070b09a20f2002c1d4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 920912059 1250 920910809 920910811
    0xf02060c04121a07020d02070e06100c0305040b040303030c02210306040e0a061805061312050a021c3501050d030c0507090605090c030709170f010603060501090506120d0503 76
    0x40750049060b80407040f400c026102409444220158000601c605016a0304204110003003c201800f943c080c2000d01c0070074800144034207076104002c0458003500c2814012400c403002002144c0c0842c0d80e0395a2800c00a0041000c10311140050066a50786580030448400041069000a004a00d10344500c000c10000f0701519403c0b0303c0724003a0440c4000032032100d22440d12100107046840c0440091880c046081c40001460001d881e20009425000b250303080e400c50b950420241444c1d5034030402e41c68140d181c25044403c00025485400e40b2004035540862801e440e55840b45001e0b0101c54055130450542d01c0300348102005004160040140740b4003800005029802800d0440d11004551105810441c0b50307045146c0403038503600c040020307003407421115500407422a00c541c11404c1c030300001445540c482c4640c0b010001202401200380313400340000c1558081c0c1e10002c01450ba42d82c40e1520151200b4031903c4031241c0f40c03800040c403e081c140c00c0f00708200a0385010b0511024500710984080d00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 920913309 1250 920912059 920912063
    0x1f14040c02033603030d0906050601020601080a020405040f0209190f09151503081305010e0909060a1a130b090c0f040b18060d0e0c0a083003070c030f02060c0412 71
    0x14080c084003c0da1018030040c02030a00c50140442e4039159810907009482018100d641198000b00c010000004042880111240c0c103d030003003841c0d1164203241195204868020790711844030b034207100146540040c5041000ca51807030501121804800000441d40e408001078880c460007c51071291414691000d07004103441040c1140641d16900c1d4184c094014040350807101c010700c1c005000940e04140c007246010802c442401c0700740f518006154440c00041e04540ca89900e8000c0e80c20700c40c1241340e9240c3e003540003411410b00a12069a400d0181074003212140c0a20400c03404906501c00e14001c03980004000c0310712510b040d00d0100c4c4041e03103503c002d100c400111300d0501d88610325074840c0c0081444500480001c605032103482091801e09030888240d520074020080100300f014000b00e100c4c40902500300070b02804900c1d0038644500c4c0c000402850589100c00400c203c8010f4019461050903802542d0b4407540c48000700c0140da84d40000da9481406500600c0200081e0203840112440b40e4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 920914559 1250 920913309 920913397
    0x50409050f0307080a020609031312022b061802031e240f0a0905100c031401031a100b09130b1503010513050c0301030305031f14040c0203 61
    0x14910581190468021440845104d1800075800a0b400c1e41001443c1e00001450082d514200e003011182e0f01d48801e5100c1c440b03844120702c05690540d616003201c880015041994100d4640c01001c400910f0545820b045400600d0a01c1644000d41c194a0852a0781c0e030140040c15140180407080e443e4460300311100d0768900c1100200580308140b0400003c2c0700749200382807240d60920310000300e5015801403a40000500d041c040401107840021140307000d0840708000035200031120001c03001f0300001620120745099280000042010b101c03032403c03e031030394452340c1c0e14039899030307880e01c4120100c0d84501901608140040e188924000c500c0c0c14810451250003d103030b03613a0380041858024083c5c0d00d42a9482d001c00100041d0030502602d1210440d818002c200a14211040d80e030940410f0001408000000c40050490b4600f00e55040401106540d0a48480c1d640c4c0c0d0f0070f40c1500b140b0701040307000d281054100d2006c14000019101211081d544600041400785c4440e00749a00c0700310241d24035 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 920915809 1250 920914559 920914573
    0xa0c0203071203020307031101200c010f020f04300b0c160c140102030c0304031101180e0601021e1903140f030108010608070e1b130b0c060a05010b0405040905 70
    0x5421002d080c0d00d19220f03402458594803139060240c0f511840708610300c0141d041000340182101d49050310032021880d024015107502100f00c0160050420b10405140d076440015820318135400b010140007103624807c418440d24240c18100802d0107002c0030b04400d00c0010725068000108041e448540c410f14800072a41884959030310300704003294240056680c081943c4050050b80c1d001203680803035000c20300055140180c240e45155592149100207418a00c00d2080010160300c18184035009510340c07103400303041c5034489400c0c018000f820388080780544291011540a000051240c200c41069030f006880210740740c00c141c1841c003501e1001242001840c42110041c01051070282c032944249070603484e00c941c14207002c85c1c2141d043c0d800038451680070702d074200b1021126001041d4450f1007079004d492109040c03990758102e8060030320380b42645c00e0403800108500070f0b46400f401034a0540c0701104d1132504ca2001c41004c56100b80600111810208070501076800c25802443d01d11740700314229120 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 920917059 1250 920915809 920915819
    0x5040302010c0f29091203100611010603061b18031707110406081b150f0a03090c0b0d050a0506010e060c03250210020705030d0c02030a06050a051602120a0c020307 72
    0x2542d40042c01308010083c0c50003800007140b81005403144041ca41c4801610f142480c05c200141003403031348110410000e000340448203da80c00c0d00f0500045034404402e0120401074120f422940002e00741c041d00051003000707a0b070100c88006200e182202d402415601e02113403121540a410780c09000c081e20360001d14006d03c0c00c1911a4490707a402070503403030041c00102c281458440c2850002800030f40c4a9024500c03400c003440f2101045650303007810340007c240e44102118043d030140420403405403629104440019503840340d000249a14242c0e55020001da50340c8c85442e408940007925503a00203140c4401411703080c10590f004001c4400a6011641800b240740e00ea0746404050687c000c0d0030500c400d00b5901141489002006110141e0019102050034503000c40c1d40d4203130b40700c0107404000c00fa02140c0c00f0f544042c04074400d1550000401e201e9031810852050203000700340d8008206900300d0042c00f2400e8800b0400d0300000c00c01c09212843d007200c2110458a0300d00550059030705000300440003030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 920918309 1250 920917059 920917103
    0x5010305041a01080708070b070c0608041b0305070504050106180519170307060e030a0c03081905090c01120216080d020f04032004060305060a09051002160c050105040302010c0f 78
    0xc000c21030f000040c0310785c0f400c1c104010708111207036008150420080c056080010607681c0c0c41c60907a045860b0840d030569580c10040d0b00c00c0300c806085140c2e0b07032503940c02000340034002c103a2806680003903034240020307640c0e11011120690004100324800c50720320020700643c9031160003220800000e203041b5103195103a42d030000b281c1d0f440a9000860750f0002030810b04000d1180103041d0704100c9003001d142003003d43c0d18040d00f20b1000102c000d041000703070000507081d07075442c1104807015041c0c08410402454070f621001d40e40c1424540050104403807032014900211180200c80b686003090241c95040344955403031030440d030026840340d10401e80910101148510402c050301c0110b000b080000c7d1300c04060400c2e00403200600c01664060790910200b800442c030002181c0c2e030048609a00000c034201746042150030180d1515603002110b000007040c0070510038a41c0300c01c2b800f90287e41019601c659039001504e580c441c601c00240403030701201c4c040780400e1800b005801c03803a018a03c01403018000c4141d500e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 920919559 1250 920918309 920918311
    0x3071805040c05040906050d0f060c14160201090b030c041404020910022a090f0a060e16080a050601020a23070e2205120d110d0207121805010305041a 66
    0x440003c2001c03408118091103802041c0003010240c0e000701c41c0c40c02a449003001540d20000180020740c80724024104544940c1d201c00c080900308403126200e41801c00c007800b889044400603400148003450205905d021082102c2c00307580d5554041d03240c10301d04810000c12040b0703e20b03500e13489a0f0130710952500d600d813046400c0c1103820540c060030b11050701422141c400c5036049507442d405080d0419440e01502d481c030b445500035500c0003645005503620765010f000350940360400001c9425003070603c50b0080c039900806482d0110343e1544a0300e55039245424080ba00201c8180d40103a00030a100b02c08182d8043c000c070318072a506d140c40700e5082420918580b604031a2381c804201d404c02e0b541001101c0d100305403450441d01c400b240642d0002e500351503481ea52540501c0444030303042d0003c0c0010052582c0c1d070000c80324841c41022151103520b165080c02c0227401003103085d260200200480040c0c18411003e80a1581c071501c0c10458090810300110000c0000070401c55100044805d140310b20262405a6 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 920920809 1250 920919559 920919581
    0xb010c020915031b100302030402210706020d02010e0601030209041a0f04120c020a030206091306150e01020d02030a050d062403060605091305100e09010615090b0307180504 76
    0x2e03451001801c0705061504951000100c059404401c584400365600703a164000040e2524015841f6220fa000060300140302049180780b003920341e0000ca061203000300340c0404951441d02034503003203458104203a09840e070701300301c0344000c0d000b03100144014586843c40c00e4100340600c2880140c40307207a441c4850150700035944914820480301c02c210070001000b19900003100075180c0074070072003010741c007040082940d0302000b8400d40010a13802015201c0400754017108040320400c2c00303115650080e480b2000c01340002100007030b619a24040c4c40b075000040d0a0880c60342ca500840c50305105040403200ca0700800b1441341442e858500008000130742e203442104d100c40c080342041d00b41c83d49040103011520694410720a10005108040541d035480c0d50b80d002d8048880f00c04562a560580484001030054100c00d8032070303002c1400d10246101c158004825a9103014050780c0003244501c083c0d1300140d00c1c2c81010280c0c6d03010800946142d1140000e0801040000c1030880c43c01d0f122000501600d00704000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 920922059 1250 920920809 920920831
    0x3070e0612060906120c15160803061509011d0103060515030f013002030c03010518060601090e0a0e12030705130b0414060f120408030921030a0b010c0209 68
    0x3400700924168100b5070304400d084880f51009017a071707021140c6601a45040314418a05814119000324016040740c28041c0d211001c6610070b001407400e40c100750016224240103032070480c1101d0300e000039102103032101141619811180489820403c48800c034400d00f07113040503203d500018080c2c584d00081140380d031500ac4580d44a00c3c00e150044581da005a20042c2ea0030104c42544401d0061410300380903e4110060030002000710b40042442c207401c2210154156190408104c852810742810480200501c800e64046450761001114400769034002c00b2310030741c1c1a00100d80e294074590f0105024117160f2060314000c0510100205503508100c071040d02140000030220709001d44a6401f4000d8504040c80302d040c1410104880c07410303000c91001d5802604001031160950031070707100303980e000405c0d1480280c66142c1b0703240140b8640c00030788820380d41d84035800300004115401c0c165102c50311100704260341036075141c81107a00a0120341422a0500400080c400007586803401403602c5a413100003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 920923309 1250 920922059 920922061
    0x90f0c041208070308060307051c030c120305011701060e0a0b040f0f0b040c030e030403170f03070507020a141f0512040f0b060907080411060903010c030f050c07080f03070e0612 78
    0x8005d06281d4004004511a400404050000c1e90b60145c1c8101d1200c3d004010214180692505484400403040050120082200b0b50411298503400441c10f076450a019540445d41040600382a12000d0003048c0c1d1081100e0000344c42d00c402540514a15400200080391002194843d00304848101c00200e0707076a512a10f046ca150305150041c0c81d40d172049440e0400c00495110325482d100e000300e000040c0503030800d01c2180585c01c00581980d100c00c41000c5c0ca6a03880c2004136019000f40e00a28081b40944c0024400040244101080c0145504041d00070a5030185081040f400d0001c0300301c100c4280582480041045888030004520540c4034030000506a5041e003400100c1100040559116a4041d42088016a44000200c3d0000d03031040e1402003a442d4800082c0160140020980d0598030303207a401c140e186d5250300000e80c0d40541c0c0004000d680c0b1601c0750610207100c3c02d2070191806400308441b1015441d04002168010250710304010008903200c0022165801a50402e0241c11184 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 920924559 1250 920923309 920923313
    0xa05060a030b040309140a0f03020d1a1503010c03020406020c0f04020d0204030c080f0616050c070308070b0412020f07120c030f050625080609040c0b1908060609090f0c04120807 78
    0x2841403220240450301c420007c0d2030b1070b04890120403d0b010090150303001e00d07001802c00c00f40030604c6d40a55050f01c6100034925200403d642d5550614900342e21a40c20005e1407030405020344210303001e44459030b020300b0416a0140a00c24190000071546801640c2000000b204600d00d102070310207141f08146800c00180b6240c849454001c00c2100390429401c078605004064041d110900d00320400c03402c0c150b40750140c0782c4d08103050406503880a00b240e140080d0b802e0400886030b4100f4490380c858a4514546041c440c02282e51300001078186426520461050103400501400c1035895441003c5440075903440b565075111345071503403900f164164065030900c001d00054451405d40c101e0513000310301000b800700200800c01e1102134410750140114901040c01d0200d01043c40026142c291010b6a9078908181c8400303e010540c81c0410000e041d002c040741c0c480c60701404403105018001d100d040300b915498100c140e00640507200068510b000c0200103150090380f612600b1550041c02070310b4441c01a8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 920925809 1250 920924559 920924579
    0x1c230c070e010b1b120a11010b06161a0103110103020705030d09050327130b01022104290421050d020c01120203041208090c060414011808060a05060a030b040309 71
    0x5040515821201050281c4181802035a102d0006441c00741e0030380c0b640580319801000304407010ac1d000000001c0c811200180350460100c401e02c50740c2110321208103825440c61801d002c1c00020600700c840400101250f1080d0082d2940c240640e055034a041c440946407000c94180010458040d00045000da041c03a044108910240c1c0c0b08000c0e241c5e14049030b04c0011441d01c64400d14081d000e40c0d984099100d640308100300001141c00000011070b510740d14480c0c5019030818424200d2006d005044040715030b10082c6150304e048200c1c00b000703090905043c2c5a410840f5041d240e8890340c0b25610588001c02e20400c00c1c2c3c03500344840d80203000c07107074020000100302c110300c00c40301c0300000d0040040c080090001d1144c440005428503001009031240c0d0f03060340c01c02c0c0549240660007400490081004a062401c1d004000c2c000d0301c400081c0103145918456104d603901c5441d010b40c202c000000c0c0c02d00d01d141c200326441003000348540c41007078680e070b1000c5c05030105450a900040c2141000e205801e03030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 920927059 1250 920925809 920925847
    0x230306011e1b050c100f0e0d06020c0102071113090206030c07020312040e0405060a0603081905041d010810110307081f03030201020a02390a0806091c230c070e010b 72
    0xd41d10380105841c0503850050b0004414001e07e42c021080c19a0a0050050304d03415110181f20660080d0740e5000b480c28200941c0e5600400580300e012609002e5510300305502c5454081c90380502454115918803c9081140c5c110160a80c0c06020b031104011001d44000d004102620040c07016600a040a081c03151510000503d03441029213000707001e00c041554003084d186070122144100340440140201101e9500079503200100060503080003646001e01855414140c030350042c121101e10203010480d0080d1000300780000380b00c030010804256464881e09115902642c0060002184418501c52000d03000b1168003d0740140d502184030048035078144070103083c0c9000e201d40d590101500c0003484000006c2800b10ba00702607010104030019031a0605188010a4410155001c078a000c0041c641c031070188003040840141040340101c03030341c1c0c050010244411030404510701d14820040d810744056104518400340c91081c41d0300015070714511902d07a40600034038142281c8075500e003520640103d003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 920928309 1250 920927059 920927089
    0x17010c0905060405040e0f0d030b031510050607140a0308160905010207140a050409030f090e0f160c0f05010e0705010305091c091203230306011e1b050c 67
    0x30303160204002903a0303900241c40a850045400003240310b5489a22071510341a09081c44140c01348010320710549030141c2c0019840c000c1039042c2ca28034050315017100d000320800c54680d09070365000e500038000740c1040d00c050072207a4444d01030b01c4410092243d8480c54449040800c400142d410b03010050541ea01d105100c0880c0d40c1c030700b8512680790802c80040c1d1143c40f44d02a00000d1035078142c111007256100c410810080c04080c004002c010305e1400c1c001e040e003180c0c4002c040421640b000009044288104c0144104407450510019840781500c40d01d01d5a02103661004001d02440000027041468404c000d8880c42180000307840a90801000e0800b411540300f10305140c83e000420000c040e0105805400f034a003000c3da103101c0300e00d43c00c094a802e042a00174003100e07080c0010401c109078104034404005400c8103401001040301514042d50740c88112500303800209aa101c82c1c44004036003000c45407021190618120322100e4403170b0400c000002d071034251440d501081d00d0000a00340080d1030a0040 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 920929559 1250 920928309 920928317
    0x6020912060f1008060f1f0509041406180a1101170907090605060901080115050c0319030b040911130b18060913030f0503060a0f0e0a0e010606210906020417010c 71
    0x6ca0034110a00050b44024580940f070031014600d008421400703405140a01002031641010707082c1400c0c0a149801c4056504040f8400d40c004245d0100c001e45846541c04a0080280800c0109549034240c0e081002c50060600c2016004030990780400b01500340314404520060400d140341103150b200380c40c41640024001c0404001403074699034081021415600781c2c2d001607521034a030400840c1c0510628030401002e000100b4481444800c14181039995100340e903090101c00744420030031040f01e042c04001081072042410003003007410103c1c500b644081d10028002140740c05640850350310310b0002260310b003003c069801c10050b40f416030780039a0804422081c91a07445030381c3c0e81c0642160003054003202030140c0800024000d03640d02c6040c4007d003050042d041880340c0c0d102d00130b600c0c41400703640309118182044401d200c11501482804c2c101c0340155070301a1240892001d801c500009aa20490610313142d00454000c5649070005000400e0b0505c000461014205c07000307401c4600800c1d8000401c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 920930809 1250 920929559 920929561
    0x90f060e100e15090403120e1516020c0301020c0a020a170619020d02161203140115090317040303090f05062a0601320a0306020912060f100806 63
    0x400e2100645030151802410b0006403070300c400041d140f08030004954154080c1e19001040109948086484c415410701c820521010340b03245030098607042811201c0d0a508140000a0004400c05442100180c1c25005a9200e030005070040390aa03445a001344686038090b03c0010110b05144002400405000c500d03540d244c164859aa6110f900160500101800074510804201e485038100c609a001c540700840d5240c20050082c84403c00b1110306036200d120380440b0906260090140700b514214031203051840780e003098007506081111207581010014103001c0480003442c0e207010209030b41d1b4105801c1e9100c5143d8500188008440e4015a2a43c850b00f1010400c941f903080648040c6207a1039480658940b000b281410f50b84000c91019200b440340c1c90000900050410113078000400031041e0059403218a9030145000400402c0b154120040e81d0040010540c10b42c0902103980c40248180c980a25407060f443c900303207081e0340c1006203121900500021030564421000280500c602804013 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 920932059 1250 920930809 920930821
    0x40305030d0b13020c1e030c0a0303050910020c03130f0806010306020901110604030c02030105072609031902030a09090c08060d02040e070602011a18191401090f060e 73
    0xc0740520503451a0392a2104201c503410ba80c0c24074925818805050110340b6195583c10303a030341d5514419016442003000c0d0111260540c0c002c8203c502d1484040028400c5070790f941d81c00c400411009000c10703114026801e40138902d190368001032282003000e000441d290000d426040c0f0703015400ba4000b104101944108100c0d070040030400b0f43c1102e82002c40140c54440450050381e007800305003900e48081c0141d600304030416030440840d0300c0c0b2a0095000300300c0e40d40d6004041c1d81e00141099040c01323403684000c0c10f40201103440c09540d40a0036020559080c248615103841c0c2c0d5500700458080960004154540c8035544406100010410001c2c00d11420b040c0800242a40340042c144500810f103000940056403120b170050b5150503036481c00c4595180e40e40400171f00030031402800d5110501c0b4040d03207e0080c5850b0f000c41c62040c04102c20350b456522100e040507140500e00c1882103c154842900c440c1c3e42525260b401d00030420721501280d000440100a411100c098214041c9840d4500034801 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 920933309 1250 920932059 920932063
    0x3070b060f030d1112191709100e1203040b01030b0a091a04170d021b07050f090403031503080901261801090c0603090c06050307020a3801060212040305 67
    0x70240f225401d0040100f109001500c1c1450900000d141c0a0341c00010340c00060003610700c03041d56a0781c2560381c0a060488804040c014428181c544500d00c1d40440341151101e4402c1c2e010403020007441e0704860350442c146440c0d00d480e800c110f174195501d0007140010002d114a1201003580142d0028080040000c1c1ea03444c00072050301500240006c12010300050104040310411a6030300c40307014003060f01c6003641801c00000e5400100c070104a00b00171241c43e004040009511019039200402d043c40c0c48a02c2c509210b540940200700381c0805840d4000b078010040c2d01e102301c0700039500a141d41547c42c010a000580b8441d100c00500c9170305183e40a8000e041203d9540c044d4200d002100c84144000250749801e024044140b0301810094100400240b49509640400c125034820654800184e6490b9001d4589000071100c14000da0420010000000e80715491403a80e00300710009100244070865036101c80030980d030854109401c0300001400040e030100022900c10003031000309480c280c1103607661a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 920934559 1250 920933309 920933323
    0xa1701030f02011b200f0a0b040501030f0e03031f0e090304150c050d0e03010e100c03060602071a0702130507080a180c050922030315050a05090f0c09060a0203070b060f03 75
    0x2184090306090041e0311742d610803202d44078003403000305244240c03901c0712042d0317009910500c200c5010910304200030320060f072107007e0b00c4e032070b580480003650840c0e8407080390140c4075212139080a007011948001081449042001c01d00441d5688000c60300c943c00d00000d100c086c200038600fa8144040040c50000042c1d0020fa0000186010b1800c2c0d00c1c4114600086405400d200400d8240c0d80580103079181e50480d2a4401c1c002241c0956091180c1555040140d80340da40c5400703280c5042080300c0a01d00c903082000e00804034148007820100380601061580004c58005541820001d039101040c891268114011a170360030345088a81040c082d16aa544c0c107850b000c900c80c55005a414400050603600210000b02e0350b0b0341040300c02840500d170342c078005004140d104410500c01c2c009810210f86401c002407014180d81c1c0c0070300441482d0300c1c4c1540c1c1207000300d00103021190f181010400c405081d214400601620305082e0019038991900e498078120104004110302d0040c04681c200d4001e80e0340004da00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 920935809 1250 920934559 920934593
    0x31b07050a0f030e03151b031006180302180f0a151a0409060807030317010f090b04060302030147010f0314040c1d010303020d050a1701030f02011b 65
    0x300b10381007601c1d081d5100c00d00c062a4a03410700407914903071100122140300c0d911500c110b420504001954032010800d0740400e403248240d40c1220b101c2808000d004110603c4901c44d40350001e002c196903640014000104042c56810b013280c0d41c411b20401a240c074001507004a1840014461600c0e20742c105c1c0c4440310507120b4110b440d540700070b614220100c0101154064108031505014007030b1500e8200340c1d500418402200050000c0781419490010007039418141e03081c02030302404117460041b071440504499000c030755100c0c2d5240310002c01a42c0c240306000c446c0c801607010800f8011007981c0001c81c4101c03d0b60104041c4402e40010103801c0300d120007070346001e409003041610b90594a80440007404000b4685210f940c801040c8814021102c06060464420401d070100300180b141107901d9006007880300a025030b0201d24101412030040001e0400020035103400c8904c4041e044005d10403040a0f0f00541b0352050004640c0207559011a44625410400c45101c1440b0096074882150b12098080 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 920937059 1250 920935809 920935823
    0x310140d0519030905030304060329090403050904022b0c0e1003180602070317010504182004050a0608160f09020a030f090c05040b0d02060403150209120102031b07050a 74
    0xb4080501604114020b080f000d0100c036180e0f070301c2d024050010a0701a4208040d40e9401d10700d500500c3c001d00203801c400c1006881c1024944655034141c625030803c0034201c0d0310540034002c1042c0001c1020801e062070480e0071200c0000200c8404110440e100300d0345280822408488401070340d16141c21381030010581b442d00044410a5004d05800c117004031130300908890000941c40281684003840d09030488070003201d003c541e40e071141080f0444014225003000e031040c80d020000429460100c8903502c00d0b101540c4040150f01c5000a02110001c43d0713908901540c461003400300350707410450f0880500f04108412a0310f030400c81aa2a5800d80b48101050603800003140340ea00c501c69041101803044070038041c4802d440c1d0f0300d851014440c460040502403854448450b46074030344001c081491640152140789400e0554596000d000041404581401d4003004100c070940c0304e04441c1425521040300060312402e00c1a202c3c4600880f04203036041d000e40c148940000b0034004178076442910340c0011 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 920938309 1250 920937059 920937103
    0x18040c180801020c033001060302070b150d02040c1211040801150806011205240603010e030f0a05180a0b0a083105010902131a04050c040303080c0d020310140d05 71
    0x2000d99a803130200b01b5040e2040301c03e075000180c40c80d01038015243e0940305036080b0080f03540e01c058507218900c012100f40c0d84202d4902903900075003010351040348484030b1403905107000d0a01078900b1003600e0030246482881c2900180810144c01c083c800c20f845401e04040b054000303803070500102c1e51000107004000e8101c500c640c159041007401c002e4003c09a5003000480d8000c4070300042071002280443d44107000e5404d00090140c0203d0100072a030f0b21a551569a80c1010820701c01214a90481070021265007182d5460003401d603a0350700c0c000000d1080080c959a20f00c282040144101805030013107200a41000602c04401040c98412f0a01300d18014013180c0b52046040c0103000d04542900690401803c00302c0c0b0034290b4154101c0400512442110480c00ca628021703c400c4a0781150101c003c140c042c802400004d200b00388043e04031140450007802c001071381d503000003240e00940703200c201039980c1c0c4e004000c1c14040103445100c001c8101da20105043c0c5588441c1e0b101e0f000e80060702100c1030103070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 920939559 1250 920938309 920938357
    0x4060e03071512240312030603150902060403050703050c010f080f011a0d0603030f1d0f06031b1201150e090c0f0d0213050a1a0f18040c180801020c03 66
    0x80c0c011540c0100d04c0740030100140200e4001d20410941e80020744107420010310005035107000740940f500720796112030b8002c0101425140343c801002c1201049030300031000c01c000004100100560300203540a540900301440b480c00000d0705000b00200342c4001d2044a60411404c045000a0541158100c4180c003d5080400702c00008074829000b12880a41c600040802455441070704210640d1b469150307410100651009040c0400d030705221250b10980c81400b610040c10114051a0420700c070509174800d0401d0010300c0c1b52213800c1500000407001564004102e803c103040c0c22584c2407951818540e0120301c0308004190402c400a1000c040300b41c00080389000b1510440c111030784a403121200315200c0c8500c031030310400e2030068443c240c46865030381c4001c01c00101010f41002201c06941d9001c0c586940b0403e0010b06070800301c483c0e96a61203483c404a0b4545403802180f220020b20f41e2401d0340401001d01e8560050700d9500005520303881400001401d002c000120381500c0350030321240d0b40446940c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 920940809 1250 920939559 920939561
    0x5120d0e15150d1a0a06142b08040603090b010b0309060f04050c100306090c021f0e07030b010e06010210020a0c030c02130606080708130f02060901111204060e03071512 74
    0xc40040518109200b9003018018113000c45014011000040c000c8598810900e0441a40d00d01040d6010300d4003083c2ca44001c102801480e80380d00e181c046e802020089488100c520f801552080010070f485101d40410010130001a50151031041d844608604080750150750750b41c002081c002003140400b0100c8c0510500300304029001a000381246860684030100402030840c0c2d10551882c58141f500130780e455800418001a050b130450188600710041d0000e00016241582101d00d00e0300038800f010012070502d2500c0350180444800100c924140748000929107030040e08400911403051010084099001110300022605840d085084545c107000141c1702d40151040e2260b00c6160050000e0403a811040f0144500c03102c1e180c00f41c190381e07440401c00940071841070051035040d00f943c50f01e005152810181c810000f0615006821250844100e440c120b88a66070301100c14011404008903640070112103410314041d009440000c0c43c000f6000c442030b50651164085c40000d0700301352004412 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 920942059 1250 920940809 920940829
    0xe030106030804080c12011b0c060e1c080601021501090908041203090518100b030a3306090e0a050c070b010914070f0f0f03020705120d0e1515 63
    0x4114003c2d561540c56001940c0c40040b450900e0044c01103840119940c9410f203d0b500541c00300c500500107c00710300c2c108071050480c0d48801c0f101695039000340c0c405598108206440d6140581c04052600230011014205179801080c1e18115440810203a05030122520400d0444602e0704012442d01c1013450000202d0041e50844490800c1030038842050603480304056046540588005413120100c018640180d00111105009441404410040e4143c8400210380c4a03420410020390b002c40a58910320141301c00b071111001d034000044007d1043c40c9900722800400c550304041c100c951812a41104000b4020407400c03200d582d0344002b03420000c1420803110046e034070060703110b499a11802904020051a224000c10441d050002a6014081c1050400c002541e40301c03141001c020804c1100c880c14a120804201a002d0010b6070003d14200715541c0f80d6200020340070344644c403020404080343d20401010780198090041004408072501c0840d0b0020401902d942035515003101240b10519 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 920943309 1250 920942059 920942063
    0x1021216080708040311060a0c0f0204060302030d1205090a1a040c0519030521070f1e0b0f130b0c091804030e090921031314100f020414010e03010603 66
    0x200050050100f1030410001d000b502c1c85a0103202580c1c0421090107628040e5540c03840108513802c00070004510068a8055807510050011400c0b0780c40341e0102c1d0418104503031240102d00100c1c2d2060710487c65006290707001034080d0062000489540300d010420250405000c200d05000d80800e09001c06201c400d005003002401105240410014051485025203c1a5490f024502259024601c0944a0300304817544800032410301c02e107916803504054420604452140c6044058481491803400394243c160103010751200c140707000d4440d0318459000400b010159090101940005031380203001c140c00c82c42e520029900c0d00e00d684041160319a210b20880128049081003004040d407100c4100359404c1e0070303129540c035a21100d400b180e1b510340c001c00c6000100f400851410140d0075070409142d00c12042410098940d61584510182c0041f5141c0410160000c0030b540d01169928020422031440c608021480e040c500110b542c01448000754641c10001c0025408459135025001074003d16 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 920944559 1250 920943309 920943323
    0x40605100f120b1903030f050a0503060915031002090a120525090207061a01080108030f0c030f1b0f060408030708041505190b060f09210a0b06011d01021216 69
    0x401c06510304d0105005512044001404610303030a5450f1344104140c0c1c82c03000c0c5a450f80c03402c5485a800300500820011301040c5108000394400c41e81d95030800043c0c5080101090060f6100320100501c4914801900071030741c9800790b51250340003d080082e041c0c03410081e131a00490001c211510324040d046c6550300481820f0700204031007040c441e00c0e602c1604141110b0300801c0840d501c540041d10401c000344903808480d041804071468064a41008100d13040070281620f14040c090240a2000d802c6402c3c1d6015035260304407800c1204030704000c00700340703004860010460380c40e0507542c800309171000500480402c10300c440810100141e05007042c011010010007807250b0b2504a6082001800c600c2c42c0c40c0e4207134102203c06005080110803a0343c001d5a8141140c5846042800e101e80540c031003a0030704407000e00b003076180703801b0340c0c148185400c80388a809040400c0c1450b10004204141c142c100116500d4200703240c0169a070000382404240310042c1d1410784070151030007e002406484d25000e0001 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 920945809 1250 920944559 920944579
    0xc0b0702010213090b010e0405070207030204021810140702010e12010e0f0714031c0e090406020306130c230f040e0405100902030303070c0c05040e0606040605100f120b 74
    0xaaa0190042d200b642030301d048000340c040d80d414040c070544e003203880c007140400c00200e40200d00381005d421260340320380c10740125060190303a41c0c0401c04a9000c5c5440b00581c0c6d0030a10030a0940c64402d01102c032a05551426082503180d441c241003851050a5000b81401507058a100003611405501404980700100070000102d0704503003a0b840380c4400d940038199001e1400085100603503207081c011000c0024008000002007000007110280e981c00400d418408132550340e5003260b4440185034441e0b4451540542c8a003454401d2010f1406080f060310074050030413082c10641030780100103264000c00601c42e0003c0c0311100440c4403040c4101c480001400c440000c0205a9001c9814214012841001100e01404111500700110340c8019002076250b00104080303001207203c0d65062060902401d19511100c0d581c0001a0445000c0d039100410b5420a0040020078a030030b00c1044e00a000c1650900074079469208010045110079855500b0b00c0031002034036084041c554080002d0380000703881d10201c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 920947059 1250 920945809 920945821
    0x15020d06090c1101052a09190f03032d030515040c170f040521040e010312172a04030c0b030118060503071814040b011401090302130b010c0b 62
    0x514846800844d40c2080d010034a00ba0100100f16501d840141e59110050307504040000741d03034444401103600c40c540b5452649481e00b0b5072200401841d6011800c083e02c8e246141c09400552140f0002040803242400703110b40302c400c83c44074031409560785000102c95603030043c0d404450020504090300706180020022915030002080030407141e110000050a80c1c840200044000e07086800400d55003004160180d21180c070000c115042620744a0182065240c0301001c0205500342e08c00c1e19045075485e43c06401580080215010310080c0c551260b082c035001c40146180681da018140029000300c5842e441c20315034034282c0303001d03591121401c4420342d581c611f49070554101b0700078081c05000b488003240410005101c1c0b502200c1c0c014001d440c0c42403601103944000380102c001240305903100d030300c5204000207100c083c5100301e10528100503103506010240040350b40404040d81800310411041c40543e40700416902072049050010405540c0100121985800300900406440110042c020307 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 920948309 1250 920947059 920947067
    0xd0501150b031503010b060403121101142e0513021c051501092922060f09121506080307060c1e05030f070324081915020d06090c 57
    0x100503606201803003030002c00c20f82010b080b201090741d5264401c00400c001c20004010014a2001c0c5a0301d04014081c580d0021415003580c84860282c4102140107040010480711486500c10000c00100c0d0100c89044128000070007076480d0048a200303d40c0898140b42c039100c160112222841c9407188208152100700c112005800195041014140c90707041c080b00355403144140c0d404442c00b07620044480540d400307514804000c2d0054001c2052020802c1c401001440032004900c3c001c4031250903d8180350440c000c00c03040c0030302d5a540401c002002c0801040c0d000784542c0203041d0300159400c481d07a14845110f4003d00e22030344590708038003010803800d00b800001c0c0e000e80c10309040c17521a06402c0e5444180d282c0500800070100c1c0c0031030000d0002c070340f4103908603004951185050600040610031000221a01455201d6080d02030102c038100384070800085c05404c0c035040b0401501030381d51300140d44400820950031400601140e020540ca2103000a03074001c0d00007000c030454100f00307003005654010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 920949559 1250 920948309 920948311
    0xa0b1c0c1401111018060914070504050106170604140403091a0301050d0818120a03021002161707083007020c13090b011d01060219020d0501150b03 65
    0x101c40d01c41d8101d0406554011526526510074640240c050800e100301d6540c02031003900521190032414854030000140d491041c450b00300d00810300741c4041003403e100f041c6040f840d600001d001d00c0c109801002459080300c000865450380c602c0701c83c01c940da4800450300906203140001c20424400c0280b106041d0072007680019910380c083c03141446052603007041c10a110038420b0b90340082e2a403d060000ca503408024280440b40c40081103640350a1a00141d000c0620014503030f540d40218107903404141d0104030032b5004201c5c400e821360911016030100d0682290080c40540514160001d00c540030f1010700849030300d10f034031100701c98176444044510207081d41600c0c040c0804152111041c14200d9540052034485d80e49503000f4102c2ea00024240000450926202d00406444044044c00104a11142d90103040710301c8540300200c601401c4034005a006a00c4a03080d07421001010006074822504090119010340b648a840c0344140340c51070041040300d031080e8807191550004141d0381c140d24021 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 920950809 1250 920949559 920949569
    0x10031d030a030c020f030705030f0711030708030d1401080607051c020406020a030905190b2a0c0301060e04080306010c030e030f0a0203100c17090118050c0306130305030a0b1c0c 78
    0x1100070078021840075649100380354000d40235a105008495035820072000a00701984a01c81ca134a14980c0200403c1c81d080c0240c001e0b590a400101e5040c2c2c40f002c041c41516000100081e8000e055450301d0405502c8660140c020720800000080802d1990510a801e070418200804119034455507402c00039200d81e400701003100080d04800c000283d0b0316202c2c00d0034844d44205092902a103180c034118000950103180d4403030340744000c205590300d0a20f6003840a0103000c400303000743c119841c20300d00301421102c20341c04c40421074001e601408007080d0360000b1340b1b074800c00078208840b85e00003d060580300c2d00070f508a000c0d0b0500c100090452181e102041d001002803098085800c005409416202034500c00c2d60720300005114904100350301c90f00c405549800031040e50000032858042d030101085000701e1441a1340307a90002c41e004085080400410394404c007282403462b0210100c0e034008103544406082c801125440384008a4650f0320409410103900d10b21002d558409000d24001000c01120301c54 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 920952059 1250 920950809 920950813
    0x2010e0405040305121807090609060e3c0c070501060801020414190509070c0510110a03050601110303100f141f2c10020a0210031d030a030c02 63
    0x1620805040c24040c07240110390580f14941031038245080020704240c020710041903a0f1410004600c59541800311740050300c00ca10010418074148520801a114568032112680c1540e40400110b0940040b00b5024407411030306928451043c01d4624250102d828000c41c2e035101035205000d00000300c1402413420a200704028403105580d20350043c201c0c081c620034046030b04a070801034201850010444142030102101c1c0710021a1907801240800c0301c200c904501082007003002c00c061003420044c82c180c00c030300f9031010f1050280e1500c509500b80036101e1a001030507203a10101e81240c0c054035960300403006c20f030100d07910b906d00002c403092058042c0c40b400380040865240446e580408000d80386601c200030780b40181d490408a4a09481000f1850301c400f004101603400440015880782c40c0b401c4c0380341c4860002c0c810010400c0014080c20007070744109545c440d403140c1d001030300d520140014141842c03c0026502490090803030203040052a102c415000000301030803a60b4050380080516507065003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 920953309 1250 920952059 920952077
    0xc0201020d18060e030f0f0c011707090605070501020714010b041505090c070c080106090204050109090506090f27030304050616082202061c0b040902130c05070b130201 74
    0x30040d0748510002000c0c07002055601da00b03103c003030b0080e455030010110180458016202c1c2126060410317408840901d075640114058218030740e40000100040e07110102e8990142c1440c038005002d81c105442184113000d4003050483c1400b8080d81603d0b5800e07003041000e442c2c1040d14110310f00820071520403503c43c62400c40140d28401080b9a03c005a400141c00d090301500c2d03040000c10280c01c030110407179103621032070008200c2c05003c3c0140e50091108031009a01e550600002410039001c94000010701c0c0e00e449c0802440340e5648003200e400408841c411805610b8650b00b10031070150390191814104080c08104054200004c01903100da4000c005555154030361444400c3d0071000710b0301240002e582103001c07036078002034060400340010400759850311815480c0e000c503802c1c0d0001000e01d81681e070400c82442294030710340900c42035400700f04da040108003001d0f400101c903140314510b00d9000c07039a81ca0081c9403250107031040310341541e0045102d5440f0700c0d2141000991421440e070490010300c10385 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 920954559 1250 920953309 920953333
    0x1a1902070504050c090303070615051e0112020c0a0320070b030402150703080c030a090b010e07020106151209110a0b0d0c021209121e010e0f030c03090904210c020102 73
    0x1000391755020000501452424890f0345800c000b500c103440c410b8090942c1c40034005101c0e034a200642c034179103400c200d42c0d5048204520014102c061a803c00c01c820500401c402c40310400041042e440c0c4a51505140020284900c030210b18801100008a498426510007081c005540d10203144030b14401c8401c0907410b0140d501e040414041e0000040200701181e0110b0108100c41c009581d100c50800d80000d5960b0840d29900102c40b000c0e0b0204101e184042e050000d102e0f82030282c4030180030f203845503910f0320103000c20041c889110801140101e5036180030910811098400c44480400d00611140780c40c1d82701c150404286e8001c0c04c0d00f6440360300c0c0050200b1500d00100340e2401148a07284200c0c18034080100340071902d09095000d08060154021040d0340c10070042c50150802d2503079000166000d03092200781c1c0b514401d180c03902d480358024002200c40c110300004513003460303200391043c4189854600c0d100302005482d007042c0c000300c041c40400c0c0d204182c2c06601a007009000760700b100e0301c0c0325000c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 920955809 1250 920954559 920954581
    0x9081b0c101704080d0606050c15010503100218060c030406080f04150207020619120e060c041509080d020d031a03060105010302030c09030102040f170f03041a190207050405 76
    0x1507440400700e410b60b0014519181d02d0b42d0b00c198000c0c00303401a546001a20401c2a04548080d00311101080001c00c030100c03004000c01070940f128286018140981d4101b5000981d14444140d02200d07054000820622220302540200030414002c0c041540b038082c100e540751f46a80150003030800060300303440000c0c0081020b0350801d0003141c02c4503641c20b0b00103100d96004081e40c4459002d9030481d008000c0301880069086046503504c00f01d0707a07001c0e5089460340003141a10849061f5014540c403003c180800d000f075400c11203003100e902903c0c1ca04860342526043e1070a183da603008030742030300400c180b2400141d00442c1142a0501c0c1e55020848014007100d01c100b1348158a44050300b40e480b0000600403940070b5130003103410140b00500b507410f02a5001c0022309907845900111304501441d0410492600542c0085000046101c0540341500c4200601031356030260f4400d0301018451b90411807a102454401c681c02d4000150204041135158800a5542e6001c0e00c5018010ba240100081c1c1600782c03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 920957059 1250 920955809 920955829
    0x16090e13020d0b1f0f030831050306011406190c080a111005150f03120f1201051008070f1b0501050f09030a020c0105031e160305100e0f040609081b0c 66
    0x145c44505807243e41151607245498000c80040040c080300711a1508100c2c162403003a02810305610300008d25281050103042c14004180d001300d0240040d048500c541d5500d60094a4246460904218038034000c100115615111400c1c007500d02c820010310b40300d901d40c1c40a01c080c0310290003811141c8096000e04d000f800c071101121803400b07409a451070820180360400181800d41c40050460b016001112b40c1000c003540000829000e450b0f00240300032004054043c0d45004180c01c486001e215406550080e2400344010409000c00c007240ca807070054580a40c610800c81500186002d07002e00141c0317400c90003080c0070703900c40d0b0031203804c58002900d4417400005c50388180c146070301420f01500c6a2005490940020344a901c040b855058401220003400c0322891041d0703040c1d520052844080c10003d000c5900203050407004040c000014804610500015508840e5086c00c00956540324240340b00100315944000b0002d81c1d00160080c0c4030303c01000036103100c98001017610011140030781002000c680c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 920958309 1250 920957059 920957069
    0x18040f0b1f03052503150f0609060305010e06240f07140c031219110f01020909101211210d02190b0604150801090602070b16090e13020d0b1f 62
    0x21300f40000a549109030041845000e4402481240346e44030f203104120480701c3c0d0001c1d000123840160400c8042d0381030054500403c15088000382504105020801c100c0905110005030050342e40e0607507001c100c0e06d045800941086100c1621031185103000e0010810ba000d25000701e02c05c01d48000e11618010038028900410750742c010b89040301807800885044141044c12040c00752110000722600c4080c800c03580b03590003402c00160b03034220910400912420103051403182c40000d00741480707003503401d528002c0c6582d00202010303003800c8000300042040e041c3c40300c5040200c603030342040d440c0481c0014204018004031b809440c00180c070705001811080c3d410602800c0e1480e02c0d0049151428070b6030102d000344030452055446136460710380003825143e00d038804480c0d00d980029418144240c07000842d40000c04189030503a4a4012100101145a40e000f4030403883c001c2000316000903104807114030003503030203096a01c144150b401d03c070b4000780c801c54030086480c014048884241e152140141c050750 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 920959559 1250 920958309 920958361
    0x120706031b020c010e040b150313030f0807210204031a010e06030109020603040f1403040b0d05010501050405090a0b0a0510090905090f060708040314030903070309090218040f0b1f0305 81
    0x452407000700005401c1c00061641c03c541031048d5942500c114074020344c800c00040010081d64005c0e42740051498002c000300720300700483d107018052032540c010100f20140b41c10002c22900400d010681c44001d21580c0e00c02003050300301440141400c20f044000d241220405101081c03150380e44c0e424103090301d1003100d000358410800c04c00100080c00000c1450aa180501e0244090b11000c02056185070300907081200101030118030541c0099582c003902c0e001d88000c2c40d040381042d140c207000c1246014082c0c8603407420b949400c10a0100c1d11100f003800e009003801400b00004d520b401c103000c0c00d075803018010750700301c0e81c2030400240d00b024000900c100b05017140070042025658801084500d5000a0300440c204000d4200b81c080718070a40c07000c2e42c060031090010355075a00c0c1510b00604902030942c0105001401031000c07001d50796080d40000c0c90400280c90118951205501e00001441000d01c0700c2d5019000e24083d20103410034046002d40703501c09807020012034807110040c001d09205210300d50030035 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 920960809 1250 920959559 920959577
    0xc0405090303011a03040f290907030f0308090c041a0102120c0303071b080301061106061e010f020a05160e0f09062d160201240311120706031b020c01 66
    0x190081900456015005020912621040790745a204466000b0300306680c0081080d600d01014040b640c046401010800c01021b02b2451a51420305000100b800901407081040c001501a08288100c0b03c0c4544014010440040c0044517002c07421542c0c80d100e401486003041445034080120101d400c0100550015030441e56031040803140b810002c02d0755a9929041030442d0000f0381d5a1002d076010f000705481e010f05d0484440642445c094005091622810310200c80302c0109508004041c2842400c0c030380500151000c14042c1d01c1c1540140c401080c034401c070302c10070000004d114522016100b0051520629449044108481e01001d07901c107411600140042502c1c424403403580080302d0701100341d10059041403c46040840070448640c06810450f1402013000b550a01c0351180d0388058500c802c0550150500d61282104540801020350524403001c21481d83c400c5d030358222015015086848264841c5001009041d11060046a0380100d6001c0c400d41c3d8000b01d184a820b4106a545082e4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 920962059 1250 920960809 920960849
    0x50d06020309100f09141617190b0709150f0302030a060503030d14090708070e2701230103120c170a0818070b07030c081303050c040509030301 63
    0x7544050705072034280c0304000c42a40c4400c80d0340504000780d0f51000c40003900400a081400c0c5403220f003403810b0400c0d00143e466403c06207000c080c0300c2c284c1d40000c00784000c415040c4026072804d030100c080408000348030b0b0310749410814803a40b81e9104003800d03620901f505554065140d61602d24000490224101c2045595098825405160302500c200004280035650b9070100c1d00316880748074180d009a44407610b0310f00e000790300b003c4a90050203442c000c08100b490306900988420043c0100403000280c400416207480d0841c612100414200b40f2290203034003040b081c1030080051064900e00d4031420041c8450003c0080e100074102d030b400c40210782008082d001300301c991501d1800c04407010b1080720685035000c141d21015014031803690b00d606109041124000700c210f81c0c0100302d00078540c0440b009102080c113483c140d490290f03060078001580111031411100900900d88030004014403103100005105001440743c8002034140c5041000d41c5600c118a038a0344424002c0b0004031540a0f0400d40c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 920963309 1250 920962059 920962061
    0x2010903030807181814100b0306060904021b0c06120a020d2702040e07030f080304030c020301090b0402180c03190b090c0705060106030903120906090210050d0c050301050d06 77
    0x140c08400e07071a0078a03613940100054850880d860300490701c1c0c4400d4506498140415118004280002c003482c421a407511451100035400540505a4211030110104c0d00c030303484450030307510300c0740700100259240c84664003d0f251815800000c410700307220340e104181e42c500380f000460307400b204e4040e030518065560340c400c1006503000058280125a61701c00048000448031840d1b02e1242d069032200003807030039500400c401d413803602c00100c1040d000a8000c00005401c503030b840d081e00780e02514964599855081c02e80e5051300c1e500c000783d050350074504860300b0080c3c1c401c0c1e194441d51088501c101151909c0c50903144810044542118119040001c41c00907812a80c004084400a190100305100d5080c080748020b403003998210725002001c03500b5803c20005204c01402340201d13180070815504070ba18024484104e01c4240701c0301541c0d0b010410309020303007a003080b110160040d040300002c0c11960380c000c2c4564881c2e00000b40052030030481510003440b41007203e0403942c00410500c9106801e03110a0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 920964559 1250 920963309 920963311
    0x503130809120d0906170f06120d0e09070c111504090f06210c05010302030a020f12070906020f0606060c07080f0106050f040203071704060e0a0819080103020109030308 74
    0x958981420301c54070240d9a41c1200308141034281d0400340c1403603480ca1601910700d10b00c1d0741008061101c11403d56429201000040342e000a840921500c03540b0f4040214038410102d94100400740680c15540c504150416127400200d1003d03281c0030880d948000c0c3c103c0c1c60040400004262954080040da00340c64012520b418540b041c505403440d1565036084003040303402c0c042d03080148548589040000705100b01c0c55290095002c490103803401801d80d10035400b90654040d250505034003002040100300030340d051725180038100c540184c1e40c0c0b40c606800044e04408544075030004101c480080303502d91003c030b43d101520300c03a60000d000680b90390041154613000b00c41b100e4100e104178000062a1207040120f40201100400006000d60902092018046209910030302507401002408001a4400c0f007442c0041c60402980589459604d0040060000002d07481150300c501001d04080c8070745400104801c00130b505182d05410303240e15007a242000b00744400787c04503980d0070041010a020b42c28031 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 920965809 1250 920964559 920964563
    0x717071b260f1b09070302041d070203091221040b0412140a0c08010614060304030c020d0c0f090e01110f0c070b0703080103061505030c06070204110d091a0601050313 73
    0x900d0104040094007440d18507901c44035100940303404410f240c0d82c1005246684c0100d1340349001d515090502840c580b00400c010310350041070340001d001030f00c000d2003402956a1070742c00908c88883e404074000c01701da560004000e0003810300d403060a041c200c0c0c05c0c150100d50450b00281c0004e41410314021614408100d00103058030119090b440901c4040010300c0380150b4144a034801d624890f090880c0d550840380b181e00900c0e0305008120261a00340c0d14241520340c080d0b45890003080c02030191002c01c4400c3c2d845440104a8101c5400c04282076503025204001da4400d00c00030084044000c1c0c0315800c1c1d4050308030f0303179407800e10800c0040000d046440081840503110380c203c4040564602c4040c2090f03211141c180c0001da81c0b04014000c1041034020310700840100c40181c40c11030f061074006500c5020900f506c62242c0302c002a41c00c11501c07140c01680c40c0040400906031102a901880009041445c40448840e0446440c0b103210318058003c00d4040d110680d5198219070390300c1a0725078448045442 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 920967059 1250 920965809 920965813
    0x1120b060712080106021204050d0b09010f0c050a0f0503010509011e030f06020703110a02030606120c040203010b0a0e3f0109050109061803140f0717071b26 69
    0x4072010a019041504a0070303120359606045600d021402420092090f06852600404203c200202e41e0380030491507107550401c40c2d2084603250311003101d0052040c262031550050804810940950700030300038000819913903d51305064a032020b800c44c0c081c071003406000d5000c440c3c3c1c4011320210f16841d2501c410224480a1010b51300d031662203007580902424412546280c002580c481015846080302c0e6103100c054006101014142d400a9240c01000b400f03140229020400d0344001c41c02007040c0e0510900c05841150f503544c486440c9041e0b5880303039010801160b00d03405180000d007001800c091404050f200b0400045c080300140358a4030b003100f41c05000c1c4414410350800154000e00c2844900c42c460000082d0244842c84c280041d10412020401ca074501c1004500120780c0000b8090400d101205041d42e884115403020a81c034066400c02030001c411001c01c030605201c01c0d42c0200203041c00703158241000e1a0800800d401407080b030242c0b4020f9540c0c004c3c204d4185e100342c154900c0c1a050801 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 920968309 1250 920967059 920967067
    0x18050a17041a09040e1002040306273903050d0923030c0406060c050c010504120204151703031503010b010c12200331032d1515030201120b06 62
    0x1c0e41c0d840c0c50b00200140039055070008d02003080051a21901440560842d001c1c1e091801d600b519000c0e4842d20000a0080e010401c2c02488400358804c0024460001600840040c185d45c0c40e914003444560008a6031482504c0e00c240b84030b4000d8800c001110040030055401c1c6c83c8000c99024005020714405405111f07416485100f6680c034081c0340d01602903030345da40324015601e0400318644101c9240e83d03410b001c000c000a216024400410704000342d01a40c000c280c21082011b81008900f442c0d005840100c000404c8460180e404402035008000541040c040181c40c482054220303400100754031302050b554201040003c69101040c80c001d00c860400c5c41400a04400d030860350305200b10190100e8000080389a50700c0342000078029070803131007040a10011590804c0d0041d640361400003400602120302c1c0035499160003000d00c00520f400900340c501400003898134401d44c0c0385000500e602c480c102080c402c07221055110820483e030f01651200c030201009180c0b80b009010100a090704014104 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 920969559 1250 920968309 920968331
    0x3131506030501181b23030307050a0f050706090f1815061e0905060d090f1a010510020303040c0b090f0a0b040302180c0d0f18050a17041a0904 63
    0x31090780b50520102c2032a00e2403a030140b80003008100c0c4a641004800c80c18803045c13018400e100340500c1b420501071640075180d0340810000340343d401142d8000300648100400a000c1021640400d035005204400b00c60b0590b0f1504800d50700c82c0d0483c012200e140300700c0b80701000303901e0003503400d2081c01c00c40700000248900070070300c1001e001c1c2e03e5401003004903072846180c81d0220044040c8030350082c95440e00300303541401c0500141c0340348509144802559100d00714070050080c001c180d080107a074441d425411a548001c8096443c460034131905120701c1817450030f02926070000c402c81e4401d907805620760713283d81d0401181c038403d50480300c40c0e907402c01c0500b0304e07089150b02d61203413542c0908035122800b5142c610b0b5204020031078000301c07250b0b14061210010311034030b129950142c920066001c2004a10000040b078000c0052801401c044034044120180009115012480c00c4201e40107040e0000358101c008210001f0780320f948905000c4a59900c901c060104117880a810524402000800c00314640 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 920970809 1250 920969559 920969561
    0xc040506041b090305100b090c131e1d0103120c03020f0a03020615192912090d030c0926070f0608060a1d07090503101a030303131506030501 62
    0x80200386000c6400004107000740201000b5003c6d507600140000e00a841e1208049000b241d4040d243d4150320390042140040110200d41c60300190400107480007155030280c0d5031489419140c0700301e41c0d10442943c2d10140e0005020007480c140c03038000302c9000c540008007000715082c441d052070036001c5005240b02d070541d0400c1485480949402a8010006401c110f038581c45030358454010307544200c0445090001c0d07241d1101c0d00000b150050f075070300f24076074100304030150101826985900440c8000503110407030702c0c0340c10303060360040c00410100e8500441d0841d0540480d401d510341d00001c600c003461300300001c20b80168a0504a500305124440c054034080e5128645a41c5070050b00d11190f110034180714095000c1180b9900c0741080300c410341c2041c6000d40c0c2201c0342504d800500646031000d0001504076000309440f1008003009000c03036420ba81441d401b1401800d0060032000000d481c610034a085190000540340500004c00aa240c040901d0b030750399040810410402601603200c50002011a00c2 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 920972059 1250 920970809 920970851
    0x50d240203070c060b030a020a050607080c010501032f0901180209030319020f030a0f111c020705030d090806060d05190b0601080105030a03090b03130f060204050910080c04050604 79
    0x40d00c659a94943d01c1c41e01d20251015204868000c0c0c2c412000c240169580079021000ca41701610100e0342c0302200d007007640ca40c0c891841032107225800c000c000420405200c1c080c50b5104842c07100402d44800b50680e20f20b8059031500c1c0540c1c807115101c0140680c401c024200c40724603800344001442d099060020a06680112502c06400c01d02c1100000705907805109500c00e03004150060351801504c9240034064058a01b40c200801600000c034034a510402c00071102c1006500b0000c11781c00050550003980d40549008980c064050401a10781d40350252141000761461840a881c544d600c02050003402801e420303042e40c1070303c2400b86107064500c583c880c010705c0c94012058050b2510303044b000500200d8060380014001da10000514000c41e03440307004841900c00c03004005075652181c0004182c0d03d80041c0b40a44800b0b42411107204104003640104110340c0d00707544046041e41c4070440040380c4075561280006a810190541c0b00b1460181e11103503202c80004e0000810b01c0c4d100d000c40b245184 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 920973309 1250 920972059 920972071
    0x15090a05030118060c08010b0313020d050316030e03012304051203041101140c0a0b091614040609061d0703021303060507140a0f0509060408120d0b0406050d240203 72
    0x420300300083c003405410700803124080c105d0304203003010794917101d2400a1844018803202c0c0d105022a210003c541c4d50380010072308244c000c0122602c9005102001050303442c07001048001c28a0f2107460109400c042c09046040400b07400c81008400802080080203c00107004a0303d0b4040c664400806103288400303103004500551403079030001c0619001601c2000580da40c200d108609001c0d08110880000303d4422503a80302a2404043d1140c56001e03145ca15144401c1003000254840800ca144050f54941c04002048505024003544c4100d07410850f9824000d00d10714070000c1505045250080e40110f40226084c42e0040c03800c0c8842090805c5203102d074004581e540c0d200d1050200340795002120444030621200143e1500d1704010001d00300000d4201d0950600001185d0640c03030381e40e0442079500400c21a07041d155a0036480000307205990040d009a5440c9180401c400000c1c10944150025504007500d05d031058140341d2105404445000301c2954820180c450f424624842ea00143d8040c0ca = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 920974559 1250 920973309 920973341
    0xf1a040b0301120b1f17010e100e012327011e050f010806011719051c051309020702060702030706020d0e040203220f050a0503030106091415090a050301 67
    0x41d0f640d10f00818804409005109450010500488019502c00c107100480741d42c91440f40a000441c04418050007000486c140c181c010005104e1903004079802078070258441e9002040062210041320b0340c510410101220758010a5000811401d545000b002c1000d0115003810040d610303030030300b0900350343c5149010007510780e03907681081c19102c4500880c1e801101000d50620f00c0d41c18800c01781c0e0b80358014400c45e44005607103900f100d410403091004500d22214040c140348108054101345541e40b1142c451600034016400000a00ca84150141d4005240e008003250b1018035156008000c0e4200345010703a0300c020108580700040e40c00f040010010072503600500070724003c0c0400508008020000540214010400c1203c040c05220702d007181032000d581800d59500c40c0f400d0000e505049054010954440d00c0d01000a00000002a41c12146255961007103651159686541c01010050b40c9800201880c00041818000c90281c002c108026000320026503440380001d007941c0c440300584d0003c0c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 920975809 1250 920974559 920974589
    0x708100609050708060d062408060106020d051801230309060604051b07020409061b0207081e0606220f051e01050117060a0515030a05100f1a040b0301 66
    0xc001d01d0080c254085102c0c10407694914004000c5404001020001000d590341c62540c00803101180000659805149080c0c82c00903845015040e40c8050a000d0300015215003100b0481080c4503400f120313480c0900d03c007078400051203500103540c2d030200c44c1e903c43c1c11240d1015440034080d0000020b18801c590b84801440c80d4184041404201d50b4003130800c0610003841000030711440740d02d0040798045541070b10005000d0015092030f1005005c541d03442030502030b450010380c41041e400200384040e40c0302031040c5d030007040c084289116104120b0a08100a07000000014042d04e030440394044101442c00681c60000c066480c8a0115480c421410000940d41c005005114040d04000c1c03030024035421101c0750950504001030304121007080d0072400e0f40b4440c000103101da100c1090140013081c010304030200368030080301c079034482350070844900d00002d00c0c040c00a40d224240c403404a044900f200040030110741040900c0007940204000d00070180d000300400584207545034000d50003042012010480 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 920977059 1250 920975809 920975819
    0x306040605011e110102040f0e040c05010503040c090b031e0115050409030e100c210e15090d110907051306030c09061d100e041d10050907081006 64
    0x32100c0940200d41000398082d801030128081400002410a482c14400a076041405106000e4400c1d81c03c010a4040301d00e0000030140000591980502c1c440c40f2440d8030b1917103c4004407014001110003400c100c00a09040041e140507034000540010060706940032550210306201150041400c18074081e95180f4100b122602e40e42c1781c5001a1004640038860118540c50080c4102801d1102c42c1c400c0380f0103c56a19081c4c044c0c16540030751940b2a0142d104c460100040c56a003441000c1c1d20b00c0860040600e20b281443e104030003044160750f107020075042150180600200065001080f10f182c420080004e0940c2d9540c4952442843c1c0303070b80c8084e0345506558407080c031302850745c4c456401d1505000901458a0300010700ba13080e1078280c9410054200b000d03403260540c459040049800030030b0340c0003140d1349642c005c0f132150000c10140c1c1c050001a81c00c98107401030122540c80d201c41600074180251804a054000e103400218107800c07030751141e4031460301a042c403541e0418139003456610441005 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 920978309 1250 920977059 920977061
    0x1a01080309031e0601030b1807030b06120d0c06110d11030105041b1403060d060c0e01180b0708071703070203031e0f0609252a03091205010906090305030604 69
    0x51007150620099000d02c0c520303807075030303682c0340103006c01000e0308110000508080b80c01511030300e00c5505403040f00c010030303030b241800c41e000481507415a00030001103035010203401d8001000138005002e0395a041ea03c001a8860034000c0692240c4a001c2d820100065003d04035680200e600c51400071100660717079494001040215415010070388802810154641d10658204206100180d0000e540590300e98400c00024900700c41a00020070705460102e4248a030b03903124401d8020034200382c03100802e0805e81c0910f802d44070042d01c151444a4410803114000810180c060700f0046e100342d001030810403c1d6044004c0b180c104589000050780b02000300442e40716a40d082c0540769400050803960740c1000310340303541102d000400450145000342c004c20002c55000010005031003025040b0040c0444074035000706203442c20102c000c25803955240b42c10104046100b12040c1a5050715555644c1d03203400c0320104014070349481a1810f541c3e9400c00c0c8003040f6030f4010055001d01c00d81e00c4540da4541441044 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 920979559 1250 920978309 920978323
    0x2030319061707080c180f040f0b040b04050706050c0706052107080a05060906010e0907020c0a060f090f0e190902150403150912050c160305010509060a0b01090306091a0108030903 79
    0x45e2046110342e03846c18500c0c1c0c03200071046e08010b00403441011991641003850f038940515030018091985001080207002c1b100c01141d020343d12036016200e101d0781d1114100e030603006060790703480b15820521007084182e008000421250140134004600181c035100c4070000c59408640c07443c080307110b0904105030320809104182d80610103c0b04034480c1e0504000003005600340d03140090180d50340d40c01142d4910300800903c83c00340d1004050b8401a6150800201a907000d40d5850012030520803001c9135284000042100707030313903803030018012540c2d6200407003070301c8000c00381d049002d070780c0d1400d404000d41c49048140d209010a414002d50392407461821000c02d42411500042c442d10304840080096403800701d000b20700d41145841d544805440380100c1c10001554050880354075006000800c01c401904503a100300b00b42e80c01d4410943e1444076501c01e45a415400364001034800c0c0301840013400b15409182514015058200d641781c01402100c0c407401d007a04664a103900104401d091854200141 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 920980809 1250 920979559 920979583
    0x140106080d020a0c0e040807060606090512010e0a080a1403010e0103020a0506070f02060c030f043c030201121409010b030105090109020f06090d1502130b0301060203031906170708 79
    0xc108600c40381e100d62106070361034059910110304c0c5102040900c00e1000523121010303000760342080215502d1070068400d1901e841000c0c043c1c040d4078000c4900440600c10386a1945000014000c6038016541d0724a041c6d220741c01c0c05091100a2083e1125540442c01440c00380c0350307503036110102d941103004000d003611265211a103d507504025078000143c403030705210505c540c11b60348241c45018039821182035002d80d801e80b2059000210380022000689409070518070130900b41e440407281801300e07100340c0b1080b8081f2100c00e0f9465950403c01540b040880140b100d840702000154488440c21103d4040c03416280e15030160344a580c0c0d0b5a25143c2071190540054401008010760301050b4003042a2441d070a420354403d60010401040c5c9071580e17015441c80c6c50740f00c1800684940038030720081c002e4101280e074004203d14010302107151a00c40088a0507294140c00035800c60b41c5019258102c9045402d202c1c5c251a100c082c00200103110104000e030790880600500381d16410300f50b89034982400c0d81c2403 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 920982059 1250 920980809 920980813
    0x618100905030a0c1502130e091c111903050a09080d0903030e040605191e050112021b0f01020d0f02040f030201080a090f0f260306100c140106080d02 66
    0x20302000280000110784599500e800c2c000100c0d15103007408080d148040c4518801240002034400d40700d070000e500107040e03d002c0c2c0c40003400761b15806c59681d51109441200d02c1c1c0b03820040d91560405004030794204d400e60080007222410f41c03040c80c0c0340c0c8010b8203005089011503000f250b442c10350303a001800c010142c081000140300c41400c1c100c009105070300724400a01400183d190b0148684c40b1504864050840604446c03000e4196030900016443c81d03100d1250442c0c19942c119241e080052590011910140e540c9161400d240741100001e43c8100c980b8003014103000c0d8031812310141403001da481c2440386400180c41d400103200c1002a518a51403079000a441004140309000513030121005a03902031030401d22540d0b40d03944200080040715006841d00d00c00402407020040305829550303040748036130107600b1794024000005202c500300b02617240c0014014030004540b8141000910680026441d1291100c1410380f03032a0007009007074451815694503044103020551003009024032144c00b602c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 920983309 1250 920982059 920982071
    0x903060b180112060e0715020d03020903060c0903160303030227130e070b0f0910020c0904140307060513050105060a0b0403260d091e080306061605061810 68
    0x14030840107100c14026001d01d5030040000030244800d6501c101d8071040d807001226100d54448050351008800e01c8003280061107003a8480110034803a00a903015054050005c241079160311107100760b160070120842c3c0c2c051140246896203c92210340c980c00840c047d440042e590341400c03030000400001e44c0c032040a8442071003071084c1191202d6650007500c804011000a10074000000c60381481d840390321000d080c540c04901c0e00f5070181c0700802081d01c00d1003110700d038442900c02807003a40c69428004078140c2c062440c800050109100458007490a100f18055910b090034650b034031801c076903003611002032003410a0004001c002c024801c0540004003210000b520030300d0499050f800c1d02c65400b0081c81000d0a054100000203150302482100c00e40041107500e50042d07060080040150030307010f680780b940c989220302151103801d002c0003041303801c002070f280741d0390341ca00c2881159400360981031341940c00490fa641c08038031300b4003140d8080c44200001204500c2140c1c01c80c2d05d0520300d039014036070700c4d0301c1d001e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 920984559 1250 920983309 920983339
    0x2718190c1710030f0803060a0f150c051002040f03021302161101020106031e0308070503060d03030207110a0e010801050601050f09041d0607111b0a030318080d0903060b 74
    0x4001040380c900c80001d00400756032050b41200c1a84480c1c0c2c00201043c401d003640e2020403031210040c5204400549000d80e00035642c04201c00b104e107003172250a84100080140d114130610604010404502903000c50380403040c811104812030740603078003a1199460141d010b1045203010b10210369802c418000c25810440300408954001041100080c0441409196802c10364000e410aa0017982c012100007a003410407820040110042c075011400108200001086a802082601c3c0512009002d48440101d19507050740250f021a40540b002565140b00b42040c0d611600c5000c0a0b100103045504554508041c060940d50003038011814002e060094420090011040d00d42c81b600071200400c20b90b0010142c4480ea40212075010311601035241000f07c0150000c503e19030f40e080010807030b000c400d1900e030800401d00200300c009034400301e60181000445d100300401060346002c50b00d271010160361110124901071441c1203c1c40441c1c1c03908820000e004d0b8900c525013840c003099034031181d0340c1800 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 920985809 1250 920984559 920984567
    0x12160608040c0e010e070206070c080301050618090901090309091a131b031a090108071403120d090c06051206041a060706050f011205032718190c 64
    0x160190808010324100010140300d0703903480300c2c802000c0f071a82071041541c540040d4441c1c02d50442e1010b0243c4512800328290620440c05090020b0308200020704590034407041101c5903200700c11040010040003c4480e06940d070440c0701d07010380c020100004803641240381c00307484071419602c03004150b403a045c1d10310b5138074505000c200b00c0304008507124403801c0c20206020004140c000b03c4022000c00100c01900c040c0c1e01944401a00c2d10b20100124406203600300b0010191424006c805d5680c00005080000c402d1000040c240d1f90700c0201070303e110402d841c03040c1e0703c036401c038918020001c1d480e840590240003e003403000b400b81c030f102c0ca0f20b40d10307003030100d480714814040280c081d6015a941e55106080410a2048280c0a010003000fa40d940d000908100d8003404041c0d070381c0d00740aa13140d00005501c01803480425143c40d0f101019509044201c6850032007a0f055030750b01c906038261801c00795050307940d048008211003145c0030301c2e94403820800b9500c0b561540794860410307814270b40a80c0034502604 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 920987059 1250 920985809 920985853
    0x13170c0d020f060103081e0d0f0b03190b04030c050a06090b010902030405190507090609090b0a15090c1e020f010b060c0c06030a0e120a0305090304030f0f02280512 72
    0xd9810b0340d102044e07140d1f0b400c3c1074100ca81000000c3e1000c01c00700c07900040340d0407100f104050803105002c0a1054004c064a80b01000e48804000b00349181103000a452540320580c8a4003a01b88a80104001d0b110310b818150140b1045440707555400c0301108208a5240e218090300070b0580840c1035242c1030303884035541c4c1c141035a0b0700301c0c041da040d68030b404000081042c00301400008009000303540e0380d11400ba005e4101c50504681354111440020036007000351045a02480d51403140b40340646c80d100700d420080c40d80f0142c1c001081740c00440b02101e0351180d124401e41c13038082d500500803103d802403c0d03400c50750070303000491284100704015400319000003040320346001c04a600540d0381e21075848200c002c041030903602e01c8a011700c80445403212032050281040300c000d03441c03d10460341c43d41c190320340328815800020b107154400a08040882c80340d0390501c404d10701c09050388140030403080309800c0d2100f40e00214620240d40c440c3c1400503081485c1030f94814002c3c0402001c1c0840040244201184 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 920988309 1250 920987059 920987063
    0x5070b180106080f01060b03040f150f0203040b0a1407050d0e010b330910121409071d090705010e0a0b0f04061407030801030b13170c0d020f060103 65
    0x1910501140240000680d441100c00c5000000c001c070a07a2002070548440144240340955460014006415a0101d04403031007182e01c44c000088040e0290b442c0c006001c034030380a00b0482e580d11200044411102d20066004601900613074400b407030f20200740402c1e40d40c500d280100007a28142400740380c540000503120030404009011a5214801e05c00d103004100c09940d05a00c01b9003c010300c40310803130349c0d040e6000d514210118800e03061800e4030840240e203c2c0e2507145d40c00c8036003440c0c2d06003401d00c5072034080300e00780c006000441d2001c11100e46401c0c0301410740340c0000d190050714081012080300d44035440707024024101e000312803603c650a10348840040c403030386060007050b84d14a4401e50742e000d944000740240d101e010b529081200c44204042d0054050103001c0aca091008a2000300076605661040354180e454401c41d82c2540d90b01c0d440e4600250841005c240000f0b0301400003011764044520501d1008606921415070840c218544a40800c07803000b07540001307140700c6500001040142c1525 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 920989559 1250 920988309 920988323
    0x30b1c0b07080a111603090503030403170f120a06060806010c03020c120c0d080301051c08030601200f15060a03050a030509010c170c0d03061409040c0b040602030d0606020d0507 78
    0x5629140c9000113000801c6504400010014426605102200e4040d241d24040d40c1e401454070b40728414903940b44102d000c040d000301030002c0c1c62040b00d09400c0041c00920040c4090904210048454440422041d5064505541c50f06002c1c4000c0c0d6100185503800038091030000306882d86514040e485855103885a4024034282c500c0c0f0480c0b4070104004e080180d4041d00c5c1840f00e40d45410070700364941007800382c10300c41ca012100072511070b00344880002d201038002c0f504510719122000190b810990b0b01e12840e243e1549107112103220b01d42070010080f018004030103040c5030b01c051000302d400704500a00140c441c20303600b241440416030001c0c06a800e00d50506107941c1d00d601d008010ba480c800d490300000e205000781c0c54862003003000c51000d08000b0720140111904044640015000e540b01030149080b18464580704a440b45440d40806400070700940c407170041e603034a5414070040d69000380c1004000d6400010000035500c684e200d00c0004010340d101070085d0400000000b0a10b120b04a03002c1e10322 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 920990809 1250 920989559 920989561
    0x30301060e130e0a03050d050603030708040b220b070c0b0c030f0a0e03101b0c030503060402070f05060708061503060f01120b0409140f280f12030b1c0b0708 69
    0xd20650003254503030700311012036910a43c2890b0040895202410261f20103080c2400300f0b109060000940c1c0e2500d51006030281020b0809804e020507070811400c042140304075410001710394401881600150840d600c54641d10313100b60400303943c680c5450740648100a000c0108410800001c01036880340c1e000f1006850340c40c6507000c0100e076042454800264907004510300c9810890596012800721884d0469a0903c003155500980300c00e0000580503012480800001e5010300d000e500606900348036100f00b0707c420036144c40300c03444d0130701c01c03505240420300c0300050145625103145d640031071358202000546146410344c040b1386200070754101c142c14030046500e80724103c01036402120550001900421900c42c035410f2131100407a407a0701400442c0111003104080110114072106d420200d01503444020000300c2c9a0560b04544150681d4502c5107144500c0c0054030402c0c8224148003240c0c0e0105401ca201e2017049850a81d0b1420749401113244501100000c0f01d41541d56844102420300c1481 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 920992059 1250 920990809 920990839
    0x70c060e010c0602120712020901020d0e01090305060c0307021e0a06020a0302090301020c0607030b010228290403030b010801030f0201120f020c06040c0504060803071b05040e030d0e030301060e 85
    0x20b980355940c00100344074000301d8012140c508201c0024851456a540c0e4003220380d6910089080344140c0c50042d006030000140003081070700031000f5588420701032420541d4680d0700d031615070034500196040c84109070300106025405904108028120b041075441c82650b4500b10410741d81c40504100041c0010b402254580311280240d058400504001d40207541d40c510b002181c64941c0021289400441e103000c26200c00e5500c005080b0300510400c2c800400715849030115084680340e40e0341c0c122041d409010f942c1a84014400004004805d40c00d08032406d8101490003074155401400b0031810007121a00400100d080703e800d090059030213081c941e5480120003080006065204641e00c45a40009903002e8010f10003e08076200301d0089411280c1319442e80b0400069641c00e20407115990f100740701c06804121260711075103456541c08480d500c4190f5903404501620800e1200d00001c5d00007141032802d8003028000c4c208124059800ba61335517042940c0982941c01c0303040b0507070090301542c4008003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 920993309 1250 920992059 920992067
    0x6070212010b01031a220b03030a0f0e0105071509030903020a0b04091d250518191407110312010b13081203040f022809060605070c060e01 61
    0x50158014021104031180c00e030845000c0d0001c00301d0140001d150007403011081103e107182503255080104040f403400007920641c14120010821045101d0b959240c00310644e03800c000401090b034443d142d02403844000030000e040d401d0380a2000b0705000003080840c0c0010001407417821056200e15000405800743c0c01c007155558001c0e0402904803851a101141c1c0b0f240f1030019208461901c0c0c4140190507034a21041100e0700584c003421126802400101c200510300c4505261000c5000c4c00c0304684e40d5039400060031150202c04030380020b01082e00780216460f4a1154060105012609100346003040d0141c082100b0014800c00c1000812802d8080408041c01103a40c4400c004c10714507040d584030394070420142d120145108034800e501c500091500070100e5100c16414040e00d0407815a543c80d111000e5480c1c0c6032104aa00205400d00c81d185c00c05e042c2e500c848080728044540d29818100a014030403208180c000c401841024007481e800100c9140380e40003074070881d00d4496100025a00169 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 920994559 1250 920993309 920993317
    0x2092e0f03020a121d0d35280207031e0305040f02150d0f0c021e0316020a0b0705010b102d0e1e010212042603210411010e030607030b06 60
    0x22482c0a4825003d050542c48880d501e9030034070903103c601c1c00101d401c555000c414210003182440300d54220004800b441c14480000e231035000f040e60360318141c1c088200d24080b42d0060100f14085900e00b0448101544160b03802014000c8904040101d42000e40307502d0742840503580c00030b200300600340d41caa40807002c640640700400030550050102c40130481d0343c0c1000d001c60801000051058910740d4103003076001e84140c501c4000000207146083c0d400300a80b0b00d0f4000300c034000da07000340c1e1880c0d00055107050580104107031070140c00000b400c0c4c6a050104074420601086c64000c03c48a003615040d80b20030380420b44039110707038001c82c0b5445140031a400e0700c8100d6101d844036030266a03480c0740440418852002200741c00241d0940d083e641c080c425000c0e090050340692084030307a04d040181920000b2500001040740a403044030305040b21306500191720808076a92001c4c0314250f40500003003001c0e82c000c84003540806d00300b15614038100008641d0711700005060340c08058403171411202c2d54442404032 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 920995809 1250 920994559 920994611
    0x1504050c130e0d0c170f070b01030302010f060906050f06281701150503060f1329030105071e03061203170702010b0f0402092e0f03020a12 61
    0x80103024100d001d4540003804505500840da002e00380a001807144900004a541030740308804400303205200700300e005c040d08201e14140f10b01d042007020034003098180649500941c400e5001244501031055420f055900e90740c000032a03641001c0081c070055a030940307941d40115080d54082d444400341e1640c03000c00346030280c0280f441080c0d000c191907042d40c4070008100450303400d0612421340e40c1e50290220000c54000c0840000f940601c0860240e04d0302e4404034844941c01000561a040007113051400c030f400c0031480b1940080300c0e9200e801d9100d8000720131079410004a0081207249040740380504502402159020140001c80440385840d010741d0000c0003a041c05943c084a051311407030080c1c01004102600c1c0240f2407140001030001e88140222031078000050541e0008903400700500020350841642d0301c0c0e0203591002c00140c1c840c9984000803217080c81c0c502000c2d082620b003101400041c16201c1410416004203d0100485e800c070740031480b0709d40c20540004110305c440b10035480350306001d416 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 920997059 1250 920995809 920995819
    0xa0309080f0a0503010e100501170a200c19080a0c150c0c0308180a0204020315040f0914070e1b0f0c0a0203013b010e03120f15031504050c 61
    0x7400038410340c8100654140c2d1846c032801c40094649144000b091403040c86038500085503d2800b29043c04808042078004407241004180300004100e10741c0f12a050080b00501d0710004604580030041c20804403c40c1501210800c41101440d00c444009129100c0c1d9034043c0b1500c0d004082c01c1000d80c00340c40b81c840104160400041085120040c400f0b004490154001841c1d000859104203550050064400e03c450040002e00301c10b07400d000c080d4000404c3c1d8031910301c4552280300191100e01485141c1d203041e0390005001c00d860300e8400401e540d40c850262503684405000d01c13280300c0c1004030940041c2c5d42c0e00d800460f004100310a02c0d042c03043e0a0307003000001d00860746011103000041d101840600c2203000b80101c1d0407089103004490312404991401c2e880103456614514540700d0310020703032058440013040d684403c0000d0703499035105507005040d000404041285610a0250b440e4010501407000030110071820006036072807080d461400041d002d91800300c1c081002c10071566141c0351000e00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 920998309 1250 920997059 920997067
    0x5040806090601030201090504020a050d0903120c11060903030609180304030204091b1a0a0c020d12110c03061b1303021201060501080603010209030325150e010b0409080a0309080f 79
    0x8a01c9440302c1e42840100d02040d220b10000c20702c0d251034000da440c88041d5030b0f102400c1043d400040d00282000352004e405001031104180d00010315409247c04003115034845441c2401c1c984900c1349000d00081c101c150a400600c10f03c900796480080132500f040c91015400f100c0d0358850702035030231449a40d10081d4800d142400c1d003c01c00c15900500b00009134034000003d500c60b520014220b90b24510b145c84010100c08114075200c00340107c04940035070703002421010a8901550722200340b02ca1401010010404080c080d4444403420051315803810000c0e0060082c0d810544006002c06d4a803002d180c00ca00b0012a01d500f43c0b02266000ca0b0065400500602d900010801814004d1840c0d014890002e50100002407141c2414003c5410038880030300110324144000f0426100740041d4100031541000e0700c001040450910b030f5800d201000d00b008001008042d042c03100b0700319030411080500a82c10b241154002c80c0d000c0040d1084440c4c64100498100ca05280c148180d1080040c0080b61000100e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 920999559 1250 920998309 920998321
    0xa110102190e030c06033108090901060e090106120e0607090f0806060f0904031101110316020d0801180213090e010c180b07031403070e090105040e0c0402090105040806 74
    0x34030310000002242c5868410750200e20500d6141c80c1c030b0155080d00185e0403c00b00d142d4042200c824000380d200106207030701c5541e988001203150340040000743e40180300414a080c0624041450b1401400705040216034041118003052542038144112801c0c0000c10b07031a1803540050b90410b00b02102c1c6401034910910f0801da015180f140c103401120280d03030034010302080c2070100050050140340000c0416403c154030804200d003070407000b401202005007400f8030000f090824007400000031191844152030740f501801d100455a4080884800c40d408004a03c4481d0307040702e0507606540d21011518100396200d1a400301a1191003800e1032041c20030360300000c100c01d055000516640380c40000340706000340d80d00d0881c0d0000600c5110780c014411044104888059540208401da01c6800c0071469640b50740300d482c000d03400481700c5402080d032542e40c050b40d61524038100c501614046804015080340090f015507540200003c031030003140c1c00508100507130b0207001503800074588501140e50500e020 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 921000809 1250 920999559 920999587
    0x20a091d01090f06050d0611090307121a06010f2f010204030516230409060f0b03010606110a03180807031202121207031808130303021218060a110102 66
    0xd1040e0300c1c800780f800401007507008450103400100c0f44010403003541c40549855040c020104000208840b007030401820606440601030880240f030000981104034105052000d0320080001120f40c0b0410b078001080300700d030380020010510101914068407849060560300510300700070840907400c4070380384401441d401415001881501d122ba0b082d52492841056030210900041c080cbc00c3c003540388000300c030451070850250084112801480456041c1c5140c1702e401c22220780d00342240c112902e40c1c21b0101c2c203040900641004011925101c651105511120b54984e001e40700e008007004140c80740c03200d0300d491510110b0041c014900940303680955a2030b140d08850345180c1124050300800c0c0c018140c140150302a0f80c01c40c0b85032003050703490781c0d1405d40c102e005000e4480111300b4070b050071401c0700110348074201a0490b050304040444010b421f608001e403522401d818600b0400204100881c50300085513404505608195100390f107448845d80c01b0348501c02400c020f2041ca40c808210720303a1842c02 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 921002059 1250 921000809 921000811
    0xb060412062a030f05060f0105070302031c14090a0201090510051b16080a0f23010f05150901050a0e04080c0303130c080d081501110604060c03051612020a091d 70
    0x495207041080666040c20b0105485045846d1a440801468802d41c1035008100601c1c69601c6481620715040c4012210002c0c500c140304d04d40d05050b62540c0044010b100a44c3d625082001038000384007000e060750000f8091425401086c0c014400480702d5940300303000f50b040d10041c0a405698009000e001d02843c1c1e52400b0004040a200805880000303143c44041901080b0340d4002c0d1103107004003215207920101d0822818a60500d41c00c250004003002d00030701c690081100c5907a4003081500386a2210612032100c203040c0e03403045203010010001035890710b001c5011240c100701812080c0c2e0391820140c00da4083c44006014030b0100108005020403910b86d17041e4141d2003144144540c64580700031543d40c41000c5034200100d40201d02181d21007030001c0d0501005481454604529080c040304941000002e1b80c04a85e81620303106280041501805442d0303004640100e00d0010702400500180024514480c1c18130f8030341c0c009101c034a01d600c190a604040c01200e0004c0000f9240504001401c00c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 921003309 1250 921002059 921002141
    0x308070609020f120a030315172b0203041202150f0c0105070c320a0809090106030b03030a0513030210080603100203070918020d0c11100b06041206 65
    0x2041051080d41440c044c0303001107012050700c1c000c012045890b9000d50003045103030b6444245c20f070b030b80000146180785c0c40c0341d0007410003642002d0440282c8040c4c0304160404642d0340001030780800421032860380d0780001654111034100711041c103804520b00109011040120040200703480c0001d001d40d00c242c40a00404510300243d000700407642d200c60040303c8820f2801b100518800b4134601c02ca491251503000c02c451004c0c2d10400042000200602c14542248004201ea2002d80030410b03040e680340000f00140103200c1030070180500088080060380300d101c2c0004d1070091000218201c07803003012468a40000d198042c00c150241c0b40480c0c00a041d000c81100d0b024401c2c0f00d54144001c42180750700070343c3c0c01008242c5400c404141410456484100e4003641140702c15802d1042c8800009540103e083c00200754442c10244200c982105003407000c0703404510715070f909201071240c5039101c1104403021614078041c1042240321038600400580b001140448221420b210b64080c02c06503039401d656441 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 921004559 1250 921003309 921003319
    0x509151f0f0f05040b06160201121506090e090319030e0102070f02190302030d1b05240a02120c09030f1005220b0c0c070905131731030807060902 64
    0x9a90303c0070401512004051650028000d000c003000c03400c4d04044005015105040c65000c40070426201d81c00c940740441e402900c4ca20030101000710580109003100680701c11244a04180b411050302503403840399048600c204203e151030080304910a40c8100014030780613000750750301c01380c0341032405419074040c0b0183d20881102d0000302095204809802c2100d501501801e01c8680c0b28000359400c00c0c1d240d802c940e46280407188038000680c1031014031000e0440b060764400140c0802c0b040c1810703d200400828005204000d0b10280081119150f07621899016450741d84d205102c0c04a800d000080340d40000610039510741080381d040640100e07116a05110414101400c040603854101c5454074000c0d00900d030040104010b0400c0e50020010014440d0440c0c19080c2c0d103091150481d2801c8420303620a01480b180e9001300701480760b507040f1028100c9101070a001d845000d070003081d02100300c0c214001070500018040c0361f016145603030003960030600f130310786940c1d05080c040060500308100302c0c441c0c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 921005809 1250 921004559 921004589
    0x13050a0605100915060518180f07080c2a100525080a2307030218010e0f130e01020a12060b0c121305060a020a0212010509151f0f 57
    0x83c4040d1041d0300940505601c80040f407813504034256525441000c81e86001e6800c150407880a031940c0c0c0885185801c88403914070306190203c0d1101036030001034501005c012010f0309101c09805101d094800c0d180d107046000b80c60100d43c4442d010019128800b84140f8040c80040004403922648907501c1030740b5001480d124a20240c0703600c620414500403150100b10b0b07a10200309100d16580c0002010401c80203000e051f03c2072086010380c10402159800002a00061417240f10750305246600040402030a221058844010009030a25200310016000701e000d0f1030380101640032a000642c6c020340e540000c65440c8035a5070020840b0214a1000d1046030600d071000070400e60100031130f1380c4000c5000152046400d490030f01103096100d04040e00303d02965000114242c0d503840000c2c805400c40d90020041c0240c980b05000c1c1c1c0218aa01d00407550349014201702c21344d040410980c0c0070b21395030482c030407541d9103039103281c01c05038407084212583d049001c0d004910428403c4402064503000700405a44e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 921007059 1250 921005809 921005819
    0x12040f11060a0207031707060608062410032301060f0e030a12140c01050a0506090609060319061407090f08010203090d0e0103140a05061c080f0313050a060510 70
    0xa28819541542c005034406401000841c03040b5085c900f401c6d14000d00945040c400d501d91b5029a01c1907000a00942c100d40c0c02d100052501c0354110b5403e503150180d91960228a00004601c80002031564080c96140e8408070106c0c0032500b8400002c2009440c00d03c1d0558440200520f25204c8032214008147c09400703060007841d00050104003194070602d075030801c01342140b00b125101c1c0101e105c2c00c0884000d001d184200182801498400c2c10340d280c000409143c004100302081c9400b07000140a0300d40c00d41406555200801c030100141042e160305224804646040d1005000b40c40c1032020416191003803110071540701703407031208a542c405c0341c8019460701e0b815064201e22042d9400c0380550303c880000707a8114056074290116007014100040c0d00c030140100780d8580441140d100c81416900d504210035490087c6d031907844004200e0101070024529590b00040b480b030981004032a020220011300c1c00000c401400d20b50503842001c0c1c40e40d0b0306803890450050030060351310b012130b0740d12901c011038 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 921008309 1250 921007059 921007069
    0x213110d06060314150604031a0a05070f0e010f0c0506010306060510111b220903030c0c150b120d05090a3003030e0a0c090c030c12020a0512040f11 65
    0x2112610a0101c03040d40c456400341c032100517603956956000541440300102040040401444141006a07030305524944010158115400200404244940900b0302c0f0900d0342e2000e503e034802078013802e00c0c4000c1008000b094a08040c0744600402521489002108000080d00218110344003596800750180c40d0b10f000395000e080c4041c07080780c16841185120542001070b003001e43c002c00702402c40503480307031020707c6981010b0700103025030342c1c494942c80d1180c100755244c810b40c511550180b4140040c030741255240e0110010000740e4010080d11360280040c151369005644505150000c2111610440500c01078100e811040c100f40c0300324401d12000034010401c0310342038010500d0020030840c40300e4564141c1842e8058030800d5041603500c03054030060000c00c0100300c010300d004801c2c40c0c032400e192101080940310100100c2c002c1605005c1e4428000760011039081641400d100096182c0452400031103440c0516400300842c0b00d00d41c42440705028403c01d006a0b803d0058800344602801c07402401 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 921009559 1250 921008309 921008321
    0x50d050120091e01051204120f14090603150a0f06120605010822060e1005150918010e10020d0c111b151207020706090803090d0213110d060603 63
    0x540c10407540c0f40e01c07039950320f104001c0c42d480843c1418114181742011242c0113800384119070072180c00008000c0140751a820a060f0240c04d00d080c6070000a604c400d68a000090007500300c01c9004403408004036500b00c42c58602481030007006001e0310400d030f40e22995544500900d108050102c2c1c0c1e00000345021240f0350080c802500e07011b840c2c3c042152100c40385002200c15100d40f003d65400e20199180c009107031b500450700200210300c01000d942c80041c1c0038104845014101520300c03140c40042c40340940702c0b01000e0354818081e0003c03d1a503070703030301d440c19000d440301801c01040707801a0441403941b210654040c0c0b0b074441810100b08a211003820b000c3d600b000054000c08803a60260503186083c2c004c03d40c49414480c800b4204a00c00f00c01008000c805400c070519484c0f40014070420070045550403c0550000c0040303280500c000c6140c8a14170781c0380d1150000c2d0f036010360341400e0200c0c1035441d4000d0400030440c80940400c80c07184104c50240807500202810f1030300b00d040c5140006d07143d120340112 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 921010809 1250 921009559 921009577
    0x20325021207080903010f0c2015100f06080a060b0a020a0206091507140606090412030507140a0e0306100605040509060a0506030406050921180109050d050120 70
    0x410701c5115803064080180c10039403007118540380401c200116514280940081242c1081c40802c04010f00ba00207410742c0307502900300924280d100d03210900351600280366001150035075180a201c1d1941c81600c40300d2140c0e508105811840c0c0480021059802850b0394440c40070700004005840d01e809805100f03200740b400c42d90041c2d00c81080c0a000d03103020701c02040781c0c9100034460720741c000f05240390340656040030710300352601058071242d9204100d0174800aa4803000c02c941c0d02c501c43c40c107070b901c14411300500f680010402d82e8a00018000314014010f241119695680080d2602c4000700d000303000000c4103910600a00840000c40c81002c40c11103280c043c1e03002500c0c0c6a04050a04c0e040c0b11b00040c000f40410340c070564031040001d40d9110f40c001580202d00840c0d0200c3c1074645007000901d03103664103880c0b0000124808000b0711003a090016110800c0e802c03000b942c0c402c0c0d80703072004030b0310b00450360880e40e480803406890100b0808158822041c0100768180829201034260741566680100c0c885 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 921012059 1250 921010809 921010813
    0x925110705060f09040e0f0a06060317040e010308030a0b0a0e1b0f1602030703080f1b060601170403020f0303070201021e03090a0f06090b010f031a04200105040801020d02032502 78
    0x180244d180b400e5007280480d1051542198200c4c8004100c02e4988040310805480d8140c0d282014024031034600b4160014000342c03c205840e103860301440c5410000140b0007e043e0340008404100013103966008010311308070040c03801e0180350300ca002d041c0003100180d41038025980b801003d000c1f002000300940e6801d03c00841d01504080e0b01203407480307040450100c1241d060041240100000e0a248058518a01c209180c2034481a80d566211018440c030b144520f4a03a02442c01c0100f142e0303200455840c1101050711a00d41c3e62117030f240580c501441061042001d0101008114410350305601a000c1e0078900651207400715041a001e6003244010359481025800920210703011807007541460a0343c1c0e203d00700000e1520130585810a0012080c2c021194500c1400020003d01c40c5e94500c1c5200c1034194002406142065a1600141039034808100d59100c21900d14451070381c013480641d002003a0340802036640f0b080e0122041c009510448145080010070100c070401802c011006040c0c030070060300 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 921013309 1250 921012059 921012067
    0x80301240806061c050a150803070b01030f0f0507030821010b030109020703110601030302030406030e19060c170c04030c1a0d0b04020d0e0a030318110925110705060f 73
    0x814020700341d014028904959441040d03c488140311362260a00c6454807400c00901b442d07062010440c1e8000310f40c00911283e005101510114261030301c00b90440354004402e0f4903e11843c9051403070103460301e20107419030103942c0000044c400528002c040c5c15149150b00204c11000b00c00700a0104000e0040f82d0b03d0b03040900061180701001d5000302280360007820311100304604100d815103050000d0f00308900581012034100010350f0540648901c024000c0701805421707941c901114010448a03c000c0c00450322890600070680c013a0b40381c4a5808001c1d04181c6891800b0920000941d006100332a0307003080403440041c111000c007140c10703130022081c010329140c04040d80c59000603040c122141540140d0070440c00407841214840c01c052140b0f920041e1150103102c1c1005000c4880b0a103209100c01120f01950f000500d501910118810303044030364070490744881c0045035842d9240c00b095500040c84000389500544c1212a102c1184c03a1042110b0509844405020035030103030503058044140184 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 921014559 1250 921013309 921013321
    0x40b0301030b090a120e04050a02031504091103070605030609070c0201051c061d09060a0e03070212030f070b0f090c130e0a050106060e131416030b0307030803012408 73
    0xb0154a030803039060400c503a0482c40c0c5840744120381100d2071035180800c01070005501942058001d6550000d6400011411450b00c2d115201c8080252540c1d20f21456a94a85034100100802c80b480e4201d4060100c0c0c08c42500c40c40003900b0b6500544140f48500309100c0021422031244883c4c00300b05038103039643d5061101d05110158024a00d03568460119140c5002140354440740884088445105041d298142030511038135080420140c500c8011b103040104ca801c0e112000411240d0090741a19616204244010401c0c21030003013440040040300009103081c140500381c9c90f070038003239100d100828682c0c4e140c000100d0f60b00c0044120442d00480079a1400303044441c288d1022038510884400c0d00c8801010f5a60182100c2842d0008008200b0120f1141d003e41009190701405902078071003000350207980c114142d04448020020b5a0400000c4038540520344250080d0403412805021035038001d0322881c05000d582c10074003a240701c031903800da007031803030f52034158080d5002d1358040d103403d0101e40700c80c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 921015809 1250 921014559 921014573
    0x2010b0d030e011b080a270e0c07051c0915050909130f230d08130b130812160c17030603030c100509070803030906070f0e090f0103020405010902040b030103 69
    0xc03100d600119004c0c10a54000c100c03a40e000b0801000300d90f49a081700400700742d07040160324400c02c0c0d1111220200c2c005102d4690341c0344580f5007003581041c0391a02e9080e6807400070700d4035140040301c100000c001e00c5401e40e4180c01204c60301c01c2d5100d242407584220160242100c0601450582c103034003160190210f8101d0740c00c1c5003564840c0b802140c40340314070011a00c030043c4020400f50060703131407003240c4980d1180c180e017407080f54400201440c0c031005504110703409200350710072040043c02c1481b1940c003240320a020001c03031740d48050703005600342d8a601c0c5808035019803170030072a0200c0314000e4103104076102d01c1c41500300f03440c071660281500105c1c9401e041140802d810040c81c1c683c061208002c0350503950b008003c480744074140f00102195924200300c000342400e905912800c02ca500901c28058112408540941c0c48609403a14442c1c026640364201c038014001540c0c0741d08002e0749800d1000044001c0e502c5416240203440c2031000e030344c0c1c0e0003200040b407080b0300c02c0c10035002c4180018000561a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 921017059 1250 921015809 921015827
    0x3021e1825050c01230106030e280b07050c01050105060c0a0f060f1a0f040c1b030909020301150e0a230a030614180616050d0e01020d0c02010b0d030e01 67
    0x81e032508a081c0b802e40b101050840e0101da2584c0183d150b66005844e45240c3d10720002d014120600c0c0030301c82d84e0b502204207540e42c2c1c401008011141c100b20450591362400918016006400c42070070380c02410b00c02000340040c2e11040c0d41d10b40650810b070000c10b0b01d060200880302d80711262001400134404c15201c0551111348207030100c0d01c840d2640c5400304010128090580d0526040c5440f481140d1010200074000f590600c10901403400c0c0491601000e03000858008100c810b00d8110b9411041841c0481c0d0346002d6800140a4600c040000701d072950781c000302e004140708152070b90b550400d02c460411513400d070244102d541c030301c0940003203c45103120150060f00991020b04006c000503140d680e03610994095a0b0b89458000510041245400040400c85605982040035040034100441d01307030a0307140b003011f0a0042c0000003543c3d081050320395214890707003c2810000c640712105141480c02a01c40c030b03c8210019801d00050102e14909010f00c00c4c0704940c5030704d880345511807038001560a981 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 921018309 1250 921017059 921017131
    0x4090501140108070e0f1b03100305100b09180304140613090c0206070302040b0f090f1305191104050415090212060a080a020d0201030e030403021e18 66
    0x5200c1040780001030400c00075034040e0015602429416003010f50700109040c004115200c6103240d80248207002c01c048501e80b05500510000e10707680d43c3c8500314100d003e001075000600c0c0c0c1c8107a90350318004100f0b41d80600f00301d02c821940c0318110380300d14411505981f4440078440c19a0030800c0100f0910030401c40031070307610502624503410315094103201024410703140e000700546505c450356220f060b9410301c0040d60000e01da041c218202400d1041c24a160702a040b507410002100180c899142e640c1c2010284400c81c0040c0f03e1100404070341015005130500340c440b09a2101c440c0d004030714170f900d00e004454007030280a040c2420030b03103031804000107050696540103020800c1100805d880155000418a00d1845044440e290030030700103110480c6203d9001d2115a00418088030050380da64100383c071100d409103008280c11000e0340d489070843c411076000961210310020743c0c1f0380c03002c070034030700032801c245d04442c00b5800c01c6601654480301c81c0111441407041c0d000444000d84c2121310110070704040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 921019559 1250 921018309 921018311
    0x7020f130b150304060615050a03090606030816060b0414060f12030c0c0a0614071704050627030c010819060e0f1b16060b03030c0102070b07080603060106090504090501 74
    0x1c080d00841d04840800d0010b82000c003000041000b80210760103154000c01c18001c40160241d080c12008210f4025041d16504054554144c00244507250700041d01540c2c000c4441c2d9902c2d44072110164620311002001c03580304e030401e10440001d1405224881490481d064040c0140c0d81d01410031402000484a003540720003059492400680200080c00560030404010009000687d0400600c00100c1c0d101104001c0c180700b00d1180018850150b40d8040d80c040031002e95401c9a203283e00e40341c055604200d8220300085902c020400682031100b849100500c81481040141c4080c1511007400f484000c3c0401c1c02c038400b0407010303440c690b00701e0145030305c0c8040051816180c90003c29406001d80e506249000607100307100d00310113000b80740300d070700584d0b1074000f441c02040d1a54081140c141420140034680c1c0d4501c003071841d880910440c0c00758640d91000310f650303500302c3c60420161402501d268000403207000004025050005a00c0d0580d1021b40b03804151601c1c00d0104400b80c100b800d0700726559 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 921020809 1250 921019559 921019571
    0x201090504050c042c1305070e01051302030612030c030a090f0b070b07030902040513110102060108070b070c030c081e010b06250c0f1d1923041b05010507020f13 71
    0x10303000b40c01c168041e1b200b6140303100491546040952511440c0c0e0000380d60054680c00400c46a600c50600605080d0700260260b12a1740742c0001a00b100b03c0c0441000e00f40c08000340708a20141c01200902c403162440e107076000c51949818083e90425040c0c05000703003001c02008407030301041041c2c0c07140354004210320300400c505030964045000d60310161480042070000440e14420020410400c603607140c0300b0305c01481e031036140c62845656603001d44038014100740009010000e04c40108005c00103190803c01c54a106a0340c1c1500310340d03d0303440d25190b0850080c1c0304400d551050040c02882000c2d0002001a801c0020071a582d400300400380c00e40450b100c08803800303900059401c2c94043e009280b100c0e00a600c0900c0c00d46e0310030005540360a240042c0344400200306950150103114070a10321012800202100020550340e41441e2002403641e012191808020800c4100428007083e851020f44400b00d0907507030340055405000326070f0029400316990585590604055404402c1d03422041408629 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 921022059 1250 921020809 921020879
    0xc020f013209100206091518030301030c050301050915010506030c1605010b030f03040e0f04080408070b07050c0f010c02041523030105010501020d0206041202011b03090201090504050c04 82
    0x300c00c0100c62100c10900c0100d903582c0e09142640300210507548500191480c0e00c1d201c40c01948403040e00d159075000c00c40d00c4010818142c5282c0c00d401384405040201c0e40e0f0b0796180e040c51041c1320000c0c461144030b0f40c203100000d05aa000401c103540060185611800f4590900b02000705030340004241e04094a400e101c0348076500c500344200180c041c02980002000620f1b807040c141401c0040c440100c0715481003008001c100d2041d0446030f4007c1c1a0401c00550344c866180441203442168010041d40c4070f520b401180c82c008020007040130600c01c404071020b4441c1c480500c026032001d2032216011401c0b455001c0c0142c2065040b101072910306141040001740c44190b03211250710364014421880c0c0340090070808a040c07d10a041c0540004d000400d614450010000d40e40c501c01400144104904071424180358000d410882400c4a02c0444440e55504c0d00c0300140103116007502a40000c0e040358000440f4200340c41903a00070840032540b245440e007000c2013171300c04558980b4900504040d080d00090 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 921023309 1250 921022059 921022127
    0x803070c022809180204091a09070e090703080d1a04020a020309010908070305061b09040c121b020601091a1323130f1b03030807020d0c020f01 63
    0x210060914180c1c11541e07540b09040804081c2c0e0001c00c030662400300d00c200c4040c030094032940f0482d4116030100303031510707030741b03480181c1c82c1400c1c0069240b41055001c0c007030380700d02c045442c0c810b07281c402104603403a0b40d40048480c0d07603034130074031000e4103508040140380208201d40e0440180750340c0b02142079030f91141c5980418100d90180c6410300c0180c03c0400c1503c129a44021039500610400d4000c0289a0840c0c598545031117000d8041d01c1000042c00c26002c00c03920b0a810386d240300350700800c02c102c940c5a410024005141110a4214041c1b0f0980c0340c40c1071611303149140790103526076801490b040e03080420140003400407944048142c40302580400c41d641ea160070341411444c811001140c14141404450180607840d013400d25040112800c01c0542c107100c000000101d500050505400303081400c1c402c0c40030302d80c0001c1c10b40d1201148004000c2c13680155046000e0300c102c0d4225140303c410134400300d03010000708400950001d03006070802001d610030419100d4011044140c0319005121141c240 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 921024559 1250 921023309 921023329
    0x29010905060a06090803161704231c0305030c04330503010b1219020d09030f0201060e010302102d031b083405040f050a080a0803070c02 60
    0x4411948500821501d4104000040010865420203034015400c20310426280e01034040d106c004049094000703801e020400c40060401c08281d4000d0341d4558503052004590020b0643c2155210b01021242400d1308080784214040f070316411151080010b01d0f5000c903615071002d0065814074500b40070102d2032510b845801803a01901c06901908009010703012181c920621051a040c44014401081040606001c9650401c1c80812000d10365a890f41404440b503000304070042071a00c0030607044d44030304481d482441400c0c066158103c2c03492803030700101e003a10b0717443c01449040c40700d103030040005003031400c1c2d215000c0440f1306002ea0001220f0062003101d81ca0362074046409410b20207003215040e0144903004000d206010300e04009d000481d001341220718040d1101600709d40780c02c0411079600651524000102100c1c804944803105100c00500607000342c02181070500e0310003400140fa00e0140e1840080700c20200c0a0b00031010b0130b48840700f080c1c00041001d01030002208031440140e9a00001d4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 921025809 1250 921024559 921024569
    0x112021e04230105030f030406021b03150106080649060912080a051b0c010b0a0b070606050604080c09070e030a08030f0f060120070e0a0608282901 65
    0x2840740d071600003051b01e401b404100310000341d0820041801400d9000c41c094103982d034815001207000407003501092920121000140030100c8007400400c00c1076000c40c4040c000c8030211040203c01c45280229440841c0685002c0b01d06c1404d0500040f8003050b44901140100508058261b50b00258595106407108240f08607020000e00c0e003205c2c01c07035802c507551503005a8108002c00c1545041c0481b0426a140c00029032018000420344c580c0e41e030025004140100c03005454180d2040e90f03403040145581000343c089800504204000c942c5040010950f421614100300800c20f181403001400302080c0042c0c081c034100300501c7c0082d80991400c01000c0502c91240000396602d2409200341c402402d030103080840000d00c24004d110030f41e0f0340600b4010052140045210384400c1c2200c0240c91b200d4290f208004c034101c0081000008032140d0300a20031118a001a1003010002610500b48598806840ca841c80525501140451007072b507001c00551f0058040c00e0242006211142c5981c1000d0303102d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 921027059 1250 921025809 921025871
    0x1020406080405060a06050d0212160b0a03060603020313060902030f030406080a050105010809060106031521060b030316081305040f06140f030604060f02040f09050f0112021e04 78
    0x1e020803c101008090783c481c0160f00d0400005041100041e0807014071400a80309103903003881c20300b40480c14001040440a68500c81c504a5540e00070b07003c1c2a0040301a0501080c902034000a0b9607001e402101d01c2904419492a00312045980e06d00080a1000050360035100d80100c0f0f9040400420042c8042c02c40c8e9281d64503640f9029411209490f416009030341040348050030b0182c54140016518190390307032801d01003110800e4010f1101c1180c100e5001c28107004c428944032000c100704103c1408001c0c0181e50a02c041180301080c983d83c2d05c03440c068001e50100071100c0708080703a02c41014201c41c01c507200c0c1c10300403541e41d1000581951030b094060343d043c599411081100508184002508050580b0f201c4007d041200010762182402480540b0458030f6094242d5014645e0781150081c052102014464a844042000003018100c8640c19031010800005c201c004a0312402845294010208038a140c07810031500c0a240b000340c8000d80058036448117114007a002c80c1c001e01050b20b802c00c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 921028309 1250 921027059 921027061
    0x1e040906090f020a020309010806010225051002010e070b1c0603060e100e1504020d080301030503040e0106050403020f1903150903030b15090d1a072d02030919080102040608 76
    0x1d0380c01c04441c0d15003501c031403251041181d1020660080300f5a400c00e4400d0030222095610440140d0030140d442c800050040b017000080c52180b40c03c00003000581d902035444a00364124a0002d90882c0d4240541520079840740104111182e400d800810a50f81c07030540103200d05e03101d8640f5800740c801581040396565103e130b8085403100800c000f02d00907260944005d2080f6280441c1c02904c5030841d140b510901c10407100000d080d516071f2107114010342ea000103082e17904e40c2c1d641080c603106d800ca4001d888814481500004045110388260f40030b80b50028446408518424104a00c0300d45618081e07254244012001001c00c40460702c00500b04000ca101280484030380c90003c04840da05640365100700e0044034400303002c2c88820240c4154010640d681c900c038034000d00b028034001d0030f0002c003030302d5241c2035034200003010743e01402401511902e01d03400c52010002d04004001781c642c0043c040d0059005002881291904070070300c1580c0c050840d07400785629103600709075084e85d00682000b00401c42e148 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 921029559 1250 921028309 921028319
    0xb010e180606010f0509040e030a050712020607020705010c11090910060b1804090317040809090108031c0f090203120c070e0c03070c02120105102c0c1e040906 70
    0x3408810108003005070155150200010303000c3c06000e941c0344100070010408003010303240c5a204141c100f6080713007169140d00c54032100615941c00301400311401070002c400c3c540c807c1d00000c0c500380281c80680141c203025080c0001190892208101607540d89982c21402101d512a441114001c02c2034601601d150003110701004180c0715035500c611880d0604000150103080c00011001880408840c04140c442150604545440e01140c003002c43c00010001d000801024800038000c40da4161020728290b170340e0342d0b00700d9100c3c0070368210f0074050b40900070504100c0754140e00071190304c0c0c40b9030000140c00348180c020070714009503070042a0785144001201c014003c2e0800942d0020031880b18403904514000c0074a110901000d0b0140081c00b05038030a0500719030301d0300030101d889248040204034500c2c0a4890080c200d02030f00c111001e21116600400e9640741c448500c440702c02c1d02442110840d203400580300b8040e40704021070004168030320800c01005803614010b1008064413000410618104 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 921030809 1250 921029559 921029581
    0xf0c09081204081009060b060a05130b070221070b0d050f0a0506010504091a1f11030a020a0b0c04121b06031b05070c05060c010e0f03041d070306030b010e 68
    0x80c01c070744244080244001c00c102800054500c030341c82d5998a0125101c00d8500d4034a01030000440000e82c45500032440300c40f40c6a020015001012450b01c0e204500e65460b041840b85203d0b025002c2e400124801107081d01144130f03402c840c1c0003a1103800322140669110140703c0c091b0405800420345076110001e1041a503102d402054110b0030700c0e0001c12190518100207095446948500c070b50240e15600c4440c2a0320002481c0e005c10900903141003c04420040c1e001490741c0010242c2001c074000059945088400009841c0d1480180d0010140030280c2e45483c1c045600040c210100307604200004100701c90022001415144644061100350758110414501d140036a00540f00305071070039118034030302c2c0300c841000000b400303a41c20082d0f41e505050510720851411504940e4002c40001360494000e0350540c400c000101e00312007601c00e4442d4582420f5140d1080b44144060140090b908007107100040418640010040c20005522603590340c0d2001b044000341e1060342800d140b00d00300288080700c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 921032059 1250 921030809 921030823
    0x100b040509010e03070b0a0b060d0b031908031807080a030504030b090a150209030313060801080c010e090c0c0a0501141015020d230403050a03030e060f010312030f0c0908 75
    0x70500034090070a0711001c0c140d40b4040c2e1400500aa00200003081c1c1c20f00d00ca1b4070940c08200094021603654405140a00150801980e058040e10846014444001403001544000c0e90310aa50780d1440d01c8441c24148000c410240d240f51030700030003c000840000400001c00820302c20b4940b50f4030b96203181030045103008010110b0440c2d0b0072201521000840140300c0d45003018915800507100c0c08d104020929502607103100341f450441a8101145054001440074102d030850b00444400c44043c000440d0913414000307880d604454030781c0101e09040140d4010382100102c010880b43c80900304d0b100c3c0d030700b55070703480715800741841d07aa2090020040d00d82182c0c6024200c1e4403d00841c65008030002036031800071006440030840103a00e03440d10400084214501d4803d0b455075992100d8580c140551280c51180084001ca4a400b5411503500b0000c41c00c1413240d8a80d2203890010f03031842c0c4400c40d60b8280d966860f800c240e0f5603005044c020b0000c0c41021800041da0f560034040a0038406c540d460f103a1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 921033309 1250 921032059 921032071
    0x20a05010f0507030c060902060304030207260709090305160c03020108060922170d06080105010501021f0f151814061c02032d010b0103060609030308090a05100b0405 73
    0x100309003144210342c0c11400b00c03280990f151800945000a41c2440c1004002c1610000d40c40180001417100b8954006400802e598400c101a0345200100e9004440d650400000b910311f5040600c041295040d0b80e03200c0c010700c80c000e0805600d0103e0f001f000f28001a00c000c811900e130020380750f0620565038081d030b00c542c0c04201901c2c00740c0d40f8102118051b0748507040d000420400656040c80c2c40404c5914102e800031001d0025030740781c0300d0702070303100d5035001c0c000f05c1c0030340300733003580f803c1c00004c2c80703601c0014401345224289440400e603c150f8040c0c3c10280441c03a03085400305840340101f0030b000c400140b81000520071030918208c01e521050086060714001540710031503505102c1480303510b43c0c0300e8000d030800d41030404400c82e0f0f0000070300c00f0038188103906140d1100604031201e50820003804542018080d41201b008000b4040701400550480e403c90040d40d000845046040c40024007850115410801c80002c803408241e4035610706241c03403500142d840307400c1e890f502841e019091500820390000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 921034559 1250 921033309 921033317
    0x5072607050c03150a0b0a0b18030f07061e091e23060d0c0e04060e041b03030219110a1512090203060609071b29190c050c010513020a0501 61
    0x10090700e01c50002e56009480107000d543d40e01b44a0700740f5075856180d000104161184e60ba2a43c50301d1006440c4255901c409038024081d00c02c0d425401c65020429005a54403603c4185a07060795405070300544903400c00b0035050088038107001c519200102c042d4010162100000786109040070700c6041240c60003600d00070f0091403541030246c03c2e40c2e403c007034552118402c1000180340c40032000403581840c3d03140c0c00d1a002441c0a401040010341c440c0704a02c1103024038031803445050310b041961461012884003500681025582440b04540840c1d4108054020111184a44142d20010300034020580c407406180385040340102490f0380180d601c41c2001d1281e24104481810b03a0040b945581000709494843c010742030001c0e401c0c0d40281021070207146540304500c2703004800e1501000503102001341d07400002a24445002c59032203000e40a1041200380802a29a800041c2e41005051102c0c202c40a020f0140548140c00000340b003501c0c407400303511802501c100d900b4014004007a00c5904518108 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 921035809 1250 921034559 921034573
    0x1008060d0f051b0613090e0a0b04080a0e060a0813111305060301060504020a02030d0b040e06090309010e040c020a020d022b11060f072d05010f2a05072607050c03 71
    0x101880000617021545100d81c0824400c0140b61180e082c880e044c040100411245070a2105024031540649800c0030542c45a09207000f90b20200312075070282c00d0348040000c801ea8001030503180b2402c45c04131020310130311161280a048400240f8412001035101035003d95400410500e0b00c1c0901448009000a0318114541140c044009403a84070307944440b0b4605868030203219403078907141d00a581c00301110065595508041042130345a070310000030280061b04240000403035140174450368000c52129001401c8528490b0b0901000a80d0320f03600b41c1e4001404035680803001010640b415540c0c640405901c2d1001241c40c1c6002080d11540c1c0240c01f580080c042c540c451314104040b60452134220b886007103000b414a201140c1044070201c00c3d4984da00e40c402400c01c010301500319500c6c401c20f040701805207407014004200e03440e084040e04103024604842030b840300e5000f4001008000e0095620038400113044643e4803c1d0040c4060264a44e800001d2681c1805000e000300c0050000c224058040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 921037059 1250 921035809 921035827
    0x10f1a0604090b0d0210020a1b0509220804141507050c15090a0608190b210304050a030f031103041a311802030103021008060d0f051b06 60
    0x11402640a04010b140c2e50301c00e03030003050b541c0360109401d9075030090518510496010700291680d184400440c0c0c000075140c01d609411001d02d03c001c7c2aa40081c1074031030b142c1d8690315900030481c0c1680c15200200074096000300442c1c0d0040040001e4090003000982050304031051024031084500c002420726003e21201c000240082260b1207040c000301d5113580120404100d015030b03031041c541c0380f560100c5880c1000423011b0304902c00314455214980107441803a0903000c001e0644030140141540202419040b0a01c400d00c90500105050320030100c2741403030385803070200d43c1d0f56036150002e40303658100301d00b10f00405500c1086004440c0c4c0c0b940c069410507240c6907501031158452803600045039004036002c881e0a501c010300407110541e0807805c1002c0034446004e042c00c094640200b119900031810303c1e440c52141c50003144e040b40d0780540070500c40346c16000101c6844a014120030b90010744094000c000c40c0605180c5005240908047c0001084410081058a80300c00c1080e000310010711903858 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 921038309 1250 921037059 921037069
    0xe060109090e060730050a1112041b031b03061d0601051005280905010e01020303060d080408150709120f020112020903032101090207081e0714010f1a 66
    0x1c0c02805908000400c17400c034007809104510440b00e04070b4240b003062100b400c025065000b460241c0a01c1d80c040201513044511400d05202c0c070508007031807200a002060008041d03074030360100400d1003000c01380d07150b4696a85034605803402001240b440c030b0b0002c091003400710500c180c0d0b00d0f801c00488400032001141d2400303501c50005200303140c8154180030700340c402d2034020340458000305800b211440003205118041010110301d944014002085100041a194000e0100d0780d135000e0141c0042d400d5503250420480e5000002400308d41d944403d11001410f0b03030080040c042c038000140461f0a40c0e00c3c01c82d100400403951607200800b001c3d0054504c0002c280c4400d80c41010580a01c1c2c55408101c05518070b80c080e114010300701e5058880001c45605000a40f2600e8074204000e0384810b61690341e0f581180b0a9004054010b0180c010400850402c0a0080c02103d0350000400c811410b125203900c98110f1402d0f13031180c101080c0d4560920029080c014420210040601001c0143d17800030140891 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 921039559 1250 921038309 921038311
    0x11160f09150e040807030201020904090b1f1a0c100c080a0b04051003021228020405090d081f03080f03150103060612020724141006050706020313020405010e060109090e06 75
    0x4d0041c0300f00241150a04d4403c0d0100c0340c1204014206000e081e0b40c51400009005044031541c400740c3c8100900d001c4003600302a60303421544060403081d4030000994105034140c1c0314480184c1d0ba0302c0f4600b941003102c03c09000c5c84990344299100ca900c02d29043e40c024054900c140b0034140314614150410411004860108040d03a0f015a0350329000752070310314564940481d4800c040401e0106495000000540940481000e07100760340501c801d40342d100b8582c1c0e07505056885c500108080900040c00280442085e8018034840080c002945a581e1120707092540020940e61070303410001b0800c0030200c5901028012903c0a18040201e47e00d030120040520214400e0b1044e140e800080742d500f0b0000407401415914070b48050400d5910048041034010150110f001c030780c10703106000241d41140185013a00c1200c11356120302c0e00c1c003070940d40c034080250f0001306480c40b055074000d05200580c0f600e00c99180603003d824504049410315200242408c0b04507802382c00410304040110303070890004a030603 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 921040809 1250 921039559 921039563
    0x91806080a030c031b050601090f0902031c050d1104150e011409030c12010b0a0e090c10030f020a0e12030412141507121104050d0311160f09150e04 65
    0xa4040e01a0340c0750440301160704c0ca6610031754a94260b90352090080204155048074109542000700307100301c2480c0810b0b00e1000c140a5896002044011500c000c082c0444a00e4107091602520700659220420125400300f50070014000000c14180001c408048084078841c1c070900303200c040c0001020000782080035030505508507039030110740ba030303150340781005156036401004024002c0c1d0a40408454000c140c07505125106440300c0000080004514a0076030007014400d02500b20080141c1c180202017860424107001c1654502d0800c1a5009a201508034494140d8640c00f080c4003030000c101e0b000c0043e805412168100f00410000001d281e035480780000d9001c0c003840400034010070894240341d9414144158070a11500b0484250f41c4945c4002400a441500704030008c00300c007040806000f540501900000c4400004010034041c44841182603070300e504172202c0d01c180401d8240f000c1083da0049805040f451001d1003a4002402581060032050803c100c1c507500d4020b14184240c030143c40 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 921042059 1250 921040809 921040817
    0x130b2d0d020f03010903030f050f04080403080903070906080d08070504050303160f1211010e0601060e060c0a121805030c030a0f05031e180102060c030610050712091806080a03 77
    0x940c21512250500550007000500801884845040203809892030200e40d01007035141400141403040150040c078001d58201807110700309421070b6035808265014210b9107515105060b13000500304054028540034290b090083d0005100e28007020341415000392914080c0a070070300042c403041d20004251440c05144580036504a26603052901204007000406014031850a80450342182c00002c05484116240d0080000c0307440141304540b02c180030b010f4000002c0700c06c5e600740700510700030010308201441d40c401d0303e11b8000603903101c204956100d4041404100d8114407828009603180c2c1d00c800410055010340405e601000002c0c0e100c89508a004028000d80600c0c0701c10701108005854510303c40c0028840c0d0502c1000e8102e080790850320406005000800070071015500c00300300381d8002c050b003071004c40c15611074004004903c82c2804e50001044000c1c40a4008140c520780c43d13050304030080d200d0029960800c108640003401c0407030815003050030490208400d400000d16130a0054042c50 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 921043165 1106 921042059 921042079
    0xa02030403120c1d131e0c090810090c2c091603061a060304060219090f0b0a20010506031009050307140c130b2d 50
    0x100c00f5000a5640c010801c000c0841600b03040f1620008083c3d02d50380c42c1d440707000b2003200c0001602e00d00500c850301d1541c44122003886000c0480f00c1514045103907c1c01c242c01035654001f4200b00c0b07500f566aa501140c14001d1044203d40541291340d06541780644803900d040c420782c803204030075544040001c04500398500010f00504c4c98140c1c0c440301c14440c3d00d180c0b110002041449142209a941010b007000c41340d94540c0114411403281c2d50050710307032031502c451301c14006856036550140028000140b1204000381507441c1251441103000d607864001c0442219140800d0000201072002418031a1000c2e01c190410361042c0b40c254202d4540300040e100100c250780101e0740260036034004000d8100860b408070100702c207040708401101e140e50a50008102c04d11801c00d2558000c543d1503144c0d800074941004000792402c0200200030194514840fa610050010b8040302d104155001d = true := by decide +kernel

theorem cover : BRFrame.Cov 920863309 921043165 := by
  have h0 := BRFrame.cov_init 920863309
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920863309 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 920863309 ≤ n) (h2 : n < 921043165) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
