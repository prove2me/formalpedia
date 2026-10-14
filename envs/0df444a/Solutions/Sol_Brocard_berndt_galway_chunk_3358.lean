-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3358
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:25:57.741984+00:00
-- url     : https://prove2.me/submissions/8b7beca0-8c98-4d9e-ad05-249e2e6b4456

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 603776978 ≤ n < 603956834 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 603778228 1250 603776978 603777011
    0x2212a030a0c0201171e060f030709060807080d120b0114120f01090902010c08090307052106010f2103140d02030414010506090c09010e130c020706050c030a03 70
    0x122408040a4a0303840c001d205000c2c1144030060022800120681e014800280026000c00e0044081e0b10301c0d060701201e503100b6003500420203440d0541c8842801e00340a8142e0302005803c0041036503000c080340b160f28040306241005a607a100141c02d420000300c1c04106a4004005070205103ca2000901c3d24203c2e40104d400c03441080410f1145403002450165030501c2c00c5105104811610014410b0380e21f0707040078001e03100d5281c0001c2c046414401081300045086018048244024049443c880d40d01c800040340c185c0c501d80310200f440c220180410f00c42c1b80a220380b030301602c04510301c0740c842860420b000c1803540000000260b20b2030800c005108042c803d89501c1c40b440380d8591523340700d40102540100030b40c41510225040c443c88000d60116031070600555101e2840105041300d01c1da43c0c00c110340c0465000108180c108511040110442c0d543d54007801d80070f20a5040010300020080c801a160120a400c00814000103101030701d00c1c01400000c840400ca0340d89008500d00522441440 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 603779478 1250 603778228 603778297
    0xa03050714150721060b090904021305071e03020910050c150702100e06011a1606111207090b03060d0302030405060301120510060e0609090c090702030405010221 71
    0x11a030102100c18003400340d078007100c00080544c080111203011031000035031408442031403050000c00101480102c400f868008440e560003030000d40815800204407480300d044680c115003080101d003010001d03454040701812407900d1040c06060444c50080c0c2407000582c407404064802040280c0041c402c3c489900500100300e21100300e00c0c0740240740c00c040300080d494103e01d42550b0005454108110761050700098541e0481d500c00d00c441406140c078148081d04d5511800c401e501f80003500d40d000c400035190703110341da20603001c80b61981d48070b10740b10119408414000c1c00034410003a001c042805081c089000322500a14110f4400c401c3c2c8540e45001d03401c502441e030040f07070300400c04000000c04141c0f00b8100480588680143c8140c038034140901c1c0c017160840d0085c10511008400001c01c50b081000745950003101c0802110381c0d030751007640050341d400c2045401d400180c0012508100f00e5030104940310000b9420342c407061000c440840f400388180030301a040089550100c103020401044c2d0b0703070840c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 603780728 1250 603779478 603779503
    0x72309060315130b010e031609110712030b090610120f24051f0806010f17070905090601030c0512100305030301170c011d040911061809090a03050714 66
    0x4083ca4081c3c52900a12070301c43d8407400300700c091035a14034030714001c29070303c2c500090813000601d181c0c10300c6109002408040000030624504000241c08100c2e0482c0d81d9428106030350f030104440303044030b00340440d0b072134040c0c081c6004900c0f10300c2d48a86181c00412850345030540f9100014071201030641c020280c003030b0402807040e080c01004440a44241840103005031901910520361000e4080e1401400203030f03c0507828001000a0049161584150780105802d0300519025450700c10544603504980816142000400c3c1d10b14010400f07802e0580c1c0e03165002400b402c04003e046c5003a940601580320f800c01d10042d005041000465031940040c80030b000d55041411241c403903849013400d640301740030200903243c14070410a4050701584219003c040800491180120b8800d04505020242c0340701c10085070031591144188480d0f8441d02c0c054940c0700f4080d0882c40a01c00e0000a00c251a00090071701e010b60b4000c1d903503c07004203070420704448410703a00c03481a42280c1e040e00301c468101a0480703002e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 603781978 1250 603780728 603780739
    0x90f031a04080d0f142d09010212130c06090f0b1308030406020604060f090c031511031303030e01020f04051003110a0e0909060105030616030e0a050303072309060315 73
    0x1030a25a0f0322201e01403402110710703245c1c2d407121456000c00e411224003111042d080f141454441c8800350300019048000040050704018106122000410044900640408404504406011030400d040e002880d86080a10301d081c03e0200100c6905a030740180c45118100083c03911127407a110242c140103000540980361156111240203403212401d1b20f040e90001d080c0125103a041986114500c0035640c040c0c4009116445e40d600c003c84004485022045581e40782800f158103440b080080d13105061102e500800b41500b464040c0c1250703841e40f1410300e580c0c0305100710000c2c140700708200e6050f542c0071110072180c07072440c441c110040c0010310346210f9400342c042446422190003245c025151031048540300901e599180b88135176103aa0902c074459050b400711001c604480e00c2c0d86032401102615280100702102005802803410000c03050032505507100008126a4584c450382e804421800c11800124212400c0c02d102240d00948076003520034003000000c2b411b02e809440d41101400c1c800303001c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 603783228 1250 603781978 603781991
    0x3020603042f0109050108060d053c0604060b060f0f0304110d0510020c3f03090a060209130e07030c061403220b090706090f031a04080d 60
    0x100400801049041007181c680d04105040c15481490b20380d065141060b561082c000d480d04004681000e000717424540c020b000c085200c0c010450500a19a4100d080410603a0003200880d40340c0e20681400388134646080c60025514200c0400b044440d0016041000402c2c1c01483d803000031510710a6241030701e440980044c080d050309a40f42c0c0030714400c5004802e4242510b00c181c0a00003a1079a04100800d9034108219001c400c02c2c20743d018104090000c0219201d00c8030035500001c4800030b0569100ba03003c03115001550f080c000c26007000c0340c00e251400042c1035080421030b42c2c3e95155401001090707141c01181241d01c90316070105082d80c0d507000801c207001c080080a41c0b40e44034009070200342e0300d4420540010850900514205540380403203515245196190801980c80c1c7c05140044c85074060180c1042000c1004860024041c0a10201a02d240c920344030010700100d04944c4800b810341c4004008002085010040000e1940d448514445035901c2e4503000d1224071401c046070800c03515104 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 603784478 1250 603783228 603783233
    0x1d0a0b090103230613020304030c0b04051e010219030903050a0c03180605190504060c0807050703140717150703020a0201061802090a0e0408030414030f07030c0210090b040510090302060304 83
    0x1807013405030a0a0703403000c500c480c842c0c8051041c0c1c4801c031400790100c1c1d1440c213640006080c19001d41d030300138041c40c01c3c1c40005800030340d03280c07070781d6003250240702c03e42c0d008a20345070070260350083e10b20080031504040203814001d030b402800340c0c01196628000d000100a0840a041c01a14050681e01d02d1001d007441c1e0356115500540359403c00c3c40e000054405140d0510b4050b4059000c503030954005d904d41001030200d5079150310880d84144422602400ba0b0040000014000c1c500f00b69030400c1c1c400506400d42c18507141c0d0b000d03103a80c0f48020940e50310a840307918420300702d1841550003103654640540c0d01c0b007400109038003404196000c8101041082010b862403409a0302600b02e003001181c0c0307000c0141d926548100f0100043c0c2d4051702d200c100300086000030310040c203c100085c00d03074002c0d207080c0164101141c078144c000f59002c0d804211b94004c054118948040111401001414544012800e0000c048483e001764050540903000140161403003a0040e211a401154001d108540d6441c061 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 603785728 1250 603784478 603784541
    0x306030b0c0a111f0908091003061a040e07051b0708010c0f030b0a0b0918040c03060e0d080a0e0a06021c060501050403050d050d0e060405010c1d0a0b090103 69
    0x11042c00000e070f54116032245040e01240100c0c00004c0c1360040b202107080884180014091a08120b41b49102000700740441e840303006000d011405991800100d462404d4040b804203040700d000710030074400400051115040f1501d01d1500180c803440d2043e2501110460620300c08546414205548100c40000400e100150000741c0a001140c0d210001d4059180c0160140e84a0352000d50340450b004c4400d105c3c0400c1c1e035000d090542e1b0001d109441c024650b80300f1442c01e18081d141901c107100001010f00a01545025207039003000d031080100980d150043c8010003082000c0c01e02c1c0c8555072200742440381120200254a603240d042641159601d44a01c4140800503442001c003031264140900010198007507000d85003100c1e0401c2c0905140c0501c548200c685602c000388000090341d07118600e290b114403c000c03852050748120300000d0518940301c00641011a201c1c040e03442d00908001c1078140c1d490b0300c503070802140c0a2020071500e850f04c2800503400340c00c40400c4180c00c0c00030800d05108003441c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 603786978 1250 603785728 603785737
    0x16020607060e100b09010306020a020316050d02010501120803150a21050f070e0c0a090b0c0d12020309070603020d0e03160b131a0405010e010f02090103180506010b0a0306030b0c 78
    0x1907004860081c161643c0b5501621810032841c0d902c210b10400410115095030010180d01e501803055a00c1e12802c0b40c41c0710f01c00ea031031444c2615076601815401e00b42980905c503050150108142c81715401d05299960807407844002c2c182c1954506940344403520340c4840b440d1801601c0844c0c8000450861079541000c1c4808400b011741c0c4601c6207041c068000315000c5889000e540000c0f2010f540d41e51101d10018941e4003500701c560400400000015032000070307002a09000c1240c80241c00d100042840c01040014240005071105204100307011b0b40407800940c110440b10a41070150302d0340314803503140b8000c01800c41100a5800005125255145d83c04201103c0340d208001c0342030241c40f9411480700c09a80e07198014004004030482007044421039040c1640140b2072030002c11103526110115080d12041d24140c0f000d5600464005455a010300410240c8069000e461f061454151189941c0d0001881307a0380d0f2005000070032068051080d040a80071b98bc01c003178051101d041142704044075500 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 603788228 1250 603786978 603787001
    0x1d01020d0b09011508180a050a1515060f11010605120a12030e10050c07020a1403210304020f0d0f120e0105120f101703070c050102060c070303021602060706 69
    0x2102c2c0e00205a00112001032000754107980d80b082810b5907501c20254083d5038540c0d1209142c41011220f000059041298101b16481070106010008005c250181550114140d0141402841d0010710010fa0300029120121038149410340d00c25500740c905034010b0201e81c00007038101c0103940180e107049000256410525200f442d800940079010030040f000c8805d40d1803401c9058210040d400a048500e0b00b240d034200c154840350518102095000030300c0b0500d41c0d441f81e0b00702198000b41d02c195103414030900102d01102e011401400c178021009400d240b20040000303124001d001a00c050350386800e4100e1100d05da02104c428100d88060501d5040340000d248800700094020082e400f007540303d03034165002d100c1525001080d6499190620501c607400074809049082a00e070300285001090158003a040c0c03a040c0559030b0741c48281041402c0d0700482e0405410340d070010741032108001c0140e046400e400d07054640140c80c2d150b5110081c501e50624000658800d0300402e090b4280306940c0e100612111 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 603789478 1250 603788228 603788239
    0x11030f040e01050303131511010f06060807020f071a0705030c100c050711090a3308030c0d030b04090b010612060e060a0501080a0f06030f050d03050c0a031d01020d0b 73
    0x380d07a8003c069607803292001d40c4005c0c0046440c00c02003070481c00c8401c04007c44c54102002c03800e541a020a084420240d103405080b52252820441e41d0f8022154a81080b102d1010304100e608100295544a0062148140c0044200000910008c5050603100e16a0b4000c00741c1c1d81d40c160000d80240c0e83c5040315042ca1181c0d01c0d00640c040150b0288040791546540b0000302a41828203008202040700001c01c0b651271540c9892224a010000359030b0805032000e0001400550015028062080c2280741c00a0a2680c820412000310060009403410156020b140220302c4041507004034001d0030308018000c10005480001007074041e00110182c00310301c211a800c01c80f5940c2c580c034420942c1d1058540f21782006032484213001551042c0d05560307000703108010100300280a030300035804403146580242d071202062000442001f4040c05007444000451a050041d428010740400a074443c0050f80001e05d50345440a0024121502c059051a80e90070021903e404607042140e001c1c1401142c56032082 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 603790728 1250 603789478 603789481
    0xa050309070f0815010509040f020405090a0206041205010f0b011b03090b030f061c03050913150608090d02150f1915090606030e0c0d0c090603030e0108010602061e0711030f040e 78
    0x10706007c00c3c03540c46260060408011104c00303800380401040c0180c42c400306402071240000140c0c41d8180100003d00651048c40070307000090a00e5801c6805a040c0d05e20001c1c102140d100f4242c2e40030910000b44800c113004288201e817a441c09585124050b4401d1300060008000c106004500e0408140306003c10b5509103003041e00c480b024940481002001070110304140204005030070b02c5224012a600f01500002e500d0b40508024480d80318182c0c020b038001158907040001004040c4618402501140002c125111310501070910074034004040410501e0088002000c007a42c0d54034120191041c00004c001d4140d0b82808440c1c401498040e07240014140580018903912902c224680b400031100034040070f65943c420401c0103401002c090354a111481d201041c100001c0c400c00d0000c6100ba00caa120012040c0300240504205a0000c015500301380100700007074201e0707108800f5504444010f10144d0b85d46400c2611812555214121140300205001c12030301c0400000b4000d540043d00011030070b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 603791978 1250 603790728 603790739
    0x7030203060a080d12020a0e06070609021008012111040c08090c180a050c07080a0201090201120c020604020f280503060f01060f0516060203070c061a060a050309070f081501 76
    0x44480380c2d5213600000312140a807521303242c001e602800845003d403614001030094040020f00a802807081030311034965851010003146090901e10f502100e190508840c03c0d0703d040b003031940140500030405280039100c0340c00300410040031744507040301c2c200400c10882651811001031890310b04842407411031003a03010808a030314080e150340d050308099603840c00081d07507048444070140801500028500340d00b484840300007a07035040076141c554504ea00001e41c240701c2c0e0000403c0b1401d200f5414103c40d05c0e2a6070041100e502281140c0e00c1901680d090b41200300060124110000309800015070f15030200d2003c0b0011038183c41c0404856084003141c0c050303160307407101226030802841514003103243c00082040d100d014174060407058000c990341108400d819240c2c107044e40e20895403d000201038560303840400c0094811480d9200052403620b03000a85c440100744a84160070100d000d001000c00000c8100b0001c000700405001c401a0314000e203a0f64980e0650b450a6507506500c0c1e0f0521b0000100c1d0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 603793228 1250 603791978 603791983
    0xc0a0207050136030b09060f070f05030c09010e040e0106030303050c120105010c032307030f08040803010512011d0c09090f0303040f1b060e0111030906042c07030203060a08 76
    0x40b041c002803002a1a0b114020012666040c0030010600c05800320800004607030704440c003a00c46c041a5002d080680381031841c20342081c8004041c0300038405101034003190142e0140960f980005542030459460b4403800051321000c403e0031003141d2041c01e2126010745104190042d030101c91180e1000d0081e600c95100c0c45595001c1c2d0800401d00c41c045078010800c0d58071900700390002501031300340a540003e4000e00c5551482c0c1e9455140b416580008210080543c0300b10802c0110089142501c4141800d58882c0810f200611540d40300c0c805121755900c800d0303400e6104084220f03050107010b1000784040401901c4044604080d03204413105000280c1415000c2450810488220007640c5941d031543d541c4180307035a00003400e4810f590030324445002e11009080400142c0220b443c3c0721032354806240018000340124150491642087c4095419600d403041a01d003912042c800036039100d8000c150600e1617100c00718052514211060501050a802d90f0045000b0b00e403e94649400944400b450380d0f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 603794478 1250 603793228 603793247
    0x20d0e0f06123d0504050915090708070f051804050703121b03021e010204050a0b07050a020d11090117030711010e100216240c05010b06030c0a02070501 67
    0x6801c090200100b5a28036080b624182e0b002540d14141003549841c1c8180c1555014244040301d01c0510041002080030078440240c401014101d03803d200034507003208426120f01842600c1018403c104000c516144c1d400c1c04194007402d412401c50322141c0c2d031480c12810140030740c0708180c0141d550750740e43d44807881030000c01e03031003140c011000340885840c640d120f010308003e580d040300400c41d80207400e00c01c4105103040107010304e000e580103080c6050f1030380008004662548408056a104110030490740d200d49110303404544c181d01c00e4a44900240c1440c07410081d80090007513003c4180d46011040015203000e403460b1000030b448650171a030725141031402c001400c1c0d080b40c000d42d00601c031600004e166280f50440307884041c076066007884020404241350b1070307210341060003503000102070300a0b020303040c41c2d17110080c401180f40203403841c031141c113600c0c82580f280c41e09010402001c001c2000e00009410030083c140c0003418456580c078025020400c541c001484800060040c1c5d0000600d03036100341c5607503 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 603795728 1250 603794478 603794509
    0xf0f09050303040b0402040f0c08060f100f0503100b03070c03170f0114190b07150c0c02091b040909060b1824040906020a02120408030d0203060301020d0c020d0e 71
    0x851650f151038480d000d500c58014001c03a4030a4a0f0f0401c004403a1036801000045c40d1282c60321780c1181070650800c8205282c8418a40c0110480f469015a60b84d0000310201403210a042440c0d4179210800900e0f0401da858104541d0b44500100748800ca5510940075502030340280d0301c821400d010464022a600c40a9696403404041c9100501c0f1005010000182240006002031200f0030b41c01c8042612072803541c08500000f10109240c424066525014050420b0b15001000f5507140d260300505082e5038544003038081c17a6900700043c2c0303121032000500980040004445c0d2910380d07031449003000d03207a101d4045400c582055441101350800c0300ac0c40c200e121840e071400415a403120783c0416403040714407c420010f14244003070409622070703104800b0500e000300d00c090382c2d440d071202010b03151602e4110000c00c0010200001c220b08c40e808020ba585900c904803015a8030344503000020b019001c1d441c004010140780c102180005500081e1a642c40c80703080d1582c0c1c00d514651030030004001c144e603454 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 603796978 1250 603795728 603795733
    0x801060504090f0906050c0a1b02100e12060c07031412070311120f01150504030506040b180f150a150504050406090b1914060102031b0712060f0f0905 66
    0x18000c0b440c0541000c3c0344455406000110500d89444000c2031316019208820921070010303200200d180e10a490401c0c1d002c039a000720506545d20b601240c10b03001036881d804d042100d51000c15655030740303d20021020b507109c0d40444500f0300f841015001c4d01d5101e12800c40200d520b0780c216444ac0f249034001c0d2829406196a070311419500c0702000c0d00035084003402e0980c041c070100003040305c1514114606000f080c3c0343c0c442c0515581070001e40204641a1000c00041c4002070000b000014400070702240d0041c0e005501941e01d8540d846a800785c64a0711010300a940502005034244c0c500c000340c45809900700402c4404c06403210a50b140481c1c11900814110a80c0900b0a1084e81880d03001183c1245c807482c0c0c005041d185584131266204000e84001e04c203801c3c000c6004021284502440541c60610684810f40341010320001c0d540384104070307c4079261903c0c0360500c070040c881800380d840241000c1110701c880d00c010340741a40007804401c01050f11607150210b070420044203445440b500e04d900400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 603798228 1250 603796978 603796987
    0x180103091e080f0a05090a06020a050601090b0a0312080618010510030e0c0406030305120a1e0911040e070503060c0712051c061202010215100506071a0f01051008010605 74
    0x24800c85440741000181d0ba0b014003048101041036643c0d0003003540050703a90712a600c5031040410081d990070381d9031006086500003201080400c8005c00c03210f04440d881c1c2e00000d1100003403004254842c04c07950002c1d040303c04c41640a0780954008555600c20042141d145d084c1e034030800c03420014080b00780542500171103c841c0b01c5c2d000c40d000303900c4424000411411900e2084241380007034203403980c41e0011400100081900d08a04000a42454100721140001c0c061400c0d00d40d644a41406220480c0070620707103a81891052108448015183c2100544180500412900e40d666281e180d8881e00380648190000100292100c01c00c3c0c8103042c0c0c1c01040c0b03e0b064580e01004a81c1c903000b11038140d80000310b990441450200b20700c03c103001070a88400161810040d4000a030030555241e00401520021004102c0d0705001c0d08124015111308403403441e12031b01070342007264207949a200e580301500c24480c1808100840c005c8000e0488408a0300507280d0001c481b0102d411103428403642002c00e50074071 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 603799478 1250 603798228 603798263
    0x1091409011b050f090d030908060c0f190e18090d0c020d030e120a050105070806010206070e100e0604031b05150304060c14120a110a080c0a0c02090c18010309 70
    0x3c0082c1803e507101c08809041003580d900041000702c00d280100c01050b410102000a540d00307000d2142d03c68400628a030030004d4000d42981e941c4030f50780c03821290040e01c0d101d840740c142c02545041e020605c00b40c684c03418100b0b15000307211034000c00d4170115030a10944441c188500d00c522425039940783d02411403150301415560030703144050b0b803c02c4140d1040c881115483c01b403008104c40001e00d03010304004103c504104101038000040a4041d60464110800304403101d41c1185010303506507416150341000c00f40e000e00446030501d0074810386a00c4100003500006008180000141c04007144005003020740e035802c104801c0703032110304a02040900030f00000300400d015500c1040c8024103800c105014001a88291a95502c406102d071448003203141805074580c60751241403103c0024805007807070682c0c00340003d0322111004080c04040a0001035170002c0d68031500070600001e0380689001e060703082564104080350000120700d1149140b10f402072426600c40d01404003000d0b0040401c014154004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 603800728 1250 603799478 603799487
    0x906030302070e061c030302030411090103020105190302041e05030c180f040f080705010f05010b0a050426150a0f02030411040e0a08030702010b0a08370b01091409011b 74
    0xb4040e80e03112080c00f055060a100e0011351700171072407203541c2c0180e803442d003850f1410041d48510007560050300c43c11b00520050342c100040301da100c0640d40300c0b0500c600d026001203020344915003003000e5140503c00c0080f40d86004107a008207840c0304805031a03d84031140140f01c0300c0301c1982c4401041d142c5400214000c10031520206401038081d00781c0e140281c00c242c403808015440510201e81d00d80d9038608025058402d4800c2c039000d8281e1309892890b0010038000240240502c0c004d40035a1002d00403020802c0c0b4081ca00700103070507812425144521144c40501e10726260440310b40c000e9605010141d102c05641d442101e10440e88030510640c00d14040b42804000c0411f0380688000d841092a6031011a180f2009184100d2551380041808410b007c14800900d146034010030f080c3c1c0c0004000051001501c01c2040540440c1909040402c488201e41c012003000c190041c007200e8091001098a680c03e8000340154842a8204d0a4035142e400b645400c0b140c1c1008440b00710745035400d0091160344079 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 603801978 1250 603800728 603800731
    0x806010e0702190c091d06060109080c0f030c10110d0f0f05220e090c0904050607030b061b0c0a0b070b06041a0603010902190503040b06010c0611030a0e070906030302070e 75
    0x80c4c0d80181c1465180c00810782160300c50340180e040e640c00426007020005c010481c0366407181003842c011802c01d250001080c0e58902801150303101d01840101a049074908100000c06040300074400500f03080028405000d90104c0c08140d0000c2c09002d0002c01d41d90302034080e24141c03a4450350f4030078503d0340c0c080e0304542c0b581000000b00c00381c50003424800b4003015a90b0410303014261000c440c00c00d40c2024205a85808021030340c0c01d000352070500402c40400c0c004500d00b036001d80c150502040c4484907000149072842480c00d080c000000709100e41880d0040040c2c070f8901d6807400c0d690021b800740c13078980036a4180181ca400419016420001880f80e041a41200101a03c00c0d00704880b1240c61400244c09604241c00181d00c0c6d0781c0c046605a900303a020300500803490160b0900600d0f60800b929008402040180000d05201500e1004070401c02203602541549a080c081142c807400d00b01c0040002d02103201c1c10b9119442104804250364489100307060403258541c00405000d8034000d580b6509540 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 603803228 1250 603801978 603801983
    0x9080a030518060309070905071b080d0b27060108161202040906030303020705010b061e0a05090a0603090c061e030509120c0a030909090213021606150806010e070219 73
    0xc55406042d10380300d500195008116110140003041c1c204000042201c5c0010038100c100a4164850120050b03144008801541c0162440ba81c40b044003850201512444840542010600c10308c00c120a1001500d641c020b03502c08141000d5440d403500448030454250b9101083c3c10070100307030244080c010350709030100038090758016040a5481420030105e5426074000c0c3d0129030000380c00000c109085c4034000540e01c0817104241401020f01c16110401c0705080c180843d40e00000300b02e2600b81c02201038400d0342c00010900c0040c16100c0c0c0c3c0c010f0142c49012022103d07481c4010380450114011007080c008040c6903154850107500c0c00c00704030050140036100007058012984020301d986826402482c064030480001d0a82e00d00620380108800b4403a40510360321803400341c005005907100d80160b0091440008007507210880c203100c24030f41c0e820402d0000d189500d00400c031707180209414141000c9400300c00030b4420581e80c035884004440d4080350b0784030050308080c461a24480203c0d61110b01d050 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 603804478 1250 603803228 603803257
    0x807020a0b01081e01020c19080d090809040e010b09070f110d200f03070201030203151305060f01020604120c03020f10060312021903112d0c0109080a0305 68
    0xc840d5100d014080300203822030300098208500503505103400c20040c0104005a10086107400400c5240a0721f40500b80c8050501c0102d0b841c010b018448000c06440e8000c3c408201004aa2103d01c5c141c011640101841401281080e69401600c2030607c03c0020b0000040c203e0901d556400800301d460f400c85280850a012000b041c00e45c1c1948100400c01440b459034440c205100300d07078203102d09145040c1079271200d00d070320030350410070f20b40c03c080181d5031320550a090250301c9444282540b89201c81400c407280c0c00090301ca402c2d81c00f05030301c1d4100074040c00e810380702041c0d112440780c0120f88602c41200c0c01b500500c010903949265a20400c01407411902030f2059803124801100303003500f000401d07840202c0c0e00d80c40342414000e000410141140d0300005000500c0c0303c00c0c034488441c404075034103c005801d2041d200426624940240718204041c800c80c14002440e030070b6184e902e4403404c182d110780c004034856844500d01c02d50081e0300c0c010076200602c00410b03a180707050b80c0403522903100e05868401078 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 603805728 1250 603804478 603804493
    0x90901140438090c040608130f030305041515050d020616030c031214060108180106080601030b09010606120902010504091802030d18170304030c030b0a0507020d0f080702 75
    0x80b040c44019004980000c0e0302840e2400381035100340c80075540700e007079900c20342d1032200348182000054103c6040340c60504203080d41c0c0d624949446035420300b00d900a0300341f0b45032503588000c0540c076501444c1304038850740e03400d030403580d102e09044100c0c1e84108a004200061203400c0c405494554003445415100030452858185070441e214804c1c09691811800304100c6104001050f130040284e08000e0072802040000050f862444003060310064581d5042c0103407a400f081c1b80700e02c12184600031003c900d00903c0010780c0c5e80299956800c00748001d88042c216640491520036060140d501150a60f03611003005c094514941c800034203829108078184141007000046000305800351005880346401c41c072030742c0d05040c010b050819200b0300c0c17418100b15401c1202800d1072400c44800c4e040d05c00d140503c02c010001030003001e15600c240c3d000034000f040000c00010030000c2107a45940700d031030017100901060300d90380003d85c1e840d07003040d00e440042540c0312045c07c803040c400c0c04440d520180030310445c1d126 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 603806978 1250 603805728 603805751
    0x9050f030a060213170a1505130b270c06040303050307031b0c20010207120f06050c03010612020a020c06032211011b05070b03091006091e020909011404 67
    0x100e038041300c1c0211311415600d00820043e0302c20b48442a680b800c00014142804d1955215203500e030003010f004815958031404200580140f2082d41d801685c0455441079600745008020350080842c5082080e0328040d882001801e84003140d604403039030340030300054101810740d84c05894642005000404160f074820014040b1070046003140038101150f218400f6424180c10488981d00d42d000c02071240721100d800748000c03030b6800170300c00040761445410114201031503d001003921030031540140030f4600704408e00403400d05440045040360b00d0f644034420240004400002a4003655012202503042103000039080c0c1403200c021584400b0030011501c5a5000b070a602c80e1043c4003c405981841d9003c805150558114600b421406400c068a50745085241d0b20700c0d03501c4429004070788000c0c0c07020000c03843d000400c104410180000781780c00d200c06611007148000a1054034903d05240c1d030b6040c850322140b0207038400c4450b020300241c86d140c050f0b0b0824070552008400409200c0c0c210741e0b1099030288 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 603808228 1250 603806978 603806981
    0xd020403320a02130e011a01081e0a0510030f0501050619050f1c0203250f06080402010e1302071a0601030203130f05070506161505010609050f030a06 66
    0x914440c9010400009200050700c818809501c1d40d018000c0c040c092046a0400c00140b440d40d40b075040303440f00c8103035440c0c10b030031070180c80c5000e8204461360030700c6003020152194001c1340c00e51090070b0f80c41210301c3d980d11403106140030701c2040804002459501003103075102a030308030603031061840c1030010076946c0da075841820404003c001521036940d5002446003500c0c10248800040d034050003040109801c1400241c8003041480615100308102c00b9641901322901c0b160a8070381ea0024269a0300f541441e00c0d143d0800b0401c0003020080900b04000b05140c14051812010f442d802c6c0d944184543d250342c01501c607000d400b0159a0700030306207601d10740f04182c507000a0043d14410f10f82d88144c030100b0b402030305410380007500070b9060600610070840e00c805214610060250002c0b1075040c019038509200e0b091240c650086600300b9000584240552515040740100c227201d5044075a500b0201c840b81d1045030340030702800340001c0b64000100064640b9020030702030508010142c03a4880015a154030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 603809478 1250 603808228 603808237
    0x314281e080d0b01180501091206180b010305060a180209070c0c120302010e01090506040312060e0f06010f030b06030601030e0106181e06060e0409060b0d030504140d020918030d02 79
    0x420507407240509141942d100088005e1003200071102508241000000380c0117803200d000380441110302041080038016136422240c40c00a484c127500c11b682c242410843c02824003400203481c1d52292f080131510503661407181c40003040c10003a110710036241c10f90130000c0902c0301130217690801800c7c41010780070844456505d0014620a0400543d2a02525002e400c2d02d66007034810805034501002c240202d400171400951066151030520724820410800b04001d000a400070418031340c00c1010041240506401580220026200c100c3c05c21101d0004605075011585c0c280e8015100380040340c084d500030780040c000039800000208201c0e40b60101d05007445881c007044e2000f9a01d51b410f600c3c0d01d5007190310320032078080051002d0044c503003401e10142c0440507504840c0d0240382e0b54030b110700c00d03c041c42e4007844500100403c111401101403d00800c680c0184c040c4818080c5583c013141d105103030840f0700c0c04c6001c2e13024000030070a82e07403400203c01044502400038a5808100915403100c04140b0051 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 603810728 1250 603809478 603809497
    0x90308090d1407150905120601090e0a0f031d030115061d0d3005041203170f100b1206040b0a0302060a051201060309021c051002040314281e08 63
    0x84d20b001d0500c880c000d00002841e48000d014902244c0c0350f6004040101d5490305680020202040910400d081185070900c007440c0a040f00d50350340c40c008105a4000b900344c0e84504940e44040044030f0308002c140c04c035141da0469003c0342080c00000c1200c00e020b00020b048a03500c400801d24458411001310f40303c203031b00203021200b60507440940d00b40300c0e02891a684290445401d202a849000b000103030052059026080c1c0c0a030f40b040291b81014400c810500046c05184060509400e00c00d07030f082c000c00801d407440c0e03e14890016021580801940c02d070b0f8030f2021502903014858841c0e0042c44014a4028045030708005035410100260316040e0050500d000151386440d508c40302500c0c150303180381040e01302004042c1410a4080540d0b030711084043e0001108440c00d1415000345003081c6030859640301080c07040c0c00490004144901c2214018030895982c01b910704c0c0f401d815500303512213072109000d9507904044404d008086480c003104030740e90a480e04003203001d40400780c503807542e19085403205 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 603811978 1250 603810728 603810749
    0x121a03070305071509060903030810030c080c01140f070b04110a080313050307240909050a0903030b0612010b03191e1803050a0e0a05061315090308090d1407 69
    0x8004e019655410303101490704d540780c0801c2c01818450000d0003503280788400340811406002084070b9812640c0060019603002c8509850307641d6440056840b10f40190020b40400c110300050082e80f2001011a514403007800041c6240c545180c0d100325404030050402c1e00c80c581248d0008a013a1155800e840150841100443c0c544e488100805089480350f0803440c06608091810010140c040701e4104220410364503a00460408900840d07800000d50b01c4240b031a820007080c0308410800b0341c00181034071b00030b0341c2c01c1c403600e04004140615403003000d0001d480045401d004111401210014507009031249c420b800c213a06050600806680c0c05206c400700380340c08030306c86030300b11040f41c0301e0f01580c4000e00d0781c28440e1a1080d1000707003903030007200801c5042c801600d8002c0c54640d03407104400d005c1e107002012962140c81c140108100d6115034055031000b1092541042c0c005802100b00c03000312a489000a07203000c0c0f0f1082408402c0c040040b00712509101c0101c041e600e00700500c80310002e00800d040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 603813228 1250 603811978 603811993
    0x303040b090c0907140c070f06020106080303060d06020903030d1103060406090c1d18010e0405010b060712231b1009050307060518030d0605031606121a03070305 71
    0x9189021580181c40c4040c00c0c1e000342000b00303540e2150f4003000e41c0000d603030500c482c6503658000d000c0002d04c6250306003030f110300501c04082541280e05100381d003900c0d403503402004499150950346a0380c4c03000351111a40010210302d0f030400650386400070011001c0103001d4038100024454070806540c1030b00030f1800800804800c1000358101880b4003001000400da00b4044010b0780000034101000c41e0359584580000c0c403040c5105034541c3c00c3c07850110f10a0401c018082c0d0380d903800401002ea0251411112075081c000425124500031040e87c00d0b49400071034421503409042c600351560700d240400500c040441c113285001c080501c801a0880e01c9601d10031660720090724001600b0103800007419440145007810650205100100b5075407440d80c02200000c843d102c220f0506e407030003c0c501700181c26200c0010b403240002c0c5c46420003000c0320019003c0380c41c4000c5010780101000c81d28065007002a40c1540600140d41c0310b07420a00420312a406030710000d40314007000c00d0511b41143c00a0307516a02052 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 603814478 1250 603813228 603813233
    0x70909020114040e040213110c03030a0f050c0417100c05090a0b041406090d06023601080f0a09291509010608091006091a0301050702030904020f04080f030304 70
    0x100216000c4440c0b10028601814a00415881c1030058406809400c800044000040c3c007070f030041102d1038a17020000c2c0c48100f01c0381996542d610448400c0243c80c1414208508038001e0b0050b14040c81180660604040c00c19064030f214464a2003c1032046c4684020648009290304c5441c04a03000c076920036a407000314005200d03032084d00358440080040200030030030080da000b0403241c3d8480411036000383c1c0d5208200002d44180743c0d034100606140d10000d14100750700518000000a6001c00740b06425050f5510b11070b09614201c80c1542c1e002c1000380c40043c2018200315000380d805401000c0004d1202447d03211800a4032072094a98010031084411300700a405100300c103984003101d280c15018407007800c4041503401a040c854001441270341c8011900c1002c2c14081d014138165000000c000380e0381d031901040080e0064441c10035030340603c80030702d036518101801054440c034542e030003c40c9010451005d100c02580501d208c1c0203881c40034170012520704420b1240d100d901c48400001c6441c0d04250 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 603815728 1250 603814478 603814487
    0x60c15131214030705130807060519030506010f050c1c02062a090105161406180c0a1428080c06040303020c01080c3c04080a0b07110709090201 63
    0x102030303003400202d0002000e980408011298410501e1600e141c0380c20b44a0f040e021040d245420140329801064800309001e6401005400b40c010081e40c00c0005000180c42982250803d0b00c10340c0c00070b6450140e0324143e901410080007001c0b4110212801c2c1018280c06103001004100d410006800c0142130240b0003c002d15800c4503211000da2802d1040503813445458140b282841e03543c10303c140803485d007580003064805c00c05c5098001c0032140d661052842482c1c3c480310220350052200e00800c1c000308807010000340840340c41304090300703526045080091414002c040040302e030f5440641a0500c001d080b1001085100680c50016500001e6050884031401c110200e0300c02402091700b1b00c001c1000c00d900280d041681d081c03e09103000b080d00c0e1007480605074420910b05080704400c22841c001e15104c1140c0c0900203040005034038906c40c03048540c00da12403150340b0514201ea03020803200008507480100c1d5640142c01428080d400403204103000b410701c00c01d0b510072004256200c42e04010355820 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 603816978 1250 603815728 603815753
    0x406050a15030f0c0e01030501090b012705190f05040605160f0e010201020f070813090501080705040506032b08070c0b0a0b04090b090109060b060702030c060c1513 72
    0x3100414000c00344003401c540c1d100c14680c4400b0784000503040c420b6040c4500964210003418032050380140c5580c583c1082c82c0600100c15044400301d06540001401e005103520721480300d5842031004240e081c2d0a02d4040142c40060504403642c10044c032418140019445403c100e00401c6401041f24035140c144001100c0000703202000c00c40b05547c5608509601802e005031480260a1102000140c440100d0081c0180c91840e5100030002030341c2018403010340c0c00340c2545400e926044803030716190407140c000d40784280f0400010340d001410621a924180d041942d200360060201d81d244081d250480042e8420303440d2480040700c040c1c0c2c002e050302d903100b900a81d101c0524103080c07611281d165510920808001c14102c1841d50f00c10901746c265032281c1058034041e070040d1072078580b800d090a03598001e021001080360b80615180d0300e01c80354280b110560310030b140c004001c2c02c1d14003205400d001c9075601c412139068083c00703240103450750040c00c402214002c0d80103441d1110301d902945480040c80d140d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 603818228 1250 603816978 603816991
    0x709060803030408030703060e10090c11071701150e100e0f06100c020405040606170c0a030f030c0b0108010902010e0f0d080a050c0601090e0c12060f040c0503010f05040605 76
    0x280402402640c80c00401c50b504079500009881d640d5881500c210020021034108000c0c01c0c030001e0a00a00754035411803801920001c8000300204202010b041e40c2003041d42c0005480b07504110380070440742a14042403520708040d05c0010940781018600250b00050301d03000348800028110600001d052030301000d602520848503010b1f51814800c4040e254200005d241c60b100303485504040c3c1b0281d104801034486a58050020300c810b003010324022002d0030302c500403400700f00c0c00e0b1b2103a1600300b8400150500b036080058003d846803401c40d11901584007004e20258140300c1d41200950010f841c420f6458000c00c00d007000040c40101e81c0c800100b6401001d002c0710702c01c0c02080c032817607120303550300c0416044964000202c954400c20440705403000e008440d4118070314000c0800000d4194420b400100d6036090840648500d41415010807601250381440c40f289540140000b945d00801848450f4015005840461850b035440001900307455aa6518400d401d4031441400108515801007580252 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 603819478 1250 603818228 603818231
    0x5060d0207050c0102190605060402070b0709031103120403140f16030b0c040b1c0e0f150912030c0310050d1a060303041a0f0c0706050c070b1306030f0b100c050709 72
    0x801c210b246c03500880c041c00010b8050703982d81020501d0740d076840d811112500d03800300f6070f80802c1c9004400905400414807058071011124000a103840c50003080c545080c0d086030101a040900710786a418645150001465040c42465144a044241081907000c40325111107460b00c06415071810030301e4400044c1088203080e20900050043c5406441540c40c80e03407400c0c0712203c1000e0a000320b81c019140c031203054100350048003014094a0000320300700041c010300398100045038032125040707030b558035803010300309506201400442c0600281500540d0010191aa03912426403a200007030a040b81045d0300300e0301030444600ea2450200d0840d01240c1c071a2040b009182414648075844010860541d81000d40c5d92000496010f024040c605031003d02000800b1600d002d80c4845004c2d0160740201401038580c82107080018404000c04100c80e904801074003140840c510b0900c1c1a4003038552001c090340a00d441d050b00103503944480072013040138011665006225101803d0850038500d0279000038a015 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 603820728 1250 603819478 603819493
    0x207030905100c0611070209090303061f0e06120609130b070c14010221090105070c02010e03101b030c030509060f09070812070209090c0d0204021305060d0207050c0102 74
    0x80e030054048400c66606450706102d140b0a4602100c2125458000070180d40c81c0a40900620b40c0c844060a600d52094a5014881d00c40806032a513a0104543c850b030b004851900244000000880c0c0110a010b14208000f403802904c001604075000038000140e080550020403010349001c14085402c0500c204410801c542562185090b8090040100c3d050180e510241d8082000400c178084056860600031510b6000c0d51604c822840d8440841c100d220400c034001c1452036506111b0030307015035150344488a040b101d680c010346a2180d500c00d402d5050180c180c4e804548a02c41c0920302c4840000c040040032107000e0b84000d0103c42c01141070008042c508030030000b13044000100b050304071130340083d13a69060740c45803d81850f12000d6044120306018241e00c8481001c0c0140c003420055100f02d038940442d984031804070b0780e905074405105503c02401010703c0094241503000301603455142c4000b201140d00c0e0b6010034030990195241c0400c09600041c0913050200900c2b1606521009202a0009 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 603821978 1250 603820728 603820733
    0x100b01090617060d1a075c0102071118090d0c08070501022a01060303021b0d080a0c170703050a030b0103062c01090b060d0b040209300c0d03050c1207050703060c030207 74
    0xc549080103502d4103c044468050281008a410f400da0034000100030340da1103c2d280f402011644000360410b0142c10703301c00140910311504407140c41403a840000300150749104e201291111122003040d503c0039410051080855000e000820842c00c1d032102842c0c522002403100d03000c09512a14041031a45488420301c0081d41c04200445950403a8003101142028100001e4000d42d100c10700900c03403c40040d08035807042e044510208007900030403800c0351848400c0c0451107581704005005000500401800907200e00035400010400c2042c90002005600e50382e103075280101495440408806443c1070013080401c0e12500da025000400c02440070322800b030003041d4240a50071000c41c03039039150842056181c0303c542c1582c4000100a00f801c07035104800c0c0c4040403001d07000000e218162940c0a554050ad0000104041d00140240c0805005445030f03e0448083c0c102c1c1110060354054901080954400ca40141201034080c0717011f84030051651030820300300c4001f0f0b4001e405050040c0900d501 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 603823228 1250 603821978 603822077
    0x9030c0405071b02180103140d02030703090504021c0c030b28030308070201021903050916060504090221010915170c21100b01090617060d1a07 63
    0x140a002c1c020f840c141c0c4200c0c030000c0e240981d100c1e40300c0b6004030410000000d1002141650140716405426101d951620b0b282c100d890b88600d10010380030486081040040f0f050560080074401ca90310000d502c8000c003034400b542590980782817400041d803141d052031700380d10300b980d0030131504d45480e03005003502c44c055086504001282d20014040c011a94001550503000390116540110310300300b40a003021030548003500a05068403c2015841030520342c00001d00b0307444013001a24082d450720b0b810107103800303000c4001e5030200c4e20b00708401300c001040005403010310700b409002e0030380c488000c50403041802c031914264960f540182c0c04e482594000360507140011448003070803c0c090700d403032102800f04101c007100040105540a52441040110803c11090783d01044c1244000d0380c4050400303950340c07000c40b083d40703a10001104440010020529520380424407611031446450b4080803200c45c020a000041c800b10390b182d01041c01400e00c03d1500e42c035030344c180700035007d03510000141d0340302c84503040d5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 603824478 1250 603823228 603823247
    0x90203010e01090b031e0115050306040c29030a06090b1f0f031b08040c08070503060c1e071103010b09010b030402090405010b0337080a05090a1a09030c040507 70
    0x24015a0303249254011900c0502c422425000700000800c03951401c074032164020096402c2c003210346c2007100b9000c54207140210300bc0307020b00d80202680c11041c1c281404e01c0c010000c0c070428480340744414051040a041e15001079440f61003000000210b0510b0803080f10240c0e110300300c101d44154064150f50310640803619503100100d1440c5480c041d20042e45170294018204500d03400300c1c0c078592800100031250302c40b103132520551041c204065941e580b00c456039515510340c05402e0b41178210100040c200128503001d000d401c8040000c104c0103e00344401415240d104510a0360003043e00c8050b02246e080c02d01550320440401e8410049641c50502c110324035000c0a00000c0c820000d04000c1014410309420003d112603001301910364800f03101c26102d90415080d0700380104460783e54020100098505e02000080d40c0100e80c442c6060301c00202191550f0190807010fa0105080402044481c807000c0092640342c1002e00700303941ca144107010145000041101c540c80380b03003000c0400c240964403d400300c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 603825728 1250 603824478 603824489
    0x5030313090209010302040332030c070b0309100e0303010f0b0403081b010e25050d2402130605360d170c03090901080f0601060e190b0c07090203010e01 67
    0x40c0c540c0e5030703c40100d019209035800600540801c00f108100703240300d0f10316005403403404403c10220b070b2540100151a401030150089060b0000750041099580b0030006591104440095490f10748169180380c00719500b0001060541c0d00200051000b003001d003c00801900395000440c1c10540746a072501c21350300c6031000303090071040c003d040e02c1100c000c01d411003030006c890102a03960304150045088000030712001030082500307015000040501300540301c0120203400c8818072145c085c584602c4200c0802c80509000c0c03d55003000b07205a07002e5582c00c81c00280500c1e94804da030f05c00d61070301c00c240c1528400503101c0b036024030313401e8003103c1070116800f80400d102c050341e0403054403a69003000c1040c04c00c5024500c6880fa0001000300000e000400103140c2c5400880e4240003d980b00c8a03030642c0c1d5025190001c000b9404400117010803806803070500c005481c001e003490743c041c071101e41151401985502c0411041404251046805030a10070079002c1c07c004981141035601d0316440310545841031040c0c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 603826978 1250 603825728 603825731
    0x10e10020f07060f1a0402040f050d0807210f05091e190905060a080d0806040522061b0516020d050111070c0509010e090a020f0f0423010503031309 65
    0x2000c07060112409603800c141d00040100722800010100c1c1000e088210ba04054184a4078820403c5103400d109541c00e80b0701885100d02814140710502501080100094a5030b41040c4038440002c1c2001000c000d001d8040601e000c483d411014016104c0f030840c50401091140078450304403103441d80081ca0407880b031080c0c18441215841070124030124800c065075401d011041c403001c0759032110343c0c028030302440e01a83c0ca0101540d64001c0c00ba22000800c2e003031000540c20801082c682d180c15000710345c1000030111020300000c0c1103c034184030405000b100f2120070341c40710400d510140e50010504170006003424091300c0c2194510f9a502c0e40c001e04a0000d00c9200320101041c140913096020f0b0495038802103200e5079424003820181c04011051003600e101d001e0407c004210301d05444a11802002d0b03440092020900c08e50070004240e445d00c201603005441002094210b40e04c07805032030101d0b07a4521a4840651814145501900c81600020300071361041000300000c2100400010444a000301c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 603828228 1250 603826978 603826987
    0x910031a0c0d060605040302100504060203032e060c020a050108070c062004061205010506070c14011101020f180d020117070e060708250b010b0c0c06070308100602010e1002 76
    0x1290341c90107803048040c030903454994049030641d0020010810303280200c5102616664412085540d440b880c0110740c0142c10602c04140d1a445400c4407442c0b802c5003180100d80b840030f0030200b095800180e4091800105041c8051056003801030842e40500380030f180c0f0703940ca80340c00d0760094656006030b0402080c0316980c1200314058001000110340d40c058560382159a0780d40d900380100b0108181425141039440c1000026003490000210340040303a1002e03500c6ea855280c900c006403074031051036060741032020045c03490030505020701c001d01041d0f10821440361141034180007030520a20011030140500280b40c04180541c0c1c0004809001c03803082e0100d400d44e542c1d41881100c0990603203603110340002011038640100099407002d05100314949942c40100000602020404604a4000381840e2a6900180015001180184403c0741e52508640c0a0304200c1c3c0400d100d07a01c029404e800140030306040c486c003811040020001880c60b4802848070900511003592182201082140c03078650025 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 603829478 1250 603828228 603828241
    0x903020303070f120504081e0a02190201050d060608010f0b0c2d0712151b0e06040509090706031b05161103011b032d050a14040503090910031a 63
    0x10080c0c401c051841c4d00078002404c140c58078545d160031526640346540800d601c0400100d80e92003e5482e440c07031681c01007004012092482c50740141c80041031b4100082007020701c00741e14880c001d100c002d02082d030320100e0541c90b1402e86900d558854201c445641030070450b42d01800d40003d80124040346543d0038603401c1161407081140c000c1c280040c40d0050041e10303000100000f5080365903504a0103074264484266590088070300326046010106841d6400228521006120342170b400c2120801070b044501c1c2a03203c1e00003a0a0000882d210f080c0e507800141c0030320125505000d005c4c4660b000803064070f1201c0745040b000d0131314010030400700710282d1401416014892014000b188400e8041c0081041e030b1810040d00410100c41002407001ca41014251220204400e030284034100c08a12198054900b22040601410300602140881ca403241c1071404203030341c0c0c080300c1400380d8820401565141d00c404140000301c10000c080d00550041180c1c1040480c8002c4803e10341c6200045c8081100d94844 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 603830728 1250 603829478 603829487
    0x140309100201050f06010f02031e0912010e120a17091504030e01020d1e0e0402070c0608070e04111204170a02010b0a09061a0d0b060a0e040e010903020303070f 70
    0x4105856204040461250580350190b004034000d90300c2446605183c1c0d9030600640704034003400aa10f0043c3c1c02003000002803070720f007400d0000400d01d540c1d58502d84492a00060411015402e80303c0d516503403441a40e540c813401b004100b80401410512031b003405600c0344080d00100400c10755014400f41c1c0000900c0e412014004140c1031b2200320f4825690342810304005008070000c00e01640580306107840b626000b07005600011609144003400c411108050804891000080e003030681c201d602800f14000007907580340844054211603031800441e03e03080c4001403000745070900c480d001e03a01c2c0940034014800000c00b01c803000804120100c0690300d452401c5400708104030006500300001150350a10a64190040d0a58480896200d00003036198950402101d01074407903c084440310f8034200807110710007405030000580b000ca000070905149004188580e000c501058006950002d19000614052003502c800c140c2901c0204a10b000ea0346d00a035a0b4031001e008001400301d850a40110144103 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 603831978 1250 603830728 603830737
    0x90d060e0303070837020a0306080a0303090c0b03090307060c180e0108070806060f1005070b04030f0f030e0d080a0b031212070f140319050f010503160506071403 71
    0x88003160b660b440c3c03060300113195510641e10034032200803800189440c0082101840c001468280c5a5203544d01c401c01c1c5180290301a590941c01d058030744000003081202072100384131407400382d01e0100340300d8514a0f2250035441c860700b011070b1012080c001d06c034000c60700000303880406a101c1e0b00001c41d18081c000940d50100078025442c0195244100418002217a400b02412680e4110031561110748584903103444181c200d075003076000107801191007064502100d500a290f171507810050b2401c51281c03100002183c007100c041d404108401040e100140c1d000302072606100c09841e0070400308880c2c01926407030f207030000c41400c00c00040c080400d4422440d58801106072000500f16480c012959483c13000da07400500d840301100c0c21120025040c28000c0f88036501003461503450984180c5103141000315600060065401c00c6181c00820600030514810140161380c10040d0000640c54070781050b280c002c030209410b41842e80004108a65221102520a5180c0c422540c880c230a80701c150a600d58081c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 603833228 1250 603831978 603832001
    0xf15091009020a0905130e100b0931031e0c020315071101091b090b10081e01080619021e180411070b090a0c03020d060f0c020304230303090d06 63
    0x7450381c488003c003000f55100604402e00ca1069840d0b0800508c035071000c031140b91307401c079800040c40ca0000d403450700f1001441d002d0314404001100301121256448042c1130309503104070081540c00514100181c85031400e608807044c5071406141c14a5030354082034a0391010b882806c8101c1400d4085602c8600440f00035803c6841700d0001c011031009401c00141c26801080c0b4000c1103020460003099001ca1802910328440014201d99002c5440794402c4a00300001081030300801d860782144c100d56913005149500810080c40104201d0622100701c0600741811001044620300c104503803048908032158009004aa60000503100c03112410f40f20143c2d82c03071204a640c4030345051091030b1040c2400c1c010b010310034040d118000d0766586000c1070a0340c0395498100600b814007070319010001072809610648070f0610451300450416044440802599101c080300405078001080600590001c0041a141500500494880260a140800d80344e00c1003541c034500070303c1e0203914141803240c0d54200390980c00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 603834478 1250 603833228 603833239
    0x4031406060d060c110f07030c090c090e090a0f11030c120705010f050d1508120f030406020f1c0b010315030c03080c070b03010b07031d0102060106050903070902030f15091009020a0905 81
    0x5030580704a1f0346a4049001c102c07001c01d00403c020420400c0d5126071301d80e108141e01c0e01c00340e0034180460301300c0c240d000411002082c032900004c02c00080f0810000c22029104018101303000a14104141c103059105008038000d07400d00c529001e0100000419070100c650038200300f2010000600215006d200c0d0083d4441401e040c8040c0346001001c0c2900710781290441020b076024523001c52209500e0713105030241203600703100910204001c541a0340c01007a003807800b00c0380c01d450054815540006441c5682c0c03202c2c4007a5803101c0c01c42e41c1c0d58150007001c00b20b045000c04000414103655501c852607465000c05000d0b00004195108084020490321028141c4864007545035a07447c802c580c3e0f242d200c1d000072800034043d100c07144c0c07080304c0d801848040c0600580140c0421ba00b051403c882681100402c25858031540d000010010b10510045019090600d0040410700d820b42c80608003409210141e8004c58103442081100454000038200383c4041100259071204000401c44540305c3c140c01c0241d106 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 603835728 1250 603834478 603834493
    0xc01021e030403080c070b0712091203060305160506031311060403120f09060203120a06150e040e12070615091a150301120f060f050c04031406060d060c11 68
    0x9014900510702c00d92190f07840002e00c0c0c1e200070701000c05d4080c00790001e00c040b011102250f1a14010f610050019200010018040c80e450710752440c01c0c0c01d00300d852408650b444a041c01403000a0095501c1c141d04040000070142c60300000c54141d02c4010016083e18181948000400c04092600c0c03d541000a00103130b15145c99003030001e540002249054080381080031428500e0b801100401308071110f0750040e60824010040446d03140d0802010000459914140422220050800026112203507600d64440702e1444062000b140d07104003001c0110f61019002c80407501c00340c0c0444404680c012008038070b54500c003074103944a100701c0d048004464141200018400b541c44d00f000b0401c503045414100b058021f2074800c2007407000703000d443e1508a01008e040d0100c3c240e4686100703290b1040720300141c0c40c003032151210704942c0d00341e45201c40e400b0001020000e1044a14450405024400245c0024104100003d203241034562008005035140c071310700c0300e42c0386c024444809104040303020364110 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 603836978 1250 603835728 603835777
    0x60408070f12021807090b041d0912030c18030d08060316031707020d0c080105060a090b0f0108190914071208090409052104050906090708010b0c0102 66
    0xa441640c0969600c4091004001034000b284400a024258014115002c5910188401211080e00074030b100188071101c503002410f44180783c0100014081d01240c00040341160300b2039a103100c005404c400307444d4407505803c85045620811640c00066242c0c00c9581da500f00145d07151100100380306a540b50041011000301c49030008031080c4a007208905940c13140c0e40100702100400d5150002505001e0810143d1110b182c113000200103c3d030004150804224030780d070f04d0004015064110403089e9440d81d0900c846410440e10510252226034014080f200e102c00209030b8060380320528078100142480401c150b50308c0142542042000c1c03440174021086142040c4500f01c003080380c030180300d100707001000444402c42019030015070f41c420390441c07a00070490200304c05041d6204080c2d49502495442150344601c0c41c0c9d050680c1c00d001d408158840340740c481084160300000344a2030182d0401c80400c1116a80b040602d81998070111540d0384803802c4000050082c09005803e030031841d1200306000c031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 603838228 1250 603836978 603836983
    0xa11100c03060501140c06160c0b040f03080906010303050316050405030d0e0f060a0804080906041d07080f0f0a111303060f1b080406020901021903050a0207051002120d060302060408 80
    0x3d407982038031024602d5100400e0361714244510280b440701a0030030400300360824003480e94400f54034110b240c1400c9001c00d503140c240441e0810b850440d502c1c18014100d104041d00130382001d51010001d0090489e5602d1074030003521910000348811810b90000020150440c003410039103001c1c00026040714a45842c0a0001e000900f0300081544141c02a1010305505c1c0f03040021515840c84981d1100c03160b4440e0707610340e50039400003941c03a60310078002c0c04040313061070305980910001c1e841440919405d007042c440142080340003070141490381d45a4410840c80d1401c410360316805c40c40001c40050600b800510b5075501c4c0c01a40703480140080408800401e0040313681128807540399400701000410125503541d001d00c0c0510b1030300d80100d01a0000039010aa041d40070305403014040c0140d0701910b11161410302a404440070480200d400070400e46082c507410130ac101c0c007604d01580c6004100c035420201070342d80d090707280c0fa031340d488800040c03900342c240482c0e0064001980c0c0641b0850310b4a40b907603e000d4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 603839478 1250 603838228 603838241
    0xf080d0c030501051c03050f040e0f0415140609091c0207080c0a0f0e1003020406150206060f0604150504120c0e0f0708060603070219210e060a11100c03 67
    0x10010b03080000214041c6815416100108582207441c0c00d640819501500c1da500242d07000c000c090424000064403611251006200300c21802d60400d0900e01841c10141150191484040e010f03d800c0e680d0680e108640f04660300030900b240d0318072180d40c2e0b04400514054444009401000da80301e43d5559486e000111002035035400c4099842815411051204c22080d6101d51000e00c07400752030401103007092804281d04070419500500b5001c2d207940100d420ba6280ea031008070a09420907440761195814480181c1041c400c50b8103000340c40345030740041d00c02d000380d0103000b40d10508a00300291003401030040390300810700116401041e403540d040c4001c60721001c1c0703d45080015240d000940089803150f01c01d11170402600c0e05100340c2c9504052043c0c980008200f2001d52041110180369069100100c21302c080c03054007ca6508402d0040c000584407000129a06002e5490206a803035038a00068484d045620302d002058810108981d40c90000300306810010f003440c01202c1740b40b41e40c0c10b40242 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 603840728 1250 603839478 603839501
    0x301020d090606080756120604200d0902090c090a0803130b0d110304060b0f2b02190905011d0103031704080f04080303010801140f040f0f080d 63
    0x201d154660380c4424083c0410720020045140701c2c15072031040d480c441d0040390b80c24083e14100c6448400728a4000d81a0441354104e032851450002c46d40e030b075035114001f0140d41e10800c20342c3c080c8003028000c04130a00c03880403030803444151503000c82c022400070b4856002131240c640003002c24549081c91009805158414040d040c0201070907203010515260000072116071151404202c40094500020400250002a51406076a483e0980c81404864840207540194054540040c84c0600841045061000c403450640544500038880030000c640e407099108603003124040e40b1540c0303203d10028960990788415040340150a49001c100205260302040c1030b26007000d495642240c85d200c58005e0130009100040000d01c000080601c101e880002481d0028400c031200d03401c04039400d030405184d80154105a03020703440071004000d040d209010b2610000945202c480140c18030940810f07041d40e0080002e04030210340306060341040030800390022465004031040340c49032095200301d0081d000226a5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 603841978 1250 603840728 603840733
    0x14070b0403110105130324020a08060307140d0b0402060c010504030507050c030604210e0a0927110d14010903082401021011091203070224090f0301020d09060608 71
    0x442e041940110121001011005e04546440c0e10315900c01102d000a0301c0b1180129042d140c07491801d20031400601080b6955444a00321441c01c80103040c0b0b85a6142c0c0014180084000c41d659961940300e250025240c00c4aa407080c180d889001082c800e101c2c1492050b0598a440104001d0643c488040c00881388240152065a8a42e100301507484d5010b4601402600300d1358a103840490900008040142507410307c2c6081114140000e00c04586980c0550600c90300c03030446000c0041c19449050b00d00800c00490b50422210391540403a50490f020007900904042c0e540b40300703100d00750f03540c20703200f00c14907009000404081c030700203003025401e440700351407401d070030400032544800300f0103130041d8010603401008421400014000076118400341d940510104000300350b4162034014450f54402c40110056580d400d4a01c14002c403948000d0442400824000600545002c0304d0100d0344095811990b2210a1607024006402885800080501c640c500b150f11070821001750080e00850b201c1005 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 603843228 1250 603841978 603842003
    0x9030301170d050a0f031508030904110c030d02090604092d0c0206061e030a0501090c06050403120e1503040c030c06050c07170718050f010501030e06070c14070b0403 73
    0x5500307955a0000002c200403900c04e100241110380301d03c3c0c13810504000c80c40c01240102200d0f00d10004601590000c5101e0380000800c444941040d0050504803080070b1180340c50140c22801054681c0103410120b41282c0d00041c0e180e0786aa500401d6902409405000704400f940100c544641031480c45560780001405400805000c01c40781b05440480090b41c0240c9aa991501c2c100405203409003841b070004140d02400007415103040000602e078501c2400001800c090381d04001511032400d40c42070082200401061000402c490785a1054000d1810004800c0300002c2c0001c2002015641e1000c2c2d500b404001c100520400c3c001031401c89014074003140071a600c8141c00c8600d0f00c14591002c4859205000400c0001d144074220440c2900c1e803003c0d1060145c85103044c4400c8029420b44928083e110002e2041051300c02a010340103000c00d0804001560341e0156154550b840103100b0300510a040c000304060052002c40b0030750000031a02541c240c80d4544250050703940080c0000d40b142d40d84d400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 603844478 1250 603843228 603843269
    0x304050714010522080703050c1801050604030b1005040e0c0a0609120f0501020903060f010915031a0702120406020a060b04090c1a0d2d060b090114090909030301 71
    0x200d40560800680d24140b80c640c2400305907800015004c4c485540c0c4030b8194001440c10030502c11a0080d500c10300192040310460703130401040c1449040c00701400c081000040286d6590001103404072030340200b010308150380300a01010002d01a0380043e40060500c004002d2086020805140c565021285010050340f9401c01312015045070048440c180c6c0080f02c3c2002084082030300d85d541d140714400141c0342601d80000b2a0405200b03980081c0ca0351840d80c01800240840d0046c80c01c01442c10920032451442c5444581c26106609a03011820504a001c170360031500c20310111404400c03141100e43d849543d00d00081d036420403940d098550924000d14903040d45054018840081e402100303c03101103042c01d044565145100070843d500b00420464030784818070b10b00420303829400c80d9100c000818615201c1d07203140c22a00d048642c1c4a0b15141d01848560b6625041d551400002c0c42d002241c0c12420fa40c14200307201e0155016841105a010803203600000070040d41600c461080349140b800006 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 603845728 1250 603844478 603844499
    0xd0b010e1503100b03030408160305100c17090c032d0c1e13060f05510403080301080706021204120804031b0503060c131202041b0503040507 62
    0x1034101c0707606401c81500000041110341050180c24002030a580c90107a60700001450056a071001701e100c040380c00800c10034002c05002d00208421a20b0707041c8411030070010024803100302d0300100403500c0c0001c0080b40084800300041498804081d0449080f420100c0d40c9101843c0030742c040c038804520744151940f4a41d030201c1d4900e41c00070042c0102d440442c0068100c0020340c16039034110303000101a880b44481c070a09015000042008005000c101400d0070300744001420003a00510842408a055140e909034003480072855074040202c0c9801c01c0410200000d8071251107180040103070001c0b9012050069150065040b9411241140c10507640c4070f501f80c0e25000b0f0a00f403049502814002001500000954514124030030803030070746403980329540c00f40e0803908001c2d802800e1140103410f001506042180036086403203c0e03800d504207050312107420f0100d095401020407000440d4020811512290070a0101121198141039042030b000401000743d0000c803001d07221445200000038020089 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 603846978 1250 603845728 603845761
    0x60b0301230702030c030304030c060c030c0507020d031b060204090606080106050a03020c0106031a090c040204180f091a1515030601030c0c12050a03050105030f2104050d0b010e 78
    0x4910403103003910303008880d564001c014165002e600007000b1015a42c8424001540b04a200c1c0c2c43d8400310311420304101c0b04031441424100b0601d03140c84483c0c03042c150000140c3e1036a641c11a0041400d22007450101e4182c54200040c80c062000340d8141c00402c0142d0f0082d01c20307158800e10030800c4540c1e5410440d0340032002c2c0b0403200491000c2001050441c4203030014200f030b55412002042e425926074603110359940001d017032040000300300e09000c80c4010920618001c6481101c0660820742401c03d0b200b00c0702042034541c000030780e580300e5013800d03941c03a60000301100381c0101d207035080c7d030540d4800a070511808540c1403c2c0420f40214080151900356009440d129070030810505680e24140154018050000c4410520078901d204800050707203503042d07103002e0440d40d44464888500c010050260b54040e08220710a8000c050502c035840030001d16101d194206600c1311b501da6503c604242d0301d034071680c0c0040390000c7d4031042c40c0003072015032440a4100c48030024504002da49560101700500e01 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 603848228 1250 603846978 603847001
    0x5072111090105210c0403060b0d0818041512020a081f0908120a0b0a06050403020f150403300f17070210050a0b03070509010b090d0609050f010504060b0301 69
    0x20522019459500c1007014100e00d200141c04c1c164440d5280c41403107041c00003101d5690a08400080c18000c011090103045100d02c000d6400948030407141d55624214010548035400d0081b0245011210b541c59410001a044580e400440c0c003035100c1c0380b002d40401d07401c80c09034091804000700241d09400044c5601810701003e0b02001a107429540780d5000c2c0c0b6402605540d0f044083c45950007460810030440d001c0c0000c2e81001030601150340601200c00060390003102404818001040540c4440c41003c0b44500c0456920002281c0650703100400d0085410191490340c0c08030402c2625892400742024043c0c400e40448034140c0000c604580100c110000000020110700f1907965044408030341a8002550380161a900c00030070041d01d084820485059215a8a07881c1c100200c0c2010f00c8098044d0038150b07880109581840d201004500c1403104590080001031821000d016695228582d41d50b40541a81c01100000350003501030201500c00340c41c55440c0042001041c41c0502c10001c2c40344 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 603849478 1250 603848228 603848261
    0xf130815010b070309230915060d0b011b08040305010b04020c030d0b15070b011e080d0c1509060b0111070f0e0a0b03071701050a0606140913050721 65
    0xe00b8140b454041d6004a04100e050220290001c202180c0c1241d0820a480c041d48521000d5007100c020440c80420150130050400f81034085d19a0340d407950021149952082d40d004218401984012594080e0740b16050504000c0301d002c92040060702001407003100d0141c002408442050340801c4101c0c4551900b0550340c0d802007050f800c406945411810748210001c004280c00801c0500c0500b4640c044041101c142004100500490345a145504100d0b1b40307040c0c0702c1c10b206081003030190b61000350312030040c18455481c01e400704120081c40754a40c2200f4080050126401360310742035001e8041142c000340802da690905101540c4005600411108291a02d01e249490124004000e08010b00a4130340d03503440707a44034207445d02d0810401c00208400034461034140c030342e00a06400c4071005400340742c81c7c40c2805d60421005074010328074211409604a501d80c3c070402007000034415280e9000c0340c00040c2c00c0008000c2071039081180300320b0502003000300c0200c42c602c5d070f111001100c60016024120a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 603850728 1250 603849478 603849481
    0x131704050d0210091701020703091203051e09180114041e0b130207050a0b0708271507120b03060f04110a03140102092d060a03110f130815 61
    0x145040f0090b0700582c222410b1808900703886880f09503070f0500100064029a4001074040c1c20140d0000015005154200c00040e55103865078009001c0d00c9038070500c1d1035203110450002008101c00080f12511074006000341d5a0b00010101c200c000d80c000d11403215000a56158808642040e0007080f0403e400d004401c080a48900d09100c010030400451503044451141c07904075500e03e0380700030000a40110000d2400071180d06d010311606200a1541c0c0800c940076040c444a109240c0408071031448030700000c4610040c000c0b90519180080e2a40c2c0c5410000c0301c03d10140d01c1e003210031405102807040050141000c9441850b0b03852505541d10410080c1100019011500403500207140c0c4d00c1c02011003022964940b910002c90001c1e558480b4180d40c00144d900c1d1074901480074180e40c20f0b20031410006070445600c00d01e07000c50452015030041c1c1000a29100840c441d80c80071021482000c1825181d55075940600260b411240000f01d2080030468040b0b1400b50001d4648403032040b003680d44545 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 603851978 1250 603850728 603850733
    0x50d030c0f20160f03060c14030606030a110307030501080709020708040e060406180203100f1203080429090105180604030c060b09010e0f0c03150108061503131704050d 74
    0x280b12070b28128000c018000c54075018502691004120032000464528214180f450484201000800a0000c0003140000020b00c4a0940780d000004840c980d03240d645125550001d421030b0301120500c0d58000081040303441e0582d00c100c1c140c074210400c441c0c00584500800703080f4800d03460090503544003440100804840a8100340d8050005000412410356a6040170001e403202c0c8031f400c40c00d9030084200b082c02c488000300b5400401c0d402c1c41c031024161a000d00b03030008880000000c1d04100c192000102440031440c0070614000714084000d21140300348106121500341a0b82030b000550a0801045030094100c1c2c600b005903484001400854450780d8051351100c0604034100d0b801600d40210314800c0d99580041802020580304046051404000721002c03910020b1040010f05024014080c0008003851000b00c0404207081030146519403e000a0040410380a407070783c885400401c1103810302c41100544000e034460410f400c482407180010006078000c1e8001c13250802400d803020f402 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 603853228 1250 603851978 603852017
    0x6060702040b12120406030c0513060302071407080a02090901091112160b18030f030d09080910050a2c01120f050117071e0302040e0316050d030c0f 65
    0xc602c0010060078221070410b0b001c0e82009804040c2214000000c181002050b805015a6006800600e40a407408180144ca0300c0c0891f10350150204059000c10000b04020180c200303182d01913000b608071403a096483c0c202956401c4c280720200c0c0120b540300080f402d0b81c101406404040c643c000c04000308035030044140081d800b043c141003609403085888500208400c1080039003d041d52044036a640c1440303682e0b0500130444940058000c0d484140500178405010080e600514081100810021083e0403d80380700e004408455521011107040090400d4102c0020116000e19494030ba00c908102c0d40543c0441820541c4180d442c080c1500855881d0f201e075a141d20102d003400e0703001840804c1d0f060040d04540090f001411148100e6a0446035580f040004500820541518003440001110490402800b511000340110b8030b4446a10b0341d0b80007407090311008a081c01c01c180000380a418426940c900c041d1000000c02d24110380348074014801c81404451074450f80b1095045140d217041a01c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 603854478 1250 603853228 603853241
    0x2010507050a0c0303020c122116053004080c010f0306090507080612010b01020c10032003010e0606032401020c06040915121a09030f300606070204 65
    0x1150360042c070701c00b00000345007036940e0006507000e03034003c0c95402a48814002154090302e05100c4542c404102616204034442e030b111820000c2001c03440d21540e0043d80000248902030008040f40501020003054903010b036104030101517403007940400141001c84a62041c41280070b000103a4000c0300a052503175001c0c1541c01c1d5100014a4006015a4bc0706c0d010000c40c2c4c000e5400000182041040c01107070300c0c00301d03000703140b031003101e402000070301034000020759988510307145503010300110a00c82c2401406544210101100043c1d1240808081d0200c5e01c1c0a500074080c00808400b4600410403c3c200f02083e43d03ca030004540d08080100d810201c50f00c2c1200d021f4030395045104000700c0c4d80c1c9a4580401400041c0256440820444188080710180b0545500650019000e00104c1340c041204400b00070b00855000d103540344c0c00e44440d16118150300c1441290b16a03810006035001d00304200e440d1385443e00c407040026041100280c101604105000c0e2801c55100d401400307640301500d0a80e1018 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 603855728 1250 603854478 603854483
    0x80406031a0a03050d030f020c07050d02060d051003031101182a14010912121103040e041a060406050105041406041e150507050a1e1401060f140d02010507 68
    0x1541800209000504100e0350f500111404c1c1c100115040140e5014000c203480c0b899401005d5050a0b42080030030b5403002103110751403150f01150700c06030030354071428112460204060310030302461a2086103403400f2851072000b100003c08508880000354018840d1207000c50030040300c5040c58545450703641002c450a50a1002c08040c0011402d02c0c541482404e4024401d10a48844c01550174002400d030b85160382c82800001407404040f4002111880002441601810400400d407028000d580c0345000d0741d0440406003031003505200c00c0c0006104050b01100c0b003000c004125a40799006d01050311202d22030b041c04100c06200c103100c0030510100107032a0030700240806052075982d440e00205806810400d400d0242648001c0c00f00d1161040c020706e4401c03550a0a51400750956506030792810020b6019104415210f00c50324110190301040c100c054000544010140d01c80707011074000c00072486443c45418022034000b071280c9110281d007030b5000d00100030007003612160b001540c45a200d10000c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 603856978 1250 603855728 603855761
    0x603060f12240b1f1403010b030103020603041b0b0702040c0e01120b01020c030a0b06150307080705030a0b0d03090e06010f090b0706060506070c2c04200a3008040603 73
    0x10032180d03c84e854600031804484001141d032108210707000e0700c0320001c084a2070490604100600c464400c0c0b500b12411254140d8800750790f5a26410700c004070a041a4408c4403011350440c2c0007980b0700d440801f414982d4000c41e010055480701c508165039200c0c4481c0020f0110f00099280d03c208401ca520400071410180195001da4a1010009003020841107003264201040d5040c44090309214104641546c400d181c00f40c030b503060584004d000c01c0c038010409010001d00100080e401c50045d00080e1005402034100083c2c81c07064580680703089100c3c003c10302040c555400050705980708001e607810644080d00c07100c0d03030a030030402540ac00b980460000d42d0200e403207903800075050315004003c04850b8010041350407028100359000580c0c41300f100c40000602e500aa441660381614640c003038200f54010400f003446101c04054441c0603130104207041d404040ea0300005080d100081c0303100aa111600041d00c1c900008c212050008101001c019010b100240300c10b00c90240281d00c5405100d004401 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 603858228 1250 603856978 603856991
    0xe060411030708010e03030901140f151809030a080a150b0304081615140f061314100504060e07051b0f030d0b01081305061513060603060f1224 63
    0x2540c4e003902d894204451103079100004110103182c3c20300c60580520241c0d1480c03000d0707040440c915010408050401c41c0110f0903001c02160340d0b0b903500c11141d10409030280741081c134a0104030702a240d40000d54500045107048001070f00c2c1c05c1161068540e0400607038000081e030ad0400d01009066040100102c40c0f581040006111205107801144031192107080c140700403035900e03802c0a040e80d03402e80341404000d07141400d1088034034250454a41c003580503514a5908110a900c00d8050255004018245107031041801552100018060183c2d1410303a8140041c135074a1180314246401282c030360300000c0050250311960480f100c1c10b500030b07007040c1d411a0b5038881c0030f8140d14107580c0b100c9840c4070620780c0c0320700c051120350b040600190301030083d0141814840468469a8070390703400030704039241c5207180083d80286960300b03060780c0b561011052041100d240c43e8000500201080d0040b8007244d07110090000d1868140d0301c00001c500e5000b8141242e4100c12001c40c0001c255541c80443c2140c0c5541 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 603859478 1250 603858228 603858239
    0x90f1415011701240309230f030304050d0e21060f0702010e07090f091e06180309031e080304050d08100609050603070c08030106030b10030e0604110307 67
    0x64816024290003a022115050014005410400c0410701c10036018072280040011903440081c1e00304028008004a0407614110421030040440110080c01c000403940454032402180311008424013070030040b240004600c000c5941d40c2c4c0401c54001f00241c1c40302c6c4500b100584a592492012540070b461300c82010320b940113110000f8140c46032400160302803801c104c034419031201034517000080350000f0017404e014401c49540320052030050000030303034840e0107140219003958402e0300102c0c0c102e4198151410650003003194800e59080c15034683d414581540b001c0c1800042c16846036502d9120b2034040c0d0300d1555460040d100e1640b41101c0c00102550f42d6002c03d0044004610031440b0314080c0c0603040c0103041c054401c80015061145d404804c0700c050000c0313504500c01905403003045601c6501d82d41c41440c21642c4d0341d0350082c024454100403000050300303a0150030807008510216845a07081302c500c02c00720200c400d00042c40d0020f1780618081800304a13419840d0481a0f005816150025180c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 603860728 1250 603859478 603859511
    0x20f0d020f040b0c060f0a1b2118050706080c07140c060309030909010b0a0918090c03051612080703030506030a0507150801230603151009031e0b01090f 67
    0x9084441c050307003181041008042ca00140706607c54004103080149102e440348880e01ca109010f00e80e1300707100540710001a12000b18080158201c03907a00180100d1086001400c0c200b811804100c03400d01c641140070448600030450305204100b000255424800c05031112030316900004900b140c1341c01100c580c043e9030340340c240043d0b1082d52034400440c2d03100d8901c0c061041e01c100590280004c1070051000703d0269900c01403500c126161072041608820a1048440c01000700400080c040b01300c4840c000204070300850704401c0c01003a0a04000ca00d07541e84150015210f00074402080354504014441c0020f01941c0090303044803010342250010409652983c0c80c02c512a0407103400d0701d0311a00c501444079403040304a405441c0782c043d80800100100c41900c51035042d0703072a80e480358170302000152144400383e01e0310b17082020091002c00070f26614940a0400d0056010540300a643c2a015070035010003000b2107145154842d01c00d11191b841d20100a00800c800003d00b2a21600c0c0e444000340409403 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 603861978 1250 603860728 603860737
    0x60706020d110301050f0d02131a0d121107150c1509060f1a0603040b220305030709051009090f110414030d02190f02060c010203130c0603020f0d020f040b 68
    0x10602003e40c3ca5041c80208411102c00c0c425540c0f040e506203281030010b8564081e19002c00201d20804102d2015031174040c015402d0b41b8425035000000a0459414402c003168032101c141030035211320800e04004032109454002074055001e1144940803884441d603c590b00082a83e80580d00720b0f024080310500700e0056440d141021f449140c1c4408511080c414144a1020803403a0b0b0800140b10701c140e000801d00c00d010040014018500110001c0d40704003800b150820102d4440540c40840d012034540070b0400c1e081a51410005142008042a40e007004000c254689a545c1c0342d86183c00e28020104015021003c200c81c00340b500c840c00040d070118100043c001401074841c02c4840d0a82260516251107001c0b10300b00c0c119030043e100342e04004035600368a409582c1140001404001c00c0c00460a51312903842490f201e50b10000c10403002c0c12600c4161003946218a05216005070754160440030707030250f00b41101c0c8410701040a001203620940c014001d900b0450030b02810300e90b0b1108200e444d42c01 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 603863228 1250 603861978 603862001
    0x1503090302070f1406030702030702090408030108070b03062101060b0705010e010f02120703090219090509060906090c060315040623100e010f020f010e2409030702060706020d 77
    0x12120061020580c0500205000c0c0449407030500b0564500703030310b114a1991070400540905c00000115a0151092049400c041c2d00a05500d40070b040501d0203205c40d41c8248504c2885000301c80c1c021900c08001411a4010f400080000c0345101d91110700c40413200d051010341c10590340c0c5c2d940006407485008043d2490a000f080005403602c044100d903800e40d01481840016544100714054450301c103100b00c00d820410a180015103e403440c400318101c40010140c0106907040100d00081010141d001284140c4000069071070390b0f211034154035902c0d001602d6082c111f81010002c140d040c02c0c108007459119417804e01c20000050024082812208a034000201c1d00d43c100c5841d0341009800062520400000e941045407880d4901e001410098000351280c10001601c0b0040d40303447c400c03c00c00e0540c0d201000208110350031041c602e507a032500c83e9142c91410000422a403140c1c0c80c03403e007091140c0700000c061803501d0340960030003a03c0c0d80071080450340c0039800e0060b48031141a40c8584d040c1d912 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 603864478 1250 603863228 603863231
    0xc1437090503010b22060914010617160c150c0203040501091202030a0b0430120204050a0303050309070f06020105010317070f080315040f050406182a1503 68
    0x16440000100030324080c0d000316010360304110742110745895007428400640031118222804001402400c009002d260348032030880d600346190101ca9070750056889040321419198074a000d0b07003201d994014000210b42d280030381c11902041d0340c1315900a44014001c5d0340700d101078030881800094060101d401c0d03040c580d130041c0c1c070124080c04035580002d0040040e10611200c9a501074031a80020b80d200001d020050082400802007003c0102c43c8458078102100550107148440c807404050780383c94501c0c0000000211407240c0c6003ea06800d208940954001406062100d411511300399030380d40c000742c05a6124418000c1c00110602c0c42c1540c00003903d0705038008a41545941171100d080c103004c0110503100c15042002100141e01c03907008201c850750254410792650fa079454503e20150080d00d00d680c209003403140c0c1a24000040e4407851083d03101d041b082002c0d1039070380060042c29400c03500061019012104041e20302107002c0400449450b0701050400c441e032030744441000381c000508200c0109 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 603865728 1250 603864478 603864577
    0xc04080a06051e04200418030e03011d0604120c0503030f01051f0203090f031c030b0a080a0512030406150b09010f05090f0105070609021c0b0702010c14 67
    0x4282c1d0000080a14070580348514181040d4032410001408000703100100e03520000d440c10540c40d03d1f00141e0741411882d2210172103882d2802c003c1d0620304040c602034803d500e80140c1d400701412604883c004078050302700409050f521075a5110140c4411416202405891804c410000300c2c20002940b049842c20215100307545000184100034181d19a0001c2083c0c2e1503900521542e400815226512402c0303980002411000c004207040c03105088461044c032209041c1840c0c8a50541c1101ca2101c84c00c0e100800c030781c0d943daa44292100c0160900400310b402c5039000380307036851500c2c000d160080d019000c0080d900601d011803c5921070389500001c81d400d0041000e0b6150f40c0c114240794a104034034101145000c220100081e40c00d14028001c6042c8480815080c0c14040c0c541d00021406034050410030740004604603c111640410104a1f090725018001521184c07060058102c0f000484d210300c0d09500f038668220010f900310151280d11503030030001301c80c0302d1055440c410042c25480b030390281d0300 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 603866978 1250 603865728 603865741
    0xd080d020313120804151d06090d08090a02010c0f060f060e01090510050f0105130308041217040e01050618090403030506040f060302100c08040909051c020c0906090c04080a0605 78
    0x500f60074901e140e0a01410004120105944030130300c140c01e0340c0c1800b000400045140407141c81141800c0130741250700ca250100100e1000001d100d20500e24580c80d142099030311000001c0e9100494100240024008209175000402d8400903242a5100311008101d81c814180100c04030341c03596002074110f4000758010014200c06119540d0010214482e10720f1442c05c140100395030840c5040c540d0704000f00000c900a40300d001600280c05503501204003590382d551500002c080d101c071040c0075160603500c6001c0c4000f0010b4035088500b02e0b04402450301d040d81c60103040100e9a00301c594200f2400039202c0d002c6000382d440c0482640720781c1c40f07510000ac05050081c28441108c141d4070384415007914004040c005070b6101111190050090300d810140381d0305520b0800e07503a004075402860b920341001846070402001013095400341c240d0306100088488202822a038510120841039040208030000c5182803c102011613804140d9489030b514040e542c204051420194000a450b41a81d810070301a0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 603868228 1250 603866978 603866993
    0x51c090b010f061106040b060d050f0a121713111c0303060503120415050c1903140909060f2412060a150e04090c0915060305090703020d080d020313 65
    0xb500d42803400c40e1204c00100022503407064040c0015002403e084002541944c402d0081258280e122003610309002543e441a9501d60180b102140e074400c600e2034070341c100b41c0319045286003d00c0031113100340d0944075090004504991582c0a4800c1c0803180c1c2c0040c85a10340f00028020120f0310040c100000710349050044c111140c03604074911035041001010700e81c011600c00e9500342c0d08a811501e41788443c960064416206410750510f0320301540391000400c01c1410b030814415400383d00d541e40694203500c00e5071100d00c90040b00381e5008169002003005400c4c0080ca00052090207029070100c0048100003e80755600d00300318030707801040011005500999280701c0b60b0030003c20b4400740074039424980308000300c03120042c20f80d0800c0a040c08060741d5942d01e4100800c640d400c66400380f881a143d002c480040c003065241948075031a4201c0020f401c91188c455613100d0710350700000d8030b00507080d5401c00070099404081a24403400c13301012280c041148011401051490400c0101d82e41901e0310b080c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 603869478 1250 603868228 603868259
    0x1020040b0d0b3304090e0607110105010f170f1b18070207050d060209040204031103061b031303021f0902100e010e061606050c0a0306080616051c090b01 67
    0x18080c400c3c0140300f41c00c1c04611484100e626400020940880901c42060f40c09800b4903405004111b081011003144d42c10302080c5640140426529030703c404407065441d6007030314820301c0303481c2250303401031740030032035103181e0806c1c8d107140c04000e0180c41020100d40c1c2c115241a803401c140c0341020000407140380e400c0c605241640e803200c0b4420010070203460b0a04c4003940751142403040d6030080344948a0f02041041590403107980c903400400c1152559104d080400e010f00c88418003038000d2040c000491180410004d4035410b240000c0801c0307103940d892448030341c01d0050101044065220318625112403d2044100b45010103030300d40d00046c0070080b40100401d410140a9040c14407100440300d51180c0d900500f0501002030568003180d880040300340b0f9000380e015100e80981403074a0802400302d102c18050060001c09071650302448415180d01000361907281c1510079240c035120850080e0b1a0134024030140840c9003034411032201c2c00114a81d240181c1e0713888201140c007840010300611008a4040112 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 603870728 1250 603869478 603869501
    0x1c0b0a061d010809070501030903120f050703060506070c060e01020c120303070201240501051b1609050c1c0b1f02031309050c0d27050601180507021020040b0d 70
    0x1e041c6414402803130342c0c96003118014141050b4403407001c0c030103141c0608900b1408017003c220030020507800624920017004190b035010300007800d1071400543ca140078402c0c2c40c030543d080401c0e140a503103040c030161060340c080e0303e049040d400b848840d56155600c1e40e00b41030300d4100c0b240185580c0e142c8110000e0071074041141c0e031040d284034074402c2c55124113140d04d8001941c40a0a00703542c1d034514118540141954034504038918464640d020301c0c208a410241000c075071840c441030102d51100030f01001140070740340e000c0e070107130343c01d0301c0c41c014002c0458009008100024007007085907518206484c00c0750070030441c9040581c3c0000340040c08101207110820040072158410402c03803c10b07107041a0780744210105282c106483d118401102848403a04c4622015403008a180c45005e516009071250b000b445031400c415540c00d800c480401060003100c0c843c5c11150301600c14140f04500303841c010800c1d410180c0309150502400031090a9520040018114100c0d5150325111103000e0082920b901800b42c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 603871978 1250 603870728 603870737
    0x10201050f010608070c0804180c03180b040c030c0320031902060c10020a03060810060b121302060d0b09181b0301020906070323030c1c0b0a061d01 65
    0x10031100580541d80203040d2400d0345001800d40e210320740d040300e5821a0420180c100c203000200010b8949101300128201c0d80840c5040c0078102e00d50130143e0485030000c40344045620f520803404005221240b0f80d42d405031181c034076042030355100d4940903144001034000725080b40c2c000c001c03000304407514441e141d02da410072001040001225104405420f0030341c00c0003401100082441420350805020036130441010500031900c40412220007800303030110348139010085c01250504103000d0407a028000584450142040c41c080520074070f0800040c0c020050b80300b8040c000001001a030f40d210051100c030042da600400c86603460010003400c3c640140c1588560380305e4020b1400c4000303000c50000b944031220404110341660707000202e030180c45402e806550128002801d2010182c100aa0500140717611590075a1807070f1003a11611a4401a00c3d03144140c8000e11400040c0110721154403460143d00e480424010301ba80042001c00510780c005001044108800b05c81060a41e29101440102480d1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 603873228 1250 603871978 603871981
    0x20c01110d0f030207050c040e0705040c140403030f090803030103030801050a080a051c17010f09150b0904050a0b130507030e010b090412110d081603142802040306020405030c01020105 81
    0x39000c2d110b0300314403a050640110341642881410322111a500390080e105000050007880d0309a107c03051401260b208900e0182d480b00014411200c81b0102c100ca402d005160505640781a04c02058041d850740030028107410203e0041c0090001e580291b1003a01e031080a54184020421803150310703085460580d10250821010030400500e02c02200c94151008400c991062400c0707654030a19410649954402d800015813003407141c103600c1c1129002a800c05c108a4080c013200080c400381c1c801c00030131004c1480301c00400d24007580704a420400240300010500d290074040366014007d80704900809546004000038103030140100d07041c68a00900230404198868000f0340d81c04405031015000b0b01d148407108003018040c1c000580e52401c120101c1c1c4000c82510801018080221303030807800c906040020081d0103009005031020200b501c104481d09503100c504032942d0b801001452101602081d4000b14120b0042c4010800356001d280c000d60346c0d038203140605180850045610341168034090 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 603874478 1250 603873228 603873253
    0x4110d0e070b0c0d0c020f0a06110c0102010507050318010f18020901090c090e06131b090b040f0312020a12030e0105010b03100302090c071b080618030d1812020c0111 73
    0x581c04508505400c104c8a1645d860000c15500c29403480c17410b03045050544045100d030380140309450242c40140440301403d0b0305400480c2a07900a68421012135030520220704080c0c8000304001806044070b000040035210318245c030003a541d01c9031080c017040451500002c1941000f00d2640e01606400c0d10510522065a070b0081003101d10348107851000820101080403642c1d00104901010469042445100c10549407401605245010b10002c82c050002c00602621a00144c1d02107400c940090036500c1d10b0741e102c0f40c020701c250302c140c1c204601030b00304d2550014400c1580003000340041d0364000f5405100345200c508540c0181c001006000f000d00c00c004458403000303401e406880c0e058441032102c3c0c6404000c11110f00840c14004c0c46111a0888004901d1202000c0d0044403501003ca810b96150001139110100e5140002c1781c02d500100840b0400c10102c4d0440010214030081501d041100c54070b54510040700c10b0004001a0005031a125481d0782c003c440540e40c030066005002401d4805 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 603875728 1250 603874478 603874483
    0x60507020601290906070b18060c030a0c2f100614060a091a09010906050a0914060915030108010b060f0a080a0204080d02010902040510031a0604110d0e070b0c 70
    0x9407036981031035401d03002c401c0c0340c00024003070341e50300100502180c0e1600c1c0c00c7e01d030401c003518044034545898000300911843c02040041c0c0a8003540d1010070032851505c0c1c9441620250180d08120000e01c50704861950890300c982c4646540410724250041c0c1c459008800c1300d05280003c20110003140c2816003d000b100b01494035005002c10446d91340b682c843d064803090312429915440680500402c030001420f00c20110020910641d0991360003d00a0301c0300320a5402e4046d0b684030301b00040c502c0005100309401c110421051540003080300f030408042000103000790404006811001502100402014000b4041d20b0000d1008032000c03410320304c0c021040407040c0a0b156201781044030714008035100c0c68156040754051310400040c4c88203a55001c82c00303806080005022801a442c2100281e01c015140100c7d0041c0d9a001c0e41ca48401000000d00c1180440d010342481d070b020340c0c0c85168600c51174a06e0300034400b1003007102d000314a0302602c408440c244000e682c480144c0b140304010318000702c0c01c003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 603876978 1250 603875728 603875759
    0x90c05121605190b07140d02030d200d0b03070b0c16050609030607030b0402160609020910050a03080f16050a1104110f033d0f05010804120c051207060507020601 71
    0x110314691748401003406e140b026000240300e0301d01e41d030045001d5400b0456005c00101900c44120405100c814964900c0f420001c00c3d107601030003c0002840b020058404a0300000c1c1e407080300604031241070f034603507000c1c20b441d61081001c90226840404608442d480d1203008000800b02103500390304240008000c00d44038000249004205955a18800d440f0369072641900c6000340c2d2030a1011035450249000c01c0100000d83c2d00b03a2003010807400058608800340c21800c15a000540a908801c1c034507070ba510f1050b003090105000d10b0b803080c0403140040115400c03040320240180c00501031040142412140003580807411805039083c5075214003151014000c494030018840304603a40c0e59550b04011110300160804001c00078a1a4404105c820324103902d90440c2c41d030003070110300c41342d600d510914001c2264401c0c0340c0800c500d500040c01040540300f6a503004015410007090550f00c69960901300000c088404403200c0001c00c02ca4207115041c4a2158044614001800340f07506040440f02030640 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 603878228 1250 603876978 603876989
    0x30e033c0303060d0f050a060903182108250212030c0a0f031803120e03160e060a0905130b0606090d12050f0409020a1806080604090c0512160519 64
    0x14450003034020400c80c0094000c5c03680c0c00c141135845140d13507442d01c2009404821400d03000211600f4207204501c1c00c1c940014115440480f282816150783c10600d20400b10109007521301e50004e02c10b40c5141805078602811000c16842d041c4c20080c0e040c4100442e004961001802c80e500a0008401840d00000d0900d403480e00a105115540740c1342c6804c60304140e900030400c00301e00c0701800001c10001c1054140b420341e2103540312408215882c205141d65141d801241a00003664803030300b00b0000c0c01e06550943c10030406440070121903100e010540903a2410340301603c800c46141c0089092080c807529103500500c04460184c60044481e0004040058510700a00640c8081d845403035468050720480704007200c180446030300e0b140e854403154025003003a68941d000c18010074040c208003941201010540e8510f450308041501c0c0c3d402400010316514200310b4220710a1400030900e80d4a041660320080044002840076043e100358401c02d005195224034000c021414451000748405c01a8509850 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 603879478 1250 603878228 603878239
    0x140c07150b1f0305070e0303030c0d1805030415080f0609090f010606090e010b030106170705040902400308071b0807060f080709030f030e033c030306 66
    0x1003030086103100038440d2529031035011903841e851400400001180c075a000c103003074408005640e21241c0c1620b6048076a001c40743c0c1900200b00244007205140c001c0e04000c1c12190000607080c0b009c0b1034a4610403c0c2e00c40598850384045020400324010100074410180d03986049403860812405484501c040070305298418001030000a88070101044490a15502c9c600248a450b41da940701a090520601844d0300310110800041104071a81040780d0480d45240d0711800000224403100b01c0140000e06800e04002d810800081c1d24540d40c00a400300213003070429510900140314400c400f200303040d103070000c0b0401d110207180c01c03035010244004112500a05d200f41c8d42d108504d840a22403440c024110f00742069480049141e032000a408426600c01d61039054030007010031000d5501c0101210038200040f46c01c071381440042c0e00141c41d4041b45e4440d0600700160a0b4400000341050910500c44818606021765542c0e48a20410010021500c0c030038104849551284c101ea01c070300c80100f02d980582c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 603880728 1250 603879478 603879503
    0x60903090d060c181202011e020309150408010501060e0310060e0c13090e0304031b080718020d0608160e04050705092d04020405071d10030b0909030d140c07 69
    0x80c0201c2e414503c0344e0810485200464498402d076042c11000c08050f80090b1120b040305800c40a03c441a602281c0070f6001181000d502c50700300107039804126008228000c0c00d00001030622424007655010304641d461b185c0345413044206062511043c9008240d100e42044002c03c0f6402d081601103400080e60360301540c2d1407040060362403039900d0030b500c0900901d14181a0310b002d0000403000e401900e200d1900000e0350b0340b0340003201e0f0703281449010300085a0065030702040080074642d03401140340c443c00d00160030030b8080c01d2800c040710450f921125250700100c0c0417a060035600c0b02c2c0384001e4450001150224140798403810354585090140500482001c0042903568915002c110101070321a0303240e8004490030004081c6000c81528101e02550134074012910031406a0309100d01c078080c007003034000030044103c00c005441305085016030515035035103011201600e070881384a201c3d511000066665400d141f217404112842e16a43c510303400130718000d0188020380c1400f2180521741003140010f05 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 603881978 1250 603880728 603880751
    0x10303081e040b074103010305030d02030403031b020f070506121602030403150614040b0d0308040206040f030b01051306231309060e0d0806010f201e060903090d06 72
    0x6003620390a11909030189604a0f580c1417603920b0443c14040c10700842c80d400c800e10b426203616035010a0000508542050000c200c64a00076400345500500900e00440d00c061001065000005507008010041e0040441900c13084420801a0001d1000f500c95a2600130b44110104e0728850141c8910908510380700540d034543c1c820810b40d4003440d00f00740502401d01d15854200001c0686204110501810b452036007410310706807149400c2c2c0c8002906030164407290741d5040714102001082280e1102040c400445c841d5840800b140c080c510900406065505210400085640d55200c007102036042500031b000904960000100050080305070511100d1110700040015030b0b00e141204c1000d203841008000e000150f000f101402c114801640d9040783c1c1074400b01d58000045070300300c0c007043d00b468000d00e41502c11134081c1c1d41100c0e40400300e0748507140c402043e410200c888110a100c400c80d6040d0326610001072020035000f0760340400031071400501c40302048102e8514a40034103015510380429aa = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 603883228 1250 603881978 603881987
    0x120c0f0d170406090b0a051204020a090606030905010b0a060915140a0918050601090b0c0309060301080d1d0d0609060b12030d0f0501050f040c120c08010303081e040b07 74
    0x500c603611010700750929a4003040807107550454410b00340000c440b000c000442c0ba44076001c0f104100420b98a95280c8240d174154080009005441241c1103802d03604c001621080074490680905103541c0e001c900840e443c1001401d40761040b03015031142c4105c4e1410030105070014040c1040354051914200d00b51443e100c01d407001a11818600800ca60000f001018154042440020347d0804501041d00030140d4224000311001201e181d8040f603880e00041c06600300e5840900540c1c84100b04603494040013402203803594100ba03000c0c0c1c4403030748051014602141c001c0d032030250f008011881c0041560000002480c1071100c00805040560b842035914140001a000600c45203809040c0c4030f0300300f0304560f105a80b17034006851000d101d0300d0300030300e465051400e0280c54100e0340c00400501c086154181044000e003e21031102c8107120003d403080030802c0003070050840b0714149842e4049158510308000c0c008881c018040c90140c25030f803071100c40184c56414440d4100750040c1f01e0301c0181e07940d03034419207 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 603884478 1250 603883228 603883249
    0xc190b070306171e0a0c14011413180e030c010204030201090b0a0905060318010903120c021f180c03030305060406060e011215081914060c04030314040306020d050411120c0f 76
    0x130310700e004401010803200c815520318070103001c0c05e0b40c0320a0b4003c3c034121a80820701900039100ac880a200c1801c00c01e60000100080200c841c00200103401e00f07810004524503441802c0c0301e06140d401160400035582c0180741c01d0002d10a16000e03a28203c1e00a0006080b90b11a025082c8110804804901c59021403508400101c044200803c2924a2820b010b8402c100340c1c000e6084d007600380303006400c1003071000c503400020a00b030703010741c1701d01c540720745d03403180141415205201c0c401c502200b01d0300118101c18a40070046001c0e40700011141070110620042d1800c5400c50410b2041e0301e0290719460741e000e101c102c03d40c004288000cc1c074205c00b01182004150560142c1b40920403206050300001e50b141c50038061920800328400802d9401100544400080301c81c5400050103000c10008a4040d50308218003110242c07113989010f44035510b043c1203070080c030058182240e84208010030405040700c2402c00c84030032905188000b150802050359040c5481b240f0740035035281051103d60740c031f4140e01030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 603885728 1250 603884478 603884483
    0x6090804090c050d0b0307260a050102031008010606050712030207020a09020a05091e010813060b060d06090f09020603010b0f0f0f0306150c070b0c190b070306171e0a 73
    0xd0240b4076140800420b41d80080700d181000d24a0441c0402d140e1400090700c00441d036048011001010710500d0760080344003480708200035400744d034a840c40001c9081c4000c501c43c4003a81e034000b051341d041c81c01241c01c4851681280b02444400c00c20040400c101c14041c0b98096201e01d80940d03245c10920200c0c440000540c0710840c5140007280711407038184c125025000c0e1420035281d001000100c0046504440341c00c03050f01e0702180480c00031801d00e440c100014180c8500408004c078034000c4038004030b84254081440100c455a480005001c07040751801900c007050103080041c00f4083c082d40000d0524801880713075401740c0000051075089544031400740c4140d0360074440e08540f5541342020240d8031380d1040b0f5000788110b58170083c900001180c2c1040e80d0305c43c40c2040c014480b213030502600c2c05603580049080380080c402e00000d1042240b544030046900f5100700c80c008a1400c050801500b07a51980e007001608101e0700c29600d449880010b12859040d901002e4690074018000e00e5a08110500401 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 603886978 1250 603885728 603885731
    0x3080105122a042004050906010908070609090e030a09061d0402070803090f0d0516060b060c21040602100515060708090109050f090a0b0118033503040609080409 71
    0x481100c448030600707424900b100303403030511142684004c52602a4030510008a600718140130511041c00d0003024194050307010304000041e1078440106a03d4004290311a000103200c0d800284010300c618003446c001c40d402c85000310b00b41090785401a000b4003850051004204441100703904039403011142480d1900040e100719036841c880d042040341c030752003200c258007a032140d9810307002c49480001d54580c466001c0e40e22541882000c0501d015010840903098551944604000d840303982c80000503d1011030a10040038452840c4602001b99032001d00b85280d00c40d0b05200800ca502c0c2c011a2400c004081201c001629540b0118492103580c3c8145c1c2168001d400800c40360104140036008084c401400d0300d0f5030380950346d034400300701d1030760310700c3c5203440e0000c5400c0c006c035080350050f401c170380c0141c20141880b06945612141c030058042c1d42c0d034000c4c1c928000310031850006046e0848803002024500c031103040310b030030201543c41441c8809040100150341d111000000c0c0280d0105540251800000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 603888228 1250 603886978 603887023
    0x170703060902271804030e040b040c03090b0105100e092703120604020a0905120c1306031e0803194205030c010509131d06130308010512 60
    0x32802c0c11601c2100203450400345943c8003c0c141c03400d40d03100760001c1c000c000c1d00f0083d40d9681e0f4045803000c10000c501034115464108801243d66070b402400e1814540382e900065040060030b0403952050103900c002c3c0201c400140800116601c1044415510015140041192036260b14001d1403035107d804004c1e485c0c2c2d98900726a86180100c0200000d01d4a00b420180d60740302c98040004a2151952003c0401d01c0300d9000c01c050b0400d9120f44900d50f0703051090351149080071011414418010070100821a030700c600030700c2000001c58844013144a50004084000c0040d81c0d02c1000d84000340c5130000b0741c25284244a007441990700300e00804001d5000a50420111461035115200b010307824290b508090f81942e249071800d40e600d0422140c0c001c000b0984608940015500d0742e118604d0140c00940788480403a031070380640102d00111b1211240c64000c0b00008426900742607000d4080c0303141c004200480400f10380c1c04003000d41900c904032020340d03505249070006840e120000c1c0185007c0340d8243c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 603889478 1250 603888228 603888247
    0x40314160c0e1008010506060313050a052d070506071b1a0a090e0420060d05150306250f110a060c08061002100902010306030b0408031510170703060902 67
    0x318494021070f10340203030000300740e01c074070900b801e03100d04440710b540041c400d00000c1c0340400c4940c0d03c000c0080c000d0042e1929540caa46906040c071841c0b0045004205054618105034507403964856000d0502c1006401c0641c103120025181e48074403031014001086115a070035010211107a40c5000b0306100c58501c10908000d8191400c03038204580380e2000c036040250000700e4000030030f070b19031140e91b01280c9089038000300c1409000880040c842d182d0008014048140103010522a082c028030019080300c4607424104109407500400600c00051803840d61030a0002401c0000400200040750030403043c0c220450300100c1f0303510700c0c0861000103403082c140424241700c126403102d00580d0b425902c2040d036590301014450099200841d100050b40121581480c103581c5070301000060348149004141c0c0d56803030703c841c0c05100d0305480c02da402540000900c20000080e0141d5040c00b02e042c0c82c4001804d100d10f4014151003d950340341c0040300c40480005076118841e134030120190032080c0045460b83c6800 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 603890728 1250 603889478 603889499
    0x100516062d0b09070c02061204060b06040b0c0106060e180406020904050414070f1a031312120510030b0a0b12071502101a060c03090312090414040314160c 68
    0xc5290a002e16846001314400b0352085998140890300580000d240c8507910503000c04000004000343c0700240d803102800361555a00c001040105107000407142c0358090040f01a0031540d09512120600c440e611200107251544e0342c0c691213080301044400c0781c560b41c905040d00607101700e02030158400c3c0352104100811003c101c2140600410b0003c49150f2a203039031085030144150300030144182c150443c0c440083c01c0d04002940d018020303090000e1082c02550755034000304030000040011841201121005202074072403180c0c410221030f00300842903d1503d43c40c002003400380540f03c030342c0e84070380002d0142d448043c4126181280c4070103d0306015030352103c008142403800c510100501841003640b6280071140200c1c10301c07450f1040a21000010081000001d510034004d03107c240c04284000c4078640ea0500c0a004c0000f000c80c50b003540d9031001c0c0100021120245000c1e50401c14034010b01c0042580002860302c420300c510805a40e907007a21980c006c0d0000c002c00010a03450910318080707a400c000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 603891978 1250 603890728 603890741
    0x14010b0a170c0102060105030309040902040e07060504031e0f06180c09050711030304020f0d030c060f020901031b0c0314121905130b1f09020c01060302100516062d 72
    0x41c0342075031441e14041004a031641c00a1154640c140d2090101d594103141075480a094207100500004046d00d8841c1640c2c24142240c0c09071300480c01c082400c005000c580000e4960080390444811289180d96031030400c0c0340b0303540e00050203040c2d03902c00f515400130030788070354081c15500641ca81040f5a9a00544400703402c080364103500066a2000c4103440000000c01d4034019640140440040e001e020140106c40c3e04070082501001041c02d12100400c11510406050541c1c4130300140c0c0e42d030500300c000740945000d20600e15034001141c0d02c91103000d5201380c1d003014413a41850118a00100d40e8892083c038014810141142c1c0c04140c02d000880c005220806940f810107001402180d80d250316034112041c1c0d2500c0a480071300c002c0d000401e4254003141da41543c15100e101c01f41e405031a0035014040780c0040c2c84000003607559500030310075450f0280030b1203240700b214500b00b468813006900c183c9a9410f8054000d00698030b900c5a00e001d0b40d02c1100c6044a500003c0d1b1000d851620843d03100e001d41103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 603893228 1250 603891978 603892019
    0xa23010e420a090605060f0a1b0b0402150a050a1815080103170301080a060f02070f1421041406070204330b041221020c01080108060f010314010b0a 65
    0x1400d00003d07003191980288021510002e001a0416102c900300302e409074040c2e034088007084040c4841040502d580c0c2c0a401c403460080c125414a464144113000400c031980d4400c8410040500c448085180d001080700e00801c01c910340303440078801a403990030000d40c0d99001078003100fa40700500003001d0361141e002c5049a00130451030126210104000c401c4e403000f8011100e050300000401000b181d10364001500c0407090a00051914605849501c22069141c0007201e1461074645608091002040700f0b0301d84c0c500c251090780428400e004850345070300c03851081c5103200008a207900b030581ea400003034030b007020b03000341040c005d02c012410041c1103821032040038140104191410800c100403100910180c1311280001490035003080da5400c4006207030a01240d854070002d81001d074000c0c80b0700c1804068030030380d0020002c034a4204005003810380140c0001145a201d042001007000c81403100303504490300403202e000d03010805001140503000c1c8110464104070301c84d40004069042e017412051920 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 603894478 1250 603893228 603893239
    0x31106160b070f14070309030209101d091e030d271a0c0408030306060702060c0d020c0414040b01030f150608160501031419020c060a23010e42 63
    0x1c1007504440440c011140046c00003020700605000504000b0140c0390448502c080d2000704503620500c102c1101038843d004500003148006000e00044100080403030b550400070204001d90b20312261981e01e01400403d02000ca445800040401000034480520200c58050018400025080104c2c2c004d00544100706400e10b040005659004d20805031801c0d0703080f22000d07500e50345403141085620307000321209a83c0400100240710401108000740031a0a0a036009415a040131070100030032505811007050035115150304010000d041c3c0d0035840d041d00c2d4892003c81041d030550403c3e03c040c0e8081c9100190741880c10760081641900001c00802084400440c200b52544a80044040d0b5001c102e031038005400340c10200d048500c41d101d615001d44001c010040c209140034941525107142a61035017002a920740460f250007042c14071001040c074ad25901e0f500746515000d010340742080300a040764000c5440c510100c0300c0c540c00100c8420b24050180800d03204002074285660304001c5503e20908c90f0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 603895728 1250 603894478 603894497
    0x6070503131d07020a08030709051009031b0b120703020c03040e151e24040303120b0d0b0114011b21021b0402180a060801081501031106160b070f 64
    0x50b50711905502c62050740d4082c109650141d6940000ca0f0000f400c0e03c014800d0182c0701103060748031420050034803201c9940e0350702c1c0b031450b5080401d880f00e0186807640003101d9580040c0500e4100300c0c01c441444d00e15000001c03650355041d004600034041e01340441c0072070000040001d000d114001045000f500e107525904800f41c416010007011000321840703904145611001c07481a0300e031442d0382c00e49445882c3c03141c0541c1605141c0c50082603201e900200c3c0410740c0c082d01d0000740c10280c411410703602d0060b40c40110350802516401c2d0300c035070144100e8501c4801810900196442044010950303210f0204006040300c0034604118588001905421203015400000c104544000b0725500e507413400c20801c000ca811a201408069071212280385009440300380782c010940c8507000b544d0b004003001e0f44c414107254100395016042654008540c0113040407000107101241c015000694001c4003221080e40d03594181c0c844210140d10b07c0b41c0a0140e8500d03400f000b508982100b07035600764a4490b03565401c0ca = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 603896978 1250 603895728 603895769
    0x140d0203070b161202040b0c210304020603100302030106030f120c0215090a030b090f0f03030403080109051305010507051308012c0304080102070f0c06020303240607050313 76
    0x4a00420001402d06441ca20204140c1480d0400030409240e0038034009442020140e000800e980c0700c1d40c40745c2d41d44440029021041c00c028402800a4103082005130701c80900700022815500000d000640f141c0800000304a4130403d010381e0b1802107a01030001c0c00490303074904003071407544240304007610b1440313003c100110304500c980b01020900e5030040c0010001c2d9050200c00740150001407501e90440140e0710040042403100d01c2203031040325100000d007d08074030384a099003841064522080303a9031040c8240b01c00243c011003042d0540d0f444c4c15001079540e4444541b100304034076a01d00980381d0351805080c004015400001440d02d4510441801450382d03803a52500d08072403c1e030070f0885050f06000f45241a0b00c030b03100400f4110740200703800c13641020388a1b21041c1c2282d00800f8211680700039400604104215402c100008080d140040c6041d85403020001002860341d0000b00c10f800100f030b600c501c04d80d44031030540b44071030f8000741140c3d1a8040c800c14440241c400d4000e1500c20a01c1c0d0705c00005c1c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 603898228 1250 603896978 603896983
    0x2160305010c0e0420030a1e0c0f0c051221040c050a0f050a0e0c070210020304091a031903030e1b03010609020403050d051e0304030f0909020a020c0f15030103140d02 73
    0x180015081c0b01094580c00c51800c0383d1719600301070003040303800342c5821004034041450800603140300301c090000505890202070192450030000d0041003402003000c6940c010900c041805031100d80004540c50396a4030250148208501c0300e20981250200c0310305100a1042c500d00d540240e600903104680300300c0d1103100b45016802240324599100e01100014003030b55290110703ea0300f140700c851300c0c0750500c58981c0c001054610380c81149401a400810100701c41541802000e0540002640d00c4a66071018030109032101d05904502c0404401d90781440c04141c440da00c036081d00c0d00c4d8042903459440c1c41b01e1110080e085c5003440f0501c0381d8286900803a0342c41040c8203c2e000c0326070040090117180d4101505494540241d9041400d48030f003c000c01d030040031060f008510992281c2d440228040300510054141640f9400c51100b05105004042007030381c0001e468030102d041220852150030500c00000d131011080100c0507031080001c40000100088000840c0c600f442c81000d0364604c154030007040b0ba = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 603899478 1250 603898228 603898241
    0x1090e0307030c0615060f02010b010c020d0f260406030e0106152102031801050907030201121d0d09030b0a020310030f0503190210150f0605090102160305010c0e04 72
    0x9055400402800300060b0142541ea480288100d001041c00c3c000c1c400610752a1240c0d5120402090000300810015030b030a1050380740c082c100342001d9030f01d6800e540124071a0100d010f070003064540800f03118024440e1180e84140082c5c004a402c81b580d0300100b1542105402501c90000030904004c40b40020131410f001e82c03416140c000610031040d003440202125004ca004212000c800749080040342c461000e80002c51207190071401380111001008015421500c004040d00042d812100c401d10040c0c5c0d03c030075050483c55484001203040074148000d40380745803003201403038040e00c11f401c81020410b400c00c0c0e180b41140c0c01030260715940c4d6600d105c0c201c1070344000c41e0299107410700000203000080c01c101115040c603008804503814042c5040c01050b03094050900e000c0540c0c40b141a02c107610f1050b0140c100a401c0034041110034601c2c01203030102c482818040c00301442404184800326074820081d4140000441c3c141d40e5010741ea03410a00c1c020300a80503000001580009820080d00307003030203401d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 603900728 1250 603899478 603899501
    0x60e0f0d1101090b0f061302040e0106120e0c0909010f1806060e010e2a3c090409050f060112051204061b0201140d021804090b012d0810050109 63
    0xf80d51744c0d14a1550f4403442e20080c142c2d0b51018243e104c11178512641d10260024140300500300c0c02c0755051410107000c00144e0001880500d045c48150303401c0c00310220384240c861005580360581e40d02c40000d8903000d0075031200380401c420f2809080307240d44481c808503003140c0c0d070148004015980d1140080d00c2082c0e02400360b456180400c0c804500007110390a00c000d074900d4444ea9070511010100c090140d20782c090034020301064280341700200c4086041600220f0121701c0181c0158120301d002c01d0301024040d1803021485640c2d5103030a0010b2100034004900840007017416501a5a1a220314040c100c403451000c0c0c503240300c2c0d08026140104000105d4007662410303100c0e512400340c652142d1004001ca09822410030141d0030708651401041000362000c0c4045800258070380c0507400801005c020b06c40d903014403450030845800040b0364400c40b024103544500110081c5001d400c1168056180c0d400d04c65851a0340b001400030b034203080858000c1d1940914181070000d6644c900003002600e0f040e0008 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 603901978 1250 603900728 603900743
    0x3032306040b0105190806012a110102010204081b030307060908030a0509010c120e070b041d060301050103020105040b0c1c05180d05060c0d0e01021201080607111207060e0f0d110109 80
    0x217001445000d4294580c4c456014941031032070203c0707100b9002151000c0713400345101c0f46110702030388100f00d007030328503800d03144002c2c40214201494511215a10440e810003800c040a160512403403548080c07003200e071210b4018005115000503841c00d601a070b03200300c40f06505140f03031001041046406004a882c503004d00d42c1c5452a110340401180000c0c002c51042031481c1c4650003000424211260103000140030301c040444044d01d042c400030301d42050007440b051280c0d152800600c0141c4e044010388040d19925916140c442c61030006140c40e2500342000703500d011040c40c815030b501d00d82c044002c0507c803040d6042e200d4015124011f1042001c0c8845000307001d81c0204000560360150078001d080c49014521001c110b503032541c481542264021801100c1002c001401401030708400c000168002c031652501180b102444203100391520f610103101844203a000441d0300511038039070402100c11900030196465001d89810643e6034040ba124034002103900e10090382400c04040c4110b09499070405c20 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 603903228 1250 603901978 603902017
    0x8180c061c021303050717010e060408070f08121b0304050a0201030203060a030c090911190b07021305250203160b1b03070e13062103032306040b0105 66
    0x140103040226941d0192035550a0280e250740e0785000c0e260500460044014007600341c01c1c0303010f601081c4140501101c05a06009a00106c41d00009417107500c0b541110300d0f15100c041d2858005588076880301c014140d4200030070001200d00d6510324035805207084081c2c001c0c0014040a003410180000c40e80640241c00c40b18202e00135500980085034003a000078401c89082e5100c1e6104500080c05400c0056025941c0762580100308038160446400300c011130700050170b2000f4201d0300084981500401d0304007000441c44400b151181007090840b895054000d201d6440c2409244008944d4003925403211012580006070300c9002000b100d403040f0760500c01c2c000004098584c0080018080c002c00d010340c0c003c103c1e03c076600491001a601074041666070b80004c08681040110002401040400b0603241c50000c100800a90705407440c0420b1224640c541c811503400c0940003000601c46034540c4004002d00070a814000b094074502c1180c0880701004002304000044400e401000d60140002c4061403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 603904478 1250 603903228 603903247
    0x50a06060c0305092107030516080c060304080a03021201060f090f140603191104092012090a051006090f090b010501141903050114120706110c0301020a08180c06 71
    0x44040d81c0c0c0c0145070050355005c404582c01600c5c0003010351041e01c0340e03044003d00076030741d052070f240000013021000010a006c0c00c2d1100064100e10003d000101141c90005100880350300940665140088010091020b136a40710b80107003050761a221040c0002c2c082c0d02d00441c80707035410070001041d614100d04a08889070400705100e41d0390f2010b4105411000244048080441207002e01106c81001c0c0407800e49607460308007448107072600c2580080354082c8800d0117a1704210900305031030806103221101d1b0070300d0b00d40394000c0382860b941e07030390207441d071b000c4c0c400d0301000c0b40482e402c01011101c4101c400c2012140c240c4082d004c40340100001401404d0200042115621808041107003084034074a4a2400d200500207402d50030340e00064501181d00c1d200100301c104003010f900c005083c07064a04900d110046031420307407101943e0203010f00340b02c966400d40034688010000160031180c060000c660ba5842880013a0228500320744084060718000c00c40f00b244580454901032000f13024250505002581 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 603905728 1250 603904478 603904489
    0x20a18151502210d0209040209030a080909010e131101170c03160309050a1b0b12040309080c01020a1b0902030108150739020d03120f0c09050d020301150801050a06060c030509 77
    0x1003580e000d030b001d09c4082c942c3d40d424002c1800305842100055a115810001d205071018141e101400ea001d03400208520204031941d8002c11562003410040d8000b182c50050390f0800401c01c920040c4400c0304104072804440f0402180100c00c900700d00804510709078800c506698076120028929085505401d00088007201c0d29844100310302e40080c030840e216208201c003030300201000010600804140414180c0210039400a0134180000e403c0002c09400080d56405955000501070010300040941805881d02e5a4000d460002c40541d500d59640209940e20030050340340e0300a502480c40803c4410b13000716224510400794114000c00801e01c0c9101c0500c001001407424100030b18101500300507a200c580307a84c2d032a80310791101c1c81c44c000b0011502c0100d0f0b25011601d441e043c6030501c140b60541d0409040411601c044034801036a146a20200c0d026044d01c1460400b41c10030240d0106d212001034011910804200c04200411a40c0d22030848450308192006400f1030001c002810321070400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 603906978 1250 603905728 603905737
    0x42d09151a04080f01021e03061815060a090302030607080f010e0c07020604120303060e1005061c05070804050d02030a0f0509040e0f0304060e0607020a18151502210d02 74
    0x11000060708180c1c3d5903289500741624000025502e943c0050100c2110325502120103944100040c1d10b800c500c2c004021600688103107210f00080d800c1071000403203c06600302019012003010304810b4a0b11f038000d501410102213400124402d000e4400064201c2d0310034040144038081000c0c51480da42d2910408004000001e050030710407020402c00200580c40d107078001d10003071400100310603c60389036050013400c44400e508000e44c103141c0f03036090184010000b1100ba060b2001203803095900d1003844024240503c1940c00071100c941080c08108540e500980702e2031065008905541090040202c01c985901c0f414009c0c0000c1184001c42c071035070070310401c003a040d1051302400c001078000e80d501c9403d151044424442d81d83d17600c0002c0500c41c00d5070190140700c00c070b83c055440c0390500030a94000f50440e094ac3c0500041c100328103048105061441d0810000c03180d0903481518403545440045c0c0800710340941e00740152280c0102c000310526503080240c1c4a00410008506240b001c0541d100651311 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 603908228 1250 603906978 603907019
    0x702031b15070c03050d091e0501050a1803020a03060c020d05033c041209090b0312070812041101080c03060907050d060b0d0911031f020d02042d0915 66
    0x40083c4044001201001041107842081d114848581e20f054a0030141c540705c01036010044840303520401085c2d8010080c0d9450a820f23083c140401e0759070301d02d403100003000b035480698003c800c1840082841078552169000c240d1540c00d880729050014000e440700d00c0151800700200102116800300c008940c01200c0c0354a102c800c0780782d4040c6003858004038501040e40c090b0b490909825420100f03e0704041000001e00000703106102d02c001304400030342ca40b139440c03110103075980300020078608020a500440300400c040300702982d0a41030504001c1c1c3c1640d02450b0b500e01049540010810102c024001e90344507801c002e00e02a560b80d00c0400480c0c1d80d0708400420020303952a0807010800010310b201070301c01c0c40d07064000040c4a0780e560a100c11140c50381c01420f40641c02c22100c1d11400004098040000c8558107405a03582581d4031808009101d50b9100c0781560540c108000d60b00c0e07807070340c00c81091220144518008203131030b002c2e9081100c2440601140344515080308014801c80801d40304071159 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 603909478 1250 603908228 603908243
    0x2107120f0902030109030f2a12140409060602060109050906270a050609060610090905040c0306020d0c180b0702090915010f170106150e0a1a0702031b1507 68
    0x21503980461300303403115041c04402045115038081b81e0b09500001f030700c0d54528103450081910b81188050068495982130182c0503400c400300d82c101150140401d40c0a4000c01904a55620340e1034030340100601c52130050a0040c000d001c0005101000740c05994029a2448040c06550700c914000c01001455545244162040011024403c0d070050002440c03560151020b02a1468581f0140303090400c0101303003d100305c258088c9000c0565001e4401c0013a19070009002510382c80740e050528680b4000c4d407004003014000180c016820b08180c00000207a0b105460f034075022400b06041c002d82400c04d004815540038140003000c094688142c400c1d410040c1d030070581c0e1504c070160f51801a0100c00345c101180304a0200001c03c050410a40c0b1000340e03082483c000c1007800c0c28030001b0203590941115100401524501226131583e82c00302020040550f98075400c5a41c826106950150f004860144d203e402043e600d02c801075820f021509100c0002072140c1d082e000106103095a9130050302080d191031 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 603910728 1250 603909478 603909491
    0x50703110a050a0215012702280e03010f020c1605060906160b010303031d06010e01060f1e08150603090a06020c030d1a0f0d1104020d18082107120f 65
    0x700d1203001854007907d000380f40c4d041d84551800c85080c100080710fa660083d0b40c070400440c00c1d490361084559860a40110780c3c20822901c0320000c03100300c04591000340e41546042d2040a0881084d401800e03c2e02d450b0094950310460040c0c140c10014051251580003541006000c000349000402406100040d045044890344240c40304c101d000000d0f00100e01203590390031410080148030014100c0003680340000c095941c1040c000c80781308407040c49400180b1080c096200801805602c0d000d440030009810074018170b195000040c028942a5150180c825000040d080c540c244241107074030907800d0340024828000a99220782c025031203d903a080707183c001800301c1ea41041035405283c03001c000e0031151200c2402c1e00420040342c541100d008922a60f0707003c00710400104c00d00c2410000a00490340142c0311a0060319580240c006915001e00140640c00f401e010020140007130449032840702142c5503091b03504418040000f005450b98404070b1a4505800b40124207500245401903103207501003040c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 603911978 1250 603910728 603910753
    0x1704080a06060305060c031905060d020d0b07122714071d010b0301270209100210201b01060306020403030809010e0321040c0e040b0a050703110a050a02 67
    0xd2680e095400c450303a81e100d0000b0018440108201c5401108550025155040c1416050603008502c26041800368071500020101c0d9110218210b81d203030040c1c2185120111441d0203880340701c0c210f5417003010420071408050b100b0b14512900042480203011f900450300d0b03d030f20798250306225000031100d1260320b818120348100148030000090028151900584a0f111140c100c6400160004203116000380010000f0344d1660b44d586007c242400450410002e001a4a60180c8611400a50130982243c5644041c0342d00042070702070b00c440170408000c084440c201024140710012051030780b400042c080044034004003651052a90096000010003aa5980d21842660025482680400c5540007000f185220a00402001404003000345140403e03031389540b131000003400b00c00c000024448002404100c2c4042c1c80d10301a1a43e0910342e90386181616014285c59001c40d550042c50b400c200101d80414000d0150203520804210264103044c000042115581c1040103994110320802608002 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 603913228 1250 603911978 603911983
    0x1d0717032a0105010b091003090221030a020c0607021014070c0605030405160608010b07020f0406080f0f0109020108062709030c0c06040513050903120906010e0115020604170408 78
    0x40c00210303104501c080a15101421140e0503400b4120804c010014442c2c00c1d07a62084a2a6131a41d078180007603e801d050001c141d50320302140c0c1f80c02c0c4c1540031a4841d124184004048c100c0323506582d08803410105080144031803401000381c029000442e250100c02440e000f000840d80f034240101819040814be9140c1c11005000ca80c07205011030800400c0c08180581031141c00e80301040030050000d0300e40307420801005c2010510914080042c040717210401c55903480d0103001d92410062050284507240d0107101c3d15070803400c00584503031048541c200034620060048002040d0140c550260958a131700a00c1070314034045203009840807902a10a084c3c19071031550768098456540216140c0c084205018500442d5080b0307030340f01d84014031017001107039120707024412001301400c004038a07522510402403440c002c104180140742c1c521020030000d981c5c00038038581200c52400155800c0e0b60790300680840c58010194400050304104009404124001c03040c51a51052602661620350b03524485030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 603914478 1250 603913228 603913267
    0x2112230d090b09060403091806080304090213050a0b1602010c0209090d020d0912020402090102012918090a060b031606021506010e0a061803080d090302011d071703 72
    0x119552031030201480203a241c0b60307500102c070a00524850400d41c901a100030b041e80b0900c4890b0340c45d1706800c1e000f03034156000b41c1c0003410a08103ca4403540c440442d80003039005100001915403862000142910b40100c00c84101c940b036003181c03454500c41881048104960401c103905214200ea00040181c981c45551441850b4110141c100d004241c0802401d00460f0013080d810082004020700c07022034040e09445c46154120f400581c1d50a400c40142c0c0500346441d102440b1400990000000f8604507040203040001200c070116003c1d0030905514103200240c441410560003003a0340e80004003a83d0100c0812100201101c2044641c076056901000d8960031050050304000d080c903002c8001c0107d0250060800d08006100c60801d0f40401e0001c100c510490040005200d100c5201400380c144800245800102c44d40d50342c1c0f0020050b00251a69900440040d8600b14161001c0581020009106000180503028051420010b1607101711000a07803141750000304092990183c0c40c48045 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 603915728 1250 603914478 603914497
    0xc1403090307030e040b010f0c051501080601030c05060f040b0c0709050108150a0501030209070807030605041811010c03080c07020109080a0f202d030f0601211223 72
    0x1140e40e110030746401082e113191612110f00031400c05c0542103040e0f82005184004e0304261400c4404d084171418203500d040c280d900c254042c14071180010501035804210b0b41d069034051a03035101d00307956500a02595204403052081d00c1072080c0f005120744e14225000346010204c01c01113504845e01e03040c030401224800c5e80626115070000c250a807118410070121544141582010046076141d50046001030350002d001c08204110318000505d8203001c1d500207000b8103005842001441d20204003c6074140d038424060b00c010480d100094180d61054420a44c281e030f01d03a40d4400283c540c0030b04144c1540000a00328140310301f840c00420b4501d070401501046a02508002c0000c40c545d050042d5030910088120410385100e507000130541e128072034640760400c42c250a0403200150146048183c0d0559080303503178140101644501200c00c001010b5041ea603044007a0700c100ca81c0c00b0a0407449051100c5d00401e02170904ea002e24407076000d00003119008100c10b0700e1200f600318286a0340e0b41c6600c280e03200c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 603916978 1250 603915728 603915733
    0x160e0f0111012405221104080f0a06050c0a091502010e061f0f0b09010f030b100305040308060303040f0519030b04060c080609092a101725030c140309 66
    0x40f02c003001c20303a04140c001304815a49607282110664030b01c00100303420348207200b0700745c1ca41c011500016010f070200c40040400c01e05484011030b91007600f03516014580c4059450900b0035011840c2910010122000ca52580d2035078031609140c840740300b13a40324a0140940c155503841d10114680d8170240011441a447c009000348000c01c1264204007000c0180c010070600c58590500344035010042d01205d034400c2003403c0c1242c0350320306048201c0140ca0340140ba07a0b00302d81c031152340000d09a0941c01450099200780c440c183d45076600802c1c542d41c2d000300e102d02d03211040c03107031001c01041c2030090141c0a01d024031143c480c000d94880e1114101c0c008180c03030840310180e4520310070075801d50200701250404021543c0040d41c2c20103599590f0784114500b0850412a00b003560001b40d0315081e4020202c010700039200104c4d0b060000400341c0705501c1290709445a000d01d1700004d041609041d03400c048100c002c11010741c02c02e40c400c2c1c224001c06500c080d400038015500100c40f4000c141002641c8504d044900 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 603918228 1250 603916978 603917021
    0xd05091002010606050711030a1a060f040c05040306021b0102040f06031107030e131d010c080c04080703080309070b0f0414010e0312070218070201090308160e0f011101 74
    0x40c4848640900310140459242c02014000182c0c070400302c079041a0082c1c004440c10115000007402c01c2e5106000900350280304080d0401e280508403c24820f0404507003862041400006010075219080041400288100414000108aa40a007404141e5901c000000100d842080c40c00c983c8641c100b05961403034042d08020056060144075078030805501042e0410500d03540140c0712071a61007041e442420b0382d002400c0003070082e50001d80c1007010070300c51401034001141905d00070301c81440d42c1c800042c0d000002a00d0741d09440c044030102c6480b1801000c2e640c0c950b403120741d000d40000d0205052070090a40000d8640041005045c0303415003198000c1c1c1e51440c0c540c002c046002000c403102d05200038512440900ea4010440d400402090f80555a1f0b40b0158030001321110700040d8034070502e25056080c409410750541c003040c0000c1c440e0311079110a0312450444100c0c1282c05403408001229604031045900308120400c0e80020181031401000030104589420348081c254100c2141c4610780 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 603919478 1250 603918228 603918247
    0x90904080c071d010b09010201020d05010b04051c080904020a14120a050112110f010210020f0910050f0405220c02060a1506020309061810030203090d08071b03110d05 73
    0x450030060400b00001890f800790b855100e0034a03041480390f044030b00c5012070000e2459000b0f40403560700000483c010801c1c0c1d038444a400400b42c00038010940a0704da00041c1043e614040c0c06800c1c03802d40c10414071410a061801004082d500094480b410007406503045118824044007806050b0100144000c840c40c2c030403038a004444050384046214404865940c0110f07550703154415150ba03003074551185002a110045c1d241811080343c0040c0e0782c2c400a080c03020180204040c0c0050b103c12103205100d40d0701654200d803540562100c0044a000c104170401452030000e4101c0703009104007007505401c21040d01e19804980d1061980f20250b000364003040108403603031143c4414401091440303000305040c00c100a41d01c0c01201c55060041e080091501d0242525064809100d04028061b942207081030707000a020f0b400c141d60700411403080d044400d21250040d50301902c00c90080c0d0707078001908031810015002036640c800540c01d10001c040c000c0a051004e0000c1d090511560312002d070ba4a0500707 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 603920728 1250 603919478 603919483
    0x60f0305071d01030903090803070f021002010603080d0510090504080309060606041818060c0c0b060402070f030503060f040e0c09060a030803010e040302150114010e0904030906050d02090904080c 86
    0x1403229042022280039403122003058082402404400e04c2c0c00281186285804e07281000d56030000c41e018880030070b0340400c001400e800c10b420248281c8281860041d2150309272300323880e400d000040c4010014890f641241d849030b4020f17948221b0301e0320710300c0c00d055070303050490111071007a601694410800000c22011007401c12501da0800e03415175106141902c0c0000c0d0141c1041c42840319410a500d0740c00288a109246c250a141c8941154080203066146070b00540300203800c0c54102c0b0035120040000701c40345040c0c826612401d07000504055640078a070b038200c80e00c0d4002407031117602004c041c94000098449120343c01c1410045401400c02c1007682c0700f0013000307076402040d1030b129a400e0481840001da0810070380c0e0440d26800030300003594035140b90603401c20b60304a07a221406200c000c000140e034510050b002014110030303203620803210041024030031044000c0318040c0100342c00150812080f407141004240c40409600c00504007408400010b5082c0d070700741c800f0b642581012620000007c000d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 603921978 1250 603920728 603920731
    0x10b010806060a030c09150906120501030201050d0f0f1407121a101707030f05070201140f0c0706090606080f190f03050d0c0f0210020c060118060e01060f0305 70
    0x90030804858500080042d9140c45441848002c054881c4440d8501d10300910842d0060031440c00e41000d02114144010310f4058503101300000641d04d114405800303200d07445540d0507203030103960b00c918106054198202410143c2d0480c030903036603950421801184180705105450064010301c3c1514203000344000d01e0840f450041305995450101c1100d142c040d04c00418120309420388558140c2c2c4814903065030382a85600d0750031802d0140380c080061480c3e055214003600000300d54104a5629045001c07401c81c0c01703030031040360040d041802003041070320051a0294812008105180b0b0040543d4a0105840f01a802150141e860b24001d00412401b888405202c1141100404545046001d90b1442d1504a480030705265020015141450711030070455040f42d02900d01445443c021520042003050700310b6590b0018004c403018081075420034003c58140f002020010b00c2c0c0c13a420703d10001e10844c1e5040c0c114802e640d98940000300f00c0c5840740218000c2c1550380340e803240780b02d1070301c4e018058940 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 603923228 1250 603921978 603922001
    0xf010603110a14120a0b0c07060606110607120219030204231806010e0d260f0405040b060405040501030510140709030f030e0307151d0102070b0d060504050403090801 73
    0x181d0b12414400300f0596000e00f0a156000c0329001241d03d4100890360070700c140d4000c086c0030030208004114403400c080c00200b425a07c60300041000542c2c0300c0c021038102e40a1948481c0c01e81101c404245100d01c2034015054910038114010300d0f05d52454034030305500b8255090140885e802040c10403007904c2900507904031200890383e124800d200103002580341c0b6603042042c0c2040e001c0704042030481c1d01c00c0b4040c1643e20b4014080484900003803c0200c2e0300759500414902c010f5509220620042c010fa040c7e690b01b80148030420f04142c00c24007008054556811500d421000c1400b0001e1103942d41e0140b40d0080d0300800c0a00804000301204e0400e48613005a40115034004005120400e94048140c0c401c0325041000c00f8401c10b201d10b01100c250041c1040f00350301d4460000d0104890452082d00c1d449440903844140d0b03004410400a10855804030525002d83c0046100700f1107184802c0040003070f5026040000364250311200001d085520603a42a4001403001c102404480340074407a4404002 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 603924478 1250 603923228 603923239
    0x10b120714040b010519300b01020c010e010c08130f060f031806111c0c18050a030f0822031122110705030d05040309170c040203180f01060311 63
    0xc3c800c4006003135886004d000e60781c0d00480d10132200000d0310680080c603107000500c0c1541049100d282c4440c43c0981780d00d0009011030f21b004900312207517000083d46040c064042c0c40c1c100686084000560782607051358010381700c0010800c0b1042d403411880c07000070050801d400c44000450700742a8010008030b6601080c00a0614080041e001d01c8840700c2c40d50062603000c440880c00d0107050400060300d0040031b010031000b12a01c0007000219420f03401c03031190041c00d9a1546080881d01c03600c660b014820b44619508002298400c3c004200140c84103030b0210b0140c44074900c0c051085100c509104499070b0101400030f520081441002487c00c12440b002c1d10881e814112400c000c08680c01c81c0c0141907104824903038820920207a00b06840c11344602c941c005007543d4035085e90b61200b2024040482301200042d017054008200c002ca8440d80c0c066582c41301c0d000744018089035061200a42c0b014001c0400041c00c0410134500713030300030014082080c00300ca0011628601e5450b0814a0910004200e403040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 603925728 1250 603924478 603924491
    0x71403030405031c020702030129060403020a0510020c06070b0f010509040312200c0601050405010803040602061b040510120c110c13020d020708040e0a0204050904060509010b12071404 81
    0x214000150307081c41364804011668098a411000004d105400000b9010750030f001c4100d409400030b015110800c01c1050200301da0380d480c5002c203c910700c10340c00020f6001044080601c41828825a032054201113070045400203880180003c2003500042030442d025844081000030700b281100c0c0083c01440305666911503401c02d694003814402c0340d08045102d05645c0c0410a0583c034041a0380041c0305240c401803651140c0b980b0415031100803d0203028000c1c0c0c100000000c00ca40f0003c101c404440550b4003401068030b0740380c04100c40342c0c6003210422405906000100302541e03403001c00d405045854031084501110500c0c1d0030251101580342c401402012840c114440d000412109146001221003503400280c00c07611400a0050000b5078000504c045422410080004000d0003900c0c0641e0b0340140b2541c4409462050303116900a00d50440c405501080c0068243d800144c1c002e001e400020418a0310b400c041050b100000c5c90640d103a511166080014080c0040c009107007900c19507090000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 603926978 1250 603925728 603925733
    0x31101140103030c1a010602100506031c14090406120204051501201501090203010611060c07020d080c0d020c040b1c020603370606180e13050f030714030304 69
    0x36500c14400542805008400031040040100003d0402c00b102c0c0c0404a1951b1144002540c8034841b9180540b00c51411020605031300d00091002440402c0c80c202d0403c4007018041251084005404012102010720020007165924020f01001d007006840d41100c0184c07a00422081e00d0700581000c0d10750302d0300318000070640da100460000c3e01c4030581b1055501e00000300402d15000c0c0240b090003084071030800100309807100d0703002941203400a40c0c5000458203c40e00894441034260741c95821140108010300050911422540d0141d010321a121f0900141200c854284054240a00700507001401d254800380b5007841000103624080d9100080300c44d5540102d44562048840640f09150100014000782c03010b0708829200403070b0f000f5410350800204202c40c50184101507080d03080303050450105915104043c0946070b241c00b034659100a911b46201d02030100c40140031210792602901109003c43c1c800c000071070074038084c0b400441c1e07207408600301f04c401860f40c2c0c0c4810049801c10401d1001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 603928228 1250 603926978 603927011
    0x120c02040f050f18030903030403140705121908040b0d0902011d0319050a0c030b041a0c220f030f050d0c050a0b09010924050a0b01050f07110d0f031101 67
    0x2400440424046140082201322624601948000b00d6040c840002c0c04420043d86001013101442040111080706031182e0400440c8100032200d041558881401d030049144620001c000d200d02401c1c2c400c1ca000d460301d044030601e82c0f00c0c03034041c807165841d04240303021540c1c8030954850525410401350300404486000a4131041c61180c44a401a4440044024000148080b010042e0f1103400070b01d10700d640f8070789241c079440200e400380c84d00700c611600075a07000e0003003510034841c02c001d1000c14035240718108800e8101620701407800d404010b80d00b01066445001c80c2001c081c1d80510590580c02d070076441c00c1407405140417411030030401c2a045450003d81d000810354211588007034038000d41c1da075034101e030b83c0149480c0c00c0190800d003c029440450720300c81a10091400003071001070220343d40e00c40d400c900340c3d404500341c41d001442c1040a4082480824094410301d8881c00d54640750000c02e800107583d0114080080c0c49071440100e86008141d04141c55000b0340507401c00910503201054029074 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 603929478 1250 603928228 603928231
    0x30f090115060e0f030a15110301061e120c021b0402070b13061b0c05010c02060405030910050c060a0c12052a0c120c0111121f03120c02040f050f 64
    0x1083c070000c1c400da00e801c1c2da5484240000580045c08507003501142d41080d80740200001c0f1500714051030300501600b040d86000c100c0f41030750350944a00c0d03284114034610380d0048180e144000d04108a100c0180f8090000f0b000d030024402141c0d00401c4101e01014032044502c4c00807107482d00c190310411034000001e43d1111046c0c4d00c5440c580d0340c0c20a40b5028103055000e002d00e028120444041c1c00f050300002c40d0001c4200e10050b006000070009902e80a809a0351120181d03000340090b842400800030a1810450307180745406285091424011000c0c651890101d042c0c0d652900c7c151920700c50408140d11140420000c0400c940170701c4507040c040141103c0040045030401000704000c0f04100542c01c2e90100e5445804180072101e11482c182c40b11281d5420001020085500b040d10119001d1281404c2e100a5900c030107065402e9128184592400148545149940b034480b42000005c104016107450309449a80c903a560b46001a204100031240c0e00d02d5070200b481e02e40014004507012040e243c5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 603930728 1250 603929478 603929489
    0x92003031801110f01140117010c020606060307110703050d140f070f02040216060605030f030a0e1c0803040503030108190f1511071104050a0b130513020a0308030f090115 75
    0x624814406400e020f0502e580068510307419801c241343c282d0b56000d0500c6181c120b030a1481640b1251100390b00f81c6080c0d540046010ac0168082c501240c000d151001c001e46e00b1010b01c0c10b0900030360b007249052604040181e402510340c1c1c0c0101c400d41c6545070b0885901400d112030182d0341854912000c5241045006400015025102001075203045407180d504031355081442111050b0010154a0300c100500014000c1a009008004882c08141400407ea03110031182d520f91000d941c1c0103509000944801d1071034001c0402510186030007142440005501413030007200515500c0d0f051450180c9865089080005000e81e80110040032502c9118002d0000390b012140c50390b010002102c0801a04044120640442001070a1420070100144294010f801034401b1f1204c0d5035420300d820111200c89810f00e810007650381ca001603e280310340c0240d80c0009070381140341c1803c000b900442c581c00c003603810481e49a030f400414444240490a01c0b81d42c0220100c000340070701c201a0044002c0400b440c17140 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 603931978 1250 603930728 603930737
    0x423090105160804020402042313020903070e0c070c060203070b090d0801170c060a09050301060902070209041203021e0904140103201c0b040c06050408060708040302030706092003031801 82
    0x1044c1156529011540101b0040c146082e03204032511401d0860000c01d041d45118421422038103485183d94000d6a0105000502410086140c0311742d4403884880105102882c55082100c580003841603c1c48a001d003010f40e000319141c1c04149040754005030060001c180951200e2031092045a02c1210300c2c0c151107070490000b07035800101521070300c0c0040601040e41e02810108018500950080080c011200103e000380002ca03543e20600c1c1c00c030f03c00c0c414040c1d00701c2da014000a021960f12000c1514450140c43d005261070004a6401100910340020131055080080e86da02c452500d4040d08030700640500301030110b9451079071142014a240031054000c04403c580049003552050700808141c0c00c01940100c0004051500d012020700840e000c0b030b00c070301c013410020401d40e11900a5900740d80628004014944840c0c0c0b00ba02d83c060018005c40462000300000d00006141c2e0207403a072110b1050b140000b04422580281000140c0050f005019a100307004462a00000c1e00040a401c0b0702804c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 603933228 1250 603931978 603931981
    0x5041e0b070c050c03010501031203060b0903030301050f0102160303030b130e0a0605060a030230060903041a1b070e0903093609031c060311190504230901051608 71
    0xc20300d0420f211300341d040740d055180c14000000d2000c100c20001924050782d5040050a807244074a03050f50250224164040e8401d20051015080a2a40e54101b6005004036205a00d41c18041d00444496400840000b40c44085a42c01400c00010143c05e20340040d80511546035004121681d4100c0040041c000a4503000070030804d0b103d280b0780702d000d940c000d4000e82210f0000e4120b0325a05c2d0262161000e0000e40f260f000700d40352000300d03c00707002e00b103901d02540c5045d01c0c2c01c03ca8494030382c40356004841820100908070740740048100c40030f040030000000c0d207009840c1001c2d41031503040090034259039070010048801c842d40d810140f9015146071510101c00c45808900c04100c01d0140408041c010f0f6104051160340d0a001010b400c0340b94002200e03802492140143c2000d0b07403803d01c03004200d0030712450014150315004469140032444044140c0c210740da00c0000400b65117001c00000529002a642038002e0200c501f02550300940341d100070301c0303d800c2030701044641d40c84410076601003201c40790 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 603934478 1250 603933228 603933233
    0x806040f0b03011425120207030306090e0d120c091205070e090319050901080415090602160618050309150f1206030c031f020d14010905041e0b070c 65
    0xe00079409888060001c10810701d042e100d02000c40000c0e12045001c07001020005042c0a40e40442c1448202c1903681c202e05d01d40110600c0060740101c0003c81c00d240d2241c0700450074030320a101d01071a41c1081c80c000d0160500d90742004c0c0540b80042c0480d200d49081414100e0140e0f0000c203030340200c44051001c44106003032070800074103020300f81d0030108140c0c3c3d4810a1120400c4000042c268182c0007066140100c4104001a2510720032040780e076010801072000600802c135951015800104032520104801c1515545c40302240c4c05261609041d400000701d402c10b1040038481c04170103c0454400014100881c0c990307a07524020142094450300011409480c112044000d40365078003c04500e01e03440c2e825441c6170041145007110340e10b00a10400035001010f14001503403601c1c0409080c0005241c03408600c0906c041e502400c082c50046455416205910803030703402c4c6078001c01e101c00001038903081910700011044c03c80c0c080c3d6401c2d05641c10b10000841d40081c602d42e0031240ca0300f8180d140d00700740e2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 603935728 1250 603934478 603934481
    0x1c05010f051017151305100c0305011e03020d150e060a020307110c0604050d0302030403060509010603141c0810031b05090105010f090e0717180c01030905070e250f020c010e010806040f 81
    0x303c0c0344047d29403e082030100d041d901500280c0c140c508402012a08903000e400861414110703100280d40080c0c00360701100890b10600d12691901c0340c840c004104900402d24192900406035228140b02e41c2c000100100c05601100030641d07803036804c000d00050030b20000040c0340c601076801218440c1201c0340e070140c1018000c1048400856101d0000d222034a000d41c0d540b4001c10085c40143c0300043c0368035074000c40000208045603201c040e211954280d903c2c00070100d0300024010034911401c9000440803000c9041c40504000f100400001c2c05192418801030100031503042c2c0c17100d4103000c072504c13000c14100d4000002900751414001032141a41c0c402008a500385100003001c6060b042e40418401070036020706100c41100041002c03100700e40c12a80c01101102c1b003080c005002500010418803404240108031a0132514114514070502480880d203d40d40e1891400c10b070105082201316102c140d018085039240f070304c007402c020270890340c41c10001e0425000100070078402e903560304009076400040d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 603936978 1250 603935728 603935743
    0x60c02070f120507090b010c06110912100e0304150e01020a0213020705061513051503010e0d02070e0c0a1b060e0a140703021c05010f051017151305 65
    0x20100d0307110095a46144024001d001e402090b0349900510034046241211801100c24407081030755004403611b1142c84010050031100070320880c03184c04105440d243e583d100d00400c0342c0d610a001078104036194480c50401c0b54214907207400c050300240000c10071034000410f16a202e9625041c0368410901110040741805600c1d4802948610390b650803400280362980030305110782c421400c994054030303a09034821103070b42e41904142c1d02100c41840d0748240701d20354101540291101100782e161000c0f220000342903e001e50a03045959012130340c691b02e00c5a0411075100100f06504060f000382c100692450124031070211180140000181c2c5007144181500f140c4082903000041000a0034404105d1603d50030495800e07a41c000c5550041440d6080c0803500004481d8000c0507034480410007844601b594403034042c02e031419507845e4032120040c521800b541c2d220f400f10304800d003d0344e42001110303001e024803201d40009950004401c107401440c04940707075420004c8090fa1048140e11854202e142c0a603 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 603938228 1250 603936978 603936989
    0xb030607200c1507330c030b060309010203040b0a021c0506031903021605040e0c15070f030305011a030615161505090c180703110f1207020721060c0207 67
    0xa868161003001c2038103c010706141e911403210102401d9980300c01e540644055181c2d0711013440ca02d600080040050b501c000f0ba04040d41c00e0218504c00e26200003007003604200c402004d140d400000b0401041109440310764000524101181803c00711010b040c2a50440ba5403c0201036842d80850843d6400b005507814848900407080010421454004d46504070403a540780340d80781c2c0c4400401ca0b45880d000d100c440c03800750720040ca042ca8496003000011201e1001103000900100500404070b41c061700e0b1803688900903100441ca65141038003080c03e104424007002039038101403041c010169200c10003000100c1c1d0140246458070909015209900007528006080e210041a201c0303a440543d004640300d02c07960f81c259407405184006102d030010004012802c0b13910300c100020040390003944052040b400300c2030210301f003682400880d074a607400b1071074960400c040e81303041040481d41005400003601c03051444450900b002800d40c00c40b410000001022991120395552103107108028003001000d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 603939478 1250 603938228 603938239
    0xb071509080313060b030c0312090103060f0815010504090b18121b0d0201140f040f0f06090c05030d140f0705060f0108060a0b06090f01020a08030a0f0b030607200c 72
    0x5150b086a100000f1810301144c0c034130309200c00003503146804101554000303009400b803d125402d0098810346075105240c000d06050f178850001c03e9012413110444003619007400202182d86c40444102034581c01648042e1082d42044070034000103a440c2d01c800d800210070440440090500f4000a0501260081c006401d034808a80c00c42101e4900c220030548002c68010348000c1501c00104900361031010b8042c40481c08220003082070301d4030b42041258028050000d41604000954600920303200585c4241c3c1c403291240e89100a1110300d01e280c80040404074020181c08510100c090721008224508101c0c5034000302d51b184442c0381c440210b4050650250603583c03a03291004014426110030700410007103205000001d00b41030403a104080c966000284002e0400c50218100100200450620b60440c040e1400c003000158005010f14000d2812030030104404080180301e0084400704280301e4804da001d1002c2c4400c8980080401c00c10740351559440d03c2203201c0940c01c51818046240094124 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 603940728 1250 603939478 603939481
    0xb09012003070b010e040b0610051e03060316030507090b040f060b0a020f0703030804020d0303090b0a0203070f020604020f2b0510180302060601110c06030411090601090b0715090803 80
    0x30310040002c0a406220711040701040e42c036000b0080c0c900b801100c0c000c3c06480d4020208113940740407881e10f409c040c2986411407070485036419000404a1541d03c4500180001c000d200480c60103002041d6540682c81d8401402d52654807050341d6000584a44004107a03034441e6000c1a80380c6030044455881c1c1a00144280c6035202c0c000e0304154800f2000d40018010203180442c1c1075000300e07151085036010b41e1b5036002c0ea01d882e002c00c2510000c0100c00c906060303403041640005055810300034820010343c80700680305c4c6000343c0060a00c403d49006241150415010040161784900e401601c0303181c01d0300c1242042d8249118034401080c0303e00c0396500d40c066000c0600030002c002540c2d40c903c507690385042c04403c400340400040e44a255800801581100000849652180040c029840506021034180c0241800443e81c0d5030b00030354080e21030301a5504403802d1401e0030320035690014000c0c86c01008040c07422001c42e41500840100400c498401d9031140b006003101d800c551546900b10f0502d942d44e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 603941978 1250 603940728 603940787
    0x702010b04020711090c0f04030b0c190c020a0b0703020601090c0e0d1523042004090c081e030301060302070302070317030612033c0406050a0e03010c05040b0901 71
    0x450180b0100b644100c880c5c3c40020700104500e400e54090107480c0c2c0506007403a0860313846a124134002405402012030601c0408029460210380c046400d01c207468100d840ca0f500d005100040d041a004210040002c108603800a0f90001d2110f0440d002c01c0e800140c216805c00c011a48203d00c1550241d0000450748400c0910440300110f00e011990786000300050b107500d20907400d10602c600512004050503e0010700429800055003a5040180008118048103240043c007103500204068070404e03040c2005100d40003040003000c0b01810540c0c001c102c168032000c1ca8681d40d2205024440070181c01160500415000700902000b442d480340003461440c12014101d20a41c100310740d101d111f5052160501e00c0200048122521608231038a085826010801082d081101100d42e90034050001c2c05402810301184014001609243c1c1d25140c1d00c1c030004100078400e444424000d0b102e640b611840c04051500b00048408580000c10174644828002005079120884411000ca012840100344c10382c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 603943228 1250 603941978 603941993
    0x1d1015082a04090f1118090d030e030412170705060c0304050c010e060d0e03070803070c051e0601030254010e010e13050f07091103060102060f0702010b040207 70
    0x2030030401004244100107004000a035403a10700040c103105810492a00824240000450340340009441000b40c0341100030b8031030001c40125042d5000e90006521942265494081d4440469150340258205810300c02d0808000e48600d02c000c0010110002e1313002a859080103136000b41e034020003941c44c0e41c60001c0b024a5180e1045400301d8650080030042c0d0200d60003403440c0783c204900540034070305042c0d403185941c0060044543c010b13a07520052222200240e502c1000754407461710f030b90b1030255141031454054070380801044c0404400380701070100300500d0000940541107940407543c810b10248058184038110300130304400714030f66000012441086041d1500e603201d100b1712005a00d091104030310062007504003030090030004500c0d00010040341c503c00000c0d542000801401021035050350361041e00e02000e072000120b160b00070ba40204082115403062442c104110012a0328504d46080001d441e0400240500110106480482c000310300c00d41c82550682e0b00503104642e1040182031004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 603944478 1250 603943228 603943273
    0x6151206120a0c0e06040905010f0b010929030a0204030f260c0a021908070920040501020d110c060d1406060708071203021e0d1d101508 60
    0x40c050034034000074103094500040c81c16001c0e0f4125070480034503400c1002038406400d018000b698095101c12550010075401e10907035840c41c2d904040090341880000000d00f1034102640141c07040b220344501c0201428210399500742001e0129000ba5495441c529803600a000d01c0d08042c000f00310ba49035103810040c2c1c4a03199180b4028500313850ba000111075900700414418202c0508094200000150060038142810140c1105030400b1a40540e1034290840c40c00404e503001108680e11303a00c0502d100540360410744912429980700a180500300300c00030390f59011500740601000b0f041261502440341c180b003111841203008168503075642c3c0c3e40c1070702d401800d2a04248d104032491640802d0b034614050f401c5521a075440314146003441c3c0349172101d0041070b50805050003416020001c0402c242d0711a4600104d9060407005603844203002402c88084070031f4040c2c0141c0a44600d503072054246400122014000d1103048041010f0800556207072402c0c1d81540117000074410400c410005808905408 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 603945728 1250 603944478 603944491
    0x303010b0a0c080403030c0302250506070501111903060906050f060c01060806190b0a03330204030c0602060f01050604330e030d02030703090308090d050709020a0215010509010608061512 82
    0x88403401008048455940341c1960302d5140b50340035840801050a02000de815054003420002805502e52a1000c6c09680001e044424005052494a00d5140c06100e503001401c01780b0000c006031400c100104404086242d100b901c64603001c5180840d000003500f000000e4034100003070301c40504188005404011044280342c00050501c286180300c0d0810720918022207401c032004100700e0030f88804a0700d170b400f9210b15820f6901c0e000c620806900302240000c000951181003c2c00c0b0661030f1100003810200b0240c092035042058a00403c225a075001c02c0d07400350b81000313401644a8140006185144070710124284080010000c00180c03140c00c80040031041c0d005034107664250300e40c038104a07168429480000c011659200e801e0010030701d24400380c944100003500780035600d181a00d94501c0c0c1103155100d890040d4001034610101581844075040108000903012140d50408001800c68001400760104000311038000030640d0b51042c401d064200c4840205688e24901c0c0301514240c2c102c2101d11 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 603946978 1250 603945728 603945733
    0x501080606130f090c2c130309030c030308040213050601120c050d140a0518031603030e16080d0507150504080f030f06040c080f070f110d1e050c0303010b0a0c080403030c0302 77
    0x14120584010301086c8a85141c28400072400c5c2d40700400104081880d100940402c85244c02c0400029801d10078600554003075184c0e0960f51070a0700c100714100300644006c030f10641c00c10307082c080281d80010003988282d07011040441c46171b0fa601301c212828081c0d0049910482c0c2030009440d403c8030090001801075507045420301255a40013201f0b42c2100031300208a012354000c1001d4070700c200321420f682c51224841d14020800c842c90700d04007444d10013031003151a10900c12040400040008100d0305000380e006003030542c1001180d4540340c092130059a50120303115100d00005007000351a00c2220b100d0798051600c0358581c03e05220031348184200315109409980b03007403a503420309400b0f0b0190502c2602c0312001c0d0b00c81070744d42e0070045030701813001d000002c284005042000d6440310140541d00310400141e42e00020440382252903035079007990400900c248081001a01070280011084034103584c04004841e03550702c44140c0844040c003c00e81c000c0c0c60400040350220801d41c1c0720a4102002e8000d40c00c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 603948228 1250 603946978 603947009
    0x141212070f11100b190b18030c060f030f1501050a0302031009020a020a0b070207050609120c101817030703081506071110180501350601080a0501080606130f090c 71
    0x1022030b1120917501803010014030034000171061002e007081c02c404000001d01503071509003614021809a4024030881c107059170000c402c0005c0c000d5070101c1c1da50301c00c24580380740c0360340082d41001074454421070440307500f015000000220203034510340b5840001c00c40418119a03d10710b0240003034481c0c645a80c222000823030f03040030a0034140b0000d286401d5a400809080c81c0610040400082155545100307085024121000045641c1e86000c0d4021040b80c0c1c83e00c800d0501d080407103071807182c03003070700902c046221207044411070b09400010b4600c20795050034038070001d440703034100c024a003116484d107994454000180300741040300f84d1240b6080c01034140c954010382d1a070200d00b43c618031402c040c1c1c84519100395504003d03645c4241d5400c000340c6005d1810401c03080c1075445035a000d8a802401e0820b00010700144259135a1010090b50310000030343c0200810f505041640d522040054803c41c07080170100046001c040362940210031b02001c04804100000842c945107642200c1442090614540c1e141d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 603949478 1250 603948228 603948259
    0xf07061202190e0d0f032f10020c0f070906060305010e150f040605040906061401021c0804020621070305010f050607060f0204030f141212070f11100b 66
    0x240d071090241e0500034208040303a80e10440700c0d22041c404450340300896640c1c00307000c80c0300184068445e50181d602c1005180446021100644603030f207003501c0038180450780c1c5003032010218880b08206854000580e454884082c0c6074506002c010403405540980d010009403151035910546c120b0b0070300d403801d208030707a0b0b01c0c082142c0c81c3ea03084030f00301c42c1d91128808416140c9003080c00600402d01c001c5c80080c011317842d1800300d81102e0b9160400c40e99203076101401d000c9000480030740c1a50140c02d100a01e0310700e00340c4045038101c011071451b5400740f15a5001041c1150355034002d8402844450304a20264119204d15010910b0152049400300745048004120a989103540034184c91020f4981803a11142d50341e448000c01d941c50072608a20380c24080440000c901155240c00076000d52002410824104d42c0181031001d900c0640104110403c0906500c03522135081d184d110b0442d00b0031051440c501041510441d504c07405081d040e000d541922084000c2640c4020303201242511400d1802c0c4810 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 603950728 1250 603949478 603949481
    0x10602061f05010e13060b0a110c03010c0909020d0612050a030f11150921041d13150f0203090703051501030308060d0c0b0304030e0112090b0c0a0207080f070612 71
    0x1d00802d800100402c01218a82c2412122864150508000040e0f41950384071422202e0b04011011400a1300d4412403580c1c01908001160030f10304210020031803001030000160a41c01c05124912650740c01084052000341c095106000401c0e02401600404442e880d00c40d888400101040b004038400e90301c01c2d404c0600c200901040020100024044904080c90101c1c1d040001000303440e65100e05034085050064545802010401000a00c0d440b00d04180368820b200c0d001e410b2280c0521074180401c1000c141ea030900c0741e10f0940052980b0300c0040c10345400d07009403071107511f03d03c20fa40c00002400308185002411408a81c050f00c1035a645420303c1d2860041c0031402e10001d400240c04001103190380ca4480075001e1528401c10404040a590300b00c14030290300101d4055001c502401803010356543c100210304140c442d01d242c100320307907011076a512125490107410641030000c040b4103038040c01e00800000001e84031400481e5003a0200c195130f541c0d191154020103000803c071900c81c07078201101f0b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 603951978 1250 603950728 603950791
    0x60305070906210b06060c33070201020f040e0a021204081903090c0312090305071e050d050709020f070c0801020c0c09070f050313061406030d1409131401060206 71
    0x2000d040136034440302d04103d0160011070514000b0300400b000480d2440800c400c1c01c044c423512030381c89144818112010198030b100103000c0015a40104840c00d54540040200e0f000c0d0381040e2801c5015480360b00f43c01000b4010b14042207240740c600024401030000140181c0380007120302010408a161303501c4100c055640d802e400034009101204240006880f41c5600444450baa1804491065403038542d00d00d8031950b903011403003070940380c0c2c0035040080d011b074800300c080c00081d182404030040070794801d59104241c6c4502162940d005c18103100c1c00399000201c034069604010300c20141d90301c90f100e0301e0003588140c09440541c411984444c456003044200d2078070484041c3c862000c80f091102041e81c181c1c0c0018141e10b20403601351540400148284100384d00b960707100e4001380262511005161410740950004000d200c07030080f00000c4002210210f070103401080c1e4901264540108202010b403500752500d03103004c0c860600208045500140041c07103001c44100e01035118489150b24008180c8 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 603953228 1250 603951978 603951983
    0xb04020a11071a0f0a051603030f0b0906030a030311090d06051504090f030c1502030403080601080c0f040b0f0c07031a0606040e07050a02150903130801020a0c120306030507090621 79
    0x509000c404450030721500a805948007608000340340507c090b21800d42190400401c070003295907001309040031030091040e0f05000c4001d03150088241083d00009645000248004080644500c0c50081c000c0310301068030410304d00170380111210b241c03a10b040800b500c81100c40003005042a045c030511481d140c041c0400030b58225143c1c05030700740345403001c41e03180f1102c0c0c1040d0380c0102444c2e80881d100b006440150300c102d0013039964030590b090100005110b6000502080ba64800c2401210035600d5002d0448085035410000c95503110441c81401013140518000380c82c1c0d0780101c48001061090300c0c4c0031a60017a14030303110042c060380d640c03042000a006900405030070070503410026803d58020303001845410701500484940518081d0f0003140c015044500f160705800104a2003008485500e00074041c00c0000000d500b881c844034001802c140705950098006941003007200c80704c1740a50312007809903820909855443e84c90b1613080c0090a06482404190b02103c01a001d20046121071503941c240e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 603954478 1250 603953228 603953279
    0x705060409061a0f1902190f0302010c0f08061909050103050c01120c0813031101110406120203130f020d0501060807170f0c04020904060b12091501080d0c03030b04020a1107 76
    0x1e64001c605c10000210000340301540704000d000701034042e000c42c1d0380a6079485262030410341c90345031800900b580e5144400300188600c024001c0c5002d0342118003154464006d075542c4044650941c109000e24040742e00445190746050000b0040c40000700d40d05013605001c2e241c541d1a050840c040c14201c07010000b038040010381c814081444013490300c00c03851350203000386003240d400400e90030b0540c00c68008084010f45500006002c208032600080030808030140d5240c114114500b03203e0a5202d65502c900040041e201340c00010210740d071314401042c46a401200070000140c58819540e5512624091044400410b12111300301c00000180d00e1075514180740500000b032000410711020b50441103d80b0b50094848601080c103a10400241104142d030621750b17615420907000d414100302c00b8030000f2090b01b609000600c800d00c00050720041140c1140384ca0251000d9504046004040c800015540940002051804250300c070f41e407405440cad000000e956400369654010304841546460403110321 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 603955728 1250 603954478 603954487
    0xa0207080307080d1e0f0f0b011b0b040f0506010608011406031501030b03100e060f062d0a03060603030203190201061202060702270f0a06260705060409061a0f 70
    0x115000c0d08406003540403104210502900040405d094500b52001e0000d0342c0d50328280d100c410206400354400035a42801c100c2d055520f01d0000d20940c4400c401c02402c0840d0b0750b000b040400062034800c158158100381900c1455848900003041100e0030310440c50718603902c401a00c103038604401100c4c000c21706042414005002000150098140b207803086170705020b50310810390070103400c1c003502c01c00305140c2003d400340349802c080d4181000b8001d401c0a0041000d20740100c03c1d9040b046200c0042d400e440c0100b8008241030000941814064000402007070801c80c00004240d0004082c20524200c01d451340a14080f04a00301d0807203006114021320440c0d0790350700e0009800c041e0018031900d0700161500c40303035082841c044818091044401d105103200b0030100241c03824004000754100c40042d40601c1401e00d4401c0486103302100d0b0070f2448405800821092210200000d1004020240c40940c480e60707108582401810715201d10b18601c10000d40f002071350398600c001c80d00d140b9000d54107241003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 603956834 1106 603955728 603955747
    0x70f140f0c01081f0e040c0302130c030f0506010f0f030e0f0c0a080a0302030a030209030c10030f0b010305060a0909170d0615050a0e06090301020714030a020708030708 74
    0x6071425201c4c04444260000441007140c030308503403420b0503840300d0030180030000303031584025413080e1038440803104005c2035000180244e080e81c80402c20549803030141c1c410f07521b04450550004502c41c02110703071603010f4400008040f2007072900003440c0029021251500080903442d8001e40e1003444c1442480c9000042403015158039405003224511595010b503903070240721409028544c010502020907241007084222914000305440d04044080101a000b000b05400301030003070303080c84c4c640c04040d4041d001d5a0701070000644078004140c5010b1014009003d1004103d41242c401022541241580c070081c0004541c0301800190786858419030341c04402d4501c42035000d001c001c0c0024542d15411423885a011101501c004d40e0ba0003600000038024420b415000b0001400180403162080e80000a000f003000c2c0c0d502143c802503110103515a4900403460010514107041241008 = true := by decide +kernel

theorem cover : BRFrame.Cov 603776978 603956834 := by
  have h0 := BRFrame.cov_init 603776978
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603776978 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 603776978 ≤ n) (h2 : n < 603956834) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
