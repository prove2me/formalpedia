-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2431
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:41:56.231869+00:00
-- url     : https://prove2.me/submissions/46a696da-871e-42ad-94b2-96cdc7b392c4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 437050359 ≤ n < 437230215 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 437051609 1250 437050359 437050363
    0x203090715080601090e06100f020f071d0c1213150903020106050f06070b0408030c16080c100c020a060c021015090b0604180209030a140109141902280305 68
    0x65921a0100386101d402250f00c906c6807201c0e81c402e4001502801c103d116410702150141858203403501940a40904120044030600c0202c0141141900c14140715600c044075025000d40101210241303402840001c04001062414a800c2100c507000040141201e00b007418000150381a0b43c030840b1318203250682010f8045d0840400c8400488a030000043c2c00c1707060186911480000401050700200050001200316002c0c1d174009a1090100f410102c0101c45501c501c091018160303008040440e45400c0b2001c00c0111404030f0045003030074000c4082c9410b019546802c01c10f0010484c5845140340c00303010340300704088490205800018401c620314001d03000740c01d2200340a0341c1440d9040510008a0381440360449003110740f40d245101e04003606000c2c2d18001c0d00200405581030003205130040100e18140a501070302400c50000240d00c0500c1d2411001c0d2116500c2c4401440c0c00c01c0441c0c3c911001600003201441c0d80640d0321100c284803a010000c000400101c00784484240c9c1c02011052000c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 437052859 1250 437051609 437051611
    0x9051807020d030b010c0303020313021207030b060604261005070c06060503120901120605040203180c010305010810110f030c07023307050c030a0b0a14040510020309071508 76
    0xc00d4094900201c1c00360022802c0d00d040361500d50110b102008582d00182c40b03a80203552209150b48913210b6010154005010290aa000c802856210090500511640c80c9510750401812203400d03191614081c504840d006410604048800514424000d01d600510200c000321210b9a82000784c0c1c9442d04d0050038102c40f622080d0389240c03420701d010565050006204d2012548078038414104010240110f5160020301110104039403200380c002840d44803800070354040e0f02e500320400c1c505180e02e040140381992801c01c1c0742c10076040c0401004020303004071340c10040306c04085c400b003240a207402d0390003000d12800e03003051036910780082042145060100a01000340c03007190540400710048050041e0300b50001781c2c6520f80b010000d100320307007100b0900c010411740340704406582d80d03000c0e0030340041c0c104124008261041420141040444412846001d4824404000214860400740c440540da41d04484180308030715400404514a180c0411001d030081103100c100703e041c0c1c500844010801a4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 437054109 1250 437052859 437052871
    0x150f110a0b1f0801061a0c0312061203030702031c0912050c010e16050a0611060106030f0b040f2403080f0c16090c020c04020315151c2007031e090518 66
    0x6d50002c0d00d220507134950111508914184019030815105040060144002810542e482600d807070158142c200103002561044a50b40c004d5902c803841c0c050b40b401041032400b01100186c1c9000341c5000081d000b48140030754001c0034034066031503101c0748000d60300404d24001a02240e00c2206a04601d0415a2001e038080d2501641c0a501d129510503041e103410218a000c49541e820030300040c0001c2d4426031210b220300b03110700360108101210034003181c1100d00850320440102e440f0344168a1100500c290403031050908200307940502d00d952507240309805025800342d18210f00207251b210014041108a203001c0540032001c5c00340d0ba4910942000b0207800310700401502940c00000e10900e000d00c02e40c0d1058080b04600134818094604200c211031100c05064582c1308140158046105401c41c00618080c40180000d2160720f80b51510001600c104184003c00c80c08202c09000a5401603007004543d80c04404800c541c580d4a10076580c1030741e02d03042581c20a010601141a41d81a0b9001500403a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 437055359 1250 437054109 437054129
    0xe010e0a090f0e0c03070621140403021e0a02011202040f06120e070315051f080a020f0a050a051e03010c03090218101406070606150f110a0b1f080106 66
    0x34800c840c1c0c3c40d48511341d01c26000c1d4140c0110600300000380c0104403020100c00004244480314288440301c2d011103880307420355008022404100800c00d6010021080000103540300e5154030036500541d15551725201c0e86c020b0420201d041444001e461a80581e40900071303050b40503619944601c402829510201241e991701403c000003030700411b03000308200c82629001032030514021908004003014000142c041410613106e50b00481d0103169546096026180080260410b2100e82c0100600007912044051254038008010400b940e07811102904554003900d28020660440c149880c9004001c070202d81c144d400c01c01d8041c0b040c0d600d039020406152081b20013540a11201c14641d4001104540a2078902ea03d01c00901000180c103410100e4030340d00030007251910000b0303130701c400580300603900101da54490004941180ca42004460042100c640340100340c03d0304136a45c00390384806181026004901420124044036207811094001c07011000050a8203540c501d5198001c10766403041c1d510813 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 437056609 1250 437055359 437055371
    0x90c23102c01050306090423030d0c0e130b0a0b0d0501050a09090b0c0c01060b130801050106020a030203041811070c05010e040207050601210b160f030c020a030e010e0a090f 76
    0x204992456810100c1c1c81030356154110b6032000140211814042c0c03080e41c1032849044c07291800301c540b0314180b1180300c101000d15244c041e03030501e400c256040101400c00303000131944101c03001c0c0c4810070103061008c1c0e816030220300c8000c01808145003540640003806083d2002884120031442608064104ca80c1520096000c5079a440010100c86140000800c0d00c04401d0205014180b218040e2007201c81c59000003c01e160380c1d2004201c0d030b03030011402081707404500404120800702841000c0c0100200d00191029107003e40e0b0003034070f81c806c90044284e98005070f400f03110b0308a0150f01c2000e04000482d5034070380d18502801e041410b0115813242034005140703130700200c0f0641080d0007518403595004009090070307400c00c00c411f031288000e860507112941c0e03500e60900101d00d071400114020752144807480d02003000700038010f10319a05030810b901414140705009000650004d07003040b54a4040c602580101c01200048030001c50f6186510342c0604110f8010410038456400306d41102c544150400c40 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 437057859 1250 437056609 437056667
    0x16030204030b04030809010204050d03080406060f0b040936050d03110d0b0f040c0c1707240e0313080601091a06030702010b06030a050613090c2310 65
    0x9038455400018244681000842c0000380110403032a00700340700800140c1415250b10100b0310015074001d00307600055001e828802840031500c1554041d061410036072000c0d0303007040e41e000507a01c01c03840390399800e1b640c40c007c0002040000201a42001c001400711080d20191980040c1410500c0c030240c0d038902810b140c4a107564000d104102c00001340714a214203000d014070722200142600c90200f40c2007015002e0030101a070b141d01c01c1340c14400180d2030700304000801d030070609000000c41070042d11060f8104815070104a690110700c101e940710070108003044084a8648000c0e2039004020040f0788008a10641c045008111201c255001e40086400c941e80e1040d0000c00c0d81d40d0545000c6089010402c0c901c2039090000007564005141e000100301c0c1d40305c0a003c2040c039841103da6101840d500c0d014130005180446160719528040e80c0140320ba00c085484072180341e0050702c28201a04084003403031181c83e20400b807201c0108030080407070a41944107900503008000d680103c0240040c0364402c4a0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 437059109 1250 437057859 437057861
    0x1009080d05070f0f0f1e0c12080c0d090609150e0d020a02060405191a0d1a09060f0d02180f0603150114060702060a0201090203100903170402010c1502031603 69
    0x5000f011994a8200c0d0707400300a4141c03404c48101101d4002c004180c140701500300741c40030326400c0300c2a003640ca02901c0d074118186100c2c06e49450544a0800c1404401e0121031466801654210100303036500041040d00c0b407504000800d10b1023401404281c0014404861136800e40c000541008400141c030503084a00c141281c844810140007540601c0510003884941004441000d1400500c40646402c585402c0494800c82440d0030f00341116200041d234404c0f69603640280d210350745510034602e03811549007000a0781c11800030101303405100b01d07080c0303008a1b44d21070030420038898000e070000180c80c0700d1160b444298182101c11781c14040134000887c48034200040c0c0503649030010040c0080990070020b2301001103411208036548a901400040096501da00060901e02869000000c8208640c07040c0b500b060600541c960304d007890a02d880000c00e0300b210240c40f40100700f034a00b030034030350b1541300580b50750b5089000502103c02c2c03c94804118416640154010741700350030300b84038251200500b14 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 437060359 1250 437059109 437059127
    0x21060d140a061b022a120106080c090c22090213050f01020703020603190603020a1404050730090b012c160305040215030705070c0806060a0303111009080d0507 70
    0x2000580c403802e18070200200c5d00c00c0c003041401100c81d001e00503541d035200040c80804280d5201e441a503442c041040595410040540b40c043d0545480d40d107407403c002400c0310750089101c04600c100c940424428500e000d480184081c009080085444614214610001c0c00f0a80100c900882c1282d046007820b60000072010102e0741e00501e0a465a40d0b1601f2101001624040c0041c9861b100c2c0800f000581d540b5a07113402502c81d005070303c00300741d600d0802c2100781c41000d0611818442c0015000c90b503180035464031010b17007194410214240030307440902d100900c1d0051014018114039800030520702d5000b141a00c07180035907111450140c802a92a40340d40300242d4801c1000c10380c104109000c00d00a41005901600042844013090040c60076440d00c2e60084420100040b00000c80c10200942c03514a01e01521080000f000d4600d420804a84001c00702d010240902140b410190152481000710304d83c43e100542050106601c903141c456250f4104441080360a801d0000059846200322410 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 437061609 1250 437060359 437060411
    0x308070c210b010b070503073c0516050609190306060f030b0a020f041502030c060103030509030f0106150e0d06020408100b01030207050a02010e0102030705010213081221060d140a06 80
    0x1a502d05000c80c1d40343c00030141d01600340b01441254032521009109d1080c0d850030b8840066062050141c1985030040c10005180d10260800b20b603d081402180c43c0c5034290740800009a0720100b480d80c1b411851840503803240d20040409042000114402c441c003a40c84003200d00c03070005007580381c80d2040c581b07090340901c0403401c003419014401081550320101848a200c41c40740107a914004017402c0090038000260010b8003c1440020150b00c1824100000781c2940700c0c42c03000300002c0d0708160000341400b00c0c006003041005501000382121381d0b5500c1241807107a6105000f107581d10b98900155844400105180e0115890040c408c1400c0d400ba00843d4a005d611101032f266031000b070360041d0b0b446220341c05002c3c114801481500c0c0000c20910040c051081c0303820b00503c03c103241c096103034900001400c0302c105c605d80500041c045190b1001c05842c01180100d0810042c0d0b8078000403034440c0745000006030540b1900c00b142c10404a01007841018103001d61428080012040c40701c2001c01c00d28880 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 437062859 1250 437061609 437061613
    0x70512041206020f0c061e010b040602120903010e07080d020d051206090c090a0e010e060607030906080a0b090717060f100c020d02030a03051b060609010308070c210b010b0705 77
    0x1070324001070465005250034502c02c00c104d800c01081c54813591820100b01c4000208070302107200b49081d0181c60380e01600415a40c4602c1e0302c1d0608001c5c000f5111649840541444176000c190340c070b0b00c0e943c00c7d00203e49000c0f412044810003581c0b0800d681d83d840d41116034001501621041010040c45401103902d0054040761030086503c5407003d0019800006080f084d01203014005030041c0da6620103450300030310001208090380e50502c01c154010400c081c1030944941010088580020341142c400130031a2106e0512000d10380d20106228098038a5080c0182d10680600030860081c0d0448401c0c041900c0031048100e5582c2e40109021405100354030f142d5010243e082c0d138005542c410794a00881c0c5102130800d000d52229540440c0c07401c40602c000324080381380461246110180201c0642000d071071070008011070305005000c242c0301403042c0805071a010000500d5024002e6045004000384550102c082884d0176100c0034510300800c6100807030b00c08020074000200130680d5010b5501032904100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 437064109 1250 437062859 437062889
    0x1507090e010f230d0816020306010e060a030f14010f06090b0d111903171b011b050714060c0414060f0901052208010203160206072106091107051204 65
    0x83c264114800115a041e8403032400d0810800041036000a85181103014804250286003031040600b405d105030455030240c040207081100555400132140d00322900503150281034075550030003586082c0c00c95820340e0303039609104502c400546154008012501b00080c2001070303050f044104124003502030f10147c68194072002311b815078540705085070720190b0355806000700a603a80e500e68503908400c00000b600d92401207130380500143c41c0615040040d18800c02081003103600408036904804000c0b00d0020048081031010401209052107401e80700908119403d5240001500580f9071150152680c05034903c001240c80c0d01b0110242c80c041c1e040b4040207070500804400440305500440300041c0108070300a1003001881b01c401083c4013400303400c130000d07071340e03183c10030704031503110002d80d41035003154804e00810080aa1000042e45011030700b5031100d0224240b091080098a0180c00000f41d085c60020042030a084c220000c08500d031040017550003901c5903004060880c003072886030b5640941110 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 437065359 1250 437064109 437064149
    0x10f0e07140d1d060406050718030b0411210c060708040504020c010b0a0e010e060a0305060a1104170a14190f020103090816060b09090a060e1507090e010f 68
    0x1504501c0002c1c40005100410050102401009595000040d07080f2200348000c0c004140500c940c031440c24108440d168100b210034020514a600c03002e4248180030b00440d0400c0442c3e9411054601d0081031001088128240000d0005040e00c00c0d00240c401e0180d0500d0342e06000043d40d101e41e4000c13034541d0500e49446d050101952040100407074655a03800b0700d41255491400e4031015111441c42484998103040304071080342d1000e046640f08042d03c2001b08001500080d1042c0d200004d100d0110b000039000c070f0580190300450b005140c09001c160501d003d203a200140b4240c0860082e040000c0244006c07203825200c10000700c3d114040341c2142d4854021444040c41f00340c040b8410b1500040403222521a054503800030b6411a03d900400c440020612007180110740080204946030f203114200010840d45e82e002c0c400c80100455222a03210144070414410140102c55140080d441498031440060012046024001420903c600080388440f045148803040c0d0300311a505403c21055070f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 437066609 1250 437065359 437065397
    0x160e01020709050606160b070e1e040f060302030d031e05131e081303050d1404061101020f040303050901080907031e06180309080c0f090c0c0a0501050f010f0e07 71
    0x3401c1c0e80e000f1000304410400c440503206c403074903907a014a5800120342040c000041009400b0140288101c103404001d4103914045079240300c0d9507100f150b0001c2c0d4105048980e501402450f800a9898001c0d10300d4010030035010b0700041d84030f496861f02100c1c003400f5000d08400310390054945419051500c10b01d280003078201c00ea81d110000c10090180c0040249507150852035209510740c51145009460800801208100820310340e0928186a0800900540c02e46c000313025a1107003030700b0000710201d180c034080710030340c11600d40c14115949140c0d00d6480e4103010740f0030760182e00d5441c0090300c89170004070408008200306084d290303c001084003480c00750081010b0124402002c1d140580d0b181c40c052350501c00121702640d00d911035224641c0ea00e1821a440b4144403444031002d014580c01c032808026a902c40421940c01a03c0081007a02c4d5034003442d00b5490114010401880c82d0310380418803c0d0b8a0703480e9610390413606102c2200603c25252850624030417010764a1401180101c03041c11088411 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 437067859 1250 437066609 437066611
    0x30203040b0610110f07060813110f010306050d20060f160816030801050a080f03040504020a050c0a0305090405070e09060d110d0b100605040302030304061421160e0102070905 77
    0x11884d0042c04011060500340c2001044035900380c460f80f1503042080013541041d031107944074404c0304500421100381d40f104180310324200c3d04580700304c0c020070241039268042d90010024020141000301c401c05030340703080d65009150010307078256090100060a41440c00c0780c216040c82d129038120070704220400741c031400074101c22141220013030401e008404450880202d400200380c040ea541e04629498007040c8032050340a5000b240031500842d143c00b520000020442d8110b960590f80141e80300c400c100c04440e6030049540602440c01514004414141c0c850054020014212010800d80d1101c050555100203005112900500344000160b070317130b00d80000c51202c1c840c01021810b04a42c80c100001f20040400003048503010016410700420410014425018041c0d90a140e46480e0035500026500e00891099000b08800344050f003460b03400d81025981c400c2c800d14143c611030500241c156980c18022503100100941500012200c6880340d4030021a400060b00a002010304000c201000b82c20 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 437069109 1250 437067859 437067889
    0x6080f0d21020c060a05090607090b0309120a0c03031107170912010e01090302011a0312180405070e01230318120a05040501081006052b0e0606040606030203040b06 72
    0x8040e00e0015691041d40001c205224441028101c5403400b44801e000b00c80014020319280e46c0a4030401441a03001901c070415140588010340c0c90355030f541d4000e843c15581420491005030081a2010b405402000201d221031103074a09101c644800c003c2c0712418010068041d00c01c140c0e41c8115482141c00703100420584a0140241e01c1c55000c1c00303409404d41d180401c00d10126035441c45040300f4550b082c0f148070761005e406031030042290742c04400a40d64007e40e00030100b4020001a40c4080382040106103180c903000644240b0491401c0f0b24082c06440185401c1e42c041001500240700b0208000e8a484c1c1c03842c1407464440c01e607150303041064041c0741c9160701c5ca00c0d2031207001442440d10340701d60080c25605650781d60b1a07540b0f41c2400001405c1140c0074080040c41100b0b240c0c2444817582001c00d03191a82c080705111100b2108003139007407c0c02e0310500a080030785444e04006032080c4e400851040c3c8034600980e018810685c0d5680100e040388011100034020032411804035843e454408401c0da82d40c4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 437070359 1250 437069109 437069147
    0x5150f01030f05070f1202030c030403031104030b130c060e10031113181b0219170c06040309080a0218090c0a0b0a031808090d0312020a020304050406080f0d 69
    0x102d03000d400781c000c840040d604440403d108032400144035504c5a1a200880038002040d411420240c6500070300340000b40006007810303254242c0030408412a0103540045402181e910075505000681e400e20701414030301691000501c2c0c101045040c0a4000003000080251603a00c0c070408200f0114002e24400318a06a0820200200c090241203109614042c201100c2d61404443c80141150202e40c10700c1c0342d0020032010584020070550700852004404d07290500c1a2030450000d00c2d00d000c89080000c11002e400a0202d8440b44140c00020341d6840b4030721a864101c01151190360a0b680c4200801000b0b500c02c54003c00c0040e0807410842c41d0b03401070b0b25401154015031601d00001c00c8a00300d50443e22090b20042000c10308550305001d0701141400c5000101100100c6132201c88052040052a5020380c0119120f1000c061203128481090081c40508644801c0c01c61402500c1f9481845002d209a0500b2804501c030140030482054058404c0c0042201965000381a00c034072101d10b400e80521 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 437071609 1250 437070359 437070371
    0x9071103210108150403050d02251a0a0e0705011218030c050712031202071106030a020d0e0601080d08090a020303040b030402031b0913020f0a1d0106020105150f0103 73
    0x20045840712820318074a5104015640c10507082ca8034200581c420a4445000d030740500c000300741c10008448504854040169480b20740142907028a0082084400740661500d254024000000d0300542c00c0c0910100036034640e00c9a0b00b03941c0642e40484440c0c0b2581e00041c000b004158000c0e01540d00044110b1404030304210900c1c000020700610950075004030700862482c000304201031003600090400d04400c1624a000c41d10010541503c02c0d00100c0d5095001964200740240c40600750a203100c0201510356071f02e407800b02213019400c104403180c066828001c2c1035007200f4022035580e0503074161200400010811b0407040b81c10700b901400405d903900566a4000150724148000c002401c040340c0716560b01c1c10244145482c082c2c4c4030070580250054205e40201c40d54540715001c0c1c10141010100c6112a00c41c00082c50000305420100e90100c1d00220015402c030080c2c6c0b20726a1100340350742030400750f80e076000301303030309a800498602040c000c40030301c4403290f803a01c1c2c5200302c035050041c0340010710 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 437072859 1250 437071609 437071627
    0xc140a08070311030609070e0109020a050c07090222140405060a08030a0c030f0f0e01050309070e040606051f02250314100b060703020c24131503090209071103 70
    0x80c071405400a0b0f41d1008038141e20307040c0b810304004003500940118014210a0700d850102d00b40050180111005c0035000115104103e101d0016100c540c0c02680958140903a146207a000943c4080800c1c00c0b000d202140409020300d603070641d0001c0b16034001403111419030007401c00000780002006540c2c0200e050401141c40e03041080503124031001501c490143d4002e905004d03000060b1383c9400820001c488503104076459028a016171108001c2c249a80c0781c0e05d070151a60b061802d245c2140c0c0002c41c1d104100f0080c8003842d040081110810390315015080808041443c40070712031101e00000da0f01c4840c10440080310740c540c420025140501071180942c882c3d8400c8034001c940c0c401e5401e580d000b1010031402e11f0701445a104030031821520b6507d4611299000f17900c075041c041c401d5100c0c003c2d507101070414030100407810445080c21011280e896001c40844120600540284074407211a081e0340120035009101d4080682e0700100303160315640c0c2d841c80854440408501c1c940a0780800d10203012 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 437074109 1250 437072859 437072863
    0x3091203071502070606050a030807060911120709050108150103151811041109240919030c051c080306040b09130b0a141603020f04060806120a0c140a08 67
    0x46100c00b000c4090b94520140c104131003581c10780c5d00710300e100e44001c06e01000001c003090101d07082c050b80304901140a40b01030804200070a0078954050b00100800d0702440130038800f007048015a00d03255000c0249980311241140e0700c0c01c07501c0f41100880702c2c0c1b10050010440304d03501400c18604407900469130822078a1441616445000200d8545017074101c000340c2407a041c058800208004c107030540c282456440014035000255003010784080303034418040170300313199202140c1d03007908054103180041400341d0708281211075601c01030700e400b070181902180c90f16086154244002484a4510080000c0d0701c56140e95400940a40e41c8581d464040c15021b0716400322291081d140c100070a549000749042040d49060018900001030b0b180403000e03040151102d0700b194021061010112500094607010340081c405c03140b280c40100000f08000a4540d44010130b944103801c140e0b100d44100e101d49007003a546803144031000300a0040700c00305002c490f0401d01c2443c00710000810407050f0a540e041118 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 437075359 1250 437074109 437074133
    0xf07050102122203080c0a090e010806040b16020705040c0c2001020d02030c06041101110f0615060c070e1003060e031806041a031b03150307050f030309120307 70
    0x90306503040200b04078500348050441566400003d00c40b00da2140070340d400a040e094000d003105076610340480e0b00201329101e198110050b14101441c0e036429615850703144e9850070100c500700c7d88054140001440100e0701407000b60102c80325002422002d051004110184ca03a009071035041080c4202d8490108041d103018840f00c50121040d021340340510b2000905000808440c00e040d54020001c080b201d0100003440c0740e1080d00004001090201d500040300c2e1442c40003805241da10410b8840c070166007000c906603000b03008845005903ca10004244a00f85c01001d9065140390810201003110100c0c4001060340040740b0008070158548075070b6003c007211031030401d115185d480401c241c98801107144108400038001c460540c206450440007000d06a40c43c0c0c0c203200841c002101007800c2c03a003c0c030005101c020000403815100e01d00011070400c0720300c100104030f10a1186207400101c03828990390f03d81c5600740103005036240c20303085000c0c881d0112441550110a2200b0844140420001341031a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 437076609 1250 437075359 437075377
    0xb340806060f121e160504030f05010e0a050124153005040b010906051507020102121204170a050405120c03011e0b0f01090303031e061203090b040803030c0f07050102 73
    0xb144000e84c0409030381901c0003440c030204142c21000485e11660050706450840c0d500846003480201c3c6881d1043c05400030040c8116241b00d0031408104015064010729454034a05039181191030f00c000881d81b90403201c0c1b1401c00514050796103a484c1034031034a8103c0c0c00c62104070514013000d602140f8014203c0c080002680440e41d00c0b000c0c00704124a01c21520300502e50300c20184501400c040c00983c4d400c15818810f00900000984402103900921821005840306c05015031107030301e510888a01104111400c039907818038001c040840640c80401c0d50441ca00382d82d266401c281c102070502ca0b2100750000080b0181c4515041c1c007109580034090421059080e000755403032a040e00c2c58600c1503d40e07904140e48240c003412184003260340c0c440c0322035084a0305881c0126000c0324450300a0700e02c510305103000615034207180020840300c14006402c00454030aa03900400e05e6a240d07030707110343c9001c3d40c0907503042e0380c00400c042a610381c020406010f0510040c25101c1c030300f008503904d040c2260f0100300e01d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 437077859 1250 437076609 437076631
    0x50d0507030e040203010605090d030e09010e06040b030a1e0201110f010e10090b0a0f0902041505034b030307090306060e060a210b340806060f12 64
    0x1a003041660200c0c220242241c195000d5040d541420700240a6025180e50b0714000c0803042c0b00c15051500c10b448101400e5809403502880b5611018841d070403000071280315005600703003884602c6a003000510003202c150020617041007070011405001030706060080c16410000c2c40606411a0382c0c06100944440c00c86200006890000c41c1460b8108031010590004c0180b4240900c8041040c1c012055446a0075003000110980c403605920f0003028681c40103074100b40792445860783c880e0281042007d90744c0490489503c3d00c0450400c5041182101ca81050740c40c92141402060b046001c40d4112000c0f40c111a02d00030f042c4415085c613541040320700c0d00000d402d9200400600c50248522000342c185c2c003000d50744601d001d801180c6402617601c250440d90b110b0341640100d14402500141c160360340446014000c0c141240300c07400340c1c0d00410302c18205207100015841d0582000c200380d0b040b0701c0b41d6100c40c401c969906040040d181c000d000e11070204401007040c03201c18149003031124410003a00e0b01c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 437079109 1250 437077859 437077867
    0x1a090c040501200303011505070818033708070b040b010e181f020903070303170c04062010050103030203030702060f01080c0d020406030519120f0e0103050a09050d05 73
    0x400101148420000c80f40940c02110782e901115902008407419a1400701c504081c980400404580503c10341401800703c200100300d848540910301c0300c41c81d0a01089049800402e60b941c0c0d079005d010a5408101568150600300c012094001000c6055a81c06005070350f09142007038072070007074010080b0b03000c035049403a100041c0010a4000c8841750080c4501a0380a1005840c44c1c4450303444440504195100c4451800c05012000940441c0c0b0507400180a03180090750300c3c40d02030908060200360b10124043e01c17001a840f00c51140607035045800e41e03903826040c23108106100c0303081500d42c20004040c0c00303000f0b034004c03845215011341402580319a008594900e0b02000080c1850310140c1459101c0d90180010031110400107140c2500000803204100309255620000e0b00802e80343e8070060030f90107516030b240c048041c4011070f0f095960160365900540c3c0000d0720300b103441400c1c1c1c0814201042c60b00320101364552299104e0f660043c150701c0000792045654a5061401030390814031800250009 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 437080359 1250 437079109 437079119
    0x30103120914090106080910020a0504090609090809190f14010315060936060602070b03040b0406020f0c07180c1b0f03021501031a060f090a1a090c04 66
    0x60301e44000c1c000c10b034111504000d0705002a40c0c1030418450081004000004251b5041c2c0c240151144800d064a085540da80101c1d0060b28a030400e02c01c3d0304410380380c0800026000560b024418109070702c03d400701e06d00400b003c02c00103248000752a42121008460001c0348503008400148050013004403803003046188036000606036201341d06441c0390201c50300380401509030031132211801d591403658402105441020034084290b800a845008040603104000d0381c1100c60b0700080c141c5901e41d0030703074202d2a1148031401007488140c8000780070903010b40020300842c546070b024144840c0d41d988800c0c07030b040200c00f900e80341034201d80003e0803141c1e182280101003003441c0701c0c0d2941e41c0e000b0704144502c5440100c005042c0c011046000d8064408880340c0000c040c030038000d08140d10440080d640d0156102d051500b094040c0302010b080c901d00d0000411840d180ca002580c041d440000d1102030b50b5921461550007420780300081108508141ca4403000c1e030340da0362800b07500c1100100010f80d141c034500 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 437081609 1250 437080359 437080367
    0x3010308071e050313211a0a0e0601140a060c03020c060901030b060d0c0908070b0417010e0f1011191805040c110c06090d031b080d0c080c03010f18020f03010312 71
    0x705186c03400d080907881c1500d00058002c0d005080610728455400b045a6583c03611501414a41d030402c0c4050150304008100d0580c411504007030f054040d104502820f84034a016141c0c2c9210000140269101e00d1100003149007000081003008010316001c00c002d06903001141e0190030202c0380342401703501c640c00009101e9000c440100203110020017041400d04e84058000d1602c40c80c091482c800c01c0da48000405003000350001a0400e0200d021201c1e01c41704c0e20b29160300c41d0001075019025030b0600c1c1c0c00d0441660440c0035901400c0e22980c071310004410340182602c051540080e0f08046500c40c06000515076940e00c16040c2c1d0340707000d8540c104d40c4408181c199080400007480c00e84030717070801d02480c04241c031800c10f552003169060601c625040c400400714011115001801498508002480080400035400c0382c841e100d2151a0080c1545400c5d070031542e1400240120b8000c0c100c041002c200142c11111910200300c02428014501000030800d204142d001360030546800350400c964203107881d40 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 437082859 1250 437081609 437081639
    0xa1d010e091e0c090d08030a06030b040b071209021806010c0b2706010b0304150204030803311101050d060e070f0801090504031b02041e0c0f0503010308071e050313 72
    0x6036583d050310303203003984000814010b800d040207801c007032010000502060540d4448006150070841c11081480c1c240392075002c007903048442100080452180c03840d901c2542c0a00101c0550042035204110108a040d450a000c01484a4100925000201c0116500c1182240a4450303005516500301020b0000072091f0761100740940e0345e52100004000e22290740003520f03046644608040f06004c1c10134100341c0a07000f0b9030400b030101e000c00030601100111199070b01e4030002c061801d40e00512800c6081c400c2e5010884406004e4422000461803076600c280010f1810500070000064503e88650f01c20300001400c0303603214049104161701d03601540e0000b01c51801440c03014400e000030314160340c00800010014201400001403045880c0466544d0703000741c40300d000c60540203000000b80302d002d01c0c041d000072080b010110f111900ca9a9506105104480c140c94111100d1880c005603540d500c42620350101091020031008119440001c4091009240c03810400e0f02c45145942442c03400300600034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 437084109 1250 437082859 437082871
    0x7021605090108030d090c0312020c0103110c12030705070c03080c07150c030c030e0414100f060815010c05150106021204050d021003021c0e060109020a1d010e091e 72
    0x1480300041003035a400004445c00007022003001b1a080201e4502149100d9494000800341801c14103004100ca900050090460800340d8042c000d02181c1c802c0d024184c40317030520808168101d0814185100c880c4401913070400c1261410b18682485500c80b00e454415541007120507540024a14108420800c444c101500c060048450b50300d0400f031010301000c0c4841d13001002e21035a281028207060140035904010900a4810304c001e00810302180014081100c055100c00e000d1080491120041d48200050714126102c5121540390b009844e40c40b00e48042c0704a0403c480e0000041c0015424000350030603501c2c00b60b14a889504000d00a801c20242030f1503c103001170140020052983d9030a811402c294050310212000040d1200480c0640310340c0100c110460b00e480c0300c40790195902d81c41104113141d480140c0300300c0d0740c80720001b40691082c0c00040e00010484807040100c0d40640100e0652214141000c81400b000240410310200045800c2081040d030003c904000c0c00d00108100c0d40300d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 437085359 1250 437084109 437084119
    0x230d030902041a010225090c0c02010908070b0f0c07080123070305070e040c02070905160305060901050901150504030209180c0306010828021203040501120b0604092307021605 77
    0x43ca6250000790740c0c00a50078030645004e2810032440c402043d480c040409040888803d009000c0e0740f034009005400c140304101c0c00102203000010fa020000702e80b04040e80c610303914040c50070341185009801c503040407072170900e036015513840041d580d0700912601c8030080034441d207201d00641b51090240111300007070046007070505110400840e542c0c0800e03101c0040c0c400304e0380044c01c014400c80c00c81c5003900701d41080056925000c24041c02c1840c610342d10100e042c0d80d80c1c00780301c0b540d200400d000c1e0008007840358030b80003000c150051242d034903852101c0890b110a490200e080a90729000120b5000c400e5a520002c1c502d840486001800d0500c092100e440b802c1d0002d08182d490160007907500d8240c4480c54450200c0f078001e40185018015001c0240780d00201048130b642884500f990305c80d0710a208890104100d051120041940340c01400300581d8000c0025060070b140c04400c40c0503201c422500550403000c3d0340c1110003580c040b1480c500551a40d4024410f1090003910234802d00c01c2c1e9007100744a0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 437086609 1250 437085359 437085401
    0xe01080a030203040b03130c060210150f0515070816150207050a0b10080304090c0e011d130b0402130f05060c03070f05031209030a03060909020d230d03090204 70
    0x1c280c001044508a40519059550302d0391a4000000700303040400004003c0b00d400e400010326660b00180e48181c0081a00041240c0c1200c0c801c007482e2100141f04090780c0140f07515041000d4a07040003c00c100b641039019191410085546044040d0320080e800c5507542c2030420854180016030a04200c0a01d04c0001185046480c0e2545665030002c0c1d030b00248400c65100001da004c0ca500000d00c0001d0008030104c0b0348072503c8000c1c00000e803040d11100000240409031907511503115003d8800c0d401e0007405005d02018600701409034940054149814450300c954180096843d03500c01020f5404160000d1244603040c0711410819030318591101344100018000b442d810000803048504e010f51202c014a840503aa2070807900b1170144d003511491000d210000c0054000020000700280603007503400f08001908d80c0907040441c0c21081020350440384040b4a00c000502c1850b014400d4070008945250200f180904c061402141490000000c0d4485030350f030b03003142080e009040300d03c241d6150b08810 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 437087859 1250 437086609 437086613
    0x5032203030909231807081c020606090708040602040e0403030911040c121817180d080a030e0c100201020d0b091b0d09062d0c1e140c070e01080a 64
    0x5091208001c0520302403400700490400c01c2000b842000442480082c1c0c0c0c0c00710782e641f6102e03031592210300103030395415201c9a0b240c142500c041070091264000905510203030720340c414111401a4010001c4541c290308000205650315415540f0b8030441c480e903404184000f0b18903001e1500b075050300d14540142d080486a4a00d2600202c0c000040720386010700040c1444400000c201c0100c0451000c0c0510a00804850f01b070b10300c03503004060320040304240440d1100c1d0740060000c1e4100003d000b44c000d20060000c2400c0d680f0a0b0405101307080c0d14030882c2c040d0f082401c00038400025002c010000750b980000e9150400e40e46000306144203270211200078041c509450385545140045020034040c4030f00107103004407120680c1c4035461280e00302108005070080d4a0940d00201310004540d111842c00d007001029000e82d9010b81351500006669222103608203a0581680c1501000c1c20028000440c03544e0152022010244c107820074948010200341e807400b4034203443e100701a080300800c0d801440d24640 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 437089109 1250 437087859 437087891
    0x908060c0c0a06020304030302070c0e0103020f060a0c150e011508190515160905101d060d020c03030a061509141513030611040f1205032203030909 65
    0x2600c8048004120350715914010503a0030255588402821644040144018550300d6400350510510032101e1010040d1910742c1c0c0003011009100080d4080e0352449603440754104100508201401707801d00b141150f040380d40740c50081d45410612054142d480307214031203901d401d00400307025612504000300d5040c10b08416548860614404003804107907241036a08214003042080c105140d041b1081686045c03070342d989004030f05450785042c0024562030000c60039150540304141c100460f911081001b401441c03040000399038461906920200a20a0500414080c0014404422490080c50703032403800340ba5000854156400c240204841c02a00002060b0002181e0060382c1c02021150080d040f060001500c0280d900c41c0190381e0880812010b940c0200c2c00786140a90b0b10600050002d40010354080286010380e12807000b0b81007501d0810054541c0084402046602a0b01500d1802c01c02345084903e044e0094810150b4500010042060582c405a94006000038400610180f40103841000c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 437090359 1250 437089109 437089111
    0xd020901030b041b0305070e070912020d0206250218043507030f0921080c01021b071401030618020309010b04061e0509010305031b070504050c04080d090806 69
    0x202a621030b440841d080c0404244602440c00010340441c1036140c03286010740d00c40341107200d43c4181300306d48004220300b54002e510000a071020028920ba00260700d408220142001d9074050381c020108001c182401c460441000112480d608141403407418184180440c074000100b21075010384402d8140000290b41b400041e100082c07030079040e1105c0da4000141110b5005481d03d121031810000f400340708040d08092165034100301921038610a95a0702c60000544c140d100c00d201c0f00b41100a440300c00070740180c01403c0d20890b00c500050a019001c1165440400805461385c400c1d4041801048107400f10751200154000038a000c2c0107481c42c21088091841e10701c0c0164584640100c00603440d50400d6020001000008205011031507590f01120400c0002c0e890003100050003940100711801c084420b030b41200d50044c01140b4209500c40400031341a84000c0c00d41d030fa0701079010001500d035a18000c0e58007420807185001c0c0c0d29881c1c181c01c2441d0414003c8201d0920020135820000854041452 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 437091609 1250 437090359 437090363
    0x60e040308100b070b0a15031509080d050a0617010b060d1d0a0c0f170a0809011701060e09330604080f030c010e030c10020f0c1b01020c0d02090103 65
    0x785120703480340c80c2c12111100081d00440c1c0003a4001ca112010700040c4e03001c8502074068604108284440c403a0100440722480c00040e0a00d00d06039200c040e071200c1680040c01e01c501410740c080c1425804121201615425500d00e5040c03901d4144c1841840c4503400c9a44038080d101000300a0920010003007500d5004070b500c101c0070b42e84c1d0f0382102c0401200e8a60540c5685042e1029106c1920079490b0a0340083c80b47e0040f821607290016000c2102164033081c11100951000100282e220540c3c0716802907203c110240c5c1000600908083c0d02003101c4100c601906c5141c4529006105020a0000c40c160041040034540054104009005520941400d4450b0044d44144051a0702400715107140314580c000c11041c4144810a6101d5a000c4040d0a10050740c90081c440c501005401381e03564000e00d0700c101c7c0b654000108c040009d00140e80200011020002d06a040c0114001e025080056041c050340300304909091091071507a0600c880e405a03207044518402510450b0041401c2300d005001c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 437092859 1250 437091609 437091617
    0x201060504093914010c02040504030305180c06181f05031f0b120c0c1015050102030a0f030917070b0402010909020315010e18010b1306030203061507060b060d1a0301060e0403 77
    0x110300e80e45c0d03c14403101110a401400070300281c2090301d8018020141126881c40d10b8031298250810301d000481c051030b040600502081c01d00c0c2d044d004000c0200d14800825078800c0ba041d802c80e4180c2e10003107004481c3da003640c562507240d1030000741401c81828040c810324003046420700107111401000041d0344030301914a00c801010741c0c0d070582d07c220710303ca2000c000f2268803e40340240000e0b50b003600039841700000080703070304030b00380e40e030001641e4034054098400e000c00c0c00c80f40b507807400601c66446140d8143c000c0885203c0c64040c0f04100c4c2059010b420243c440800320010001035580141c01180204800c140840c91490403a00c0140410040036005040007120704a03c1096550500319601d0b281c0d801000c1c0445503541e228190f550741c004034410030800004003000030710350f0191080d240706c1c1c000503050700c240c100c15503030401e110b5205501c00c40b902c0742d88540070401c9440350340203032410040e0160300246910800580070024508072104c5031090b03061480520140c0074401e62035400542c1820 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 437094109 1250 437092859 437092889
    0x8070801060f081b042702090d0b25053703180b070305091203131e060623150703030506060f0304060209100c0308041202010605040939 60
    0x74804004941300d1440301540c020106010800d001300c40b00449840c441d0300314a5010900d021a0601640100710a10b60b00c000003050410104e01540380241d4098049034054000a1074900121500c44445030640c0001e2408180c2500030401901da07540310844540c1c1d416881c940c46c5089c12207004246104400f0140c0380c2c0c0001c03d0460b840308012882941c000b83c008800d2400c01001401000100d400442038855204805524290402224092403001184042c0e1044903143d4411003240044441e48980f20304012001003652481400c010f0107c080302c0c06103800d06041042184c0000ea00c10703610600070441c2c00880d58492408903022143d243c10b0104841d81c40e0400500180650682d030000000008100000c2007000d5004019005044034288401b0800103401c558003a00a003000b40420390301008640491034040c202c0d505d0102910020410f0782d00c2d00f0205050b10003040c800c8403540c0b034204c0c1c03655001c00d240b0030461801010020b14142081c0440807241000140e2260001c0391001003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 437095359 1250 437094109 437094121
    0xf0b0c04050109120b01061409031203040519080910050f03041b05011d24040810050a1103131103160e15060a0e040f11120a0506010c15240608070801060f08 69
    0x4810349c0e9040800070181d03a03500003421107141c4e543d03000701c1d8103c0d614001d20254604208804448030b000e01c0e0840c0f074046c1809547e00501400e62409500c0100388a8203004c1300c2d00b58280100114400c038800c0103510208540e807111041603141a401030790621540f4518038070300d810b107480084103c1404891100390100c41c40c500720f44250381a005c80180320000500840c0b0000d0018620304490b00c00881040265542280307182218245440115242c82c1000401d6180c01c03220401c50490380544c2201031896281c00000745003141811402c2940380c0c5c029400c120300508003100550140c0f402c1d0808040040c5c403000180903229050a8006100c00b00c480702410751902e034001c0c0c0140401c040c04100d0401c08503240300341d41c0c0080102c40784404000c030000b200401e003400703290f00600068561a00c0101565108500032581050303108070b56507a0412220b1a007440302c032011140c5503152000e089241801d00c01051010b000300ba0300c1c14440441c0040244a910600e8211210101d240c5210180c03503003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 437096609 1250 437095359 437095397
    0x3060708071d060405060304210c03080a23280e0c011206084806070816030c020a1202090a0c1b03090612140606070f0b0c04050109120b0106 62
    0x45d0005030b0005800f000300010030140064100461540c103180c0c41e1068216802101c0302c0646c204014000394020001c03540300c0c201600404074650040b1010a110003140ca40c00000d94401c46201e8420103e9055420f118072f20b00214041c001d154402c10702040e9141680301d591540b2a54019041004100c01444c440806a202001400060f01941c4030302d050b4030000c40b202c2081005001c1484000301200c140704d844081e9035201181103d03c640c044070b115000304241da4200320001c0e108201c0c10000c0650208107e40304034001d030f12a031907c04050a160040c0000d108854003c0000c1e40d04c0c001440300036a40c0c180c003681e44440d45400210303050340c001200700d8189e40741480c900c2503148880040030426402800711002e40f80c0d1a91502c80d4000c203881d4413400d4a4016800403803183da81d5022640352b0410b840180f851074064015005085079076503c071028050221116041c00c803003c00d050060390781c403400e41802828402c001d003c4400e01600c4054080300188078400030310000d802d40428013015 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 437097859 1250 437096609 437096617
    0x60c080d0509070e07020f0d1413150305011a070609080d0e0c03101e020c0a15050a0b0103090503030f0406150906080706020f07090e0a080c0c03060708071d06 70
    0x81020710541c209010190f68841c01800340090945001000802d51440020580c6002040400801e510190300405603040e280418068080c42420410800a0301d020550300b80185010b02040019104041000f012608181c0100c0040c42900d001150842000c034103541009400c10000280400c1c1031411103101d1160b811010070440c1092112040c1400200300c1030381d46030040c0c1c00d40d00302c000c2c3c0c041d11400300c41c42c82a245101404082c0c01a069090f1a409042c00c4403a144c00c5444242503522280d00001078004580d074003c0d2128100468686203000f6600a188217007001d11021915540d019201e003c010280650b0081040000341030022136004100320b902041e03010801d054440d18034002404a41c00380c02e159110721040020014030004918203e2240b1102402c8030381c0c1010022000351451131243d1010784100c03412000840c1c0c090000702044403800300181a503201070000c3c50704042c40240380c2e03018040030307000f08050b0759040740440b8030030110070b03402c10449a840d40c001005405 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 437099109 1250 437097859 437097877
    0x120605040e0307030305070203030709030f080d14090f03040e0103031d1509190f0506210a091a010f0b0a0915030c021903021509100903050913090c060c08 68
    0x1040001c500c1000d4004401024490b000340c0e0203000940e110b800c140da4070312058417842c0009600040400126444c401091891071240c911a880c100d11082c0c0182507176403500c0c0c000c81240c1d4903400c2c040d642e401080500b5007444500050b42c1030618020b460f403598101440040c013441300021603030b2810007110502c4500e002c0000c001010010b0800411401354201b8001180500c0044400f1480702207207499400031035885005480000d030400c1d05000d100e410100381035138000710a03107101a180003034481c44ca2140084001c0042e02075054144410000c0020801c03d01803c458001441101008802a41a81c85100e101960f03012007290450781e00c400c56100001c1074405042102003181d058100301000d400d0f981c21901d610351302203456a441880f6400040242c0d0140e0841601070743c01542541c2c2c010601401e441009121f2840c0c8402d0300c40b141000c400080d80011800713054903210030820340700c100b0b0303600404c003403103055980c10526001b03409002c0600a9200111041040450803146004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 437100359 1250 437099109 437099111
    0x712020d0e030310080c06030718080f0a02040f0203060f1c0803010b03010e0108121207030902030d02010f06060c0c03151514040b121e030c07030c0512010c050a12060504 75
    0x202104826502d980040e900301c0202d03002d0143c00030f505880011429070b001c2004243c1403668580703060130386910b5510b0381d075403400750b0b840c40c1c000440c640e0500c180d248550507070000d0046114a8410030040f5042143ea0080052062083c400b40f901c4910b8200d05005094505818007810302c0a41e1103411000c00d4000e064020010000c0b8400c0750201c09035040324881c2500309003990301c40200e04e86641180725017500000050041c030b51a560045c00360364200c259424001303180101c5401190400984d21000c80160391608070102c0961068442d00307005007200e14001c20090070350354618041c5000b42c071015103519008401080142942d5100312a51801e036622111a96901c0c07504078900340841d1012071045250089120350f84c100b400342d0152003030420010303220307e00e42800c05c54440307203601814901a21080c0003102908400f0070101c4080c0d40111408d01c4824130785410001c80e215090b022202a0341001044599207411900b0f0b140c08494500345814061001d101090040140703034040340d805 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 437101609 1250 437100359 437100371
    0x2150c0a170c0d0c060f02031b0304111017010f050d0305030a0213080f0709181e140a020405181509030c100603110117060f060d050a050108160305060712020d 70
    0x454000304e403500c86600c00d00040c0258507110540004a00040710024850341400c1c10b2a0f03601da80e0721004560017845a00c584080f00e1000000c01c20180e034a0300003e000c51700c042c00c0070110301000c00300d9500401868403a070440c42d00f0300002c20400ac3c0c254000a0030b008010021805800303182d01542d826a6004c0e180700a07040e42c0b21044d95a4802c480720f0344020b8040e01802290343ca40e60700614256004952070042403610310364a21646581ca42c143c45d40e908100110000010710740785198410126010060506184a004010880b03402508070f4140d400c0c01d1050400302031011406400508034206001001d59848001c5800c51003500741001c890b00036a5035841905100e94486429a4028018564410003810054070310040c40220082400d41800005055117004c10076035100030409444035040c61580c00c0d074002a20001e48031250030302e0701e84006100203442000051480e54461608001d82407554441c03030344076900030782aa0308110341421014643c21741901150b015a81c001310030801 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 437102859 1250 437101609 437101633
    0x60f13020c012c03030105150a03090b0c0405190810090201170a0c080f06130f0609090602120c0f030105040504020d08071103010b0f13090201030e0a0605010302150c0a170c 76
    0x301c00d00003414007012000412403480d203d000050340d06036036014040001143c500d56034190389800a17413a1004140e291500080040c88048641c0e020b408048450364031a030404041102900c001186065401c0e0035501c104046c900014404015911045001401c40030f50700040761500f0301c0ea2070b14540300b025141880800b5a843d0b00c0303a8240f17481592900300ea9141d8026840f6400350642c5d051303510090380d4859103070a8520354409004218540e00000e51150b40700040f106850086005a802550105071802c0d500d10b0104241c1e4001c4071010307000e18202c410300b17100d040f501060084a021700e136103c00050440d111001503008440e00084a80d8a450b4145028050324690484850281d403c00c2c5d5a20b80c2810200c01042600c8e100914a00c4003c428000c1a00100a0a030041e41090385500c0800c805100c2400f4041c4e00d00d00400002c5040d43c1540140000c407085581030404070501000001281c08000c152000482e0780000c0641c2c44030400346000e03a4030f000d1441c6c1c4242e203028005e05428 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 437104109 1250 437102859 437102891
    0xb0304030c1101140a141603090314060408040e0603030906182e030209040204051f080112020a030b1503100b010216030c0b1b010f020a1106060f13020c01 68
    0x403860710aa09048540030702c14011a00d40e01004d200c4c5a07000c3d02071081110321405021107900c0c1c85920700c191401e190030794020b15421100c1c01000d901041c5065000d0040c4041c100c40c4140101000e00204603905166888207101d2240344182c402403462a0040342c0181d0701802141c01c01c00000f06055110080c1b00c4409078440382203035050748908450b030000383c101e642c501030911100014481040000d6100784082e0040e502c9120348076402542000007142c0c55840c0019880c0d40d20068039211052241c0070405019580c041c2c000c00380003400c05119030300507510800c005080e030354008040101c44d154889144090100c2ea20603a41c1800384007411414425140e02410043e8002d0b401c4a80303859032071401d0010004280005010019000810b200024900c401000400d9006031301d5081c01040035034071400c4403071305103900f1a1150005090f10400c0d5002210004010b0b0034005003040e8205680041c00140340c007c0c060307025241d10f400c50b4006025030350668800c941031030003d2006c291846220784c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 437105359 1250 437104109 437104127
    0x10e070f170705150a0c150f0b010f0f0c050c0a0f03030909021e0a031e0f06140d0b070507050102070c14041415010509030a060c1107060905090c04090c09032003030301140a0b030403 80
    0x80102d01d4682427916562107400f04400c200f803180c841c0000156285421500000310800c1554188a50b417100c441a48030030040a00500001100451183c2103140c01080c05495030b201c125170a0051065600311113001a40c5d603810410f41654a0766007560500c2540a0140130301d5005851030484036079108602c89030482074281d400d17818208005a100e0328121512002c903880190004041107865002640321902da5810880c503051460504825540e15826613201800440d000e4191502c2041068044600400380d210b003190103004281c41109505104a4000c11301001d0841180400c011a40030700c080354480007019042e00d1005016080070390140080030f14105c0041c00e00458410540804100d000640d2604c0e034904081a00c0e00040281d220005400c2e0b100303100c020840051010701c18400c480b885012034541d102c00703034a5401c107010308982407601481002c08030240025103550100c201d0703040d24a144400700c02000f80308040780c811100e6800800b0803050005c2804245a0400420 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 437106609 1250 437105359 437105381
    0x30e060907050a0603090c0b03040614070509040b0a0b3c0712080408030103060b13050112120504140d15090b041416030b09010e070f170705150a0c15 66
    0x840503e5a5501c0803011181400303400b8081c001108824083c910100d402035401c90300403107001c240c0c581c0408030502c451a099a5a41c08100000350f002c26a0030031740189010980100d609940492405d8081c0d400c1e84070301d490810f0703a4038040220008010b5000910441204404031040d0042072341c000368220f5900c101e000340c554085042c11044181d1160a0844c4101c0e030010f500c0c0d0459286607078640c02360800c0c000c1c50303620030b22540468522102510030f40f402401c00c2d00781c00350700c0c200c0c1c1c1c100307076508551142e50802080381c100014806820800e04089520340140c0f0079050070105030601c030903040800c504c0080c03007500302180e00c01400764a000c09030085024031006802c00c464194030681d20320b9a00340034400c140680c541000800d9846180329400282d920000c50070000b029042d80c10203000d500007004000440b503052024006005200b0180c1c0407410040c032402e414400052000d41d00310301d0150704c0c070400040d20032200303101e001015400f0790f004060a0840d1108a0701c44085e000e041a9 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 437107859 1250 437106609 437106619
    0x3040602060c070f08361f2016091d0f100515090106050315040203060916050f0d020409230f130b0906040b010f0321030e06090705 58
    0x4100b40c01600300403156841d43c030615003402c00c103c81d035034a10b094200301c42860841d9880ca9900340405048071240700d11018080301e1810103910b8004001c030410340300c2c8440041d144040c02c40503001e904030321241c64904220075185124200c00c80c8031468406260040c10f03408103903240003da61200c40d04500d94400031090250240c4203414002503a92002406041541d444040c1c501c2040c2d20540c04507401207a00f001c80030301e4103040008209010001c0c0d2083c400074200008120300e00f01ca12882d1040e40608607025895418200005581200080c0048100200c65016121090300840894040e07158040b640ba07252900c0d0215407009400501c01c0c035142c1424041c4103c0e01000100130007400044501110000d911040c0300c00d05003c5000b40300c246003020803201c02c0c0100d030b22602054401c81c1c0640081403a8509481c01e030030b03000d070706900600b0380490100382480000c94103e01d000e9001e140822a07142c010306200100d0180101c1c040c01800707400751605020030441c0c0420950203460342507807 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 437109109 1250 437107859 437107861
    0x9060b01050f0f09040204050316050f04021303020f01030b130615091d0603071703180609030604060e010f05041101020106080c1c0203010b030d110d0c0807030302090a170304060206 80
    0x107441c94441d026245422981c10042080c203d2032900241601d080301900050505440d003020a1400f0603482d180d44c0764a0845204100c2d9280494140500d518251019401d100c1c8001322090700e050300b804028480d644864441e20940d06c40d50102d07100d94002404ca01141440c50b400c1f074010301d500d02903d00a005d000d0207918a071400340d0000c42c2114cc00c2030315100380c01c9400c0003a00d1010400380c0191743c503001700c240c00030f1610311a48076044019000b00c05142e4070308048450303c29100f910381e03c0394000e62051080c110240d0700440e1165026401000c041540b0b441080780500602c54503600f4907009103058244024050030b00300480f074940c82a0020000c207620b840207550f076070404908485e400410b000c0e50410100501c07002c500b000e8405070010400800103070029041c1922215400000b800c15490071124500802103c2d0320804141030200d500c05e115140c5c0304203440b07070700000b5003450340001d2083e123940c07580c2d21400020042c6a101040e0096100241d6407a98130502c148d10052084070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 437110359 1250 437109109 437109131
    0xb100902090108040f0f0c15020f070b03061c0c1205060a0605030d0e04021b0a0312020f030402150c10050a0609140106030c02030d0c0513090513080c03040314010906 73
    0x1100722003642005840b0b4072500c3d40c80355260070000c14410012144c3c044806001c800180e041e0b401e040162903020b44d201690101010000d00d80003c0f40030343c01d2180c0c85201c04000c3c80c6010412607401c0501610555208858078415100f8944143e100501c114813010001903111400001e11060f21b104400303907a059265480000103503491400742540c03640062890f0740d03d55005025062178050702800140c200700154a03051281000601149510b80103088a2010540d009280720f074003400020b81182400105c0210b40098000200000e0003810131020302007003c0310101c141c81c0300170b114500702c3d203042803070079108406440184d5401d00142c0c1800030103c5c4680342c50003001c81c0c11401005250309070703182c828201c0241030340f60300910a5000401c0102e0002d121030181060a2407581c03215540d5200c148107a080011807980001c01541c07400041c44900c141c02408482c140f81c100f401140c4030350070703088814254403a41d80000d0020303030a915400c0e450740c010f40040c1c0c80c460148104204065200c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 437111609 1250 437110359 437110361
    0xc071706070306231c020a030f0b0603030415030510120f0204051008030d0221040317310201050c0a0605010e0f0f1603200309070f05010203040605071a01030b1009 72
    0x807144c0c41e10500d811840c84a002e04000551a060000550001c0114122a00801c2030f600c1309030419101d00b622800b00c58144404900025081803069005619003840c10403504101c03004450f0040426032143d000c541c01803102450301018040d120106c4003072280f1032405a16040304480e08070300441c10280000c040b41903d6420000300ca40c60006146407140c1c0b80c05000081d0700541c0d20502d4a21788144d05044074401d81c100c02d1081c0d10a44038000300c029001044070034441d00a000c0b045e44010100b944413551480c8003203061961200e40303040406200c61005035100d002c1c1c1070071808035105d5a01d54009026207604550b040f6140306078212000d44960710181c081d4001102c10f80700503176145001c60f0240d00308034030000207040d441c68000380003485c1007007c40600e210b110b1581240c2001000b4402070038005d01c6028004c20b4598520040a444c002c0040c0d180d0141d40300340000e2150119000d4240580c0805042d070710742c600748084c092582c5a01c0c040c15803400a843e011680100024041400310207 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 437112859 1250 437111609 437111639
    0x150c0c07090213030206030c0d0905070801050a02041a070c0e130c150905090c0d0c08070f3006080d020d021c080604090201120c02030405030c03210c071706070306 72
    0xc8a003c1070b00241141c003480300315400941007403900b07501042001d20f05103803031080d4805d8512071000303030840e02d1600c56440d007900c802804070117045104000400c040c80110f8800040d00c010940c990fa214425400d10380582c1005900844d51301d407800c81001800040390001d6030741c0c1480350115aa00c07170348410b0034550001d042c18800d404544031542c24800ca260160304540c2c442c2410b1086ca292034140d2100f1400c0c0d031255004032020601244c10320a00030307004441841c0101c800e1030280340321102a5510720b590410ba030725040014001152554001e112030f0018401750407044101c60002581c00e100943e070300300b05050040103004d0010040180241c036078021003000390507134551314192281400c100050242a008a041c40b022440400744401640030340c0c068624140c0141da1074034070f400c2c1414106000f00740d440340b09410602580b11441c2980340036070110611600d0071a207031003580321458680384854002d01c02c24201c000f41c0610112001641d90302c9404c0d00c2e5000c4c00b00a030346550b40c0e050101 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 437114109 1250 437112859 437112877
    0x601110604050d2001020c0309130e0601180207050a05030a1808060106050a0c0525060207081b150c0a03170103110d06060f0b030a05071107030b09150c0c070902 71
    0x880c0b20703203103041c3d4070850b034090101300481204411000e802c0941405c82e80a681d9800d0346400205000c150303850010b04140030101140c4040c4a82400240010f4a510301402040340d626441484078550320300e241e041c1d03a0010b9001c000c40d100200d071820710b05d99942041c0322141c001505410084040525154400b0868110394014800c1c0e900707064058469410071680c01d010484030100f1003011803000c000e0881c03401e90b106100d0003094055101100c040c0c9664020718155030114a04010350304002a545a80481c007480c1c0304e8920035900c0c00102c2108030140ea034051040f010030750b192401008995100081c2c40380d1150040704001040c0503403625000d10000d0a606103401202c0410300f4158510071078503100c6da00000703605845031032405006450780c01242c1e6502004c000c02c00100c21600c40e454201180e403c240305410322010304666294280d000061460851101160180700208038403544000c0c0007c04c0b0a807803515800d030300080d03004075164a00c00d1184950000304041c1d10b01c2114103c0c2 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 437115359 1250 437114109 437114113
    0x160204180201080c0703140a0c020a08030f040302120c090903030f0622021e0d0902040501090b0906120111030a2406050a03110408010c020f06010905010f0e150d0b060111060405 78
    0x5580c10061341d8807a00040e906405100c2d0425102c59141c082100078102282c180d19065001d034a01d005110211005400980702c650040144540d281601c8065800307c0350f04541d9440c034000e41c0c42c1680d041c074602074545604480011305000001002001075445405d044240c40d80310396a081c104206030340c909182022502d4101100440d54549030000c001d490000315a035961a4075002560030f0a80c003a00c007084105030b0b610040004c61410340502e074010b1030440c40510000c4081000a0301c50000549958403d020100e02c80d40301c8003088d0000748102101c807640e50345900c1e0502103c1e000d8807a01408071070840206000d558075020501070641500c00f030356070b11401d00c80600010340040240c00c03070119200c54280130000b00382c41300f40a4100c40d07840c181c0c0504811184560403916142c011303004080b001d428840184400c51000c0c030110f0032515100014952a00c0300511803c1c8a0340d8140800e820881555606003800000241b0a00403102030780d40010f07507252248a29240d00c420b1380c004010b9 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 437116609 1250 437115359 437115361
    0x2a091627060c02040914061e220201020a060603030e04060e1312020a0b0a0e1e0307030f05040308120415090302211c050601021209010e1e0616020418020108 69
    0x403442000034070b00707091010b040000e81c5909030b04d070070b031650340e10301c500701065840402048540c0000c1254021000085240f003501c03402e06060f0f07640b401c000c0700e00100152002402d00c0301960b10030011496850f800c0001004102d850303040041ca5403602c80d00f0180914240007000415200380c0305928030403038981c8440c0707140501c140e5403107a43c1103000b041c0e001144102c00240020403040fa11160003001614000a00031400d4003030300d4145001c040302a00c255901207418580321201100b202c9815038035240030000d9000d0f1483c10344150146400290030040046001c42c1c0401200c0095401140220701e485014440041401c041d502810030060068103c3e091200f41350304c25085004502101800c02410080c1c010b11480005180003200c601460700d03841800303010758041c841c0a014a007203200807441c14081000107403030440a840740c00c5c05009510122041d215486281181d503500003000d02da80d4440c044038010f103003038400c07005070301c2146090300341d4003151151242240c1e05079060310740e0052 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 437117859 1250 437116609 437116619
    0x504030b061509040c020319020109021f02011b05090f040b06040e04060f110a03140103120503191802090112121d0405040b0f0601030507022a091627 66
    0x821102c10760b44910b82c52041c81124203655890060865103480d55000390386407050115000040d0035091201011740e45400309000140c3c40362030a00c0c3c41d4410213900d50300034291141c0c0c104d00400c2401569864849010b0b410200d15501034018002080c04a0300c10170001d403040700304800c69511100042c3d103c0c070b080104200c0001a0030003190b0050090030001035054001403450145c9265039100b0f02c0c8076100154000245815100380750309101c089007550429810359031282c641003a034a2182040c0200800059051309482000c0182d00040b10b07070034890803401c90400300c072444840804a100b0400b840001c58619030f440b10342d95074543c21040c3d00c5400c0020309001d031000c066000c0e803800b001c8048a01c1c0092a01e5601a460003107124140980e80707881c00e041c2e4041c42c40c1021b0032807030406060405001c1540d50010b6008070745215041ca0003c64114521420303880c100710052581c00c10241c60030000c84205182e412003100707406884d118210010b1109152402032881914128a00c1800007889 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 437119109 1250 437117859 437117869
    0x3210f0f0106120f0b030303040605060a0b0708070b0a0b0d060c1202030c090f011b0c15020307050c041e090503030a18080a05031801020d0c0216050117090a0c23010504030b06 77
    0x294021100a0000d032040e20720003c02e00350323841114199625611001400a40e05140090700002c2c0700d10102c0c43d0800340301340e0710719109114802018002996810100f205200d0541c040301001c48000c001d140c07406c8807407900a0117010024041300104406d200b080ca0700840c1c07802241c0c880c500344e000c1310380340c0388a02080221072400c80a006041010040c8807003060644960301c1d5580301e028080c2034940700d103000c00c0000041100505002150801c0c04140c000800000307a404034000202e5000c17070350b03991400c3d00555848400341d601d050f060402000c0c6003030100210040d809144460801e12080343c06164518090880000060240e0360412220240522a2002d140c000460303108510034807800d955640c1c03e82e009914001e441c0c660390098a080300f50108215501005000b50241c0c5482ca0040042c11381101e003074429a41081c101c0c00920040b000348030f1201171a603c1542405c0640e1503190724005c180b50030307005031480030310000d656a482d0300a209070b40413240e11207405010759843c18203000d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 437120359 1250 437119109 437119121
    0xd08010b0a0504080d110c04020909060409021507030503060405011d01031b0314030a02010606210b0301090c080d0f0513171609020703030b0a03032003210f0f010612 73
    0x20402c4000e1002156070b810602c10f84480e14102d54071401c1d2031b2000300165080c541c1524940d4071a0348100000340b800e07112240782c99070190040f07070700085030340150000c5242500724250b03480d40d1a00c0002d4404c1010b40100246010314400d07039040040d40e80b80e6403550400074600b8070845100404500400010b0003141000c04058040140308400c3d5680340e9419210420b1550566045d41001c54151003160b030911074078004014516010b0401605810b080b840e4401e419000000e0342e450b08000b00c81c9803801d4016030302c2035602c820100c100c5595618115180d04003110b00e0303400540b1a041e0b20300b13001d216a0603031381001041040020b4141c80c0050403514084c040054007014000c040e2038441c15003440001d080144292070004d60303911071a1800038102c6044044262003030b060601b0a00100b64440110304080c12041d5000c40d60209903100c5601d0360240600c00301d00b14240040c0c0130002c0d04504105402010b030b942160850f0b884601900345010400d001e9a000500b10150420100302c0300d401c40 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 437121609 1250 437120359 437120377
    0x504031e0b06191203030f0b0103052203090e090304081c08240a030308150312090d02120703060605040b01081e0a060305071511190615090e0a030906020d08010b 71
    0x10180113076070f2006401848221036095000c40c2d5143c81e2603901040324000c0049000c402d1a0400c624501940307942c81e07003904800ea151f982088a442c00c030415025486d0800508006900c004d5a03181151005550350311600500c0f8880c05a50410300710400081800e0301112400e844000c1e5958521000c482c0000c01c1304503040a0b0045036001305103e0711000d5000000d103004c4da0720b9002d82d14002142d40341d801c0d02094054040c0c0d00c82080407004990780b0b015200007210490b580d10018a803070002a03440705052a1024850140750303400030422a0a0340440200c07a8152010b100e144070fa04015200c50307000700d941444021046045201c00d4001c40b0710b55074040d40040b0006005511398850b00d2508079190082d400b2000e041d440251001e82022452204956010040170719403c209200340000c0d503000c500400c100d07200c4490118602000c241580546582c6208000c0030242c1d00384c1e10740e20a20704005402040c81c4550118500c2d201041806080e45e05403540740040e480c105200c0302e241d02003218 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 437122859 1250 437121609 437121649
    0xb07030c170d050403020a061b0c060e03090a09060806010504060b09010f20060619030812190e0a1104060602030a08060a090606050d0f0b0d151b0504031e0b06 70
    0x70410b02c0d4078441c032555000314040d5000b44076401080c40d0903002c50302010072000d12202030813484a6001d900c001c07003144444e071100012950032580c45010b4a14081c10321007980c040c0310f804010034410380ca988040700312411038048640c0f50f40c2e624184011070b82d56000c0d00011060801400c4840c0d400380c1d0f01446c440c2c4852a01d2003200d40908418280002098041c003803a4111800340031301860714400007084140d100d80187c1c4420f24640e40e03c1210311426495010021002c00000c543c021a0f50f004000c004510b00300b803150060045180d41c85805d4418116503840e0101501442c0c0c0c1084d10680d02601c0c52900150314010126800380c400800040900c1da204024070740105159100c0c2c001c4100911081d2182d5440b0000200202c098641403c820002c80f841c0c0341500c003072690341580083d1040d0308080760b03c1103030740303940c981c10b0240034240310a9252124000a03050007590140c001c2c011a4002ca041c68201c0401c1d1030002010189001c01501d06000c11002c601c0c285440f050b110151242162 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 437124109 1250 437122859 437122867
    0x103020a210902041d03031b040305030a090e0a06080705040b0607080d0e190f020108090a0501240905010b030c13032f09070c06020a03141009060b07030c17 69
    0xc1c2500111a010060445030388400218046081c2030040344884c0c035004945200004540003070641c1da0000030640480c00120340f0203940d00407101c0c0c1c2240c007d1074020064076a00d100580d030240c80300d03c41d84a1040320020031800a800740130715110380010307a00c1200c041d100541c641000c0101a02d11440d11030b900c000100000000103120000402c031616503444c0208418030406031242c200602540c00103d07090f000310f00400026083c100751201150309003810252615440c540501e82188032800504a40c03074900b464464001e880354803440140d10908058841c0e40781c030b003860140c48081c8100c0003905000d10100703242580c1c60000d441c01000608060800782e94135103400c08081c42c10002c1104020842c0005507541d045109441202d03801540c00d4119410b01180003005480c00002c003030801940464100d070610711035081504000c0500c48244e4081c2404001004a500c01d40302e00342c40c0510340b21740003909642c00c0003131f0750300c0e1a00340d2142d1f015682191101c8410812484004146201c200 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 437125359 1250 437124109 437124137
    0x1050a080f1002031b040e010501020c09040f030305040f08120f060a0b030f1308040902031f0302011e02071715070201060e160309020616060606020303090c040e0a080703081b16020103020a 83
    0x5d80039000820310110307069120352600c8000b900380402c98001742d0248025004100104e0500e00860420a5041c98005416929400c2880c2c200401c0c4c000200042c0000a01001c0032180c1c00440d40240c00c106c0390070142d234039144204000040c003403040340010f500500018440820003002c0c0d07a40f0203d10b81d0a004000450341d035108490b030064000d1000c003a804002d0003010560100c1c407800441c2c01c00300c0c1c00c480ea803d54002030b10300c8444040c03807480110210429003480e80301b800044002c1495900d07860381c16440f480d60a8607200800341d95003901c007030300c03001406c80ca105004260484034a543d1445086d161840800d044140350b0125070185030b01c580100c0b0042e203e0000401c218500079107032100301641c524180301525001e03842842194400e100b800160301c008601c2058a2804881c001611110b80006600745400600003a00c903240c0032544105058008002910400e00000c002e070175450418ac440403680135000640d1004001b0440a10055010b070b4000e059885080c18400100309c2e0380 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 437126609 1250 437125359 437125411
    0x4172d1b0a030c030b160e0a12020f0907020a050f1c11010e060c040305100507090b0d15030317070f020a02120c04060621020f0906160b0f01050a080f100203 69
    0x242d0003111740700340303603020410b025015103000005c4412911384050300701e00c1000001c0758040c0a015031101e08001109080440d80c0ea840c100d204220040d051455a01d003000b40a503c4034642041601c2c68003038482801c843d8000800c202490b0700384103d4034415007581d2401141d10b9104103400d62569943e510031400114001c110303540c412134076003e901c3d0b516800c0d4504113052003200c6218403041c0c0e0619044c080403540003440340301a07910710040c480d141d031000381d0302d40e000e44a06401c10305030800851000c401e056000d12211542d070721444500d000380d100d50b00100c4213075842000380070050708148101d1006144c1211542c580300d600f0002c0310650210f03100081e0131030392144d2006000c14134041c032905040c40038100c0d040f00810301441c11402d1450401c04502644155562944107010000b0082148019502d6502241d83c00c1020007603145081403030002e0814081c0100c0e031003003400d0070740051b447c00002a00c0754036002c01000741440c080400b0400d0041c0d00050084074500190701c80010b01c0300ca903 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 437127859 1250 437126609 437126633
    0x306050619021e0a0311030309060619050a0306060e01170a020d1a1312030204061d180c07151802010c020406150207140913030f0504172d1b0a03 64
    0x80880984035943d600e05e0064030402c50662640082c1c2c10600070495414008600780750b1012064500d4891007513104071000d44401940c02c480c0c0c0c0804600c10100502c282580328805a0b041120340d03800e16600c414005000070740164080410b035200c01071110042c01c24442882001d031260240c510764107040034807120400403c50f0011191000321500d5802e004180e480300c00c006e58203043c02c40ca0035050040003030232180030710351751179000740c0300891411340351034411000300904d81800d000481424400000e2055034001401070b1032000c2c80780002024812640300d03030803602010301c071414842a041d9006462044040e00143e07400b5030384030000100b01c00300d401e201c50f140314258054503040342800c0508603d00d48103a0101c1c011a800400c00441d1460710054114054040c104180040c2c1d0039581107583d446103420501d19120362010b842a9003400080500e404194000300c5103208a4614040c0c0c402407400410304546c0d442000e03414000008809007000081020f094260303659180c0e118280d4142d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 437129109 1250 437127859 437127913
    0x302060901050709060207060e03030712180f36230f0601020303060d080906040303030c110a0206090d0507030b1812030709090506010c02040908031501030605061902 73
    0x19000c000c5546420302c01c241d8070442c6400c10f469002e0a0482c0203607655014010b52050104496034244299800c00556502ca82e000010350060084150000e100350001e0040c651041c046010205400c0e42c1c410101098a8070086103900d4008000e802c0340e68910409410705143c1c00500e00300b14200c66501849a5000c50185000e031410381d280300031006408000c00c5810741540c0e02091040b07503170307003c01100d421504c01c542c01c00c8003490604100d070103445400401940700c40c0010b00001055003503041604404010703291241e519090024075a2070300c0440703034001e6002d202004107242c1c0d4580051681d401601540171240101e42382d5881c0072000b10261202c011004801e10703840000c01c0d04000da121684400c50050b070560070800c0b00580581410700030580704540380c50001e0aa03034450300e08424516001401881602040d06115105500c16a07c4028120010010b0030195000c0d020706800c90f074002e0316083c5810190b1f0320300c0d04944140e101c0322085001d0b10780e45009200600e260038084107 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 437130359 1250 437129109 437129113
    0x190f0c0b07200a02060306040507020f0105010f0312020f0a080c0f06011d09030a0206130f022d030313050607030216080705030c090c0a0c0201121d0f011e15120302 72
    0x14541511034100b02070401c89611003a44503010388801a2070705002d494009909031004245511040710a9003401c842d41c9148cc1c0a6107003c0c00010260000b0303055000300c07400380041081d06407241404980b91407401c1a1403482da03002c17541c01400521500300410031010600c003501c60040c1d2039402139040000a901241c41000700100d0b8444048503c8051a0051156401140f4100100c00013a4407204000c01154014000c0080041032040c1c92103414029980140002c4100000035440308031218154071b14a6509020f1100d0400c074203000084500244942c030f201380d810b9252004101e0248e000362011000c50107501d041c017008143d82c0d500c4d5070103040c060001e0001c150a010915240646403c000f621a80040060201444842c0c04580940c0d1443c94040f10811071400182c800c5052038012611091034034404940c007507600da1100240c82c180d2000c0e90580810841550309842d90615502c5160003140003481e030aa8091384140d00da4401d0b0b070452909141c1d12045c0d03202e0612010740a801503 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 437131609 1250 437130359 437130377
    0x111010c021f0c17040602040e07050c010c02010b060d051b07051506030d080c090a05190608010806040b0115030b060a0807080709080c06160212070e0903190f0c0b07 73
    0x420154002c6621440002900700081c4480e150020122140c031149820700303030340c484c020070148200b0740c04540142c0521440d108081c2020040200386600c005002c2299518045e100400c461042c010300b40885c900034502400c00440010160042034060314490f4a088042e640210004030000039140060103003001d005800c408002644240c40c00500c03803032080d0015001c0352501c98101e6803203a00120041c48080c3c80f0719003032010541024054000507400158524502180c84c0c42c10301c040c0903102daa58501000d641e8035400b8541d10141034400030004070790340300141302e168a0071805039200b40e842d14011881d0300500010a00c550300c0451a01c1c0021965020408010340140aa03500000c0b180760050080c0c0c80c003040c050729203150060300b80c81110b0004108004100c02180030003590b07002003000640d88101100d80e0368a409620a258179220368070b002514a03840441629a01140d0702200100040c0d503500490f2030b8420040e110050044020302603003c02d07a0013002c0f5101d4156034881c503c003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 437132859 1250 437131609 437131633
    0x60e011e0918054b150105041d1b0d051006022109012102070507300f050a030f0801090204061d0406030b040b070e040902030a0b060111010c02 63
    0x440451403500082c9420001071002c4620030070780308840070142030484800800b04a440d10b2081c6500e2180003010569a80d402d1250400e80d00b8050041410308000040c04080070010341d100d00031407061119180340600e000950706102c0e0501070b48050032500160104410b107100d644c00307801c24001c450125a0399000c028900041c20340210203400c0500044c5803030391311401194000311900640100c600c40100b4179600036402130b10b0014443c10180405191002c01424220094010180075681032240c4403000821076070040100480d5a614406003680208200100b03a00740456001200c10201c02905240410014001b40040d54441e50301d11018005400008284202c185c00014031280304000400400360005010201d4811304203001d00e040e40c50a00040080000d944058048801c503c00c002c1007206500c0380c188540394030b488030715040540ca810301c82100d07180040250140e0103102c620011400701d081241e400541490210300d0340b501054042e00f0b40d000c1d180101c025900290f4103102d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 437134109 1250 437132859 437132879
    0x40510080316020f15031314030705010b0406090c091203050d0c05030403080610050d0e120c03040602120316030914010f060611010912050a05190507022404060e011e09 74
    0x6184e11003111032002e5401c80318a01d400078030024060381e00718040d1000180802c46c100b1041e1445050b20001d0b0380d12204c1509140e07005e040b02d40c064902c25440c00c44045800e010318820b0302c2140d0000d694400300c06003070421080302c10000c0e450607028000248111101c0d042c450150108100c560390703405c0d449092034030f805840f109015140c14030a6041c07060210503107174041705455000440f024003042c001d00040c110780c10b080c40034188888209002031640d4034940000300070011501154222075410140c0d008080b0070380026241561080ca51003209042c90744203401200c40c0314010a03c00b90b0810500500500f10382c1c1c1c00511305c41444e00c0b54410820340b030308010360780c3d440000c1100034002002e103561100074170b94988490805000c404900504401d00c83c006030b42c0402c03244030454100001c00d1001500321303086078104038482c0f0071403d040700354000c1a401c101c0e62030b1000c013400da05060030083d0a030750340c02c0d0880000d4100148002c0030b00c6c82c000c448065061400d02500c41003645800d152201c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 437135359 1250 437134109 437134129
    0x5070213142202090103060c021c02030406050c0316150f020705030306040903090b0c070e18070302100311041203020c06070c0510030207150b0f010212030604051008031602 76
    0x1a41441d0605164800303060012140c2d001c5000e182515600484050502035452110742c00303904151501c0011041000380da101c5003041113a0f030215000c2030490700180c404600080c8540c00140c1062000308040c50291010304002544a4141c03410680c00301c4254681c1d0030f040c0304c20b070341110341c0c0c420072144055603115840b0180d0381c01e5015440e0481030b13100e803a034030311024016030700642d0760700021414507118645050103010802d40381d50b036039031a04000c29540c020901900f04124800800708901200031101c150550800c580906112840d5808010301c400310143c010041c5602d8204c2014010006002400030308400d030044070400320340e400e00a10781300d041800705029880c2041090f020414005101d01158000c072404841d0070a011811000390040701d1005040d420b0b04602c4035111201c42d08841d04642c8240c4e03900d0440316603640126510302240b032115560150410225130035042c2600700550050310106100400d554511070070389180e214400c0e510840301700001e918114a407c018030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 437136609 1250 437135359 437135389
    0x60902040507090303050301050d1a0a023403120209060703052d040e060d06050702010504050607091505030c130602070315050601080c0306010e1504090f05221103010903050702 78
    0x5078252034159a001b920500c410b0040070300c00d07490500700388200903640b144110415840c03448190b5a00b0a6840b21000c0e410105d2200f48070407030035039014800e141b40d6200841e4042c2c44d00c4117294800c4261400e4600501800c083c54806400704841095610781c035009100e107600c03941d105030795090490441c035481e101c403030315031b14840c411401d0000e590f2a030b0344180c3c2c055403044405280d15031107140026034064000075009000c9030500040100300f80d01907100a200e2b82c0030301c095400941c5c50700303c1118081c0050107407010400220040c04545c9200d840038581c04101058007a03d001000c8100d43d0a601042d40030500507404a2410700c10003103c10b00c5071070075038140340080c400c0703080c004006001c4820050410942e00f2000c40003d0389680320380d03240204007001400b409010000103c00704000d82c0f10340183c805050814070040a0320f0030612466114608c002d803490010700010202500c01010601c041e9103c030141040744c038050b6000e115841000d407094803140d60f101e0491040c000b64000150384 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 437137859 1250 437136609 437136617
    0x250c050f2a09160f0216180b040b011e05040803070b0907090e060703090602070605010f1401091508060117010e01090e0d140306061308060405150411060f16060902040507 75
    0x184506900d010744200d1010046090800f9404e4480c07008a00d4580d883c9811030700710fa013003400040c81001141201c201c0081c40b0302c047c812404204103200039204003407881e5002501d40c0c0e08001c0701040080040c1d00f0317621146040752520355030701105817550b00701e01020380d0031403003000078822000c0040000324020401c005040c8015120340e1031058a52170020300e0b03842170581b10800001000003ea045402459000004200c20350712400d0255100d1994000c407455600c40c0d00042d415980140314100c02c07107486040c80303010314503083d1007100c1050024003c207060054040d00151560030030b0788841e0181c90495019070300c9601d807010303d100783e0300d6003d0201000d801c0700017800c8040c0d50080882d14a4030302500c2c450780d01d403500e0003c0b8000d0301c1001041440e141c0518404a1b04080200f051400703280a001290140d11154402c800083d50a540080a0006102564200d8144a00030b411b800c6803003100c590418128007803415a484561804a4580b40d841c41d1200841c502441020b820140c9460 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 437139109 1250 437137859 437137861
    0xb0d050109082a1f1d010b01030f020c0a06180503070620030c03060409050f01180c050f061b010207020a120b090115061404030501020406080f250c050f2a09 69
    0x40c0a60702e4120320442d5103086282130320340d009990390a820a5080710200d0b01c241045068404010340203291444030719000a00b4002c403a14005000e00139103859800e007038040c094440940e507070040280700c14002900c1c0302d014015000d01141042c40603080c0356002e01c0300814420480455032a0950f444485000b0240c428000e10180000050540768041c10648000800a20500f0002d00e040d01c5841e0994445d0b0801b418602811000c44d00006202c0c41210a001216116020014404244c0b9031881d000b2900303104600c0e07902003082181030604080f05c00145003079410380105c2d084032000d4101c0c1da94030401c0101c1c02c1c1081385500281d07a00c03c00d4a4000c200110000b00d4050390469144203402c20001c5000c1402450300c00e203001c4400860780403000b195902c0d680e28000d00504d40481c0c0d1407041c104603800264130030340c180300004006242558810100c02032800140c0b01da18a243d400d0b1514030401e030340002007a1041014030b85509a0143c000e2804040c501c180c034418910410381030064055034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 437140359 1250 437139109 437139187
    0x810090f0204110d1b0e010c020d060c02010b1203210709050d030e010e010c331a0a09090203120d020c0a060b0f040e3f0702100f120b0d05010908 64
    0x48610f11b40d4091030040c00d80252800000d031800c14144000d81403030302d031071400041a5015403040c41004c0007903450b201503058000c88a80c59004404810321900b04001c0d0420521b541c05441d640c0c0240c450414000e13180c0c0710000f05100041c81e80f41100030038205081e03d1829038005600d104007400900c0c03c400c2c2e10440e50f40e000c910084c040800942c2d04600c1745140441d0700c182d02c29001601600804000010320a00880107641c110b103070301405000d801d000401c01c0c80390760007650f00c1e103a00a00104084181450606070395442607401085440d824850300c42020f0040c40a194003c1c05010f0100d61007840c1000c20080303004e00038100d407080340ba05804001100012541072100c104440700c071050300c006e0820301c242c2122200d12011041102480d00004001d2043c0a000312600984a1500f0712185600554407040c0700c4c401400800c00c6c902c41e03240d10b569036402028220030301600c07520103000c45580b11800d40d040c1303000496514030042440c5a0803020f0321100301c402c0c01244282c1c4400c0980d5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 437141609 1250 437140359 437140367
    0x3071e030801091e05150d050c0114040f0b0d0f02130e2d04030207030b100f0608090604020f130c0816020616230c060405010e0303010810090f0204110d1b 68
    0x441c2c5126007642c503000055202400b48200da46e6082018251800208040c0340007502d130314651007824085044d43c154034040f50039010588095440d02c3e4109980281411045802030300a07031117040700680c56840b5482801d8050020f4108201c0d942c1c2c203400050704100780e96002d0321004003d80003c14401419035460030082051035610701c5000d0502403140c481d800d04030b040803c0f0780c00c050b084080032000e00c0b0388865400c3c502411030740e9100780c2c080c2c09901c0b61002c40c1c1405081d103400080c3c1e441000401c2c00343c036001140501340f40004024a40300b030f8402c1c1c082010360324000c01c42030200d4645010020a075000c44038150042009101420492034022544006050345159a408003c213810010400385c40d40c0241d21a020750f20707002251a00041ea031155940d00c42103c0c103d0f1154205a03894003d84000801d5a043e42d4224004e89103420b40209000014a40d2490683d080342062142030050b032194400c84110503404060a1382d00c4000402250648400b03000e1400860810700180744600d80c4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 437142859 1250 437141609 437141651
    0xa1a0a03030309060605040c0f0201051f0b03070207030605090102090f0607260915090f030a080409150b0406090303170c0f0904020d1a010e060c100b010203071e03080109 75
    0x450300b4006080840c03401c000c0000e080641203a50410300d891508460b0315000072004d100621b961b4002d0050b66248aa801d40000008580c142d4006420800340203da040c0c070003640d400600c91045600c1c1c40ea903501e071803090f10400d44840070141d6001500e29000e081401070600302e5142501c583d8038008007580e0310154111141486407550540400c0c00446601d484115500010018000040c504415400028a0307011260043c481c4601d2002c44510b0708010405110303c40d006001142007620306130310b400280800034410710303c2101d400d9003c2812142500940003400041c3e8441040900b1498050004240448510341041d803000400803409800703c211030f241c0350a0046c058882000b107010a010740940e8070715255642c10b00c40c03003501c000b03440c409101640009a0350700c104408600140540d0f8421000b010066030005d40c24840d210040e030304041c5803c4030600c1100e18001c03081e02d4102d50b101c40d0b03507a008001c0f0000400d00d000e01d80d1105059000d0700850900300f0500241903a15400240 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 437144109 1250 437142859 437142863
    0x1c0905060c0709020304170f0a03240510030e0a0f0605100b0f0f16060f0f061419050a030303020c060106050f0714100f020705070e0c070303110d0e060a1a0a03 70
    0x280010006d010043d16640700902107518801680e250841e916800da00d80d0400890342d80028507102e84101940d007985140782002d6018140801d840c0d0405090241c0448000c03804824561107a010040320041000b00700381e01c9028640c6807100340441e10745032054410260014140d251003400038040f080007942192807084030b51007600d0f99550b0005003c0300303c0c0502101100d00002501c01c0605002c600e80000c1c000030b1080c081040a40480300c0c4c40c3e0201e403030398000d035091584011080e29171410300038244c282c0d6250b034101c0640d403075a5980008984100c44d800c1140001c0d00803a0001000004021542c0036040a00b40681045002205413102e405000300203807100aa81c0703002010414284081c1000d003001c000c2c20b0014088070440040650301c80942228980f060940000710142c1e080720803805a800c16441c02d2500d802902c0840241000c040302c030b8864881044484500011446040120b001c084040c115500e0411040401ca8050003c040e001a246203032428256566801e07000c140da0f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 437145359 1250 437144109 437144111
    0x30f09040c0503160e01140309010f14070c06090c1a0d0b01140901180b0d0e060a02040515030702030418060905070f020303011a09030a0b0108060709050307050909010e1c0905060c0709 81
    0x500500040300e03a1f582d1140d5007614800e00000344001540d06401014000300c00d1041400001044030f80f400700700302c0031125580054414107450b000100a504038080c1280602d858a401548882441d4060190801d4106160300005149a0030161500860102c084242441c0e2802000800803000c1482403001441c100250b8003030542152068883c0e40c800303000103c40c01d68842001da60301030010840c95180c0c681c2413181d1030005032900281c0c021941a1a0090b10f100301130141041001c40a0b00047c0840c42507000901000c81c040c26410522100c484480a010440c0752802c01d40b40704452010701031004000744154002c5541d0303000130032a81114410485502d034100321000d2036400e4028100120742c94029925840180a060035405040e680b9001c02e949054507106030030354082443c1d00c200754140d0800c201c10012442c140e080542c2c400344210000c1030340100040242e0825540483c440302c90f42081d5002c01c5134039448414800a880255003441c90600c2004600d03942d5801442001c0303500f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 437146609 1250 437145359 437145377
    0x902030303220f1b140a050d03021c120609021e0904060f0306140f010f090504150216060c03090206120403140a0906030f1823030f09040c050316 64
    0x680c88201010b081c81d5000307003481182c070384a480c081c16068a4110808001544034001199416419492043c824801080c40904524250034070043c651004400e505500481403c410905d240c4900b9072a0454a035a400c0b0320150441c0c05981210210740001e000c4d540305001d041401a502d40b0b0002240482d038400c9615034848034001009420540c109101c0a0100070b400001c001c9280c100c4a040000081d079140c80d40e4031a1000c1c02c520609100e0544481005002000046c045900c00341d00325020311040b00160b446909002c1c1603130700c00f90310380c4143c0c5004003c54080c021144141100700d070451509201d02c20b0944c00249160042c0400c4800300084074000c40c0c04c040c0140320700101501c0d4400302603200c6500d100013428801851154401081c103140040011400318441d98003400056030004844149a13200e4848984440a1010803504d0f0b00c0780b5039142000800144c032a600d6030000c043e9840350400c0a0000b46e41429020406000c0c040c170501205500030410859240300e24901901d40d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 437147859 1250 437146609 437146651
    0x1006050112050a06091404050c12101a150d06050907140f04080d0f031404031205070905040f090516080703201801030506060d0302030f0d0f020307050403150902030303 74
    0x13805254031004400d40f03042403081710780389070690b010304c114000c0064404e450402d40501c15224550388808603aa000020190b12407550b550141003480110000d002400c401140442c40501d2545802100240d01280d4080d010906005080140a0030ba480244030300f0f0403040580801c003007600705000a031021540c120030300b8009060b0f400800b0807070300700d48404413020405030200b014200210002800c28000c120003c4020384001d000e20340c580e0742c0911b4103003d60302020080c2009400003040100c0090002125583c5025030450030700f1904001803150380b01d10b0464902a1028208002c075000c400003044201d401140000440382c12140307084254414220710018461110314155002c0d41745100c46070508136044069040e01c0c8103200301c8010b51944010005001e405000040060780200580403816072003001912000700d1000d00451140b19000411099030000c9480d10000b900219007001480b40390400d5440005214404004480042d00802d03142d1100401d9000103c10001000807 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 437149109 1250 437147859 437147861
    0xc0f040b0102150a02130e010303020a11041e0516080c0d0b181302010e0108040b06040b0609030a201012021602030d02010b130b18090a1e02031006050112050a 70
    0x480c10310080408800b458004c000c500250001d69091005202001c00071070a00a1020002c2c140c079055002401880d843d40d440d5840c1c900c100520940291312a4588005030021042c0f1281c0c10340c2c020720114440c45c01814804601070002040303401c0040000900280d44905404c40d01015401c0340c4c0424404241e80c0400c07500390040700c0c120001c401d41d030104040c101e0700e440901c0304540700366510900380501e440115203121050b1800340031010391901040700361a041c0d110010502004c1e10280c00c1004100000e4241410b40a00b80c07101c2132805005256121140c01c86203000c00102d880e075104c9080682c00420720300c03a00d80002c0c986640009c13140f0040c1031011038441e0707a0f94010212005002c540d84000c0c06800d0458582d030158010b0048038504041c41d004840b001c00c0d02401403c0c0702d00b0010040c0c0e04c00781003e08103107000d01644046101088480000070018000ca00ea156030140c1148181840c01c0380618035080c801c3d140c01b000b400181c1e03104030005070b56801c0480200c0c0d03585488040700 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 437150359 1250 437149109 437149123
    0x9070912030507021314060d1707030206010317040305120c070308040602010c0305180c0904140303070c0b0601090b1c060f150e09011a0309071a19020c0f040b0102 72
    0x20200031500e035100340070194444002e001243c8241e607581301c0c945038204100c0580c4c40c04000d402c0f101603c1c03400614541030071030f0400741d480e0052064801c0160318007020000c95001000070b9005800850050060088600501102100c5640c5241c0342074030310b4640c1915660b42145c0e142d0800000549942e4514041240300051904450b205541d9990b034000a0700074008030700d0040101e800c140000d0398400c80d00442038081407400000e40a120b400340300700016aa001802103c00c0364450035030b058040c0b000c00155104980c25121001001c070f075400c040d42d80000003850a0f04200d4002c505100a407004016240f10900408004e21000780941c044401303040140c20808000c0307402c0800041c1d0104d0700000000b041c03038503100c480600007400203116180b074090003140340700e8004007d0640c802c1c08034401541c3c010441d5094035003007a10ad910300c0e003100c4000c03264950304085c08180850000810302c13840445c481c0c180010f0010309600070125645514a404203032082e0381d01c0e00090304a9009000306 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 437151609 1250 437150359 437150369
    0x14220f05040608032107090513020a030506010206010f0b07020301020d090b07090806040c09090f0215090f04020f07080f0409021321051528060923040206390d020a11090709 76
    0x400070b48042c00c0c6000c9d00a4000207014270001e410100850060750000c030310325061300c0c000c0e1980690941801500d500540c800c000880e0590340c200540011441c451154007480c3d84254407150b0b42d4244050020602c170310f070350810751458006a0520000986c0c500348201100e42c1c403600031a00541d281801d055000c048080650083d4160203200001e903102d00061032121801c84641d01c000b03040f1420322003240110507061180c601d08000001c003050050000e0702ca04200714006918003611101060240d0b00440d4480300f8401190009000b81a030710390682c98042104420701040c0c0e00144c4980e56100d800e2080508407041e02008503014242040310001110a040d090710300911790481e640004003401d12032014060b142103211112482c035006510071003030130f0001031006502c0b103408001256220f0800705801c0069800041c9030849175104101005d6011100600d8140301040c949080006070f144e805c1c21500980040d000045420304140044401600c1039002d550307459800740c805540b25084 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 437152859 1250 437151609 437151619
    0x32d07060203070e040501060c17030a060f0e0a0b090f04030c03052511030f0d03180611430f021903060c030b0114220f050406080321070905 62
    0x401020380c0e00b2616160780c440c4c0c203440c01c01c196a43c80307400711a50007030707520000c03c1643d500060b16581039000003d981c00c480003c00000d078840e554511030044022070750150483e640901c040103980b02080c400e080b500402654901100d01e405e000f0740d01001c1004000406002c0c10010341d00034540b04105603002c200045200300c1109005201c090320090310010116080ca000c0840301000d03003004905440c503469040000c12139040340c844290050030b454000240f142000c094104042191406180c2c1c0400b01401c1c3c241d078551a0752100b14030318480c00f0201c0803140d80200d07070700d201d078105500692a07410704c0403020280050910344a43d50019040c006540851600d03280300d8100f43e9140742800326071150204200c034021000c01541030b00d400c140101d0215000241c850040300c0360341d008009c40d800040c0c3d60a1440401081d1104080454015000108034200140400e051600c0b603517010303043d2500111304200583c41e0964519041d46000440c2003501404107203054064107828020b0300b40105 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 437154109 1250 437152859 437152861
    0x3081308041707050d020d02011b050d03060806060103060b16060b06030705041d13030c211e03020304081605070305030f09010306050d0b040605100509010816050102032d07060203 79
    0x4040c92550402e0803110702805504400a650700e003403080d080100e41d01409640303481c81035800564244035070104070030b000c040141c8590006007080c00039021100158600007005d40c1010b8240b403824100402c51414549030600500c4040c013900c2c1550350b40c1c00b181c4010880d402072440c010018219a824594000001006114005400c0005482a00c1c41c0d0020005802c0409003014814503042e9110340e001b010040701350000c00d20a0410400c81806945c8802c2410000782001e503030b800c01c4040480000f181601d00b1280b41d202c56078103c0c000a120326066045003083d4a54121034481d00c200614042c042044190401c0f0080c40000c00a6400400b0b0360384602c81c03100f03064050761010580500091804d09c0206403031500b841c44081540e04407038807448c0390780c5950b140c0005080140591065031080c04001407260f90340340004e800303840303020b000e000d02010030300da5101d0449254121034151f4000780240301031079840d0054100c0c0301d0984001c294500390f803c3d03036441486c40313500805002180008 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 437155359 1250 437154109 437154119
    0x80706090201030513081204030e1c0201090503120d0c0e100c1e030e01030507120c0c020901140112020d020913020912010e0c120c0a06080f0903040308070308130804 73
    0x9400300c00464002e803024012507481500c0180341d800340c02d600400060080c40050f4980d0070010076550721920a0910304100c08c0150b00040c44442e042c2c0055a030640354440181c04c5580c0103000400800e4141d004205003840d1000303140c90750058061510f98150b49210240d10207100b025050381410024000f544002c0d1091001000fa41551009071590700b80d0750701d000040402411421400e0341c065460b400c02d00041c000440190001030310b014200120000e403164080d0355803186a8010009844881c10016644107002c502c2c40d05a0001403080e150700741e00d81040c1d811003055003079001c44d41c10050b0750f000561035003c004d00459084a412580b500c0038a2a9201654000c00c140070040740c40807070240c400e6000d01c0c26107001d1032161a503a04905680704250500c49124440020703000d081d01e00104003003000c908444500e03401200001d61341428450442c4607405c0d40c64103c52080051440e02c1e0642d1603000760342c41004801010042050b00151690000586c102e06a90b40024503030b0380c070795881c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 437156609 1250 437155359 437155361
    0xc11060d020c06150117060402070f0b240609030c010c0501021309020d14010506040504020c0a02040e0d1b020609010c0302010e010507020d020c03060f010e060a1a0a08090d090e090703080706 84
    0x85134040a01d001244449101c0d60180301000c0203101144001001551040301340302c086c1d00610001c943c1148840010400034040c0340040348103e0b90240c183c0c6080d03003d000c03090b0040e0600d120542c0220030400590049450102d040801c0340803c1c20065026011403406a00a00c100d0b8002c440448101c43d0200342c1d800f060f0028000a006142d00340510140356021145c2c0c010b00b8800c646e40700c3c6c000c21040240b410103030050100061500103592000403e0340101e402c0d20440e04540c11582c2014250501c019080b0344400c0803100000b1038039600820075804282c40d4800c481c40541031040365a01001007520035008022003218a000a004074144050041e688110031103180c00135020380300d6503220a04001030007610130350403500881451391810403d0085104050030301508402000d00100310326920303002c8804e07880c2403214069501c40b1001c0004010340005840d20701e10307030014140b103000c82d9400b02d801d40540b940407968030115266210706030f20b4021030340c0c00100304100c0402d54005200e01 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 437157859 1250 437156609 437156611
    0x20304080d0504110906120d12291908031c06030f0b060a060315180b31050c07021201060f1706090601061e120e0c030c100c11060d020c06 61
    0x1c1e00c500115481b840d04000501c2c840c0c004508580d44016011140d581c80f544480d0070740e0340c1d00e840000d14880440ca00091070f80c01d00410900c1d0b070030400504480b07030401d038141c000b803c40100d01c24000345003044a641d44070b100c0d0143c0d2201d002010b00352008c4290303669101100841e80560384060180f054549034a0105040324001c3c400d1280803800544140030f8001c00b000039415800040d40a030820480c200c01e491080e03542c004490f47c0c0c4108082c0d03600c2d4440100e0310300f0310504a100201405041800c0d0388003d500403048842d06100a11606600fa01c0a0b2041e4036812030310031810184810060740100400d034481c009480385514001200048081004001c05c0f842c41030359031941d114020190340340002e2084000040b42c91400440c104d18070009000d00002601d0030320b4104603105003281c141e940702c5103c640241c1002c60138446520701040034004040302510240f07c03045201d903001c0d10309601003e000e006c0b450802007803160307030b80d554003100c04000700ea0100310346540c0d0100745c03a46d503940 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 437159109 1250 437157859 437157893
    0x1204030e18010515070c0e01061e17010302090a110d0c0914060a0c030e030102180111150105060f0c1b120703080706020c0c100e010f0504120204020304080d0504 71
    0x7200c00e1a007001c202107032100d050b100081c05103210741e10544010368090b0b0046034280c40d03204500700c002c41c4c0203000d09100d0340209100d40c2d404503c042e00c04444001184100060f000f40500041800480451201024112601114111142e98600c0c0d0f42c04040d140e850441000b00800081034102142c0591180c1031004030307540c03280d17000c3da220345541140c400005861540004240302e0800d07a41d2003800002c1519100c1d1034449140e080120120f42aa080b065003020300410b000440d89040d40c7c800010b901e102c034444000c0c10000101203c0745403042041c0241d6000c0d4070001005d019603202d0400711560100758004481c2c084560036140300081c484400a82e114a0300e1511507c03140030006254010349802480d00d61909000e9034501009500c8080c0c9542c2c18000c076102c140f9150303914046035003114656140c1c0e4500c404100001800310a03560301800510900340400d211218581c0300402c1c046505880044e81c82d159400d080790140150407611181a081c00d042004104131450b03041c1840b8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 437160359 1250 437159109 437159119
    0x60e0d12030f061e03290c040312020105101728061803080c0901090803070c0e061002071a0403140d020106050d020d020108100801110c0d030e0607080c1204030e 71
    0x752210090540707040c45281041c0890082001400428202c0001c6d1031300300c401c1e03070b001d003001001c141e00c03001b8009084902030440c19002c1010000c0c80b040c0441c024412100c7e1000300042d14084124441c000300c0c5000d011040e2207054011a0342e000c003006461a01461240d50012060041402c84180c0d041608200d03035071410600003201c0d121690280006160b03064907101c0711a034401500c528260400b80d07081c0d041181c00e10001400c000140300030300600e0300807240d00780c0c890700740020b000c8404405004180101000c18401f0220b590108680e41074480d6070703a4100100648401203040d9000300d4002520380c01c40d9004d86034112400145d40c6030b142910350003d02c01555541c007001248070070594084e4008500d00e000350015886070500070f83c010144020468000e0b1103942150854040740e2104481d4400010260300e4400c00300561540425189014440d2800710800544c44100180000c0c052010000c040340c04a0300181c151094011441c82c248014074181c20300511000001a00600030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 437161609 1250 437160359 437160371
    0xc0a210203030d2405030a03140309070f08010903200a0f06140106020f0c01090e0f06030a080a020d02071a0415030b061224031b040902090708160302040f060e0d12030f 74
    0x181008500400c5a40e090303149c40c104207041c8810107200341c0c801400c20045e401502d10124001640a07504009031004000004541c075140c6400740c0b01848100040e041207070300e044048500b100c00603403044203541c00010352035040564601840680024000c450510784040000300703a859000030b601a0f221289011100b5504408006441c002c0341400740c0741c00510480c000411070040440e4040d080320300541111465a074980b602c0e4140c0d040aa40303180180c0011400090083e030410030640548403800d5403480c07204d2190203142e96072003a88240c071503105220311200c0c3c105010303510222031114041d1038a0b03914051500e0003140c03001d0485851040000c120b14480505c01240502d444030000600104000c000a10b5028010104007002c0d03036109403a140c0a4005803518401140110b0403a01c60005504084044100d419002031442d001c062050104002c0c0c41c010300720203011036207181001c5213038001110216084c4d80c01141d000d050b0385a812040043d265140d80541040101c4920400c11 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 437162859 1250 437161609 437161619
    0x1d1906020c250603150312050d0c0504050406081c0e010c05150420101101021c05040512130311010e030114070806010507171b0d020d020c0a210203030d24 68
    0x4072100085d07846010100c2e0301051000540c641d0414480c0e070014103005040000841400c0290351091100c9000242d010908018501705030090301c01800480028010405c0e000f0360300b540c96090000700c0420064102c0004a00e079000d098401038094025082d41c0d1440804100c41e080681c0985d800c0311110050040e040100c00441a41408140014442007401028480880d4883c0c460380440855540c2040300c00032095450b0002d034452448032602081500c0c040c141242026080034100300352030300400100c3c03082e007a41083d05041d2644125001e412610074001241d00b0f406c06050950035601c1c1140160410040c1444c82e4800c0300c4980c0e4443c070941d20f641c011240d9018484004002881030201540e0303a01001000c0c184034100b000000c1010307040408aa880c00360210b81c02c00c050380104a603851000c0d4144840341e84030b041601c000308251f1400131b8008030700768841c40c03851050044004031401c40d41e060041300d0310b54032003c43c1032040005110902c040d8459003062840c0c811000400091 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 437164109 1250 437162859 437162861
    0x18070f090608040f0c09020c011a0907080f132f0105090303040e090109051c021005192d06060e151e07050102030703020406031d1906020c250603 64
    0x950708242d035000d01d143c40d40e541d440e2404a88490444101400d520081081d40d03640c809407145140420002c03a1502d10243c2c804001c9d10784500560098040a0410003907039001389a450b0080c103120802d15003a5208004000728942034407008000c01b0503038154001c521099140003140b662800001e80c82800c52100554a5203c2d6036010394054006100030043c241f64000c0846e444080580081001300c0715655090401071b07140c402d03034501011131484010980d81004480310544887e60300304003d05024110000d043e98000450782c540380c4030300d0404107403d07040c4080c07810a00410420351a40c20a2041d0034050001801010005103403100e080e6014503000380300c04520008006424604220300c0c03080e00015210540301d07245004100110320015400340300031841008155070042e2204e003004401000d80b0303000d40d00901c0002154003482585500414180d0000300b11121107950103025242000281c01a00060401030044841d942c03842c010000e03601003d0340505400c0c80f0f2040e1a100250 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 437165359 1250 437164109 437164127
    0xd02070b070c14060f070f020a1514090106030f0206091306030b070e1503041e0f03080115050703120209011205090d0e0d050c010513090f0608240604021818070f 71
    0x2281d04070178000410130f50741c01001c0305513482400d481900c3c000001511103502066444218502159850107425583c2e40c0d2940850340090241e4004c0c454a4510740b1850191a10306002a1050400080e65491503560300c0d141a070804164a040c4131441c0d0b60704094020031400c54644002c03503001d4444620516044540844407450024100d045849686802c880494907074003a0040311650810a408144411008045680f1aa540120319030408e1403801400c204040301c20284074007404008006600b00d07100303001d034000d00c1c0e60050300d41c075038440101e590380404c10310300c0921403a240c140002e044000c28045080421a1204401220002c4c140715142080f0000640540c0090841e01c07859031003000107041ea440000d20b0a81d405417148180022100c2d000400c00b070766907031100c0802540c00e041c801c07c00f8a64042c03080582d070000400800740720b40c00c000c0c050391065030700080300f00c070168060f01600680000640220035801203404005022141560090041900d140c04207140c14400c00f910 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 437166609 1250 437165359 437165371
    0x1060905010605040308031317031312050f03152101090512040b0301060e06070b090f0c0613050f040f09080403140303060a06030b0102150903120108070501140d02070b070c1406 78
    0x16038656910481c0361081e111031041c0441c1c581d049c1420303c01c02490400091030140303203548290005a078807841c150200308840700482040c0700c0c0602040b42115190010f50ba03101281a07101500c040007200012255402202d1883d403821441c0340800e95a10150720140c1098810011140c0c8150342a2984149000d640320f4071065030003c00c0180019440b401641580b00300c090300c1d0504000481d034039210f01c00411503010030313658000c0d00e1060340340c07004120b0301c8a610307001d40d00c0510304503030b1090a2a1850090017120300480c3d8a0014501c943c485903c61a610a6010010032a0380d0407841d01803039640c050310003030703a6202d60740300d100314504c01c040110ba00400c0000c0803505510300e04074003500035142c03a042c1d46055009a100c00c0e82c1114540181500c26484c52000d0365480c0054071104210400c180c00100311030b0f020310320030b010760b0360400464503014903842a441d8070340d0103d80341600a407042045c014a140400303420300240603000341c041d50010340b02d0980c2c50038800c814841300e42d03607171011642 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 437167859 1250 437166609 437166623
    0x40305010f0b0f0d030221120f220309051f080c121501050d0603061e050103021503100801060f1a18010e0a08030708090a050d03081f17010609050106050403 69
    0xa000c045113400b818001429201c1c1c01903485403044c00f8810620400024600c4841102c0051800003104001c6507290b40309410487d181d0320703400c00d20309080c1412460b00ea0140c0c10241c80c4204000c1c140115031640051100828442030005003080c0c1440702400740750390364003003152080822a40504001070f10700f41c680c2400c1800003544c400400808c0d0076995550181401030400c80d6252601300b6000340c4012354051840422140782d070845a4a040b008440517128040c0380c00c0041c00181c0c0d400f510504040440c0300040e0316902c07001d000d071101481642c40411300750b10300f2000003115070501c1c1e10182155409450503042d903255400030a4a4458407400c00381100303848000b0781c410b6018203c0103100000203424910304586075622103286a1102178265a01c400c0810420158900180b0140241c0410398006440e5825590060310403500075013040710700d200c403c41002c0c5100089141800400010f00b81d50326500c1201c00c034a00038034290240f641d40300c1c181380000c1000303401141100c0441e90700c424 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 437169109 1250 437167859 437167879
    0x60501030e0703051c030219030606090902180d03030e031602100305090c150910022d07060503040501020702281a250605010323150c0c0a02090903040305010f0b 71
    0xd43c40c080440105175802c1415802d00034515015039249501c03000f1003c0f92000600181884e6026003c0c91150b03100145a500400107140340344c140903507514040b8016248030078550302c24502034000d8020824032060620000c524010104900004a207181d40243c6030344c50103821009049042c0c4204503540c501680c8886008a500c0c01c0154009100556020509081030000c1000401034440c1404102c0168065402068507808208480440040c02d030b29030b001d2003402d841002e0b02c1c1c5a1301c0c41858140f0030003000140c2449801e4046850b031507801442c04025404c10301c0d4a410031501003074030844690401d6008104901910a80184400f1402c1000d0411750440101411215591002154180003192040003d1603e0080d180610320500b60450402241010b408003020051a41010f581c0946014142c01500c1c5d00d1139600002e1147e451941c884115054502d0440203401c000e400084400c01c01c940302e90084081c2c030640b4460340003804007080001d420802d684141c184590b000c44010703 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 437170359 1250 437169109 437169133
    0x30c020111190e03010516032726030403030903080a0e06010b090a0e090c0316121103031303060506040c020105041106071406010603140609040f14030405030102030a060501030e070305 81
    0x2d240d41031a5914109052010340400b1900750303003082e907448100b4806d5030b5000078003503014000c441d51403241042003120400e1049045402106c2c5c0700f8090080103c80010071250780192080702c40708840e024a5544d41d00301f52400400070122088260001446e14000c101810268042c800e80d00c81000f006185590915200450a0b0300241c0d140e0342c4101d03d0f55000030b011500c0350031a489a0b01a9000e401c00345c24100915007440140c107601c103d8489001d409100b9070407981c89140c8a03c0e0005ca1410150382d02d00046855403041400300c915001c0c1804000080000a4014030b02c1580c0689003440030021240b8160b00340ea006840c01001c042e50909034240c2c5003407404c05000c03540d006220302c17410606c2c0341d841c0a04140e0280c0281c0002078441c4a194001c401c8901e0458000d0000d03070303040007a850305456641d4000d11090b00200641c0742e1501c0c8801d03801e4204203417405400c008000719901d0405400c1071008000a21525012030b0619442100b04500409c502d421250000090810380402c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 437171609 1250 437170359 437170387
    0x60a05060903030c1e1608070b0a0c0803042a0f0e070905090108030307081503101d0d09030c05030c01020d03051b12180c03030d0b150c030a030c020111 67
    0x50400c00380c05100a02c9009030409003003001702000c0700301c1d810640c44222003454480c24401400030116030049804010418004006205002c6881810010b0344642d0750f030f40e0444480c0141c28020306600c4012007130000b84103611188844420480051082c21080030f010800004480d1107100d8203544103c2040008a04a00c4a65031000081c40c3c13503540c5584070800688100340c2030708400b009920100c100003150340c0007079079550040040010407800d0805140000d60711590041181d141d1910380b41c0e036a21070101441c2c3c01407048020410340e48620080c0100030a0202c0b141b04c140d40362240b030000080d440c107011501d2500c40506901074003005040803c02d601501000d808030321010003420141000d102e84a015021000b6000c60b404040e08101501524082ca101d038030303010982202d01d0071391590364000100c441c0201c0c80c500c0411901c9500340005e4007070752104061840b80b0400201c80080100100013030001003415201080710885d0b41c3c008a007211032104803d80d040f0300412007001c24002c070b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 437172859 1250 437171609 437171617
    0x302130b041506050406051b0312090105070203040f15121a18040825020402070818090705040501030e0f0105010f05120601050a050d020f0d0b0108251a04030501090302061e060a0506 80
    0x20104420b0b00ca550008e8a02c1c6107500002d20081c00103401f03401d004000708207009071508100a48025400c013801c0046e01004040d0740e104101622800c401c200c81c1103809811221209118030100300700001d1800d692000101210280a204000c074854201c0030401500015005640180c0124105030108503904000145c50109003c00300d003100400005035600d00052000610a489032901c82a000310014101c60403616078900c140204004c2152080d13101060720110351003483c012035240c0b0060740203400d004900d9020002c5508010021590040c94980703c2d084507030907181c1070070740190201c12541b180002e0241540c05101e44034100281e00c2c0030790000109900041c08108489000c500180c04a6148841200c81440a200401009205010711210201502062020340e0900400c0041103269070080711300c075000c0501d1003201071640109031400b031a4400000c1044003003509000e903032048100e9004050709c07400c6da000c0000901c2c00218501458001c2d1004645a0402041040d5504 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 437174109 1250 437172859 437172877
    0x108010e130c0801060308070c080a030c1b1707060206091501091d100603060c0306030203370c090506120a03141312061803080a0509070302130b04150605040605 71
    0x1140000100b40400f080c4200d1006500c1120740f1070f40c6107030925044a030700c5425030008040c0d0b00315100182c0400d07049420407401c20780c480444054010700345080240f00e000d40c5c000c065040313101c81c00b420100d240069414181d03002502103c1240d6100040f045da145040c1112120710050340b03004001d20700c5035800c030b944015582d120300c01001c03030306080741d5190050818082c02038035200c03002001032000034861809064014602400030908640200b81c0d2040421602d400c00030262841200050a00c181c0c119514042d920103544681203041c10404640ba5000e81d0403c5450500400d07614580410501c0300c0300b4241c0040c28030b41020751805d4801c409000c8404440b850108074581c10415041c203140049d0400e81910001034519050072811140b1070741c91810012401c112000c003103030f0001200e0750700292030392020030a952401c1c0c44c0c5040482507800207401c4002400c4000344a620b0380c10200d40c010003902c0030021450824895044040305200d290301141c0c081105000c400e22540042800038 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 437175359 1250 437174109 437174123
    0x24170603011b051306020c03150907050a08100f140115140c030c070801020703270801140603010c0f050f130f08010912031103070503070c061a01020c0108010e13 71
    0xa61007010050001440140b11000250700044907014869490a400c2c09850188010200c0d0211500800e5032160002e803101c0d80c41845400041000c0e10421100c2c01400000e44013403100390380c6800302c1e0360300c2d031400040d0110350341001c1d030001c9008000d10422085403182d80d1075403002e074681a10a1100d180078800c1408001c01402101241c1006000034140c3c003541c0b400441c3d495102000071410007100e0303045915140d004005210102e40d100c468a41907800501c0e03108100e1b901c03040c031003e001103aa40214501c1d420241c007000400520600707144200c1d401e070003d010b100c07800d0000b160013520348081c0201158003444081441c0761464003624000340000310704607005480c0e1841000049099102c03071056074450301e50131b00b0441c855142c1c0342007501c141000d0203030b41174603200c10300c45010083c003407004c210000c4000b40d03110780304a0401040c0c942100c4100900702c0b0443d54082c880c07400700c0a413809849000c0c10b12060303512941c0c007141222140c407034040d02c0c0d484240303a5918003150300300103803550 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 437176609 1250 437175359 437175371
    0x30210050c06010e06030d03021603030b060412080316020309090a02030a180f17040b12040213090c08250302040e0723010e2d0621012417060301 64
    0x803041c1000094044c0005040c0c000031460644c04152401504001c0007007094018442c40590405000716501100c0e81800d020641500c90703004518540900e5000d9035511711165100c41c1408203003401140101010b4114610720a500c99060303950b81315a424a41d08019100b0004050b20610f03130140d60040b0704032001044d04401f181070003a00003000502a00c1c4008400c200780100240d400c40c00304081030a41400d41400e03d40351610300316000e010f120211062064001500719602d01091082da92000002005012050300300340152659600540301c192003081d500b1014428094820344005410074498181a41181c0c2400080c064011026000f0711520001049400e08001d0300501500311400340b42c08030b00000e0004000300c05c0e142c03070300d0b01461101089031040070f0265480710302003041300f800380c147e600d8000201d261031140c00c2d059501000b07902001103824914146940c12940c0d82400f00310060610307103000141000c1c21250402103400341c0481c02500b0080c1c0c100075441400103000040c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 437177859 1250 437176609 437176627
    0x100f020f0f0912070b03040f03170420010216030f080702060c1c051908090a021c03120513200406030c05120d0504183201080c01020703021005 63
    0xc1e41011886060041001c42e07038520a0030070040f02d0511114220050440b0761602410102a12024001500900038032004105140c05842441e034100f045148260080c901801c00030207540f100100b401c0f2142c100c10500005610004a51410000d14640f8035091461a40c6007001c203404030b0030848641c44144801ca000d43d03218406400c0035007000010b0142565110034800c80d041d41054408203010052200d5040301001e00c120200401190520381e4903901d039911744620b884c214620003035000c80304403003010f4440900514024040c1c4680c072042c2c0d40100c0c004d41813060b244112034250941ea901080c00000c61410741e00540c00070074280310b842c00720b100140490140c0344280c00980f50010002c5c010892401c1040b049844c1e0b0080c1c1e00540300d0070f184144020310030310482c03240040000b040660914400d49960150440008800d0000e91400042141c540200a8074480c024841c64120000400e140c0120700d098503000140d0117031005605603800c00000002820100080100521001507 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 437179109 1250 437177859 437177887
    0x90b1503010f08071a071103160f1412030706020304020d0602030a0203190218010807050f03010314010606020f1c0c02091905130f0f060e06100f050405010503100f02 73
    0xc081d01c040b4030602c12050620b03c01900d003803059404821450002c0b1104441e0744055816a002a40e004009006101807e000240b400012101c10301d031901c0044c0780002c0305019120880d0403180c01034010500c54840d80d082144030580c0d40d41c48545500300b0025000041c0c955070003945d015100500e2421020f649495400480e08129000105c2c183d002007072050754450044440d40402d80c910003075180c60100355035030041d4604d00d2110b41c1400010000f013483c15018105841d0303400003112030142c403982d50f0b051050030b0400d0030707001240c2c951800300b010560340d00c0400c44688060026004142d8482c5c0d43d003c598404510100c01d4080000c2c1416007401079603200001e80c0690078a03150601c08510302031107401215000340c10381c6261602002c40d500021100e20f0140400c0d03400c00c8150481031002d00b840806864803d4608219004100402c0701840500c4c2d80741e0203965a01d504110255261030903c0101c400c207000300d076415032140d00c03954040c9801c0d41040d1003d000c1214003506103158002128 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 437180359 1250 437179109 437179111
    0x7050a0e100b0a02150f040807020d02031906060504060602060601020703031110090807020a0605031005040509030d0204080a05100504080313380609150d03020735010e07090b1503 79
    0x180040c1c000c0b50700e20fa800f000402403a1b4000038907032840262410709030780385410743c418180000d0183d800f140c2c0200566034248420054415800010258400140b416000a041d1401650b00c2103103000d2000c10a03034800540c0074410401038004259440c00c5d0b407426250702c07062540c0b1030f285220320052012a00868014103200a00c1580e003d41c0341c480c1d620401c0142545038100004001d828000c0003020311003600508100e540668000446131241c2c1a91400e41c425005806001800003c001402510000c0d4840d9028026070654404026406142c020b551041d94040c4c181001440400d81c12101c00440f158943c0c4600c5845603102030103100000e030350041c61007003020700000007005080c884d9207000580d8040b40448140080345042c0b0030020315031034034081040c0a003100c1d041d420100b5008000c004003a18141c820101d0b03482442c8502d80000d5456074034101c800e003441b51840001c8505000742c85230a01c0030b0018164150421202d8001405411802c80d84500380c420507000c09030b0040021 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 437181609 1250 437180359 437180377
    0x13020a090203010303030c0c0302031b0a17040302031515011d1210061205101517031e210a060e0f0108210a030b0d05240907050a0e100b 60
    0x582c80c0e62450902508803114848980c050007a00f401c1303440003e5000c0100d60364224a21a0300c80c0d4120204007a034501030039240020082c0c84125141421103d4407800380044a00c00c5003101d40c613a5403070440790101d9074180e410100040c40c80038100c0c00c07503000b1074011140c0d6511507144c900c0c148614000400319038030001c4440b80c0350002101c2e0031030300c0054080c3d500503006000d800d041c00c03556035503140c6c0e9503040d070550201d20769510b058210019400000520040000b4020b40a851b1085081b40c0d489a009c044001c0058100c1011802882d28410554000c4051801e800c040c035410b10509100c201c40c0205826400c503039541020500c80c9403c1d585a0060380f2009001c00740c0d60505940e00d28ac0703d203058489030044200002403403014140822651983e61a10b408140e6940c2c00003c43d20484029034014005c0c0648030981c050181055028041589440101c5125481e02c02e00151100e040e40916a04054106024016000b0f2110603607000040141900700c51695200b0003c0d05030008440 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 437182859 1250 437181609 437181611
    0xb061e030a0f0605070203120c0d020403080a211118220510050d1e02011b0f02040b091605070212070803041a03060d02130e0303130606080c0d020913020a09 69
    0x44803c1c0b1509100d140d0f400705c580e00003507181c500549103030b0301402d5004001c03c02085001501040c0c04030141c050785d0046500401850300d5286000000d00001084d44050300e030003140200f0b00c2e840810038042c082e4003900c1501030351714122050040c0c00b82d00f980d03000401c0d00044a03c1c4400340768001d8140c1003e004500e0140021300d402d150300c84502088003a88014807801d0846105c60104036800001c04804800e0000007803645014801a1483d107161a120324420184403000018801c13a5a6010669882110300b005821302003002c00889510650b48a00002c01914190140764040c1c0e0007480143d0004090320405001240101c2c40c040107078000001c90340021808021000310030300100d007818440d20001e400d500d403040c041200e010800d40c01031b22644000407814a900b6035a80041d000f8814001030700d549180c84621381c0300e64452088104d4845142000008000c0d501081e041c40801d401011007203901a41e8003000103810300640780e108000c4461154100503074802c0d164200a00c18060 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 437184109 1250 437182859 437182883
    0x402010e091f09050601020303070f02070e0a0b0418051207150213080f030403170304060f0f0b0a0b1905070512031501030506091003031805030a15060b070b061e030a 73
    0x3250400c68155034842d03e411800c110a0040e00d80e00401500d40c801207a1a10b1052040300044c01ca20b0405503510140222681100b80702c3d81c2500c0c0c0e009034203d14000d071000e110001d240c050341100702c5003e103000f42190308090320040202e10b1040081c2806800750f501e003400e0740e5101003204101c0e4421010002080b40a14013001311010074083c80403840d544602641c20141785071a0503910f203840e031800820451000002804102d401e60000031460500c4608100c0d5480840380070004005c110641c91040110040018185030390004403142c2443c003a40d080d150902c200c409403042e402c503000886490103010151481301810001452140c010040ca02c00540c03211800542101c0014005502a607015800c0000c514159011801100d6040c500281a600c0103611281d88440607000f40b545030003050600310a11400103100c00500800000400c01d4903070302c85e0503050f0f91007503d40c003c0500500c0c0c1c00107812446e00020000425041d001500c20b0100204c000034200307140c0900441c5c618420312 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 437185359 1250 437184109 437184151
    0x1205120c0a051b0901120f02040b041b1d1005090409080f0a05090f0a0b030f0405030903151008030405130b010c0209071707030501060c060e0109050607080723040506030402010e09 79
    0x44201801090412441b401d03030000c5440d0607140303402104003c0e0145850342d10201d0241c40c0d5510200110031400b05124034203c6410006045800c0000740b42c0d1885034003d4601041d00d020b464240202c10152034141c60300003114140005003000000989841405110301c03441d40c03207444000c0a0140050b61803c2c0d88950a804009a442d8030410103409006001e030240b20104114084a4100a840d04051919550780c941390b0706c0d6214418590b07070140504010f183e5002814541c2501442d800003020080350388590055603a03011f9845182d03404290404040628141503010b41c40c03e90040c90b1105030303020070350041707584080141c84040c0080c40c5282170314460781c900e1078007a8002034107150030301c040e500d0010014260061020060178044e070f500c140344032220003513002c13007029927212050b115246070030307007003e00006e07412903000c00810105420b40345c86940f07110800b40600c402c8503040d402c06040c2410300038150002801281800185800c488080d9201107c440c811031101118440300740c540 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 437186609 1250 437185359 437185369
    0xc0a0e0d1b0f080f070e1522020a030f090201020d1110110d0e0703032304180b10080105060403080d0b0d0c0503010c0801050d1212020c0d0305011205120c0a051b 71
    0x8039040520707900601e905203e40041142c00c26006100e4824070718004a0040000356481d4100d108d26054140c400c0d40e80c0c12030040c50300546216006901c0800017040700c288284186c2d490000000d0042c2c000c0444407501d14010906004810348550480b1260402800100125860303e001d041c80c2c01030102e010204400341780259440f034496933020b0704840c1d02d150340140c001c03002c2910424000300c446810704400c00341c800c140d40080001e8280b0220080101d8150790041640e204d00600034040320504440075400740780e41504079240175040d54a0a45180c07190b114540108014281c0d1b1602c400040c02c003640c1d04880001080d010f1501588101d140030101030848505840c0e400510801c8001082155103007a6003014803a00180040007400c01c100c0101ca40154070f2030031602c036610105070b16420b2940050408207181c50f9850800c805e0344c80e00e89400d0000403044004003564031200e00400301150b00780c0600301002d0000704440d044005540c1d5141080b400310a040218441d40d41e22003205d03e81 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 437187859 1250 437186609 437186623
    0xf05060f011d04110708070c260604110604120b0a29040213051302030f0609091e0f0d120b06091c0201021218090c0a0e0d1b0f08 57
    0x2402d1000401d1030003692120011124030075584a44d9460b44100c4c036000a080031125100e07407020743c03d695511680f07010071854500c8d000300303c4941c0e080d090080103038421030307241c40c4401c2541000301096070380d0b59144500310410450381c6801c200c040c000080c1e0a65030480302d0603174501c00e610164961900c030301000121140140d070314081000c00b003000d9202c2d410044440c840c807034054030056603c6105410042c0b000c4032075841650402d000d9114010300c090b21f94003540c01540b1600401c1c905450700820000d030718106659280d82500100620940ca01c0c1c802041ca076644a0401955059801c0c0c403425801c0007407141040300401c0c62000c05444201e03051165491010f0221012803c0208201c04100c0e1003006418541c0c00c49050440302096a0081100242007580ca42c05141c0e40e084ca27400c1410b030751641c07201d62406201c4038070110b0030b612408010f40d031b19000c41b6540c26500e90b8484040040d4051058015030320400740c041000c401c0d032500c0c030f6000003401c507215122072070350300d4800e44034907080c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 437189109 1250 437187859 437187889
    0x3050a0501210501110406110712080906032511010e0a0c0b0f09041a01020c04050c09040209010507080f1b0f0303040311030d0e0609010c0513030618060f0506 70
    0x85400018440c022100003490a010b28101518800d0300e002d180803030042803d090800c05088010600003010703035104c0e58100d0186802401e641101e95100a40741d1107070411070000f401385001f4007248095090500245500010300c520b48484a896200d4000d02180a125128000303044124030013503400003400b81000c04440400100103000b5181c484409842c19802014103000700018006242000301e0b0039500c14050040c001c200c20115081264070b400148442a07001d4003803024003072a0303403030036118540c410303091005142c0c031300032850303003004000d5228074019418040140304130404503000001600b0640c0c1c10941c3c0030f690700d0700720381141a001002c000303090550b4046034240700742440104c01c0e07a800a81c542840b85019120703100003400c60041c08008612549400418a040c16000986501410103040208011070b03030841c040760144106d4003005610b0b10a240c0c204002001c950103d001e000d00394201c00d600c04a240e0720b160039100d031307807566243e42502d50041c000603141001c01c28940b8a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 437190359 1250 437189109 437189111
    0x6090633050405040f12020309041103101a210f060d03140d110c1c0f0507110301180506061003090b0403081b04080f070501110601090507050409140703050a 69
    0x5825030008440640030740a66805251600c0c041010050420110000e0355403113103140590b19540000299681c1007446d00600c034a080405400250f00c0640440340030303042c0306940c0303c80542045c4840002c0e44c90b240e103481084c80100800b00343ca00e44802d00c100d100b140c0344d034115507070700341600301121405000c2c065912500100001d8400680c0100c076561201c41a0700300c2c3d5840d02ca9034040e0400609902001d5800220001800b18400401203a2212400200104100405039010048a04614980070240461030800000001c10b4000807038843c041c40060001c143c00e491100740c0100b42a15a108407519840b0b10103000300c034584026080900c0007030345004c01c80b0309619110800d19010140018092005e440041100310803070b9401003610140c2401c0710b40e0303103a42d40e021b0280e450342100d001d180c490181040c0840c0c01c1d8414080e19024402040081410307900300840c40b8000c2c04054059014440200710010703c4528900450001e9142e2180311001c40ca0100e2004d020398a0060480040d2 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 437191609 1250 437190359 437190431
    0xd0f090906270c090306110d0905160905130b04050f010912110d05070b13021002100b060705060403050d060f12030201050a05091002070201120e010c1103070507060e01020a060906 79
    0xa284e1110326101203c1d004a4003040035283c0303000510b01446000190401c1c503081900d03100510800040d210358081c07005607281403081e0348003c404101c4900380c0307902d1118604603072410041103441414640142c082c406403004080340a90742da0844600740310443e03000218200700300c082600001040c8200503440b015060b80c0200c10001440c0e8030031303080010901c118200101d95480b09180740b001c035050780030b0054030500044000c06075480e00c0b60643e0921042c1401c1c5002da103820b00c41c041d540110341c0403004110350345076a6030980c4c00e50004006904c807195595400134404492120000003000c541114007400d261500b002030940764000d01e07406010b4181410302803003990000341c00c0300c40c040d50040141c65030110f1004a13050228a01450002420b01d0400307200d000042d400545c0102e0541ca84865010143d29015100d0141c0b0701c0140041c0c120420800a0700d010319290400c07444c0510565142e4090741c0c2e00c074421503800312826a0525601d003268030203411088814000c1800d51440c548403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 437192859 1250 437191609 437191631
    0x20703020a0b0c330c0d0c1e0503180709090303050c2d0f04090515090702060f100509040c050a050f0607021905090906070f03020304050d0f09090627 66
    0x6140311004c80e00941664001d43d20040c07258070050480e00c2c50310180c9407051800c080c2036200e40ea8001c2c5c2d1100d03080500c2c001c01710503007a006007074000310104d209806480e20489070000791303140e420052000b0001c0c40701844441000030300b030001c100038103c1d40c50700269039031040c100107044450080101e404d074141080b0380350105050071039220410050800d9403103c80c54143c5c00700f84034000c041901035044004500828802c2498000b94032440317a0a100c40010803041d0304100400303c040d508040507030800300c0031805030010703e540b00e40d0001c04410354600056689012500c450000c8030103545041a100040c0447d180040140c802020b0445080d01d41140c0003001070003d1081a000900c107907003e40c29034040b1115000708500811005141e460649084948161281c0f022074154000400c1003400790030507030103031007581d01598000c1d0092a5094003140e06941e40c00300e6410250510421071030020301102280100000340407d404d200d8901c0e10845880703039500442000c4055014144640149 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 437194109 1250 437192859 437192863
    0x3060702030d0510140405070e030a060e1902012003160516080f2806090515060a0b09010503090a0803130b010503010912050a0c050105010e04030e03010507140a0e10020703020a0b0c 80
    0x700d43d0350100c900050b141c56007042916031271400170b80e0503054000c020020040c0000381d4000300580b0328000907031300d07094002e0142d0001c9070420100240443c07240d0110300140c20f0580841c2500a00300340480340782c200391060315101c030048034100321015800690404205500030480900800511008240880790b03801d042d070725110300d141120900c4234003089001119a0000141140b10f420440422000184c0d00b09291903650000851400c19511400310340503051031f1200200710307411a02032506045058004640c150f10140800101d0310500d06000d0215840e40019805810000307500c5c0d011544a00d0805030800059008601c00c1c3d25086c1c5c4031020852082602c44402954600a40e0b10421144203070742060100102820715841c04e8004100c1c410702c1d01203140158082d86900c003000f60001d00305402e942e4202c5500e00081d0503040d4034115071010801070140c0c12118240140340003050800700d407a45580310501001a803000c2e80400540c03c241c042c00c406003018a403007030718200c03002170000c1e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 437195359 1250 437194109 437194139
    0x1403010605031207030e060a0f080705030105030703060902012f010e0a0f020d0302100e0c090c130e0c0f03100302120d090b030402010c0b1006030b0a0f05150903060702030d0510 78
    0x1400f240300000d2a00c00c02d44503043c803580302a4014030032519080401c20041601c0c00628501c00843ea040000c85c018900031019681281c0004009001050542e41c0702c0015100c076202c128103010f001c05400d0080e20f4040902800020900c0c6034030311005002c2c0105007540c00c8480d0755807058100c440b80e0004a07240030400c00b40c103901901e01d4800b0740100d1604a15100703044804040b014504002050134010101e000040c140b03003140c5100762600c071401e49110307034485d001100d800340365580800c00c103c00c130700c144041d40580d11441050801c8183d460010881e070003151a501c46801c030306000c1c4114500b50340843c180c280c40d40d00500d00d0003500c01020340110443e0144807202c6902000103011603104044001201d0303417180170071000c0c4c05d0036403c0040f40b000354012440480d00b8802508181c2c00c0004800084036845c7e401400c0c46450882070062010b603400004484d00e03000c101d00211a14100b06003802078845500640e40c40519600180031140d000d0302014a10741c03130060070040b4400c600140 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 437196609 1250 437195359 437195383
    0x60b03060a18020f030c1305060f01080105130f0204090212011d0c0f0c0a080403061a01020d0210020d0b03030705060403030f060b04181515020f030a0813030c0804030b01140301060503 81
    0xa0300d494240e04c00002d01d0700d0080d041c1c440c0e0029298610046201c0c05421090060030152801441c20fa204801921500024003650344c001381b4052140d10007103001d40110000e12029140145003d884200301ca0507a448201c0d10030803c002030f00104042d070307546100000c042d0342e547d60396125803e100c20300c0e007040d12a4128112503601c2c0400c81c00c9449806028180210754001c641c0346d603d942d01e103401000742c41d440c4c18501d0204001300d00c10090b0b500104102900800b281c0c05420742d9110140c0510080d0001e0074070740b44560740d80f07103041c4c941d032130810040418034000c000601d1246041c4c50000c0c1564403145030784480a043c042d082081c900240300b50f030242c900c200207131003000c1a99410b41008144204100002080b2054005090260b9034624003c0800c3c540c00d64010f146030481540c3d4034440c02b04000c000a6542c070016116400ea04a64040c25222346010f0400e4082070300ca6401542283e0000c3c1d45100049004100204407200c00c0341841c80190006d101140c9003500298a070103000c00d0f1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 437197859 1250 437196609 437196619
    0x60303040501140913090203061f05010c051014011a0a080406020a030e070b031609141c0b0106020c10021f0b04020918040b06031b010f030e0109060b03060a1802 71
    0x280715600304141c1524507100c03014000304418800f451100006c1d0103040001d03400307030248602290704026154401d400207520b10712142c01c0c039485c1100466110b40801c0b0f0949042c02511840c0102019900506092003680752030b040903075041c056405103000c02d601c091081c4240407c454940d25402000865015810510068a03191144020f0f40603141d528914001c9005480e408500c00f00c115014600030042c40c0000540d81c5c025110a80d501603150041030900070311980001c0c03c0d850111a40700c110070310803c80c030400700c01179070303850251490030380040c005030300b0000e40c000484c100041c3c01400308440b032004243c410402d000003428410101203100b102501c81111841588a43d0110340048030050207014158408807520b54442c1070541e01100d0140e041e20210729540b40c000361015881448201c0280f0300c00310b40380159101340c40f4006c084141354940d408009001000e01c507101c0038034000d59000c07940901d480101400d090004012062072403401c0140380d007102c200000303285000c2d4159a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 437199109 1250 437197859 437197877
    0x30105160c0b31060506040605030303010b0702060f0a0f0e01050304081c02160f060501080a0b0f070306030c180e030408030406121b200604031d0a0e010b04031a060303040501 77
    0x15195400341c0e003044a103c00c411541803a000155081c03200d124400303010700c10802c05070303c40d102000103072140d81c8500b80e4168070600042c403c0c8405600106400c070b10040c42c080c5000450100801c00f5009402c0c0180450f02c560211202c41c4d800c4211281035100074a08140340d481c3c02e980700d00319401001201d6450440c4000401c4070018182e046804d04085c2d41341d0a29a200c41e07240211655569000450f01d0314242000054080000681003080079806400c515840e514218050a5400024540c00405803141700c000081441c4c00040d1019090580545602c48100c0794160152641c0c0103644002d41d101f003008001226010042d9003d44d003041c40c080c6404100040301502600c1d04186140c50b000e088030001210981000d121040b07a90102a204072140c00c02d544607885001c1160040e01240b160141e9485140c003220341c404200f4001800d45241986400300c400c41c40400360000d4035844000241441070000d04108089001d01380c07038600f006485e02c20042612030045115450601030098 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 437200359 1250 437199109 437199121
    0x30e01020708100e1c021504080f040b030a0b100207060e0d0b330109061b0b070e01020f060c0d110c0f010b12060601140a05120f06030105160c0b 64
    0x4021030004001a00032280301c118440070140090001c030103001ea01d48101c22041e1417070401803066070f0801d0102d4024005c1a181c3c980071103070440c0c0c02401200c2020007000f05200c1c0c03000d4540940040c040c030a107680d869103801c01d8002e00701c920443c00b0074030500d4009a03c070b4507640d001a030b0700e090303420920b4035801d8800c040b030206150200d4074000030100d5103420104001106441c0070300c07008640c4081000d210704100ba46080c40b0b60091101180000c4400380180045030003601d000000a0324604000c40203c190b0721102e2a0000039660900007072286d0488885645e030420802041c941a01d019224500344144590403030f1203a144104921519a020044120b1111043e01c4c25641001c0517150b010240e440150300904802d044d4a00c038040c0c000180242e100006952445404103846108014101c202008410b4109006400030400304000720204008170700c2200f40078400e40301b000181c0381402402c0500b0340e00024410454840e04030140020298440b02600160760000c18034401e41d100c0e4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 437201609 1250 437200359 437200363
    0x5060702241216080124030504170703020105040b0612070513150b0a03060f05280906060c0501050604020f03070503060102150f04050105070f02120c0102040e0405070303020c04020a0c030e0102 85
    0x41c5540880007685102001900d001501d4540300080d50755540020603a200c1b80700048107100c2040d01e04000c4026050035488a010350b10058206010340044500c054440070b18004030780c891202100141d4580c4280420005500e203440d410000458040400c4454041001d50f100b96900c200743c490582d01c0111498409241e1064a0201e036814280076001c0c1c03589100e4240d0b902650031140001d107800d40000e10644c804108100390f0380001c09143e12580307884c000b031002d03440344009422800d91403070b0f0004083c16a0b20580b00100000d84900c40c00c102e081c09c00c2401c584000703005034040c2d801000000c82c1c410810b0200ca40c40b0a0710309007243c40c1d4071107400403498044403000000d14440301c4010301201812101c61b00b807296104200034000d60791800400c4509110031ba042a0150344807010490144148002901104100b07400060030070344d6a020031a82000e0985d01950550803400382070040c140d0600c00c3c604c40720340650342076144c2030b00088000c0010840c00c0c8060100420100102a660308c2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 437202859 1250 437201609 437201617
    0xf120c0e0d1502040b0a081302010c0821090705040e010203010609030201052b05190c08130302150c091203090a0504090203010b040912090e13080c0307050709150506070224 76
    0x250700b045440d580c941015040a6201507140d1780460301e51000a61400112440415420f1381a035440c5420402c540e5140e0b0250000d0044641030081402603100320400d0980161241c0d418200410049160900b80b10449500240d07980701039004100600580341c000520b201100c2d428608103a4803c40410341c0880300c03d10f294140807040079441441c48143c40c58000314001c8100e116080c068100c426000390840342e071100c101c00459031032000202c0e5a0004115045200e0290050b02c030300b01101904402441000c48a004003005c0114402c1e956081c801c074034402000c0d242004504c7c021042002406403845841441d10482e2a9081340d0110344081d0001107100c2d8000c1e0080c040c501e030038034000c417400c01c0e01c034400d1001030098503001a6026511071058002c260089880544540d40d841e0400d4070b40c851010741b01a03100400c000c4002a07800c21000004001902000400010040b8907050001c4981c0c030407407060905104d0312005daa035610b44400384001144034410300c1001c02004201d0b03402 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 437204109 1250 437202859 437202893
    0xa29040c1a0f070b0103020a170604080a12050f011e0e0112030c050a0b0604050a09030c140712120305070c0201020c010819020706020913090c090504030e040203070f120c0e0d 77
    0xc0c0120303c8004005400b40c680303040e28802c40d03610300c01c1a15440702404100c1c1020f15107034298040c030042404512940c00800c050040362821003282c0c101c0030451070585801b603403c5241d018081e00100804480d026903542c207141118a210349162810008507592001805030706150240b070090f1200305409544d01c1c0c243d143d40142507895080003070409010403181158954000ca0074100012854180c80c410004200e5064649407c3c0d8000ca4881c0c409061400c940141035109034036000c02c01e400c5040001c403c8034030a24052511650b02c510082c00d0f83c502412400900540000f90b400503a0041058000200c083c40c2107105070b91100b103d081e41025000a8402d41840028900140b10058005040f902003d50b410309104d4901034000040710105080500b4500c0c80040038090b05006420054006020703240400501c403510001400b01c1c2e0054400a002c900240181544150000a05003d9040b0300740108030120054001900850302c8010341440303030070505104c07420840e802c00a00e1032a1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 437205359 1250 437204109 437204137
    0xc21040f0603050a110918040204200d0c030c2c090108070906050a030c031707050d0503011706010335070f020112020301180e0a050a29040c1a 63
    0xa90740d40c1c0301030000e19040e1072400006041021801d4018520011501102d002500d1405402c1c01030ba901d8003a4007000e0400c0b64800d4951521410f20301d001440703510160344c903040c0d030350f5550b4602c0c0a0004480160240c0070605051503c14920150810080e85450070403043e80c1500761707150291540020704000c409030380105c07040000306510500040c1c0f00f096419802041100311384a500308164103000f4480104040000d0a0a000046025046200c58007a1100b01400d06031183d07030702400e00300c50b141e801d00040c03008001040b154000000b5040000c0f0030b240500050b50542c1c0343d900802c0420152001c141131085a440c07198000895415401211460072545816851401340301e0020000300a90024289403454081c4449510841c1e0403182c14000094a90890a0702d00010780768480007000303d80201240200425800c2c0700c0c84206d54443c1c40642e40c00603500007a1410400c00d4102401111110400c1000240800310380409440c403c8040c0c0d0720024511503803851911800705411501 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 437206609 1250 437205359 437205389
    0x601030e060702070618140d0f06061409160f1b0203190303050601020601180b0406170d0801060c0f0b090c060a0905030d1412041104150513020c2104 66
    0x142d43d0104e40d038810741c0c155a8580c19000e0005000b0001c40502d8050724200d003110100000d50707072800c450000d8201d4811001600491516207803c0304642c1103510400904080c522403a00900d030041c10954800000768800c0d400d1406071000a00f114280749005051000d1501c03545403040440b503001c0c07885640202103c415680c0f40010750511240e921013200801d0800000c03a14660004c1031b843e050301c0703a200041c2e5600462610180c0901114940c0c140c100340d80d41804500140a00d4400b18001c0c2064000c0200200c0820000c0580d00164403000c20440202104000501480402c202281c3c011703d07a0700440e00c50a140301c1c2032686004c6004e9100c1030001d1004821034110400b00102d41c4110f06689409403088000c0d6150341c40284c1401c40f0740400c12602c40681650f59120382c2283c0200190002c0c0700508010800f282d011101101d0300c001d0420b000c0240b8503064040d40c0c22825075203001e40c10b0994401c111a56032103d0380c0c10442030688102e441a549510005450052510f00c0380d250034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 437207859 1250 437206609 437206621
    0x20a080d020f0105181f02040f060f020d0302210c0c0a050f06010503150f070e0301021803010f06030506071b0c090605031005010b0a0507031b1209090c02150601030e06 74
    0x540d10814602d42c0c0c10f9420140002c007064240910080501c0c1c0f810f0140c00d200341c0004c03503240c00004090304061001c0d428000800c0302c01d1045945805007055031260900b01000c00c00c00303403601148101c1003003010700401c8100750312807110612604401c403c94441c4d0340c035100e01e00c805030b03107010f4140e440010703201d02050038003400703c001b906008500009003622060303600c450915841e0fa20408a242e0702d08495000710741d124015948159111186181410003400c550b800a42680e00018000c010b0050640e0f201c0c003140707400c4c4184100101c051108110715491070f6034844c0c6802005000e00b05014840c0b000140841d8440112a0000c0d40007080603001c82d00e41d005400203120b50300600740688504401c00c07101152501c0b070141030360443c0070105c3c240603c5800c11074003540140011003c01c003a00145401c0444402480d0103180c0c42603011903561010300500400107142a4860b07040d90f410039000c116000d80104800c2100081c0c65100411540d034680107801402c1203d0610900748181010801 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 437209109 1250 437207859 437207863
    0x1030b01022a120601050d0809040b0a03051b01110c15130b04150c0c0504110f120f220602070602090d0605070e030a172b06081203091504020a080d02 66
    0x511210884600f085003804860040e51004240601600b0002800c0140d003c508900007401c1c002500030300214511a0710408a028845264401c681c95800011029803113a1f18181003c1b000f9022710f0144a8181e42c2c001003941c031040b0b60400c40c003598601301e412404258140c00c4540002440035400d01d210b41e1800408280d5110344101d0340c2c0751640001100050344660b04260840c0c3c0c1000a54054a04000800c0014040d801040c0c024000800c0811341459408002e0440408803580320001403416440740e900804000388040c02491100c03a86050300802d1044001e000f61700a2001601c1725682d1074143c00038031400d009a54170030481c000180c2000001c2e000f191040301107a4814003964030002c1450b07500c0c01e02440042c0051045003610546803210b030050110302c038501e072420720301e1548840e4410840c000d410a82e10f80a80f01c10081c0030a240400003407051a007280d0b0b5062031480c0403a103d90715094400e40c5901166412004a801d640e07400c40c9035409400010f09950081c1181d1101039 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 437210359 1250 437209109 437209183
    0x30303040812152d13090c0b0a0504061202090607240501140d0f02041b0e060403120c061e020a17060901031401061a070b091b01030b0102 61
    0x207610844000011441240b0802c0c6010802c0040c00480001c02030b00c400d28119a078044c040850000b860b080d0741903990f00c010700b5450621012200080320922400c00841c91710294104100040041000008065102086a0464419107404c0c4c5004c807104003030b14007070321408540ea0351060f0041000c4003400b64104680038105047c804042181c030502e0340d100d041d28400d01c1072880c240e0718122004e4140c1004c8214421252081d0300c5002084203c0d030000307003256480c800f41c030072192080030881c8403542c00000e55800608129581802e0070725503680d6120107956802c00208024540032180100540c0e5084282d6011001d090035508581e0780d03042500070742190020100182c141401107003044880c25440d40a150054100310b45131382552035418141c0b001d202c7c948060f65072128001040044584040c4426260200c241e0b80e40c00c0c24100607591820203080803a071500a4550300820000035500900806000e08022590524100050341070540d21424148100d9510001ca80d41c0310b4400303841 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 437211609 1250 437210359 437210377
    0x1112106010305041110091703030601020f06100306090f0c0e090c040b0312030601050706020301080703150506010914010201021201090603060c05030408090f0d1211011b02060103150b0303030408 86
    0xa44619a035800044040d110306480240c100030b000502200d00b4204900c0400d40903441d803e0819403107076100c02021550300c0b09055002035070404002c0c007c4d10760b81030040911030043c44004100b94107220180044c10080c5200017013030242d680d00914100301524038010202900300c0701c4240415529403200f940000e040302d00c001a4040c9905100c1c561615200d016480900500101500040380c50010f0150344083c2c6410b0503c03400b404a400003400e54001035028005840141c03810a141d4501f4680305021611006001401d040c204000340c1d0f4000490000c440e040d0043ca6111040500181d00a105048040261840075000401d40c980903811102c100c81c8200010859000190301c200c82d280000d40d002800c4c9441084035440300c0c68221040340d09040d00400340c2001c0d1070181d0340c00c0a5032403207401810110780c80710396a0620340700a01c25401c0400401c000c40300809400b510094032a07a0502005100d050402036a05040310380b9802034481f10000380840741c0d80d05107414921400e822078088 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 437212859 1250 437211609 437211667
    0xa0507210b0f0a030528050d0522080a121b0c050907110d120f0216030306080715110313290a090605090420040f0f0308030c0a020111 59
    0x100b00460030b1528903d000c40c1d4101e00685044482c2c0b8101c01c2c88012260540c0c024082081495000b150302070285001100e0070303481e01c0d86d80302186010000760070040003004002c40340d613000400c07109401040d40c00c4450f030b105030195440502c46c03d0a69681c1210f403c04000100c000080e1010491141555000d450381211450100d43d030f816400c603542c09101c3d032142d40c0c039045505544090760062240a150604801c00494401d00d610451000c03a00808014501203202c160310000741a014803c800140451b840039050381410070b001880500d002c0c400200401010001c007005d00b100500540e5041d03840f9041c3e0403100d507660404409585402c1c8907032008101740b405521140c4040c0ca04460020b1001e0701c4030260103140c40ca0584d9640c00a40e60240c01584034801c1ca007a40c22640800e0341c00d030480c418079544860400c248100c052000350007020001841c03240510208484409883d030006000c083c141ea5030a001c0300881c0982000707500d50000d0070010030844207030507400c0003101c0781101d0644 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 437214109 1250 437212859 437212879
    0x1202032d0f0a020a031b030f1a090111160c0e07030e0f061012050109060c0f1704080909040c0308070f0b1f03080a0225060305130b0a0507210b 63
    0x140d1501c4502142c0002c3d07010590902c100000f58410f602d01d15030022507100c600040b83d5030340799845507180402084542c4ca1035003503413281e44070341004100e400c180580c000304014401c0503034880651245802c203d07000745000c07070500c041003032071071742080074120f5001c44861605288801070041c04289000800e90f000d0519031a03030607500016140d100d1505890603018062901004031200da0320054141e40d01c0d5261000744000c61054000c58801840c0d030741d18100c2c0c907400680028018800b00c0000240c1030b40903024080424404c0095802901041b40c000c4c1c0a51114646107819040c00d0340004d0003e0f00100d019000c4c4440c1800e45503500e401800014500c2d59a903001c1d100880e16401020907480c6404820b00208850700b0150194031100e00441b45550075000d0704180140800e8280000302482150920810f0b0f8140a02d03a00800c0311258403403001c0c0a503450300d000780c00c0140080c070480e580c0d00018a05620810701900c822480010030001c041000140102070010001214060ba10300304c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 437215359 1250 437214109 437214133
    0x13180c0f050a120f08091f110607050a08010911090a09020720090a11160803040524010306020a050418050402091803070b0603070302060c250b041202032d 68
    0x200c0c043d65500d6024050280c021440d079541d004079000400380350780001703a983c45031404c0804a00402c8143e004c54852034100c8640407003091505200400304c1c801c0040602403441d00a030019003290545807804c5001c07030310f140280481c150724002d0300d2202c0c0c6d0010f10000006600c00d61640200030442c000c000401e040301c00c240138848003002003581d450300a29528006450420254005000d140441c60858070340294001015140360b280d26096a140400206020800c0000c100c02d044003014044541d20440c84603030340300b8500c0b41c14130011f450700b600016203000c0c4074824812140901611000542c203440c107902c103a0020310084504a0007051000041a003c68100b40340305001c4000c00019403074003a090f9942c0c1190721f005011103406115068000c00180e855902134120300310503000900d290341d542044604003403401e40340c0502c2902c0301003083c0013a01110701102c0590b00c0a0780c44038903504c000d10200345072070302d01d80c058608500c0e00581c0e800901c00e14150900300450410490744101442 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 437216609 1250 437215359 437215379
    0xf03150f010b0901052208100e060a06030c03150f060f0303020d141602061603110d08070804063308010b041a04051015020a0308070c0213180c0f050a 66
    0x881a8017141007440034050859000c0391200e4500091445600c849a075209102c0c0380c01c1403050580062621480c1041803441c0800c10254408a0003105010007440d40c0c40e103003103c208501015044803004d00e1342e900d0a02d031980140c0150ba681c3c1c0010054243c1d01ea401c0b120101031400124018011003614900007440381c00c0480340542d2070341da62860181e080c16410030510740070008980101003842440a586103428886d19002e010f92941c2044048501103036041c56000c00300402401083c40501402c29408580e0544c420380c021800945002c0e0200500290407a803000704c0c000e0900e0403d56000c0e051544000001c40760080d00910001c10540c08100544004100120421451a00114071894150000f907040111032190f2107e46403504004240039481c42103e40140c0c2c0404800010598020400741d40b025462410700d080044c1580055030002280051041e0791b0740b170700d11020f09441c1c43c440440d05282d22400804d0350564400d4840283c9541d8480c6902c54240e08400090b11211 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 437217859 1250 437216609 437216617
    0x380604021e16050709060e09061302130b040515010f03020406020c0d030c020306040f020f0603040530040e01030b0f04050a12021002030c1c290f03150f010b 69
    0x8514411820301e06000703284120b40c1044401c0194011039410041c00f00c0d10901c500e0000e4000300c003000c100309080510702c001440010f80185451780c08141041504d925100c00351130f1030365046503c070800b5460404841301402e000d081d07803580a85001c0620019840d016080700d0b404500b0b8036148a80d500c0c011058003280150b110303d4015801201c075a101ea480c10007411200c1a1182c1401c000e00029500802d10b0700c1d0b0110750407a03030028002401019450401e08044130382900b01c130094a14503080d45e40c03548501401030080c100f500c0c040840c080580c5490400040580031984464480390f0303a04012800000078031080e80c2c011510340c08070b8220304084c4607551081e9005030050042c500242d49018072240511070140c1103009500c01c00408000d07500055018011460145441e810304d0f0001c001101b04601d60080030b14a0410030748180c0c8041f40140c480d005408503401108481400480c0079a81d015100642c1030086042942402d031441f0712041c06003c40d0101d425040ea21105100303841e100e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 437219109 1250 437217859 437217877
    0xa0b01030b03030301061d030a0512040f050301020f37200f030909100509010609030204050f0103020f060702040902040e0d090f0810020f13090c1b020d02060738060402 74
    0x503030f806100301031080b43c0c551507070b030080a0100c03009c0301120b0b1201410308443d01c980c3e502a05001070304000c1c0070100ca403201d0240104070021441d15481c01c0c04115144102e00e01800900320b090700f01c0b022040700d055000b03ca602030103400300e544082640c0003000e003c1140303c00ea5030210b11032003a031107d20000582103013200d003503001946090940b004200742d042e4018180b000384030007008040f43c641c54100070700d4000c2c200e5803605064030b8114410401600c4005180c0e064030901e01c030040000d80c0d03c3c0549100350300411303100075030b85855900114000e88030451003c5d41240c202100303000d0140000440c01011007030340ea141c04a0741d854050700c02d50a140e501c2150b415900161040f6001c0601c2e5005060b61807074006000d00d41403a0b00c42c1007102d070388203500c142080c55840300c81a5809030090001040240c400780301000c0d900e4240d0015401c4030040c18064020207000c2244d80401c40048840002541c0440801d110f2400304031200b100c3d001c10b41c1443e0003942621001c41c4c41e07400c0a0085d1100d0745 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 437220359 1250 437219109 437219117
    0x3e070b040807020a17030a030e1506010e0102010b0405101505030c1213150f150513020304230705010e040b0f10020304121b051c1b0e0a0b01030b0303030106 69
    0x30300e0303a4460044075002100e0603a404a401c000010300c010b805103100809a00c6400a03603100c80305034401404403070800020180c40d4110704094206400521641507000109080c04000f1000180040380103104c0511215049480d000900903801c100040f54022a018040504881d2044070001c41c0c0e240011390307802d02000010310405280c40408400390354040806a403c0707050304030685031850f5084416040c0300101e070f0380f440440d0307540c200380c0107070500350795130852500d401480d210100da003181040c3c40100c425503000c80410300f000a211001403001d413000c1d1096400c1ea40403a5070b03076284c8405104260118950322804104c6040c2401050f070030728070007001001280219000c1c4100354861400c14001c5020411010410f9082151030402c2c05004540c407c1d0481110074501c1c01c4107400d60007051240002015041030000c04048000d00c0e541e010380e0300c621000c550610a1003a142e0317504032207001c240c3c41041021001d8154851000d0b10401d0f40c040c400400c0f440c06050301c0f4402070060030001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 437221609 1250 437220359 437220361
    0x203071e0218060303190315050406080a0201050c070e1f08070b0405130b10030c020118051216020a060e030115030503030c0a050c01020c150c0a050a080a3e070b 71
    0x109420308942e404900038042e28a807041c05100300e1008031b0031841000100e40e66141c140c162041c1020494003404040d241002020b04184441c0d60312942000003c1c100040042d0060783d66006101d80e20052058540e608114101301a8020b90301001c0c10032480560b0760b20900251004000440310308481162640034640307800c105c1800414446001441c03481a16011160301e1038503204030340e20b503da80980d0b0000c0c01c40d003030b42002401e41d007030030b40c50701d2142c0030344507865001c01c90105151611380d16030b0920039039030244a80082502092000301a5114802c0d050000e030050300584038034840081100200100d55100e61032a40c90711941c00702074913680c0148002030700d0b0000c100023007020300c026013061400e00c041000300c5800d90740080720303145071504000c506d280e4451900c00c90680041415501d10b041c01050382004005001e2440410100108400862000c5805510032410000800702440ea80741003603034050b011034441d03181d03060401291101e5070300c20107015040d5120300303034070010b00185 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 437222859 1250 437221609 437221639
    0x60c060207050309033903060f1807030b1e13031107181506020d05030f04030e1806030c01051204080f090a1203020c0f030a02120f07060203071e02 65
    0x941141d41c0440306403104014000e01580c04000301c1b03000c01c1c01150001c080b1102082d81250078110300c0185a589a802c180701c3c40a07682c00305001da4040117601144159544ac0c070541998001b0542d1500e038a0b024140c4c000c000e02103e0031145114214040316884030903107456615a50400440318004e9610b0050b0404002038410365201c1201c0c8000c80483e61450b4950120f41600006001c0b14514969030700c060302c3c500030120203031400511003400580b0080c20806809011840001d04401c8000182c0c000181094007903400d0303109a0b0f20103443c0460002d40c610051118145c10307681c8a100e40304881030701c03400d9031003602101c40d00503c2d4003881800341c50341d688600644e0081411164031960512005400d91603103660f40006201d0340c0c40003005106c407814041d0905140e600d15a0191100d0b041c0b0711b840f6100060075064155060340e146042114803004241864403000e0b01e0605402001000035041e98000083d010490058070f0150000c80760005c01c0c044081c40c000b009411818038000e00300 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 437224109 1250 437222859 437222861
    0x8040b100e190b040612020a140109141f030507020715050a0e030307060c081005060909011809081801170709170102040305060403170a0504031e0504050d030c03120501060c06 77
    0x1104015118000c03c0c1c0740c1040340040c00341c0b20a9003184645441030b544190a514019103aa001042041408504a241c0d03d0008118600501884c400c0c50b59240c0f40a01645413428170301844400308004500c0034081c49001800380c00c0a842030750040c49000408131741c003818506010b601c042075440c2c040c81d2251645055801007800011a641804188002c001054050041500b00815580d4045c107500e40504c2010803690290001401040107100022031b80e25086425410344048503148250113003410b0b00440540300b0000300400306040070074032800400141854422005e42602c51020311b00c2d002488440b44001111070702c0010710010410041150304000046803440024005440c0648a03110b591511000703071022000100160980e501000d840d408083d0031202900080c8440c1c10140c8004025003004030a0500c10a0181440e440b2135015400b10303001450301038505c02d10301200f8100548a140c03019410340c0840c00e210880340d00c813a854800c4506940d030b42c0d02c60032819039494807040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 437225359 1250 437224109 437224141
    0xb1906051c060e040803181b1e0a0b03010807060305060f0f010c060204031109011d150d020a030f0b130515180f0d0219080313051c08040b100e 63
    0x480386560726540800c3d0a0590304169120724004c0607020b43e039007414034846901c0103510403400130f02d82119020b4100080340c00d00d14941c1e1141214003174160300030f04501c84000325080811640c00808000700050038a4544003640c126240e441c10b0721811561a90260103441d8111003a6900c0600c0c51100c4d9614645040701c009500010315054601d82010341d01c000890344550030a440245419042803011710300340c0d0f04540942400e062141e4401c01f140c002c45404080581082d91061000c80201580d84518056040281d0010110800c0523038034205507001000701d90003075840707100b04c1001034070a64008403a0196564000300404011030085c440203a00380014280c041c01d220341500c10441100204004468403400074040d1441240040c0084d14140014102c0c16580383c40141850104080c40f090300d502007211522400140040c0c40c102d0f05080d805a03c24040840040300c8281480e4040c1c6298411885840300e81c00e1500c40040350a800c4c2c84500c00c3c40f0403091a013002a40c1c002e103a00ea40 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 437226609 1250 437225359 437225407
    0x11116090c030204410303070b06040216060b040c0e3d110c090114120304030602070b04140a080904090c03050706020a0510050121080d020a030b190605 67
    0x508043d19800040341e0305c1c02c4880324031003825000000642d08803d604104580c400c0b265805a01480c082c0d002c66240e008102c40600040304200010711640c845030110b40314410080c02a060450442c40c01c01c000b00700c0d03004110301a80c5844002c81c0701e41d00504143c045180028042c2402c25103100c2040811003403010f4001c42c0d0148102030ba149403100c0d0b40c108050290684480059a5a0100b003c1ca01550fa40ca042d100c0c102100c010005100031480507200e168040d180812151a10707105145148525840180003a10001d81d0605100c91a8560790080707101e425840101c1c00302c1d01e0240c3ea50100d14001420311901044409418901903000c42d110038818007241e4031007a0360b51209030500d03c40b60321180158001101250400c1018041441c403412034000402c07035941801d03000c1a40300c071031304003c4030b6039030610060f202880741c00010b541a00c2c03141e607020740d540da0720010010701500c20420090b01580c1300c6403100055101d8410745600f82c0d207003595007a00b000b4001e085203607806100104 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 437227859 1250 437226609 437226611
    0x406060b0f03010504051e130503070b0f0105100c032a1401020d0b030106031e0212010510150201020702030a0303230103050109140d05191403040c05011116090c03 72
    0x104000380001030706040307009000700c5460350315040904c0140c40c002030a611403000100c8003118080d641d4040190044440181d0750441c138402c2c94580e03e58400c400d009818030110108100a0980190040741610002d4404c64107040409200b65007283d1408001030214459a100100421086010b250b00c41e0940410b4000fa40007515a51340311203801c4a4520340b039400040503009010b09000e000e400c1801039000f00640740ca113858030001341c00c40d0344211080750101c40f40d2100759903038040a800821a86802000f02d403c140c095103002c00801c0c07080d1044090105607603444180103100380d40f09c5a80180142400141a540c21002007070703000b00404c00c400d9600a2103144800e19806240038520400000a01183e80d04100010000d5507150802035030040e06030280316984141691890082c01c4014004040c4550064502c1030000381c120040f1b90b40402007000b841060000801211000e0326003148035807403045034680b0784007001030480e40c1030641107007049100d465a0014503510060b02e0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 437229109 1250 437227859 437227871
    0x90a03080a09150e090a020f071e020117010b090906030f0d1d1906080a02042408090c030705010c0c0e070503040b0c18101812050f010203090c090406 66
    0x385260158220a0000c00010000d81042c006002d410021050106a60400c40b0701c013641c0740700103485030800500306a0350540100d0b050391140c0110b8107544680341d0006030b10405460001080008030000b00c03050340081c0d1070a5443d5a00d0f5800396100c0d0589041316000781c43c048440b414400400c170003804a5801d4400c480200c100d040c1d050040078a00e0246648146101003040b42c00710625610503515481b400036a1447e620f00610548035500b100c0d5076003050786080d030329011281c0c0240140d501403050110b000486a207110030341e0b40a403207412000c1e1115545601c1e1850103903991104001066016031010b602400907601500e000d000943c4129040c0710215102c2c204010f600c68191441d40104d8004414032041000100c5a16400000b80b0b080303900381016a41004c5c2c1d4403d4103400c03140200d10707488403c032500703100d010884821040d000000c1d0080759130340e00c0340031101d1200e84151494002c80e500c11300c10b60410700072a4081c0c081c480061109035801001c006650b4805401120b0f1290350344 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 437230215 1106 437229109 437229113
    0x14041409010512070614071e0501050f04030e0f0604090f0603020a080610030204111e1314090703051807140f0108100b0313050a0501060303020f071208090a03 70
    0x8601b0328214001c64103580d01910078984003800c241c11200070b10100c01004c18901240c00e100d0402082640e4518842c4140c00c0402d940040c0043c2003040096502d1400d54441103116030010f020394985a80c0c1c918810480c0d8203507038402c0703a1544a50081082d46081c00030640182401c10242c121071a014075540810410307400001c3c81980c0e600c6603e81660312003019240b61105a0781d031404441d01c80025000b964000da80d10241ca0080a900411081025411030441c9480034045d0a1561a00c000507000b40c400142001c00c030714030300d41c800e2050040421402000b4031190240100f400140300c00e002c2d01ea148803c050b4140401e482c00d22940d00ca4a0b0030310b60884101c54450742e10798035464030100b411150740a0150880c81342d05105400e01030b040d0300c1002186e200f07400300c5100c5480e0550366501d840140c410701c646013480860302d001003411040206994400106400b80c599226 = true := by decide +kernel

theorem cover : BRFrame.Cov 437050359 437230215 := by
  have h0 := BRFrame.cov_init 437050359
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437050359 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 437050359 ≤ n) (h2 : n < 437230215) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
