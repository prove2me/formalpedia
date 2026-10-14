-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1813
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:46:24.597798+00:00
-- url     : https://prove2.me/submissions/dbaf764a-0b02-4a1a-abd3-8f8c0e3a0dd2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 325899280 ≤ n < 326079136 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 325900530 1250 325899280 325899319
    0x132102010f020d021305010203030415050a18060e070812040302010507060e190312060605071b03022d03150117120a1e08011a0c0c0306010305010b010f020601031709 73
    0x10454285643c2d134000356000e010221104040010306007400a18154982030b2604000d0101c140380c1000b00c940c1d58400240000107650090003524161300751240b5550051034544003d01325a07103c8808d41c0708074200000c074024002207071a000709000e081582480d18650054403e90480d035012150262a8880c00048440400942d81124000802d01851017694140688440d801c81c00a542c2141051028400319420104440d6144c0d40452585004401f60600c840090215000254000105030803003100395194884807a0040c244c03496504035031031030b8081640d1640d007146d01e075104004001c0100511203108a244003c0355042c415a000300c10200d00394501503016621340d0021400c10404070542980c2c1c03501400a40c1e4290520f07400300c3d4141300342601f0502e9a0043d685905a00084070b5a446c0b03020300a108007224060100c40e1156102c1ca00f00b4007a00c5d00b4021540012052041d805402e0303c0020b5803030403030384c00500d50001160010b003030f040303564010400e00d40c128418070180c640b42c041 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 325901780 1250 325900530 325900537
    0x7090513060f12081e0702091509070e010c02100504050a0801060302090412020a05030705010f0506010f0e060f1c0209041b08070309030507020613050a06090302090f042d0b132102010f02 82
    0x380058265642c50547c030400104c414082d05021900c001080c10080c2c0f03484580950340c010006080c0301c2007400c3c0d440d0040310300350440c2e1002074200701c4840c800641943c10001030000d440003141c40307120050722107003040c5c00c0f101188000b075880860b500116010270741c042c0c01c21040400920548a045016480742895981300000c00c0320260365130100c80015107081e200d07181d0041424600046503440da010010b1405090014251258000040401e503502c814000c13a174010b00001480200c03c0c1c901140c42009401143c4014000c2c0d04203000d00e158500d00041400c0d0101607500c40c0842e41c1ca980404800508401e20118103001c1d0800c10100944c1e0342d0005005400c4424140702c40d000d090509101a03451194011020321050200600041e902c1174800356001c001d030060f802040c0e50310f080007078003c41659070f424980104845480c0c4404003501da00b151490090f68000a05c2e2609030100c071300e500c01d420f00070340411464070141c40d181c507a0a48a041c442502e10010442c015004608400c070790 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 325903030 1250 325901780 325901827
    0x1404030509011d01020a030815030d03090c09020405180402012604050706020d020a1407090c050309060f040b010909020d0204020d0b0108101d1e07090513060f1208 72
    0x140c01041400380c941c0e000b03040d02c0308010408580325030310a0a00c0040c1d030b60b0740c03071860040a1211120010304403000c2810426401b4400500310382d0003821000c1d01900500e041c2c1015201d450051030003058103a480c1c02110f0031600058001102d10794400800c90b40810050300890400c5000c1c01000c0304040b0340d95522407298080414044141040d1808a01c1e110541e48010f06542060700e50040868000c00d0354185550080d1000388140e45c1c6451982c200340d403d4200e0003405181c0780e00c11852a901c1000346110700100011601700d52940710201d0a200e500721401022080c1900c0180500381c030300d4201140844c800360140c0940003469000809a170400e14591051a542e0501e9003099a03015003281e4014010202c0c0c0707064641080e40c4400c0c1141d1502d840302e181c10004001c00c03440d081866000d803006404074501412400c10342e5004255046d81c0c8035680c45281a220364003040203c5102e82d17030854404405144a0514101200c1441c0300c42e06001c0c0c0307040f10240b0081d28040e122880c0c2c1b81066 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 325904280 1250 325903030 325903037
    0x8060f073219090b0306040e0a05060702060f0f0402100e01020c090c031005150315031005010b0d050108160e07111b01020f0610060507020d050312090106080307020112050406140403 80
    0x1440b85201041440c240100100100b20f50400108400c803589001c894018600f90380220701840207903a082e1500401700401401c80c8114001c00400c0f941c0070a21a00600586090407800c0c0c0f60b0502440480c507090301c01035031082c2e188910314001801440280508107041c0191180031450344009180d4a004480d1200c00403070020030001e910440d004658003800007141c0c100074041060000c8580c500008010340220002601c0050b00303641c08001c111a186680e0809101d5580c440882c3c074125000140c0c0080640d00f45000810000c00100b0b41281240200c0e0040005030315105da41950400042c0491040c40300480000e008003000b4030035160103920202c0c0a40f281d4500400080ca0108a003c11800e6030b007025003808803800904400c4012a2564602143c6821607800026529540c1c00c000404900c0300069501c03c022030300c42020711a009400003000044d0f81c55103495100c1c418610000d00241e07010608158116071580151f0b00207001d04000a02000090450ba1489005940c282c011 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 325905530 1250 325904280 325904287
    0x20d0b010f0318060b031f060509181b010e0a0305160906050901060804050c06040611070801050903090402130503010903020703060e0109020604121109130b0108060f0732 75
    0x95581110844030801000d281c01c2140c40208000e20001d14001c440040006860700c60020355a03400704034690880c80c5460301c6448203d030200c1075400400c034900c5464040c4001e040085c44c0051480400808501c10710007501d01c030300c007100e240501ea02c20603100318107010700046800c20725241c0c08075070740c05144984000d000c0003045200b8418050300561214083d1401d200060049440d503c0388107044611601740b14400391114507041e8200300180a405130003510115000070002c0e404040032040c1c2c01d008003078074802e585582020342610b074112401c949940c020040391141e81815801003401045030304491190b2900c0d0780029080d604407800c2900180e1210ba028820321280b031103140c3c07454945a00820100080b640424018040c91080c024000300283c084801e00504180c4007404420050486146d440d001c080d803c08400d040b1700070345446143c0000070032110300c0080c0560103507030402c510452039620f40400b21004446000d1444114100c1000c2950401000341c001c207001b501943d0650720b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 325906780 1250 325905530 325905551
    0x60e10080105060607080403080a03060909082109190f2109121718150c161d0402030a0c090c03110a08010b0903070b04031b05031605010807030f020d 66
    0x2c0da04050f00700d500c02c400070003945001882d080100c074110b940c41000c9544610070031005500500e0b1951080100354100009070040104d010010031401040031500104820304800e4175810403000c07a1190602ea0020103103d183e0065003251200301441742c0c2032a40021220303500c0c0b581ca4203211118009020101c1030b450407040d00980610060b1400c0b00c00312303011408c2d031740b20b40c081c41180100c01c9117006400602500365a1105c10700701c03003038100601003034800c100140d00b50140b54060004c070f00540c051408056a80c65074845581c0440b0301401e0f102200000c0d00b6002c49050034054000c0741d16101e54502e82c4000b440010b80c207401094000c00c00036600800017009000d489c541e10204005800800100060726086449981500d20344140c40e0345a60605000c24541181500074900500000c5000804c20050250382c4126440040540040b0340d65541810342d91860a00348801d0340c065a0000d100c3cae5445113040c2c5a0103101c1d407038082900f00e8100712060403a48200b041050712030b124629143c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 325908030 1250 325906780 325906783
    0x4050a0e030c0d0305010e07140a1214060a12050318180109060807050d1505090705040e0c0f0a210305040e040f0302070b030610050d02040b0310032009150301060e1008 74
    0x2d0050081c9141e507c09450301e0340004040590403034084030380c01c0001c00d44021079031146190b0380708010116010005c44a44400404da330f00021100715201c1c0381e200001150840c0c00c1e4415030403c070f42c408019414400000c40c3c10610181181440e60004000e0508042001010404500801d1100400203495043c0103109041203030a07013225001e0041d011010b8000f8101210000c28246c42c101c0024080d22407508460030203c0c103500069100b03003400384440399404e0102e450220403e085842444045010701840200052881800110108400a001651b61040844041500c2850064642038891040c400500e0090b82c00703a034401190ba188008054041288401820f51000c060742140f500a000600d03007404518410204a40840e880d40e1602503501610082d00c00d281d035490b220b02d08071a914103941900d00c0140c0e40801c4550129074001c0440c80d18180710710b4080c0c44c41d2070541d503400c11102c01c1207141c0c05080e0959030f00c000c001078049032500c0e420300608611210b910030703a16090b80103 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 325909280 1250 325908030 325908041
    0x180b0403110a03090510021c18050d0f03140f070b1e151306090203071e090e01030308090a06060303120b1c0b0403111c0314040b0604050a0e030c0d03 66
    0x1074842e4040a2448042034104094004031102112400020107490b98200c0c203003201c02e01c66809840202d00a0754540d50040401907041419289007a5625500c904204400e90b00160103402e040c007000c0c4550201c0d02c103500030f07120b0702000400c0b03034500502030303d0882c065070051005440d03001d007282c20310203010720500c030744002c90920144180440c180840340c19214076805003068031440d0144c0ca03071560071005801ca540201003000c3c0031500c034079064101401400500c3da100710926103103071030f1712803041c000c50065065481d1020b81d03203005d03802c40c3d0b000e850000001d4a5008180318401c92240090000c0c001c040107584a9900c240b0405003010302002904d05599800784917040e003581c1b140c0c1680407550341c41c400c150403410081e00354445007800d5504034807060f40c004003400303886001700c0841e035080c515004151980c0e0b410026008060480300c020402900c0081031109400085040c520f000d8100e903820400141001800b000b064160a00c0c55029840201a5801480361049013980500c01c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 325910530 1250 325909280 325909307
    0x50a0506060117090705210102040e01060905060a021009020f09040f0308150102060406110909010308090306160c0303110c0115031401113c0318070b0405090406180b0403 75
    0x244103c90406242c95070715040c5602038280100100410300d5014200c000724075104110b804002c558a54942e045094020b400f4020000460742d0118001035a040480450300021039640c0605581200f44a0001c0508951001642d0002d200190203182e682da001745640194030074051805145e8840c0350107420140010090f4103030606084c42004a80d8001c5003045d481944648002015210b0340b84c100b10354000d0607540c03034014001500120404c41140024540490102c044852995500900c00c0703540142c0890100050340303000c92900064000d070405040050316010040c1407480651005084442c00d2081190b080d00003c1e0400612050745500703820400d081f402800020200615908548102c2d162040d42900316580d01084088070600320490704030034442c004030302480c2d101708035058000350303501e0402c003031422000c1c0c0c104000040d1000c21100317406042c4e030030940b81004110128100420955405841c0c40e02c1e0b044446482a40044142c4140e920700c0745400c043c2002000c0c980050b48 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 325911780 1250 325910530 325910567
    0xd0203070917030f0715050c0c01140105010c020108060a030b0a0b0f0a030512070c03020303040e0a05091b120c03010c0201060614090f0402210c0901030c080c1b0307050a05060601 79
    0x480010700b001c811240034a40008080c0d59900c03141c600815840e5800d80da9610790f070300e440248100d20704294000c248420040c0020300a51728002c1040d03040078401c1c442c0e9030106a00303842600c01035001d081103d034001c0700148003017231555894440c07800003281280c503d098595910741d072030340914040d07645003520314080e1042c0c550241155a941d40e034502c0b007504c401405d50040740880800c5490307400d00f0091607000e01665101c0e66a500c1c0d1942050054801e8600d140c203100c001075047c600060402c2e00051194aa00200071591050003208000d600740c220880c002d109001074680c80074010400010490340c00043c0d100c2ca048002040c07911110380e0310825240400080080e41c0e600d00f03845080030821200181c0c3c680e50016007100f040c81042d6855091544403040226051810000c0c004040c0c2c02e03201404500320020702103440820841e40394801380d2060141841c800c1010350b495220800e110f04030b81c80c11075103846051400224a208903940c0c1d001100704102d65903c590020f455828484 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 325913030 1250 325911780 325911809
    0x13081c0e0f01140c07020a1203030213050303070209010308030c07060e1e060112030e0103020c150f0703020f03130f0213020a090608040f02090403141606060503060403020604061e020d02030709 85
    0x506040074010f0103001014024800b00b1420217558403407034298000d101c404411000c440141ca0082d010b500450300010220109034000100d81c00c000c4111030200f91f0040020001c0c2e800c0daa0341820a41014041d00d00c03c03142803140900182c0e40784030703596060206200810500540f01ca190004540f030303c5142c2c03c1c903080b4000420550903402c1003d280550315007010300b900400080100c009008119004000c2d2141c0e015000b0318210505890b4045c20621403240301f180c0e41c000003641680f2031802c001404d00000c00c0000d1001c030342034854501261249050f4a450242500022104211402c241c400790340c2c0000c101122941010f5900000c008a08005c0318504c0c050700d40720010090300d1000781c0207002c0ca800140c07c162003413041a440e114107402c404d8403102d5030030500e025000010b0b400c039550391801c20007082602c1c000915030301c543d40c140d004101c1ca0ba100c1d69043c01038680d083d00100c01311074640c0e01d004003509034000f42980030040d42c001070320b83c81c200e40c0c000d00092381680b10506410300d02 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 325914280 1250 325913030 325913051
    0xc020304060801060e03031309091502031006080c0921071a07260408012009150f07050136021302090d081305032413081c0e0f01 57
    0x71020b103044030014100500c58602c80030100303080d8412050345031014403080d200416031701100d0f070007078201d1802410002c000a07200c8c00d24400b00c0c0b0040e541107108854441e420481c41d80308815055000b100c1c5280e06082007600400304034207000d0903240058048211030560561842000302d035004012216091100c220062000c95080c811500301504401c030445200c03005400b050302c610b810752240c1a40f01d64803a902c10300c0600800104600d10400c0c504c0207122115000c02c0e60945881180c01402c020a402c10f40d40000125444a0710f18510210141f04413008981700b885170455004401400e032419081020070190034103000c81585856031007064000025031903044000103105615080141e40d6480680060740225004200600d221130000b49504002e600350300c0002159000c1d0700700e031030080d940319078044180612403030000d01f280c0540c0065102c41410312500105809910218901080202850051007010f040c040016032a0380c003246621408012103d0121203402c020880c00110 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 325915530 1250 325914280 325914287
    0x16050a060218130513060c1814030d0504051c1406040c031208041109070c020a030c0303030b03031804021321030e1c060c17040b1b0c060f0408040902130503010c02030406 75
    0x303410000e801c00e45d48a100100c45030203060501c034003000c034400600100749d8070f40c40806004403071500c450180c00f503c140075034081d025806480a030782c0002c1603c4480c1000003508614240780d44000d0300c040c003403640604801c040c14403240340038501803c3c1b82201141903041c50050035030450f00700010000c84008100221740a000c414800050480c0c00e404551918032044030b0503003c41700040e6010301c0c00d140010401009070203000c2124031070388050029040c042d040680701d001c0c0d010030480c6101c1c0000410a9440c1c207078000d1840101d00c41d5101543c0b9201c04140941080c810020003007209462003400516401000201c120081260f0985c118040e04401c0509018190001010342d034036500150074a50090880c1c0d411090344c1c0707407100c055280c0b0341080300f82c0c1c440584020a8050104540c20016442c0ca0100d991130503000700140710b544c40b86040e00d0b0503d17070005c10544107000309001c0403402c0c0d0000e00040600c012001501c12001c2d041c03070100350031107100404000c00e55000f00020000280c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 325916780 1250 325915530 325915561
    0x804152a03020d2d200f0706110313060509012a080c0109050a0c1d0f0403050901090503030c0c19320a030614070201050103030516050a0602181305 65
    0x2030300e08104041c02100301c0000c2e50101c0d00041c0c940c0c1621000045100b54094031005017112413450000300610002d0b4016120a032941c010905038000310790601205014548501600441500300c3c4c0c07925040c0c40c0d84000c0c102850b084000022000281800c0e55a4044080c082c20030040310354518a0000d03000350040f0303802ca140010044500481d282c7e640f648294001c502c03036904041030b02c070b00040a1a0084182d100390141d80100b888045002031000a041d200502c107101c4406400f4140e180e039101650f4a4020008a41c1045030444000c07030142c8052018040101c00c001c000c0060301c00305030401030f5840c558003a100440000b52410402e9190a24504200ca01014000d4034041c5050100103400c1790000442a0400c6149800108000c3e0315807154015503a008410b044076100c8082c1203081e02c1c03003840b010380052428007540c1e079907251454091080c41d20074000c85816031020b9072884141e070000080f50401e4148005013901c030381050031000c040142d00e12000c010b81c3c038207041150305074078 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 325918030 1250 325916780 325916803
    0x5010201050f0c030112080d0911090906010501080a091e060515030606030304090b010512040807060c02010504020a050f031f02090a0501171b090409050c04180c050d0804152a0302 79
    0x410030203010301c11f55030b086590b96844a8002d201070a81400e00765100c44116606500640c1c442001402ea8000442c0a80c1070b120140d560f81d486881e1111440c01414108a00381c8418010380340203084180480e024411883c0f09090105040c546034002d51030020404601d94000e4028004001d450f54001c000c81d0156500940300144503540b501c01202c01d8060141500d41507122041800180081300000d818400e00c66101400b20744100f4100304d080c1c0f03c0070354009400509802c1c040c4a10704e0324950301014140060304039420444c0030f41c0d403043c0394a01d281107032840c0ca900003110740203800c00340c07a4080985028201405581d001c00124000749900030114088110b00894010b0078002800440b8a0010000c105001d08581400d0040c0c95208558246102e9454501114000d0705500400050250401c41c4040200d29100900030300003440340b002c0344c802504010101d00c4081041121b02a41e4040c1c1d1000d912001c0e465402025043c1910304031506a0001041e40c0042e5000a9500d03154 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 325919280 1250 325918030 325918049
    0xc03090b180114011e050d02010512070e060a18060519030203070c06020f090103050f19020702040f021218010618020a0e0a080120040609120809180105010201050f0c0301 75
    0x1aa02441950043c400802c0980c1c1024000000180309000c2d10343c980803071006102001c0d281641c8408020410103020702c02030104200744042140030103414100b61f4000b00a0508078041e90801002803210350111031188049a9000c0c85a2400c41885203560f02824050078094580110059801600820901610b0405400200041c5114032803000030207101c0d84298107640f21079025103c2e51450b001a0140b40c006441e2000080702c04041c2c14445000340324140789001c0c0c0103100007c0788065031042200742e0700075807115504044a08a840100440d19406815017003509014407280140902c02143d00d54980c1004005d008881c005107414910a0b108580140c0d6400186010f4800ba00202ca055034080600d9000180c0000b042d00060340b0600716480da1200e2151100501503d0f00450142d5400144805028001c00c80d4416408031064010403206084c0a4408005644080300072440001c60700310300010000c40d6024065503801510f4001e401c4d00390720301102400090b0005100c2c09c42d01 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 325920530 1250 325919280 325919311
    0x80402120a050319080a2018130209031002070203060f040f020a1e05010201090b04060c12050c04060e2e051b0303011e03080a1409030303090d02010c03090b 69
    0x40d0003009407503416036000c026a521480e00c032082011114105507040301003802030000a0345a811845445d4903200680802c030007926a82c2d2407a80d581c0c21119200502c01840b554480180d42d4440d075060880e0a1500c0150b86c83c200c00b0249401c140e445401141c0d60307401442a00c00603500032903001d5101c075502403501210350301e03420007031003a48142c40060b412410b002004613204188504851500314424184500c040c1c1c0c80d40120300721010b900000d0060406013022034005a071a80040c580a00035240c13005075035201900d00800c039a016114001039060024041150541101c08807000840481d12403609a280407649440348a80340050f108801c88055000c01c4540114141c0d51541d650035940d051900592400a550f03900a01601c0662003d003c0740c1d4080004080c4880300741d9a02070040c0c0d041c1b07000007505440c881056014004c5074031040c03015540716101040514410840d01d0f00a14408000600203400c45440100340010103091024030382c00319400e590401d17000001c000c906d000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 325921780 1250 325920530 325920559
    0xc03041205090607030c030f050708030103060c0e030304080106083c030c0a050109020f060a09090b0105040909080306040e073609050a03080c1602060c010902030706090306050a0606080402 83
    0x60707500c02c444007030798803040200b000010302d0351050091255601c651241a5a4034000781c09503078901905400800300081000148001003030b58100803040c0285041100000c0c1255000078203503081038000d4406699121010800c0380c1c0c0400240d050766209103c0314140001d110505440c2410310000407010300007814a00c81000c1080040b03405e110110030554030030202d18a03140b4042d12000c54141c2c032a00c40d4000c04601d604c0c0200c01c80e02d040c1d02546910501e40d01d46028038000d00090901c40e8188403091000007034182903405103001c0c142c0701d0981d0554900c0c0660801c021601b5050541240750701401080c8070447d0540d81c00004120380e0b80410040101c001c00801300040c1a004020340c5505040d010070400a0008005d07012074440c3c1c179182d09680c4d0390004240c440c01907840c68199120016000005801e0000c01000c408903084000314204000b6000f103840d1850940c0500005100d2500800520100e48a00c90700708594010500c02d043c500308004190303070b5020700301a01c180c0038002c4410 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 325923030 1250 325921780 325921787
    0x90118090608030d0e06070504060f02100c2706121d070602030c0d031a10030e0d020303180703051518120a0806010305040203250b03090106030512030c030412 70
    0x1059203040c28010191680c2c0c8958583c2c0000444442c3c0c503040c40e1071901c401c00003046091040b5020307a0703120300f8180350030380031130321000e1228038082940a078110441e290b020300e005074540c2800f07680798100c600d02d4000d9220111a240200d01600c2c003a4000148601c0e90300000703051f00c80034080c2001c604030202003845481c450560018200b54860b21000280c1c03c0d0300400501742207020007081d5401000070b500140d00b690a0b0800b01035011071804003c0345540b5290507010700001e000d00d800605c42ca0180f5200c0d00c1c100c0030305400740240c0c1c004030401c020048144940c030900490013004c0c052107851603903129a00c1d10f0f64100c0b00144160a00081c1d8424007070b150a0300001d92900848500c00300c252107400d4280e00180b1840008ed40700030006d01c03194000c0c0079003070040782e014008200c5071002110001100c03c0c007640100c10680f07800c1c000a20a04030b0b1000d50701800340c00340000340040c55483c00c10314003400c680d10802da4010a2080201003030070442543d52140e00720b40d103607011503080c58085 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 325924280 1250 325923030 325923077
    0xa050117043c05070b0f0d0f09150603140d02030315010513030c0504050a06150c051608150106181e0e1e06090108101a030303041505010b0702060901 66
    0x100244500c0c0b4840d50055040428040d1807a0089003a14101d61300c4005c8035200740305007a01010740003810820019000080d034840000300e1a009400180c0300e0580e941e03001002540f58110b0324154668405000303200b168441c451200d8282001040d420203120b00103501c90000030014140c00c0782e140310000c1540d02880840d42041d087c0d8104102e869120b00e070a0044094502034103019a00c1c080000e40841c06a10500c015268034411943c4000000c58003180e4041004404807014060103050503107401040b905000540100c5000d800803201100301011b51400581c0b14a042261442c100b90301141004c8000e400d95501c00e034516034451500c1e00c0b4100c20134031075210805919583c410800f50340e02e800c20b0071411055000c85d0070341548400e0100066008207005101c000c1c0c010040344400002035510807035450307001c0f500309811142d1080001c0d04580003140d0540b16500c4807040b41070512900d12801d0b01403c00858003c0c240410303500070410500641c0810b034140504800310350b440304001da101 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 325925530 1250 325924280 325924343
    0xf031109120d110c0127030b0a06090e15060d083603011b03090c08100c02071d040201110102090901060f1107030816020121020301050a05011704 64
    0x101490940400c1032030390b602007074042600080030351001464441c0d001c915060034040503503c0744c0039400035048400b0489541202980035000325000000003601c4020501d02c100c078030a400044a0703180489000540380020010b03101c0380c00c0700c0007540c070141588847e00c2d00850b05070b5840440c11002d00d01a40035108010003007000520401c1003200011350500812565045040000c003101c0c2040c0c141400c0e121400140140801040b501d110441d1081e4130a90003103000f0400c0e40a03140d51440d44504180907511140c0c40f03682c8402c010041503404002040040145011b55011042c550344a10700440010b04002c2c108a0901c2c00c60b0794800702501561480c2c1c20003005c83c54079507034030000642298070580d42e240200b031043c4017002d070a510100e0600102c2e0303001181036140190002c4071400341d214201c8101d040c005042048c034803c1032005c07403405801450440060756941400200041001554082e5040141ca000707139090040c480c6030100c2d04541d01400c01d0314203505014840540540c601403 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 325926780 1250 325925530 325925539
    0x1306050406050103111f0807020102071403120108070305030f030402040f1b02060709180209060c16050312030403050a0804140f06190b030307030c1a2805070f031109 73
    0x344000e101680d40180d0490744950750f800c0c1513103000028088817a0090903419111070140005070308542c0101e5101c0e5015915100041c275100c47c558404060f9503a442c0080101d920114546001030f650110700c601600c000d4000b4415580341d90f560503a60701c00c0d28541ca55803040400407408544890700412130609000c00706110828001140e055600240c4a9040061080d01b0101e1901401510900142c805880f1a44608050160b05201941c0300d4100141c1114040052004030141440007c40e0f00038222900764030640b415040502e0400111f9800403249401c205000000e5000303411100715004030704285166544606102c040704061405929082c0244a0903ea0011010030514841d041044000b941202038440f00c504494000824a1701a4010080c110110780111004070000b4401c56098904580c0481c01643c0b1800a03140704401c9200c200780e0681c41d07040d44042240030a040c880030000d5103441c21008003000724200c050303024103585981c5107403076240302401c803001c0c46005031 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 325928030 1250 325926780 325926791
    0x110901060206071707021504080d020c060718060c0b040204060302040e0c24040519050310060602010509060408030105040b0d0f08190c0309180e010c0509031b0303030406051306 78
    0x100a0b458182c200c0c1c0b0000051500a03012046260b2200d01c1c0e40640c0d04e643c001c10142c640c11040b610082c034080d0003560f0714a800e000d248402505800208000703000e00018040900b0942805401030300701038650b84000460080600800d0360043c09807801c13075000106409079480b00d0000c20001c011640010f500103041504901c5940c20005018201107425198803040304040e0b001c03d07004c0b021909000c1c0011908000030482890078004011314095803d480e1440c503a0703640c0000e03203000d00018441165030380324603041046580a104a5512030300210240c0403d18045e6036001d0103200500506120380d0b501e5002d5a00c5407150584076055540c0f150103000b5100703103030030f11a000e0340000c007003036141d06852000700f00c82078440d903111001c8030f40c15101c00b00001e04107011490b441d20f49201507060310396034000e4425114402d000700c220904541c4c580941e80d1302d5450078141400460490706002040040c40c891480e100041180d50142e00518000f42d644c680c0e6107441c05218a426001d06601e0401 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 325929280 1250 325928030 325928039
    0x6170415140114041103070e01050c070602160e0601090312020703020d060506090c041208160203031b0c0609030a12030212010e071205131202070b0406030b0f0f0d0f110901 76
    0x1c1d07914141d5600c0034a0f1590355094504100c296a41d0405082458809102154400380101400c1006400c141001800d100903410721500c0d200c003d500c1000141e01c03094441c1c0014502d440810013502040300500d9407403501e800064111911403100404240000e220301060078402d011002c007641d80100341c1f03500e01200c1e0070308070050401542c16034407401422010424010300740046404488000403003082120f0309895500c1c013500b200044a44040640071004016601070004000c4038802d4803118201040480c841c61030400e045890a0051070b04100b500140d41d0f00140003041c1e135a11810341c015040c1c400400700c001c3e00850707407a10447c810000c00170450700500d052a91140b80e80c1e41c0d41d41e2071011030075000010740d1020b6a04d00c2c0485034140900020601840740309910f0049401201c0e4165900d050454103030740b2582c04480029515030b0301110a00d040b9155403546d120850340d0311503a101c0500090703c58034000d0340007032500d50100049810019104110340350381c0b0300102400029030b5079 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 325930530 1250 325929280 325929311
    0x7050a032f0604020307090c14071113050a051609090e070b13180513410c06040302061c0605041109030d1106010b1b07030507050a0f06170415 63
    0x3e9608a100c1d02a62102080902041c400c501c40341c8400c3d42c4001d40c1c030518115502d42584000002c0e01c000c11422001e4089484034495407a4422030388200081a281040060b400c58401411481c6200c1b1582c2104a01d154012645070590300d1600d0001603011000349403030702c0d20001e948084031011011450302018401101120103c4034049100b624404840410204441045800d91007551480c00e890000c07481801140300e0000d1075100e4a040105001a107a414040344440d121992010198040e010001130050014030345007507030700c14203180c11940010024010100c0101e44840c3c1045203900c00b400a411540050074054401c000c19210529140d145501044e4510701030701c0790440759807000e4801e8a440ba000e80340c502c0642003030313402c100f501400c6601403e004032130048006010305031904c00340110001541301d60024081549840c0c00c3c44181880ca50000f4074003180d03034404025040d041481410101036500040c841651603140038040341b02051244040d8a1420603013260b0750a0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 325931780 1250 325930530 325930543
    0x1e060c1819031a19111e03070809010509030703110c030a0b060301060e011508070c12090e060603070e01050c0313080601030302060105090c03060d0c170601060e0a050109121e1a070507050a032f 85
    0x4582c0d940d810654ae03c0300d609003a50b5054400c4c0d11070b940704114a0012901c103c0c1e4800b0610740441c144c07001c40400d040024581b450710030090303c09044400a01c60b982c9400d105140082200e6108901d0f42d41c50846031402070350315469008107004980000441c145e200701d54800c416680191080d03069546550001e024000354011150548001c201240c0140740c17902c192841407909907501045c00c0c0d40c090044490781c008690f00000c0d80700074883c050b180007107926580050318210700241240d40c55414000d18094042e48468042c0c02104c0c1030142c0d00c038105040720f611590644110706940064030341500381c990154070065022000d22803003d0b030201c0c0480c0c504d040701c0d615a542d00f500d00c1d10600304a2850303200d1180c1030124003d03060800207039014004c00d9051a001e01d40e03031520710302c44000310380030140103c2c01105c10004905400102007000303180c0541100c954540503090568175901c855641d404218050140800c00c076010341c2c42c580c80c2d030078820074240c000e5106925503407a4184550b40c21 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 325933030 1250 325931780 325931791
    0x290d061d0322180c140d0b0913032a02150706140106090905061f050a03050f010e07050304060b211e060c1819031a19111e03 55
    0x100e8a02e012241000e0454040c161105010018008802e072204030005000d0b440444080c04011160405400800005088442403040c008078540c3c0020b0100b0022241c02001060310384070092070207010036840542c1c00c03a02d034003444082180d0801c64244040c0b6040001d002540701001c5406c04210010000180140b54450304051025005150190000000034007078100041c01211041210b0700c205c0c0c01440d000440600702d0004640d4031303d0342c031400e09404500003000c10000140341920541c07511883d948030395060b0341d1604d103504000c0040b9400300098007080c2000307008400700b4284213059100010060b0001c1c1040da8003400f0b800c2e000d050105500e01d00380a030160900080196a8800540000c1960900948042c0d03582128584031034002161025201c0761405520159031030790034920114241035806081300601e5450b10034106ca50020421460000050030703c031082c0788900031080b60914001011581c1c04991009001074001c0856039a034900661400701203602c8544000d50240 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 325934280 1250 325933030 325933057
    0x15020405040c02011e0b0117010e07020706020a0309060c0302190b01082a01180b0301270b010206010303050d1416020f0313050603040303061710290d061d03 69
    0x100030b01d40c0306a080301c040c4060984001007140b200c206050b202d03030240000050505200ea081014803804802d00e00c003d80141d105001d00340e050020f450f804004a01c000c103401d00c0140903081c1c1980e0010041101ca2041c1c1b41400b00622429003014006d002c408000c00d540320042664540034100080d403003800f8401c5011034040c1c0070f154010b40084466103041d56064595002c8001c0c0a00011a8808613540302e00181c0030b03001d2004030350b00a1000045000384004428284044500385000f0018070701e070b4046542c018a0302884103016600031404a0460340c150030b2441c0c403040380002c400050300c1080ca210048045003010441108008071102101246690071a6400e02220003460f54910407441c08152000c0850410000f518207000155801446490302050071946d501001044510540e940c100c560051a07808079030b41003510580a0340c0984402c07540300240110b0091302c801c00020105e80c040c2200740500c00c107010751074000e01410f501240651711000c008800103a1250800035a60111 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 325935530 1250 325934280 325934291
    0x30308103501020a170a0212070f030c05031e0a110703020609150f0109020d020d1a011205010f090b0d0f030801030308060d0b01050105030907080f0d03051b1b0102071502040504 78
    0x5070205200790340844195458003002102c8001e44140d241e04010b08601703105408101451207130055a00c0d9500a2040d5218440e40050400020b010760f010045201c007080424410403a0081e14022001412000c000181d9001d44481074410007034204000340301081140000c1d0f80080650001c1c00c1c3c3e100c0d80c42d440540b1800d2410380301d460354040080c0c446400254041d40144407001007503006020303042c031241c00189404202c504000503034800c1c814210351a08136034428001d55800c515901c0740403902203070070419507042940c074800f030701c1e032a00548a050b0f58541c2000c0b02030f00d4004c030300c54000d5005030490310ba842d0203103001420f412090204030005803000003c01c02c1d60419800c096902c83d80101e00e0700c0903030300709001115542c0009058502c02d1058003000186560140030038071444015001500308000e90348009025250058a503000090301c0c0d46000c200c29004030282d5030a03030f034188000d26071152100704260181c0078452014085205040700c508401142d076004100320750003640e00f4007a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 325936780 1250 325935530 325935629
    0x1203020f0a1106030a1401030c030201120e032a01060902031b040b040b280519020606180402030708030a0c141c050c01020d021803011508030403030810 67
    0xc07a8100c00a00411072840311402c503890b8604240507641c003040c1c44100140000700f20301c120040100c20b074401c0c0c42c09840c1e82e506100b9542e0003a40140306202c5050103002e840e10b1040e0641d640c0c0728146502d50bc0140c400500008030030580b1310f4044510180000307000c41600c640c10b40c8020341c0203881c18121b250603001d80c180c54120030410340d000c4450010082d4203052500c40d49805d682d100048244041c82c149260040307100000e240c1c11004440c981d41c40781c5642c10040c1c000c1c1021801c400314401e56100404201c025a1852882c010301400030703050001d681c03200d10201e03140058680188072540004162207040550000100c0030440c0103203607407060070b00d01c0d651298403460190003044001c040d18480208882c0038200a20204d0801d03800146048241140382c42240c000010100130a002d40e10640c1d42d0b4a000d0040395119485c0c45102203842d4a8812080d50380d01c51480000c003401100ca000a034039142716544000108041848100000482c80208411400080e11080f02030415184441c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 325938030 1250 325936780 325936783
    0x603140f0406050615120f010504020c0715050c030a020105040326130c050402070c03150b010207150201060e0405030309070803090a05061b01110d0c08151003151203020f 75
    0x140100d400c011a01140c1d110380d242c0d40003070f103c0142110f4028482c01d04c82c40c4a101d420001b0100440070018440039404c006084554a05041e40b101c0d104500500c440142d0341e030080b41d00400c03244071611b004212440410181c41e14064410550038500000c920441502d13010740040d44a43d12070f5480c04120b5600e02d510b5900400750081c2840d481140304000f41d02202c602c010a814107006030104104966030702d0006050740e00c407400c11640c1d802a100c04004014021a641c2041030100f00180a54510900000d540f41c4c210311500a9038400b0343c4007032003424000e42c0b0200c0a001260781c401d0261426003821940e030350041d542e1004a114000001440903004010780b02c0383c0700000e054503441440d006c20007555800c880c000041a000308807001d00205400d00c81c0202c0c010b10507850903281c1d030b4540070b83c034100c50903400d1078028802c0c90003c01c01140845200f0200b00c445c200c41407a0140200881240142200354034546554001880400c4001600b414105038600c00d034201c403140e507040d10b441d6 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 325939280 1250 325938030 325938071
    0x111f12241a19080405070e090f0606240307050403080a08160306061b032109021c030f05030c0c0105012601150e041b240f0e19080a08040603 62
    0xa024410101d03150b9160038031641403680c100e4019030031a0300d19500c4000d0004c2840c400d0f1805e840d56888680b004d280c51205122856220004455000704108990240c04201a21800d000b0100340f000000406103405102560007440d0407403202611a070324000003416061064900c5428000b040a04881440c42800749405580740c50391100390000a003624018a4041c004040b0140400c07402c40107144c000b26080c4000c9110041c001241e800c2c4e660052000c107450b01c01042c0160b2030400c1e2010042034029940000e8809a85440766480e070364000090814000c030410f5104a509007000004c0b6042c035040c108090180c7c12044c051042c401c181198200e603011800742c041000506010025204088943c9600500454030f008040e0503e22a40c010456181c00031000404261900c0308229000b04404071940403d007030407400c41c121140094070000b9820981481021445890340c1d07064044219100141454005c0305d80621143c03901182c9500240034020010385400d0100c0800c410792030300c2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 325940530 1250 325939280 325939297
    0x120512060603042d02030a0f12021b06030c0c0604030f030e0a0510050405030c060c030103030f030c080402120709021303050609060408120702010b0d080304111f12241a 74
    0x8164211060100c100001e1008040c1241e03ca41c10004c0303002684041c040401410b104605902074100180713000c403640c0640a0494085500040721100f003a48160381d0f60302e982008480890b00c2c1d903a16044035800e403180d80354180c0180184801e0004068018003032400c020007585040c03109406030140300b50340c1c4c0c0300010041c3c00c6034408001c5040c1104d00380d1006070814061015640381c06820410b1602d0150305950400ca900300c004010801c1c0b40d8003030801000084946000d2004070034001c401044000050b001030b01c20003030420084040310080204400500c2c02c50300541d00c844510340b0090302306801d1b20007543c8038091400050002030002c030320148569800140f003402d00500e030a94003103188005209806540da40d44039074080b036039200f9101503007030300c281c140c0ea0742c07490310b41307480c210405003110058043c10010021000407504002080e00d52071140c0792202c0fa542c015040c041c080c01d846240d404003044030340321010041c04040d00e180160303008013030f181c80070502d010800c410520800e0103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 325941780 1250 325940530 325940543
    0x30406030b1c05060403110c100e04060e0108250f1e030b13120f02060c0d06090603060b03150402211e03090315040503220312051206060304 62
    0x424481140a907112031803401020b85822034405490b00da401d41d4582035002540c0399404181000101944110403581c070124010180c64480300340400715001c542508001420b0000c070407410b074010f440e580c1c0420300802c011903520020356940d001c110f84502c60031040541d4542520001082e070302d80324482c401115000c44002c62214a884c001244126000280282c3e0000c45c0d003000010587e0700e24514019001001420000701d01c910308125807401c1e65030000107010390345d46c0c8086581d4000c80d560b03611040902d4580d0b80c1c0c0b04021810001040260040c040452a010740070050010a6102c2c3c416240c0690440b00301d484907141c03800c1d0107070084a000f94418109200104216091940850780b4100881183e185120203280400140d010065a19855202040c040981d01e001c105c0407030400907a00760200542059201e554403441562540407c6161102442d14034400d00350060000b1a0040807400900c14203060040895200040200072100702074049940b0f0300d03201040f40d02a642c401c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 325943030 1250 325941780 325941787
    0x12100f0518130f060c02010f0f0b0a0303050903010b0915101b0813080a030806041503050a0605060a0f0303020610051f08040204020f120a050903160b1f0303050306030705100203 78
    0x540404108542c03022295000c841014000240d603600030070309104184d400214a0322580380c4d10780c040714154102c00940a040080c0d03881c283d2160440380781903c1d0149070040c0d4987d0b82d0340c0807178050300285840756001001a02000340d48803211071500ca0b42c050031104100503554a280887c0d143c581c40b03040744107052020020703d0000f10107000820b40ba21303030180e400c051540e41c2e519090130880440c0c41034000c61034040c00c019040c0303000c1c82050049118000c89002942c119101c0503035801041c0b00003880c05594002080160340e0300d844680050500b250608041a01c901d002511541c040da2031003441000c24030045280d14050326400180c84141103800c80c41104c014045822000c090026070308964200150006000380c04020030040c10003004031503032810110765010848400600c20f003136541051200504051400415540d4690041110000354940d01d400048111301800662204120018004101030b000001b03940b203040c0440903500d01aa550041c0710815901c4131500d40140c1080 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 325944280 1250 325943030 325943041
    0xa050f090d05070606031401020c010e01110f0f070827010305011a0a140307180b031b0c010e100605041406030d0f120c09150302120708040812100f0518 67
    0xb60701414500b40240c2000c00e184d40e0765292030700702141403082940141d40005400ca40d0407824054038208040c1d1100030042101880502c200b00d0040c21100607000000040c04924081104141c582c12904607080b43d940300d0410420360b05030841f00e500380b12409200c1d40742c9211076000340b141d82e048550403241c441514900c0030140e0b01d9544141a8601444021440b00001450700c001a42c401c406644031092640f428081000580a8030390007422480003c100b0822000346184040240c4104149856164142402c4c2d6502512008800015500c100260200c05200c0d54100d682110002d41c0c1c20400b4012024000042c80300c01c654a5815a01c6008807042c407510604006a083c0c040386054941c000b1407051301c50070b83d03025918090000320380c07840600001c14903603002c5116001c0c40c10110709c1c1c80c150145003020340c8030003032186e414000755038005802c0c804e1803000c9505064400081c0d2245107001100c81c0000d9009006031108108074041c08a03140c2032110001d81000450340030f505265a55 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 325945530 1250 325944280 325944287
    0x60816050306060723030a030e0f1207140111040905060d0203150a1d251203030209011403101701110304060b03030702120c10030606081501031808030a050f090d 71
    0x1c4001114620408840c44541000742c409043d2101744407005183d4032428a240202a60706d21002000036420020100400d44000540d081440d43c2e06101e9680742c2c03215042518030442c100403e041c6650a21481c00310501d89180100165194414100810703200c000601c0788103c441c1e83d0003905a440845810400c04003801c9844d404003418001251031079040446000d58440c41c20a080b1551182008c0b079240000b90304514200e0500755010380c2654944414a01900750400c4040c0c107160b0300142c001c2969101c4c2840311481e00c041d86405540c2d08041c42d10303440840e07061050344816400b6800d28940d64006003c0c1174035506100c0111415030701c0d40d4880381c0040a90340b00d12030749440204000e00043c0c039246010031134882d680001d04407012101080c017240310010b800c2001050318104040c4040c94204401540000410000043c1902d12200580042c40552900071000c414031803444100300700c12000390300c00d410410b400d11054036000162170144600741c5050b01c03160405240e0000c003d10 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 325946780 1250 325945530 325945537
    0x60a0c02040b0312120112020a030605091006030305070302070b1c021b1f06050303030709090c02070306110c0c06030103021005180a030f020120070b070809090a0606081605030606 79
    0x24030020b02e654042c00002e18040c2c01c1c0200c00c4d01c0500120340420381080d100005801803000400321241c0207465030005209000d5804010000303650303980802c02248040020104590300054100207454a07824042d100307400041c0220300511039510042440305042c02034400d000b10707001c00c40310114003540980f40690030407003100029041c1c111a5203070501007000b007100d08400c90300002e0503001d91500141d05490064100078001ea00400034000840d80c840c40980481d010340100203100140e030b51302242405140d9001501143c01c1202c01240b4401140043c00c84144043c202c1d03542941400502c0b0b0340340000d20002e0351280100491882003405000100302e100208840c403264280d1210000701c4008060f0030982d5038948914524085507000198100c04815160708514000d08246010350707600c41501440104040200c3c1410800102c0f03006d071941c065006040c514686068200f140007811540304400006200a0106110b0849150f40401090380d13a031b1075a103955201d0061001990 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 325948030 1250 325946780 325946783
    0x40f0e0c01120207020a0b0c06160c110f1807030c082202060f0c01060302100509030d20010219020c01051c0b0105040b0c060f06100e10030905030f031f05060a0c 71
    0x980130032440c0c005980c0c280340c4802920004c449170b9102c05100511526141c00140141040d1304850304600180340c0000c201d0300c00caa40811681c00020501001c200c00440c801007140e0003558080d1002c4e6580302888106205840f03075507080007403c502440494a8010680e220305200200110505540e0428860041c9290000d0071040c5400c1c2036080e12121a4800d998082161359125014070441c90000c0388090054468504242050428030001c1e1b01c0d552680801010710505c600300404441c9040300d4100c400941f0b00003152102401d1000313000a901c1c60b0705240042c0140042c241c810340c002c00646d50740d00c0b840041c407036280440307440c400024030980035410b041c4642400300146000d00b1000034450035243c103000e80510b04000c03190340014803000d000c0620034642120419000c1c0d40c1b019040381d600100300c45000c0c900003409426030051403003da0140542c000090044100301191004600886120142c01c01c100045d0b200c3d03001600f002e0185030b5024208210038140e040c41100f181c407009 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 325949280 1250 325948030 325948067
    0xc0c0b04140309030601080705010306050d0305120a200306040b010507030503010e0606070f030c0203060f0115030911040510080609070308090f0114030709031103010b0a12030e100509040f0e0c01 86
    0x103d05000003a00d0841c09038044001a88004810311075940e050240380000e00c801c0d40e851000d0012964060550301525103030f542c1c00c001060014a2000c1c054010545180145d1071860f04001e0354607146401e580212a410b00907810300c0407101c05544200121402190166a41130075a400c0c400e2444c040803001d80b15940c00070041c4071201c0440c098000a041140c8280c58841c002549441418108400205001c81c418030700001000604c040021520710784420345000106d882c400d01e414003d0f403125285060b0400c0c6031000304003020154280d40310070364441c50102c901d0b50f56000c1c2c03503591741c8405001c01080c00d0b405104000305414070380c1c10f0800140050420303010078520035254044a400c211822000075140b075030200284000c841c04100c0324035080d80244281d0494030040703550410580304032a0429540c1c0c1d41442403622400c020404040c004204017200000310400402540040b403282d44100e141c0000f2100590b031b10f11440d0388088601c0d026105041c41c05005403002030034003070781d070511 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 325950530 1250 325949280 325949287
    0xb0901081824070f030c1e031d06010602071e2c040303061505210c0c0f0607030b03010c0c240f060f0e0903220e07020c040c0c0b041403 60
    0x100a4001c0107080740d1800100d03110920b10f08004020603903480000320106040c60f02420002844d804104901040400c0401071144080310508600030080207092607091000c14030312107940b03c0003140850403100a46e08a038206522680852010030040c1c402c002c141014180400c01880c8886048801452281360007950b0a80e0404005210104a6045002036a01d5109010041000703000c0c00a114041c603000d41040b003000c0c0e4102e200c171000c1207407500508007140001c418201e8a411554040c1d4583c003600c5d103100b210344040f03940c1c00041e200f02c0302103030602da1494032034141486000020340c0140e13a20110031066440381620350f1040c00c40582600204d43d000d0790450040e020300e402e00ba59040c40024420300d09214641c281c400c5800403403d4119007014080c05000003c00da540010b00011243c041102c282921020314400d83c1c0301b5140711040a080140c4c06401160184030b415094070180a04500c80008544408585d2801072074510703a100810b0208108800c0190416000d00850b0714 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 325951780 1250 325950530 325950553
    0x6010306090e010902100c0c180b18090114150108060f0a0602060412081b1309050702060a0b060406051b030403020901120312110d0b030a0b0a0b04060b09010818 71
    0x10755400301c80d02c000e41d0303443e12850700450130101c550a0524941e89450f0305015180c0da0382145a581c0d0344981e06028100343c4c00303403002c0da11982c02192007410040c002d55814040d05a04603003c8011a40c0d0600c0b940703865507043d000d902c90081903114141c0d040c2140d403850440001541c2485015008942001c807004e01788c2116210307199950050861a0020045860310b0325248840d8101c4010807000c01c10310b1002c0c403004410004521404032900c4c00f00644035241c001e40c0a01440450b8403404030b82e803d01051100b1160045039250080d04110010f000503031500080c01020f11482c030408000800c1004600039591055100103100d1032110103403854581d40c0c0d00050720210080c0c02018501428030540d800300358008520400b10004840248046440301c040388a0501503120004100c548a00c0244682d85e400c0c042e840660307600c0610b610090801c080700f6030080029030322041c040ca25000020511540c450146c4c2e003100e6051b99005c5044e40c41940c8a40c3c88001070b00507850311f200707007026481d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 325953030 1250 325951780 325951799
    0x3020d0605120313140a0302120c030303010303200a020a060e0f0a0807260d0c0f0c0906061403010302030309040e0a0c09050403080703150501080711120c06090601140906010306 78
    0x220090350b40301c02513445080c08001e4410b00d02403940031080e4501126003000e41d54039048404422240c048030140301100901d000c003400c118901300c08035890301001002008042c1c000031a590304100281c040311002141007640c03030f5241d00d1070001960101c100c02040102c117201b294501c11222000d00702c2e6038041c0604021a1141c5181d40040280360404002405800b045a62019003803941c013a418000d50b003513250507a03e915061144004018440c120348040c02481541c1e054001e17440b54481c4540da0369040c8903401011035000350000541400c1030081102d80038400d03030381139030b070000c000e0f40ca406200d10401c40101a4040c44001900480e00d218000c92030b2030b0010f00040c1941c600100e01c51030685401021035400500e40000e151030200c00001c9201e06c160b050066030300a081c4148540c98086080d030310a040040b500c0c25074882d0b0f07500c0b0361510781d8080140c00280c80300c9044030702d1601d030f140790241c950800b401500900003491460521782c2c0391021040303810640c1810300059154032000b021 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 325954280 1250 325953030 325953049
    0xe1b030c090409050303070e011b020d14031204230613020a0b0a050d0b1f110c030a05070906090b030d050a09030c09052403030d092a030b0601020106051003020d0605 73
    0x1340d44541003c410020100d81000b40ca100c020024a000c4100c42c40000f00850301c54402c0502a018902c95500382d410848c00444c2c81e01c0210106080307039116264500a054050030486003100d2048102c0c2610003661440040c0d05600740000015080c966143c0c90301070002c50043c03100707036400f06580100294035240c02e0020601811703555201a52154000212400d40702c11138078180c011000103c02c1c0030143d403541030b0b046600c0760300d1800d4650601807000c0c6914004081445a50600030002101c040000001c1c0d01d2040343c1843e101441196030ba40704480848010314641130305500304419460030b0070302c02c0000b451850900c2c01c1c403012444d102c0d181e9003c1202c80d0340101480c513641c1c60500844405d031842e100414044020500326034420341c00844c0d00c1b405002c0607002030b0790f21002d604003044104103503c44410320020502c8540c4096072082c80a8800500c0b0a9407144894404542c065106001d00c01c10345078040c00d00034a6400510040b4003c1d8801e4006412076507075046d0101d0f44d6030750903215 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 325955530 1250 325954280 325954283
    0xc0d11030f040f080d021b06161202010902150c06010302241b010e0a02100e0a0306020708031006030606020c061b0a060c09050402070218071403130c0e1b030c090409 73
    0x20003c1c82c10103811034039101030a17880d0010355000311840b8070b4020500d440c084500800342c8407951101242c01c04510710094000c8010a0422225501002d4035415408110b00500032140d600104848590020181c4607050503021160800030040c40982042900c00500d582c2480707083c140c182c4041e10428450700b280e0810039071105846140c40c5020400d024034000844500301038400240290f000851090003e03078144180f182e1740c03103011040d60b540c858420040d44c001d5001d40d5180d070700d45000c00e216401118500302902c0c1280380462114800e1003401c0680301d0760f40060429507103040030440c0c0342d00460045031b0000c103075542c0c040c1796450074041401e0f046d1160401145010800e8000740c01c401c0180c0010740a50b00c140904800350303690030003101e20000b40d004941b0030f81c3c546132012907006034019000e0040301000002e0000620a056009103468000d11052880548505102d0a14102900c5291011040c01c1c072100600141d10011138018401110703641c03030588201d01090540b00c29000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 325956780 1250 325955530 325955549
    0x6011103160b071d04110405030f101503030c150e010c020a14120f0c0102040b0f1e07050307110321030103050f0c1012020d06030f0201020f030c0d11030f04 69
    0x19100e0030000c100c060340f50811164201254000680302d503861000f0344511066206585841c252626a5990b00c01c4070301070034000c0c003500c078040c060090340c99603003003000e24043c425403804024440940c1d00200a02c15640d141d40c1f290b02401942e11b40c2e1080c90015110503101c503541e03040d40049036400b44074415050b0175a4000d800903c6031410300080c6001640c0284200b604000e0820392904039000440d08140501d1088540b0b410240c68224020300454102c24a4842d0003c0c1890b40000450060300070b2084840b6a9000c0440358200c003e600e005000009107035602c107202c0080020360504655940301805021660b030146d0420062b000f00400d441c80101506c0000018410310000703214600300844500d009000401e0514041815288801c440e501008000c5200100ba251703160110381041c400e55a0910041d9107038207007984031040c002d13000c0b80540300d007042030121403001005485031440d01300082d1204404403001a00c055220038260110781c0420020b800415102e50040c1c000341142e682c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 325958030 1250 325956780 325956817
    0xb0112050a2d0c02060105101808060903070c0f0317071b0b0a030f0903020307150f05041401150f0b0d180f0203060903040b0a0f0e1216090203060609040506011103 72
    0x40050b0116035440a6402c01c64009500600150b11a00036030440c4541c0c5141004148001c911000707021085a00410614050401400501100003024007911802021190f01c42c642e01c0c20f503582c03102005c2c40003c041c11291101c00300c0405003000644540e034041c04000c07000040110700b5081401e881e820841001602142e0600001c1d41846141515035040c1001c1004005540f8042d66a0040c0700006006c2070100c400c4444400b07280d00259012100c0038028841800c02d0301d03111010100305400c5802a40c6441c662403048003209210000301d40402601041d050f040502c1000070f070348480d02c4070444603101c030303020309022002c0038440140da4011861400840f05034410036041070b4003e008210360340e02c00d00080c0544400c000884024a8071400c002800d01c1c0320b0001038401c103c0e119060303603025a01ea502859000c0c804180040300c000001c0e134861f142a19003456000720300040d6a841c1d00300c08240114545410031ba405980c01090504180c860340020706101440c590010700010014006203 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 325959280 1250 325958030 325958111
    0x70207090e070503070e190903360302150c060103080d060501110c0f040b0d03020106080d03091e1a18120a02030d05101a040503100b0112050a 63
    0x348074089003881280e02509030680340c480021342d03514040c01400b07007029014001c0b50036080d10310300e0b444415079030348000e0110a129042c042c0c0443d0314940c0002044204180c000c01d0f9440442c07140d2042e0407101304840d161801d640038071180202489081d45216001c0061300351000302042064003c0d072180c0d0f64950744007100c09a075000e07541264061414011151078580c521a4081448044c59005136810b002c08503100000401074000e6031400c0b5045100c480d0000709150381900b04000740c420720b0b0304490703500c3c40b0618106d040f2188640050f00d40041c01030020303c0120003100c00240503004444240d64210019482400000300740c4014100800741000500180c02c148842031490a80e01c403000e0801070350000217516072161042c1d90340500d0392078000556003042010072030098810800c0a00180c0d5058800340c0301c0398007900481e4445c3c4210b6401404814090242c1146254181d40d20301400c5261b500480c0981409001085140d8481007854000c24100c404c0e8580030350441415490210003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 325960530 1250 325959280 325959299
    0x2707170c01050a0f0c290a0c0216060503040503131e051c0b0a090b0a1a0307051513030f08030402010810030506063606030607021606030e15070207 65
    0x285040581841814051851003607004050a6249242c81c2400c0c51700540901c0c1c5031078900d50704980d44580f59401c01d070109090b2440003407944200846201004144099041640c4c2c601e80070960421110140005200c0b4900c101d000c0c6403c540b20b01d04480c10a40030a820f401c030301c5041d82103441c00020354001c1ca03406502406019005044c1650b43e00d40c600c045481508401e01541d0028000d811124046000c2c40041d901042175079030000d200002500742601e841001c0c04c0000c843c4156080c0005c010300107440c0c080b80300030031074800400007001d2140340300d0000d00c0c68000080c6155004542c2c40c0000c04036280854110300705200e002501c0d030b00d1800d440050701e4080041d1200369800c100b19000d0001038400505c240c0c1185007100c1c200d5074131003100b8a11482c002900a103088078120b001c0740c1201c298003000b00358080d0b4011003d44841d80d9031810100e0b030311464460103000c0801c585074100441802503100c80b01101a8100b500e400b50b0816440002002e800d403802070040c2d20410082000d60034 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 325961780 1250 325960530 325960543
    0x6012c07111614061c110301050307050102010b0d030f11030403080406110105060f01030e0a08040801020a080601050703090501140c0d020d080a02040b0414010c0203060112030807030e06270717 85
    0x982140040d4030b8180f01d6150b151481e0101071a000d10780001d524030070420240640c1c500c004084005000101512546c8000c0f90000e00c03442d80a4465414003150a600601604c3c480c00d10140900c405c82c0120f890456042c03020b40e02c003400784401050a108070740c101b4002000139500840d4980e5070b903132424030014030b50400c0c510b84440301e1b45032206004090303503845401c2800300d80c00d01c5c0100b035220740d081c091400c0800d000c00003058040009030000b0401e1040d005003455242c0c540300d042c01035684c1d03001515280700d0034500030001040f560742840a0b40c083c580c0c100240c0712402c0d0302d60920000b54042490300780f41c0680c034400b690104034502a035a0b440030302e86030301480b104415418a85054454000350065000b509580f8601080c081c0031648a903280d085801d070020100c0b0a0b9503590800080304201642040e400070b0510310018000b0750081c065941c00101c8100200416a2060124512810f8a1410145112050303100c001071440820082000c5d20142c0b0f18080803a2250900925000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 325963030 1250 325961780 325961803
    0xb07050a08070c02030a0b0901180302011b020114180a0b0717010501090b0f160c030f17090a0b0d1b02010c1707090e13080720040603020306012c0711 66
    0x500d201d00c1c0050305d0200d008007819a000d20034440540325911001d0150124401b9800358403184854a0306043c0e0540000145c821401350b01c600305440b180d030032420f98040b0021180320040040105080c5084680c1c500c070100030650903100540c20568844142034415a00c0d50300041c2e80034141c83c900401c441d100c3d80180401d08140c10540c1c500000e154580c0107002c8290b0250b4400700d01c00985181e90040c02c3e500750b500819071711460f174403490708003100d481d80c09003911000c60801811680000b0001241e0500da801481c0c0b4003c2880e1507040e80b8660701c0040048003031034176103010082c0300724941c80f00078009181c1d80010031032031440f080041604c01d05980761000560610305002600c0d40056004058468254000300c080d80c8001105a43c041000001041c0e03050014a02d0248010305078110700d401000c00340c0c003486202c2c2604002c01d6402a020283d810740014004005400200c52000010150404401c2000c03101c82003044581100f100c4040200b07201c00023a110219040c440b4205d00c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 325964280 1250 325963030 325963037
    0x30705071505010e0a0f1409010e070603050c0d0905101103010503010b27071b06050a0b12070b030601140304080c1207030c02090601031b0e0301110a020a0f020d0b07050a0807 77
    0x10361404d410103d411102521100000d07a40780b04081320b0001c9604103020a100d0b0428054603030401e801c1d101d008001d034008070085400383e414007080300781c824004c09024240c40c4008506000e070407414000145032032441290548240070301d0489030001d60064821540c0608406910b941c508428982511903004c4c0f03075442146004040c40080080350a4140d16148040c0e5004c0e0071303503074880283d4560a10230070000c400709500c0000020002e0355004107100b068640018090503643c1814081c41700b040c0fa111080c2038200c00b009100c1900f494024550080e01403404d070318042c2d01c800f5104402d5005807020b4541c3c580002e1313240da480401f00902c5034131000c5020001d00e04145514010021900343c03030002d2040104101040880c2e00c6034220848161402c611040e00281d0700f40080c1c0b03808801c0150900035401d00010b010700c0f0021400340c500d000c210750003801c0304c00103542c2e6184c0440480725040343e02240c000107403008180f00c40041c61042c0ca00c6d494007071b500d61074001c0203031008400402c90002c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 325965530 1250 325964280 325964291
    0x103021201090c030e060c0a0201060611150c04210c0f0305030d0b04020702042a0201060b0a030b0301060b1201030308090705011704230a0201092112050c030307050715 74
    0x3800c0400505504490207a840011900340326038088000e080248450103840c400c0c002072150700124800184081a01500200900c82d40c0c1c440550707140702440c1c00c111090700141d402d003d85401c0f005101c0d500400070900c0e035280c1500c82c0c1301d070380301d0710060801d5000c03952802c1401403c0044e14204407001c1c0c0381082d1545170300c51230341d603495580748684450000c425803580501a038030748031398056038440d40d4010003e01104a440e02d15554031002c1c030009041c9110220300140b4242d00601c140e2040d5160340c540c651400c0c422a6040d406007002012158040d0340e42e11001403c103150b8000b90007040d035420106035440d455400c0040044002500003003294008000411080ea00507011114400d030303151000c00c2c07079500c0d820b00c04903881c0d80c044115000201562414041032010800f4802c692003601c580c0382039130322400c2d41003800b42da440c08003041e615244000804500c5130702c0d01c0740460f0110714050345495104001746003503402c00d0384d0702e1003c58070101e0f0030020041000510f000d98250114100700c0d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 325966780 1250 325965530 325965547
    0x10b04020f090d0302100f0b010807030b060d110f0c07080f010204050303073801050310090b04020f0d05070608370b0d0c0e0604060e0906060618031009050705010302 73
    0x8244500301100f0b10500320101404101030082c0a64603c507403104004201c3c49050104c1d14001c0c161003034149000484000016621074040c0c450403020b01e00180a090602800e816050002c00113044203c5e48400c082c0140d06450140348010200600500b02812609151492243c541031980700c0d407001c45d0740144801d03c181d0f280001a180c8c0d540c1c0000b000e0882d00c031100d00c0400d50341e004030300034444200721500c2c1b840300070101d50740603040362000d408440762101404c1c1000211050080d005040325603d0010801500d03065580030030840004100203c00100b0350358003450640d00364408404a5000c00401c602c807a036819403002150310021505200d215072408001c0750003005611240495542c111501703103511f900c00e036170400a03400040c1035400c80c3c40c0c068a00030b04008a460074801d03400d0882c00300d00d42280d803002d0f40c001c0600c0002460319450301c030b003040b03103940142d2013516550308400d40080c005d0343c00b0449108020440d880000f1206a5810480d00302080350304010f041c540100005807 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 325968030 1250 325966780 325966807
    0xa1d030903011401120605070302040302061305030c12032d0d2c03030f07030b03030412020a1203050403140c1c02011d01020a080d0e070e0108010b030705060a0c02151b010b0402 78
    0x1714558071440c00141e550394a81c098009001c3ca40000c0c1d0000800300351606105015101101955801c80c219008816080c04014002801420b0f40d04160010b11009034010b0b11031030f01001305040c1130900c800400c8134500c4081603821950340846802d40720146a2514502c07040c900320401b2482c14800c1e8507d0020241964034030000d055030b00610600400185c40724442d070f21200704442e004040c2c1c1d940d640d40366492a54848030084c103900c5042290f0000035a1034401c45021071003a8035459980c00c05245840d821140e00150485208900070b030300305000700e0b0f034070704031030590051400710407a00e12809400014032640859917003428605040135907450076a00000d03d40c4103150b119224654030410704100da8003030461090300e25103074410240041018200c01c400380d41622140c034000c1020000304001c040c0c0e40c02140c884d25400c10001c21850010038818601da424031400607003c460002d8242c1001d6100b03a0080400404c20410074584032854103023030040c04121882100d0550503d6442d00c1c428 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 325969280 1250 325968030 325968059
    0xe04150501121a04050c2101060f0e060607030309020a0b1b0a170706020c060903040312080606030c0f0702090405100b031c0c0311031c0f140604050a1d030903011401 73
    0x81d00300f8603c0000c003040810000d81c40c2800000c0d055071000c0350b0284400c0c40304060540220307415401c10344080707110000e030030468080302d04c00d0031042700544460081c090b40307501c2403006070101030302c800b015000340c0c41e014400001801c16241c020350f220400d29080c1c50701c203440d00b88107029070801241e68000c10307030a0102c0711039407481c0d0051545c2c07580249002d500030300c40c0910b04083c40c0a040e0410002d45404001f80c812280a1161a2184444110f048076000c87c02c0b1703450365211a003030011552695002d4080c01c90480001307101c901d40035075900041c261540841d0115040d0744000324645070304900f1b0060b01c0807408180d008080301102d00418020403407041400504100c0380240403010b0510440141c43e5480180d010340c1d40c1c1c3c18804043d5076803c0d280e00708440c1000c1c24001c14245a9210b03100740389442406040c1041207071030340301c00c1002a22020301385020b55074590651019030305950b0b14008402c00795070002c0d0390390700035081494259985590b140d1242d61994004004a02c000c00f41c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 325970530 1250 325969280 325969313
    0x20703200d11010c1a0907050108010605120403050702491106041e03050714010507060c1e110f0705100e0414090a061b0e040b0a0e0415050112 63
    0x1466039104421004840c07001043c900605100902403000240f41700f440c130941d006445150548100d561100d0054448074001c0c410840004c004002860f02d01c01d20300700050304988030707162070352809000744c00003115243c41c00045070217210300f0550b245c501408071900303e04407901210b120130041c80d520a054030350341041030301070619902c404500c542aa144400c4070058140760300100020b005a480321244d0811900003220715100b00c02c40807803010401001e5440703d0205950700352800d50ba0740d41c0c1c0006004a03244001c24402404000d0308102c0807102441286400d5540750300c0c04440c1451441e10307040800c0628803241d04a0001444103480d84000a20310401078141200c2060400b00440c00034074081d2448950100c0f91020310803023400128015a805014005c00e03c00314114510604404c55a21040c1e80407030001922070f034440c01e05802504100100400443d400365841060480c030380c00031a02103c004480c0c50400c101c002c010302c1254090b203018480464048090355402509070403440780e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 325971780 1250 325970530 325970543
    0xd0506010f020c01140d09031101140f010b0702031609090c0e01050a0614040b18100806060a030f021c0204030506011a040b03330a33120c020703200d 66
    0x505c50403000040101d8942c20b2003030f8030070400401a41002040d8510310543e0064550920b0b06401121466a02c07840c002c4900c040c600180341d04e007075100c0380280d100c010f04903014040c200c04081c0e5000306015482c0101040c0c0804141d080040c80c101e000344601c1d82004148082000c0103000f80e4883d40381e00c0058680c203080543c2c030326602900c0031895005a034011202540c002911071030850503940c019810351010368282800c1081e003041503500020488980390042428000001d0461291300f100000481d8014010310f040400d60030344142a80252041075001e030001802c004000c001c02070316005001c0c8001f00c5215100004060a1604c164496149854808030108512130f802419400d0901004031181c00e06a4401c1c0c00e02d801c210760074203600c2c820303402014009094014810218010b103106030946410f4210802c6040b8035082003207402041182500058101d0041881034902040300380d0010401e03240340d45400c0c4a200002e90441440640003142800b254a40100078907a1952040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 325973030 1250 325971780 325971797
    0x71505040f0b1309110901080a0209090f130b0c03040201090f2111130902040b0406050f04090501230114040e21161a090c0a03030e030a060c050d0506010f020c01 71
    0x7a80d03c0034620342070b005880080e1038961000e0070240c00d00000c041c584001e0300d03000f180341d54012242c0102c0c024200d90b1a0440d0704000020f103210007184020380d02840340d91894110700c00ca62254000c40c00304903083c161540000080c0003d540c1c01c01e03041c10080442e0750071407c04138103101141610010f86d81c80c00107681e40d540c0b145800c0220410a501e40715402174203650514160309900c101800d940c207020390003145008103403400c40c2043d0085070291200600041d002849020a12008084551054917155030314204442d007400a001c81d190141c002c00d0001c03000b541007402030000c038001d414a01c2d114a01c0e01c0b400d040640c00101c1c03080c030704510050f1103002554450907603020503c1041001000d00016140384001c0100182c088185582d40260280281d99407520b0182c4e2805003503003140c1c2c040000041000003911900e03650718007000182c00d640d210070071a5208000c1e01c0b401c010390340100f0350220314040309400ca8840c0c3c41d030101003481c3c488248404a00065103e814281e03c1c14108007101 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 325974280 1250 325973030 325973047
    0x103030212161a06042f0904110a081617010b220f1e030b18010212070309050f0d121d100c0210060e13050114010305071505040f0b 58
    0x8114160b29040001d141036110a00b851404070350b412a1090b10540c03a08040c0d4892181e90000802421121104c80ca01c0328049000b920094000a03503495106803901c401c0415182124003824010304251580a914140041840c02c0c40b2a0000c4282c1001800f00a100301108d105207000c0c11030b8a242007a9689420802d0050051070082040c807803120713601c400006075021099900c50480c0c1194100300707000101da0001c0703070722036150b44006094615108042400c0e0152411001070300542d030000107242c4480c4601480d08002e080301c43d5000309039110148402d0007418000003000c0c2c070714a000340c110541c01c18000f400d06100041400d00895403460552055402c5400c14112411000200c1d052113220f0f81210001d0701e01d041c08000103000b00c04c0101404802c1740100801d65040c801c2c42d00300d5540326105107031000082c0d6001e888543d290140040300d03130100140a070285005401030f00c155030a10b1489507901d000c1c03681070300c00c005040204220310140e0190392020b54400b229101d41d1038148 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 325975530 1250 325974280 325974307
    0x601060f0c0204051008010c1b0201030b0a031b0302040b040b0904030503090a0c0803130b040602122a0105040c0501020f0307020904110916120204080d08060a08030a170c030103030212 81
    0x107040700a4025240000340007602420309052012291701e200288038101180c0d100f160800c00d00754180b103188050186503401580a504030440307059000e0b0141da0665a071b500c440c104a203d02c00c00d9800f58400362018003d40c142400f8180a041c0217440900229242c20b011500c0405e005001804100c40400803407882e030418042074048540004503404019180e0880640300e074881d441102e0b00e10442000047c05000c2141511b0071550560040d000b0030f80800e82c2c1d100540e00c4518200010303031990b034011503641159104180d164005500010f0f091509190494403410580c0001741507500040351466811000812100344590691340421981c0740d62400104110050107801c1d4048121010019404000000d501005450382d454120100c00194540102c1c0718900685049422156403892182e0146038481d410000103042d48444075650f079051800c54025210714800610007040c030340220010008403540120800b55558655451581c010356100114808020451404070300d40360000c95 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 325976780 1250 325975530 325975547
    0x20d0801120f050102040512060f010e1e1504020705011e06050a0323010e0d031107030c060213051e040f1406010f11070608011503060e15030c0402040803030403080c0c0601060f 78
    0x40103407922560508d404929625040200d5815200310010000018541c01c000c0910f4091a040e0b8403800600312081206855043e0092000c0d450829001030490b03e03071290310080488074082ca00004030501800340c0000c424000403605c4812504100051010ba45d52607c903104491b8460341083e09000b82207000490401070258945465107841b0720350290310700c0416038225034840e550302007000994406503001c640c01003501c0500004c06684880002400da54010318024802d41c0c1900b048176a10b4002034100e1200301d1440145000d000010030003402c0c14080c000200003075800c280921030340d1070914883e28400402d401d04002c1d81c0e904645c400b5000e040100d40c4001c1580c1601e0708151111005400d068082c0b1480b0340555041c1e4100030340320702c24403c00c0190741c41c1d4001ca088948884403448100078440f0325181e498010042215006ea0300c51000384002d0641102440e20313481c040c20040c1c296a001085003000c10010000c01400c0c2d0f40100d10380707064910500b004400e000980c041203030b5255 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 325978030 1250 325976780 325976789
    0x151e03020d0605030105010b070507080f060f070e03070920090d0303111b0c010f02150601140903150a05220605041e0b180d08060909010e060a0b01020d0801120f05010204 75
    0x141b9107000402d0032219440108070701070060089900191f90b43c0300d02540c41d03602c00d02102198102c0780100342d940c0400103007590844400e184c1840b0711000e0400090030040f481d07215402d1656200c5c82158003201358010300c94020410048207003041d0b42403020400789403201c1401420159136801500040c0e464034242c03548881d403000201408119850700c83d54070328003140801c1c080744940d030608004070320000740c5103826010341015401c0c1c0d851340710041d103a0b0000c2c03049190502c1024442d0300c4841d00e08100080b01441d0095031048982092034294048420250202c0d44500c07040c90b0804011071111500f55800ea402100081e069880c0e0074030b108000399400700840d400c6504c0c40c0450900110000b403500074054442001c20a140c8014030a5440040c0c2080c40042480b8a000800324904114142c0d800100a0000f1892455541c105406c00c00120341502595545075000003c659041041001e4082641404032080d410324035a03940d085601c40004222032005820a010401e00f0340550b4001c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 325979280 1250 325978030 325978033
    0x6060507080c0f07091a0603040f02040c0908102901051b071203030203060f0402031504050a18030c0b1f12050f03160b062b03020712030801151e03020d060503 70
    0x813919181702c0300141508180280b501000f03044819640c2c81c0c003904890181d40e00c10703000064400c550b030903c005019a8100398040c0702d40240c00013001c2c442805000010690b04200142842881c020402c08581800f07166941030070410100c211640c10208480c11201500c1034014040c43c5100410300d407120541140036040a002100800c240d0540c0166006940484402020307134052003d204c01c07408100c8071070318a4804080301c0b00303242c10301d0350000303800026880c4085075105200c41400c0c1100b0600208070300241c81002000e0a1041c4020440c0c2c00c502c0c02007449800c0c9032103041102c20006280200c01130020380710f02d490708200c010841015007485010949031500304203960021b000c208a0740c00e4452001c000c000958624041c08e90101c071448610b003071030f40b0b81150b200a00c14602c41034811019442203c1c0041030038521040103c2c802840390ba039401883d81424000c007044c201141c3c14000388100b04c83c410784040c9964a04e50125255850f005865450b80f400c09005000d190380040d800d03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 325980530 1250 325979280 325979293
    0x50a081f0b04060813020307051e041a1509030d0807020a020909070501030f0e060112020a2103201c0302040b030108011a03070b0405190305031602031006060507080c0f 74
    0x449048501074803c5038460b4841540e6542d841c0d0b0000c0c01c071100e04000961507082294180302d249402c035811521850061016a8101071203004282192691081103202842c4120101c1951070100c29401c0c400d034000500724144604171021a9035025044c0010003405512800141c034284204880704960b40c006000b2451410300c41203084d22102e01c4d01602c0d0000b1300303108550b422403040d030203a142c0440c1e0f400c0040400f80e00e0a03019050038050488101d0344800007500028204100020800705442c90308141d1040020610f000b030701104916982a15001b00161340c018030200110b6050049001c0030510f440c40910800120020302c21030f0056a240d082c044008035406005600c11541207892503841484468110100760703a91110788580f0074114020081400241004e401e4402e03030b0400d8640c100d507207a80301d0b80c8041c2076401c4061600c0c141280d00400100790b01c0c00b00100200350700c40b00320420030700323082442c028139512803c10b020789840d000203500320091004100ca41d4080c045202543c01 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 325981780 1250 325980530 325980539
    0x80304120c021003090b130201050f0d060b070305041d04151d01060905010503070b03010b0d27080a030b0618040b030a060504030f020f010204061b11040c0513120201050a081f 77
    0x10160180169046d05070580059108403540d000c070100307150141c407100e013410901101c0c0c94407607200c414518011515848005a11640a409400785c0391082d240d45071114101602103146c51040d200504a050b074544c20320010450b00ea000020080c0c006c5408180c00c075203020703801c00e00c005004000c0c60703a61070030000240e81e02d40b6600c039905840044042c0c3e903455a6035000803c0c540420301803100444820007215494100704d5215451540c07000501c2243c007603921114030908528041c09640c00f03400080c00c500700302da051141d4280c90004803000c80c14009603180b105401280d0413541402942e6400c410328042e6820481442c0c0c603036000400b40020318280c82c00500003000c910320000944a00300702800000e03018001d070b5060303c1151740c410005140d0240701c03460010401c0b10680d4482c030704070040d0410f81c68034044c0d490012440c3c0c807000c2d0381e001c5480a090180b09540d020900840842d6141e900503030340b00c011643c00c2649450040b41e03e07118040306100031586890fa951044c15107920004d03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 325983030 1250 325981780 325981787
    0x40503151b030f0a1119031a1f091d130f05010501030b060f100516030c02030618060a06140906061b070f06090f330315061b120207050303041205010c0c080304120c0210 74
    0x480742710300d40e0340316406103503104100841d949003811140300d00c0090368002841901c00c11480f046441c05280c0f80d00341c08000781c44407400c544003030704242c403003201038010880c2d982847c48035850700c21002e070342c0b01c0b04034801504011308600801100c0645907400c418580103241c45030000200d0581c00a00740c3d606410005506000c2012070034407684c3c9030040c6e5000958648a070710a2a0446401420b05040c4241030f808000760702c000240555031154062003080d0340050005064600f60b0081e40c0201549414010f041e00305d400550b00145c104040208140100740246403c28103d8002080d1403550a0510b40a555082200c0d007a02c2401141000074590079039140c8c10040300600040101c00c40144c032594110b03448041d80050b040703407040b90303422800020b0180301c0c0000038031400e1069540c40c5803540c0c00203003158071592141507003c1d0301c1e002110901200b0700c10305030030506608042d040a400f5a69120103804014405401c00880d0301482d9905070103406400c00c0340354001d08606c1150700c11031300034 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 325984280 1250 325983030 325983079
    0x90618011d03070b0c070f03050f12150f0d0812090f060f1504090803060111070504060b0418060e040f030909021b06010b040503151b030f0a1119031a 66
    0x1980d4051042010810600c0d50100b00c4846c41c0e00080420520380c5103440642d034079404441103e040784403c201e2410003c1001d078406008140c606910703070000d20705100f000801e1001c03207080e510800f501303003081d0009600c0c6400c03194404821130401c42c803a6251109103050103083e2030a0a62802218100013a0f20070b0204014030840c2c1c4400b52001d02c07a40d00003884115900d4240080a482c02000860003641c0100441c140e075103483c004480d03400c0d883d00d0225080d0342c0180d004a01145010a05100500c07103030000c00034040f1072010400038580f501c107034101401d501501c050504560004080281031080f034240380a81a03180c030540d0707544801e1001200d08207500c0d44502080c003980b000070030400c403c0c80481d070032680005c004140074405038074040203800016042c50f045611102004450240700c1014500c1440b81d01c4050449180c10030404c026502107084100c4070510811404108000d880341800d07102c586450300080c4510042c1c03000d0b400710580119280c0c010006c0c0000750b11441c004020 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 325985530 1250 325984280 325984283
    0x103031107060f08010308091f050409051302010917070e10062006061203160b1f0f0614090301060b0a0e0303160f0c0e04031d010206090618011d0307 66
    0x3200c41080d90b40c1d03411115011611008070004a240c801000130907a22000b0b401046001080520a8200321002441c01c4d0481180d075004100d01080800c1001d02d40c0c422184d0106164a082000c0481540001c0c03240c4058001d686031102c40711150850f00308100808000f810840c40c400c610342c2881d03138101e14203030118400c40000801d0800f84000c566000c035441d146d8084a82c0040c40079481c0d103401c004c01c0700c551b10414002844244080d0b01c1d1420440114032000c0e006054000c2c040c00c050400c00c0c0c2240004126418000d011041000b080060301d00312030071900c0924103150480da03207201201061040c65a02507041d0708000000c5000b038040c07802002100d03060f80f2601d8421007007905250f200c2c050706d40b015400c0012180741c0c4000c920101804116244503440071302c81c454840580c000741920582e8250b00040b021780d00840358041880e04012001d41c240010309240c90801c4a05903110b130000c1009441c2c4180248554404d0401d411450304146141d551100b400700a0400c00d030350741c0000c0350 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 325986780 1250 325985530 325985533
    0x30d0b0f031f020c0a05010212070e06030403020606060703110a3903061515080a0c0306030203061602010b060d0504060605060415031a0901031406090309030a030c11030601030311 79
    0x404400d64a0700160303030480344407191600d076a01119103421600a40000c90785900b140070300120400000ca007071005094030740080806903281c0c1000c10b0010421001180c615000362410003d01001c203400041c4240d22a0085030143d50740c0d6880d203021241c07400c2140c80342d040c0c1d01c1a041041c040100a009001d0300650070800240a6064400305083c80300034250b811810f00000c120a1000c102142c126018002c0d021040c1d08525680d000c0c11080ca04031000d100e400146a0000e10040404034050b480c2c0e22a41898148005070441e0000b0751281c0019103100003190b80d0142c107880c031600030340100205040050146480c0c010b0780c185200545412901100c049184c1000402e45d450300030b09480c2a1004203046803002c64001e00160002c1504c940209040d48100b032040307003581d0b1401801400307188200d443c0f01d0304407210003006251400c06450346010303403c00d1245407080d84000862000c000d03018079041144123000d0910a420100204066800d4098100040107040d00840c2070100300a8210 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 325988030 1250 325986780 325986799
    0xc140307051204050d02060c01150806040c080a0305030f130605150910030b071101380a060509060a1707020d230301150318120311030c03040602030711030d0b 70
    0x102d0040503480f550044652050344002542c0240c200903028140c0d031030380c807400004c403035900c0ca924559559080c1c2c041c00459211004102c20001400404e1b001002000c00804850240d40d5001d4a00d000080150380000c20703500000d07081480384030700d0307900f0326410080400090401c40f100c0b403102034440300e2302c07409103094001141c00d03010a03030b8420080700d401200c20451a290171804540c08445207541840a40d241c01092103a0200c03520281c040000c0d01c17260100101c0c01503810744100700300d00d8a0a02c110ba88004c00c10241d41c12404445c2901c4003101e000381e0310034509405440c100f064401001c00c00c801c02040000f059000114141004003a403201104001d01c2c54441ca0b0720441080c240364005801d0004005680c2c0203131a0120741d000c20704000c04c44d4400c40500181c0304032406011348060b482c3d0034060901c690144680750640164011251440ca850b1410120074440500000d140035400400644107a101e2036141c0d011040c0c88040d29565000e4003010405411b03c044d11500c250f581c003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 325989280 1250 325988030 325988053
    0x6012c091608070506030103060c170f0708070e01020d0e011107091a10171b0c07060806010504060c08070812010305030705100203040b1b0d020a0201060e01051c120c14030705 77
    0x140643c221030008022a14683c2140c0d620070140c0f0b01c2c1851501403102806200422110303903042c00f88070380042c4030102598a4200c03001401024050020014070050600084079a6400f14140034850070b181080480107120b00c00407111419112044c10f094014500b01042034065900428407505446250110300124501049275242401c400703500070441c0e650710b81d00070000c0700c80d20f103034000e81c070100460311402d880d91070203d01e0b48032650403090b80d084030400344100c0ba040141c003500f090080c0703440b40c14241420700250018030b9640014144c0d400c0803e00900700404103044909076038030404400b007a540e4031314146980c4d4200c0c4904940c0c601501405040305455031007503a2003150408116a00c40d200c1c40103c88009030400e00d035005c07002080080d61070a40c00350000f802d06501035400001c10707918240c030b0b82d202d0610603041103120b1000110742010300d690124851103d6600311803490301c00300042e8401c0c3e41160341c030500104900c10640c10f403e0060008400f6144160184042d00e06803240d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 325990530 1250 325989280 325989283
    0x203070e10030b04020607080301080d030615050912030409060803180102240405072403060512121b0709020c190c27090507081002030906012c091608 66
    0x101c45181821410300001c00c0481c160085098000d40098030240c90159940c452982c203901c26000310f62a50f020020480040d60b240c450480103080e00d0124424840100100504034803990766a00d1180900c400e205060390014811a130040c0100c140800c0b50301c0e41d4080d1140c403034010f140c001070740d511500b02c01c07800c2c0c2d400070691500e21005402c9241d030b2081110030490f405200908192080d1264a601003031540f418501d00101c00b802d0b00140642142418000f0250b0380139400c5503003d1140c08018000044000401904000c52103810f55191f004a0001e040b20000741d0f94142d900c0d2080200000d00c0c00126070043c00300400d080706455040d44100300d0310f0301d03c010320000145444010081040603101c402c010800c5c101d0800d0728004922034078503000301613a01c1000151030542040204225001d0204a0100c08000300c640c2075017140b6051030207988407041481801264400343c024052144d903c01008100320210080c10040ca0810b04503035a40c0348040307124060580380308103010490400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 325991780 1250 325990530 325990559
    0x1505180403021c02031e07061e18050a030c021c060617030a120c120603120e030f0715050f0c1c05090d06021b030d020901031506170405120c0307020307 67
    0x4594000f1450080c801900d07520741201b20600200042040c0301d00c0002031070780c1c041d9501c1d0341c0c680e42c0360036410b0042000890444071045010010480714012410001d40d011682c0c912082d01401c4c56003403114280007240c1302c80d20310211051074081101ca060100803a0b54021020703140b01800b6076a01c82c1d00d4000d5203981c1d200340301d0304801203105461740c0c42d11031280d42c0004164070490700d40550751040a00b03142e426584035070411207455000e4496804182d070b00155408004008030010405641d8901a40e070700c80c802d41c040d02d0310f400404458050260300443c121010108400010741e03507130342440e0b6031640355040560340d0502c5c3c104194111103068451003d94100c100010150040042140d0720740b030003548494088001148016404d5010510a001134009900c8000340541d507008410001070448038000a1810f000451034818029123511814803850a040640940309036215824102e10303045844c038500c0c4540c580001c280305080004806050094030a40440e0301c41501c84001000101 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 325993030 1250 325991780 325991833
    0x207090618150f0603020d140709030b0705070212060f07021f0203101a0a030606030612060506030f030c0733140f07080720060a03150518040302 64
    0x2400c02515100c1030074503510100040c21003200044075203076502c0000d502403030154850000b00c6c0d408601c140440c00540100c08082c040070310003141c40e24001d1009440d9451901001d441500c85400140880340a9021511416001001102415410102d00d940d4100407100f95940c89000008140c2142c00083c40f6103c0d000003030380d0f0726908850600e029000350802010f000d680c001c29a00020501c28a064411030b41060119499442c5550038001d4165449d0b948600209131078071404100194800182c07050031a0b0240000c0390503250b240c0003924103a5860966140d5010000c1c0b001460807000076a43c040b00c889a46450030506180c045c8040c0203156281c0041c3c003544120420300d128490b00600c03002404440c019810300c80a80d400403c00d400000b4121020100003881c101407010316040309030340b510080c0d0240d02132070300c07070300803c6190080c00c80040c10315844100f1500d08480f606100c0c0d0140c01e024101c0240510021031070b045002060f0303001c0d001b501032980c1e07400c140e035494081805860f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 325994280 1250 325993030 325993049
    0x14150f060414070816091214060f010302030a0f02010c0204050a02030a0605010819091b06020c120d210e030f1905030f16271e1d0408120406090302070906 68
    0x19a80c15100306180ca05c2a118881040418000810007890303010103956a0fa010300d1500d2884500c088040e86000405021010310000c00c5004200603030340000c49014071030744030100c8071050f4420310047e100300b241c01c100203601509103010409a460994003561041d80c6403a001d00007660b6510040d65185010740304540b0380244032915810651180d0040c0c013050b4810f030103442035050030083c003850003450741e000480180c10001070b1001c0351038241001c1c0a41a10040501403098205a001c1c04603040e00081a40b00d003143c0700a1001411150b001500801130b400a40703a60300b06104140c1d000c0d80c002c503030303203900355014140c900000c911502c00d0702c2c802c00d032050540d000ba480e42d60324481c00f1164954100e0400c90b201c500030481ca42502032002811944884201049043c01071460035030044150b410703841d6003240c100304103201c1c00e00322202e0000c00c2610b42003005d4556040491491040c40b015103807007000d800c240010070203141d1200625034000d9003034032400c82d1a940010180d40c91407044c0d4058 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 325995530 1250 325994280 325994297
    0x120c050304080a3501050603131112012307030b0603040b0603030f0a0216080f0304050906040204240909150e060d0506100e150102070314150f06041407 67
    0x1001c2500601d048081e90074504146113080701948440c0c0300c0c0d08685842d03400842d54600f44501640070300e44c05410101c60180c20b510b4040c526008480304004040e01440525503440c20544622074008840308105000340107024400c030784555080c1a41c0030349680e4040704800500c4003031203845600118040140300500e140c6076030f2505240c0d1000600b0b21030741344c00200851038507500c000c0c2c0100000740703803034014091301228011045410180c680c00240c1c16044903896411a2201108407000d54000f00d405200d15151280401c0080c02180c01c82940d81120084201c0c0403a80c0c070f80165100c1c0c14641e10212015140d0180303c1c10349945c4005811511000641803008040700c051403984000c0107002d560b03200c0410f442e5989001c0c0b0542d5000d0800e015003c09200e0040103910f034692000800180b006140340e00030000750b40d03050a10018282c0078001910700e0003d00700b4408260b01c040d00e90740401d61410300c0900010000300a403441403240e4940443c0c4542d41d45c6159a4912994041d200c0ca0b01 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 325996780 1250 325995530 325995533
    0x1d0f0103081b0c0910030201020f06060616050c06031e15010f0804060b031f0f0b0907051e03010608011409060a170115090902030105060a081c030b040c020a03120c050304 75
    0x30204030702c0e95800b41a000d141009081c40c1c40350380043c0d208100e040260400d4519500003e41800801e1001d544503403c0f5801304405500c03044101c5e00b010707000000d214601d20560422608007100d9101c02030740080c0000070700180c3c90b00180842c0800c038030200409101d0303d4404040350392044090402d8045990f000039403d0460042e2425139100e8050394006c00c0003245c4800080c00c00baa0006012800441c8402052101103684509126000d40381000c101c0407440800107202d4810042c8020208000024044402d000d50408c544100c580c1380c0b56a40c517541c6a180c00b0340600004d0042c1400050040040c1c0750524051803824003d160240c001c0c0139090030040c03101d1440000310800c9045640b14130b403210310300f024130b140800106a2141c0000e980c0b0706910406082d2200541064410039950b68248449480860180e006410b0088603400d21142c4d0f0b8000d40140c00e005600650107843d040316003250540225078115114401d64842d401c05d40d500c0440b5003110250380c0b60900180c0306000250 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 325998030 1250 325996780 325996807
    0xf0e040b070903060c0f090b0717091206070f1214061302040b0403030305041e03080c1c060605070501060602011e09080d060b040f1a0d020a0e0a1d0f010308 69
    0x190040078070b2800042d51034582d00c400c02a107108801040c0000d6003071000c1c1006603488203500001c0c0c040300708864075000c8142c44040d00c540301d210011455000024051450b0355403c4001d0480b00159000d82c1d145142540c0b014000100c10310221010543d601c1139045628a00d200700a4a0580c1460015558444506004103801e00800048009508120105540080c000074000441c400d0790007280c14a800e18140340501c1d035040c0c0051034840d80c4400c0400083e005a641584165051006915000200c100d01e40448100c0d1300c02445d1441d02c140451460390100040800b07502900081c40455602d4104034200d452488044910b0700c40441c501c8500350003604801d404d0350040c111541001c0030000046c0450320103a11007101c0507400038081014110403a0780a0040c102c1c28000c02c0c40b45003071607490309948110003000e0104ea03400240440201e028003061901814003030a03281c40d0035120103a020120f0541192030140c1c031120710002d110008039021060583e81d020b04c025084c05104d00300c10 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 325999280 1250 325998030 325998053
    0x60310061b0b011512110f030a020403211106040c06180320130b0a030605060d0f050f250504050c0d0203040302070f060305040215131215060f0e04 65
    0x5204078035040c46000c01e100d40001d0b03010384102860b011a028011001903c800c81c0e08810030b0659040c04422134604034071038140c81e100720600c0281c030b60f290350f181201d00c021721403074200401c050310034107030341b20750000e4a00001440710072034856840d4011085085960743c44215001800c3d0005c405040c40388520031214445d8950165001c80c00e150f480c0d50707a00c483c4140201316641c890070802900c0e00a031403d00f1410791812000ca87c01c20119001c2ca022807145050303800043c0c5903d49420100b0080e840c7c6c44440c490094107c141580c07d8412880d2a58841c080c0441d1003c15120340302c01a126000860901522840c0b0a001c03007054502e82018400501001001350800c4107080c490000c0f03101c09030006610541c4264007034003400d41412801e01f0400c0d20b42c1c000d84101440c01040000503111007103060580013950403039640b0b0b004107030700d16208114150803a0602d00c3c189612002000000300006000f508900024490386485525400440b10684a0140c1181e0014089000b080800921 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 326000530 1250 325999280 325999307
    0x50a0c0515030435280906090e041509030801050f030304080a02100207031b0302010818190501060b18120609030f070501060f1511010c020a0206030901020d150305010b06031006 78
    0x100b01d1244c150351102242c1d40c000d580943c841a1104520f00c00414407420825940005410842005414188010f0000b00d403401440d11076840c22001c41c0902541031001c0d00040000e51040c0f00354255440c00601e43d00c0300f8422580580705ea144406040d15010003941c0984506900421071040b13140c003008124029084507400307500480b600840440c115500b42d141c0741d00041c2c4800405891880010100d0000808101850304036010170908248042004d003150170805103469002190307810800c0c01042c5a501c000e41c903820010740100941b4100c1081d03200c2c2c0c0e8013101d95001340c4600e6002c07281c07510801ca84600158004000242995816002400465000e0f000008070540c9030381200758401e4103a003146450500c003080d0034070703010f0f03000290a0502600400030711419007071040c00780d9110a4070a00a1042d1000300020b82d10f8003095040d41c44403081d808081c031166424070412440909180010340d42942030419500c0d4906085d8200c0303000341e88900d40725008900d040d0003101c554204454 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 326001780 1250 326000530 326000603
    0x2104030206070f11040504030c030c0302010e0304060207081b060f03100503030703030b270c0a0e04050c1914120c16050313080a021005090607050a0c05150304 70
    0x100158860301c01404a0b544030b80c0150b141401182024021501310001041c0f20324101820440040d070b1021084011076418104105074000c5460242d001d08840c40c441482d03440041400207081d40d00145841c111504c120589298407140807407060309120903003045810140400040303c40e54001c000441e80a14481c0400707104548a40c0000d045500c07041040d40040c1d1107001c041511324203c03403421880320701d04e80369546c80c01074090405a03904c0d0007080340b136180b50080f82204015001ea0800000e00c28001c0c0300300014642003c41c1c164540024012003000d4824a680b0029030740260200e0b802c519051a030103040100c10005014240b0005152840c1d46805010504c280c08140819001441c070501c003440e03e440741140b40f403400804583c0000c1059018012800250326070000e003921400307007458090380e43c1e03148101140c079030301c91188010003910031410341c0000c1c07090609003a020303030701c003103805660198442aa602ea14081520007410408023401d10b202030309a140e000380030800301e822 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 326003030 1250 326001780 326001787
    0xa140c010203010e01170613030807020322080f06010e040602071e030801240507021207030b09100b0a0803090d05100f0203090f1f0b0102030d050a15080f21 69
    0x1500103007aa08203a110002d006032250040c407090440040e82c04140c4400c10040c00c543c58900d1014480d2880440b001c0d0a221b29480414241d030320910440d90f210b918656500d0303206613003880351070020a00307100d818100c0c0282c100c08603518402103102c9049411160700c04046444503166803009501500381201c0344010801400c05140b640307107840d0042406500c0d00d220941c900500700c40007a0341c10b803407508445860b584450160760031400b550381858041d41c0200c010054500c44515284041d000030780104c0c8480d080119080c00041e60702809450004240a0072028078103005c1d00140710b0141c24420781081c0450b01c03071401c20850844101d80034004641340090043c202008640d0071070515a14907400004105004008200101075081200700602b8104a04040c0f940c218010380c0c205400c1c1600c07070b500c20381c542e8401c005640321105000d00c03c00481c10425507840047c507103003010003184201044006848080440c0c03220007426450040c003e03144000d20039040498104412061611050 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 326004280 1250 326003030 326003047
    0x3071d0a0f0e0a0212070b300906040c12020a03030c030207150e010305060307030803040b250e0315071d060712082a0d02210708061003050c0a14 64
    0x10301800005015003409803c4503039550050105010700e0f6041c008003070307100c55030802038070a014040f01c2c8020300d28559400017140d4004140c07600c1226181a460141582d024000c0031100483c0050040d482070100c0c100152703480c2c10501c841c80c0c400c3c50281d402508103a041002c0381c015440c6000c2a8880e20541e00d00907110b0a0704403941d051142d07000c1c00100c658144d4582540c041c807895401c400100d005144007403031552002c07a2803100038070007007884c0145004039410403040b4001d442c401c3e0760b05401034608000b1002c0102006010358000713229202d450218020743c18421201c2e8015207455441d4084060424210154015604010307504402d0030050300003c2000c0c080c9080a80c0419601d00101e801c1010403000e06001116911010909000722030900302d8004045905219218902507203034400c1048a00b08410140c60303007402800c0c9142000384441e0f00000b0580315840c21503101110400d401421001c44070111083d0121020030008528054041e40c000c450010780b91010300d01c0c08141c1c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 326005530 1250 326004280 326004311
    0x204051c02130e150408040f081c18080a030503040c060e030a0605130209010806180d1e030b0d05010e07080109020f09100803131401050903030d11042102030c03071d0a 74
    0x2140d058440b03010207d420304c1325210109483c4001e1110b14010704040728500e800100a201d18000c00c01030008a5640071ba0655400d0414002010510f0903900f560805060140480c4c0c01200c00b1503604200c3d220120b1800e019400304100760102074008c0401d04841d0759040000c0c80c1c00340c07684212908041003640183c0d100980b81340a440c580d405024035090062411640c86500d4124520300d4006041c401d00c400d50040c0088920324100b140ca040703c44201e42d095004000c40840c264000980041070340a0110540024142c4445d11080302c16895070303262142d08a880c0c19900a41c42201c0410b000c0703003854401141c6130852001e840422280d07035a140107915582c0284400c60a008801d90104100001c22a80718041035080c00d20a00c0c121405001a44a2080c01c880d46110b503919009a1000c000850960f4054031500300700761007410210082020100c0d84010480c8607100b08044140207040104040040700d41c505800384c3c4410a400c1441c5c0303c403900400c501c1070b00743d45400140c0308814 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 326006780 1250 326005530 326005573
    0x8012103050d1d0330070c061512030302070515060a05060306030f010905060f0f01050105030a050a0b03031804060f12030807020c0a0905040212071505090f04050702010204051c02130e 81
    0xc01c15003110381542e18280200c402017480003103003280c001d19410010410382010b5050700700da0b0702081c001103000075008040305000c21a0004c40e81c5130f01040a06081580680c01045c0450045049440ca00214002c0c00040107040762103d40000d070420701048141004006142c10030401000d40300e010481d60121401c640442c10103551070b5020030140008400e08800590304280c0264000509604000010b0301e940300c003424091f905559080007540194140e4041004201e004040c5e9640c0c041083c161201c10024103407051040b0302c0c03d440096484280c414920440701a0051000f081c4d0300354405540e4100e0040c096010740c0500540720000b03076160304a480c090072a8040009581c10140140184410100450112035009240c24850149044c1c403500c0c0e101e03542d20f001555407a228000c2104110089a4150040d00b0082405038250b010b402400c140c2d0002c0c0d4000c0c1000c13103c0d03440040309a912120194103c0304400c90880d800000d40c1007050202642000c5641c0d0105c03c8004a02216 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 326008030 1250 326006780 326006797
    0x60b0a0903020a0e1302010507020f2e08061302070302070e090a15090f110607060203040614132a050907120b010203120f060102120a08012103050d1d03 67
    0x200800340501c118500040600007518980b480d00065103007a11044000d0f82450340043d050000c0424920115908d00111045400700500700c40c031200c0054003000403824041c0348000340782e039501d641000341c079124000c810300c10480281644000100351021000075800b401c802e030214080d202020800c00042100940908c1080e0002e03c1a926181070519440e1100c41c0192100c50800455501140310051400c6900740c001280300707294110000091038034401d00100900c043c1c0048100000d00485074402d9060b20328040c0040c605580340784100400000c8414010700303100d9500404002d034821304a9500c00c4540780c002042d0380e04d4446001400703c1c5801c0313500713000084c0c602624000c401b4060203a03100c10030080c001141002c4030300301c00034180d02300180001041102c45e000225140e00c2006224810050304c641c107940c0f138580303800c01080720000740100224200c3d49c05200c2908200354084281c40d03a00743d42ca03a41403808441820700501440813140c29026049040c200c5211420700040c030450 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 326009280 1250 326008030 326008037
    0x15030803040c0e0910051b03150109170c090601020d02030f03060a1d04200a03020d05030708030f0106081605040b0304060f020406050d050a05041a0c07061406210d050d060b0a 77
    0x503c003017104020f40e20f006040d41242542901012203103114041a260000c03108860f6012260280c001240e4042d10796101d21f9483c3c0995490500180c0d000c55064520340702030b942c414441e1707601401a641c840581e020315006a000708002000c03602020027854100500812900d03000303607580520603410075100502c1d09036500030000e100c100411800310444400c0030844e08007800b9810800207901e48900c1c0b001900450001078003d040041c240226011a40c0c01103140e51241811440c9148003d024000c40d4086034a040116581d0410465218121103143e079945140504000c445061030308050070807298a900c902805000c00c075180060000391030300d9620640c6030341c400780b80ba90507654050101c03039440d843c12040c48003040c4148160385d0141ca030444040120f86404107011981e208808010b01041d1805404c14185048050042e018801c120390201044515140715194034100246a00c250751180c220382c1030f09800b500180c10741c5002c503c800120035503a200300580c0c0e03500040c07100d00003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 326010530 1250 326009280 326009293
    0xc0402042706031a2a0427140f0a0203040804092d02090a0b040e070e0d080304030e040509010b18090a15020c12120a0b060903190b06030115030803040c0e09 69
    0xa48070000c0207460445c50000284100d604200c499941131041e805100540d08038084e00c50500388038404034018601b0300100c03c0100d6000d18800080d0240142c1e00d10001589410208003038944a009880c090354004119502e03113444c00554100902c0040640b804c50405400391040044401c41c25090a29003184056503a881680c00c0103641d03000c64120310b5103c5010b001c2400b11a020980b0558082a182031003252040804005450043c01b4a002001c1c0000007082204040e40030b88180c4107000242c405020a4030740c1d0504e2803d0f0340301f50b10040e8001d034200b00c030030b0101c05c9400000d9810160200503202204096210040040d000d064a04d50007074001a5114164400b0001c0500840112542908100c13410200364000f1002402c03042d18203880c1c26100802d6074070b0100b02c64143d82d006003281c86c401001404000b01c200303824010307200d200c0b070100059814101070244044104510300d0280d010750030740d501c05d40107400240050b00c0c0040341c110086a1800c07040042802400102c0040c00c0f03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 326011780 1250 326010530 326010541
    0x30a020a0606050d15020c0102070804080c0108180c010c150f090b0108010207030518040204050603070f030e06090a03080a020403020405070809071e030201030b030c03060a0e0c0402042706031a 85
    0x6403034003540424001c00784d03094203030041170700140b0b001d600075212031002d41d8a4220301107031400390040c003c026024607800070b00020003101c00140e20542550a8a40f141550b8403240500041300041c400000282c214100400403584904800b205d40c0d03100d1610260301940c01d41002c0212030b840701c170321310140b50750381c084009010a42da903440c010852000250b2070200541da004207240107506401845200303d00400c84142d03601e4040c3c42c060440513101da905d91501c900000d200e440c1c04c61660020034a040130803103031000041405840f82d0401002040054143c1ea811200307841c004060040d41d550900c404030040e45c07103020b07590050403a50350b84038460914400761402d0244a03804524005180317084104800c11400032101269024240000c2105241e00440d051018002507554907000750341c04c10504520561000091543e444100c404034060304044c0030480c812801040c52001407544019101d075140410000e48048070403001c50b034a6600c3d52020320f051140788c0d0441c81c58844004000c0c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 326013030 1250 326011780 326011793
    0x406030c09230d0611091c08120907180507030c02010b06030c090411070c0e0708090a03050c0a17190503040203060621010c0305180a1a0a0b060301080a0605091209041d030a020a 78
    0x100e24910f240c803012000c24180c1e00d2907441e01c549500c04200749c0848001070507945c004d00c018030080c01d0035503002c10024194482500100000c82e00d05011070b00c0c200b03603000c03000d105119400313060a01600a07460743c0c1f503081101d25250040c0c40403942c0551038808111421582c0c601a10303000340300f040b07941c980500f0990b0358a03402000130800010890410200304c0d0b2401c0c001900d50410b60103040049d911202c0210300d03401c01000030300143c1000c0e0314100035a00b00342c10100404541301103000081e000024107a00300e0b140e100030f48010b989544404041072003032504d0041e604030044202c000c00c10a401c000851401d54000d45d00210120369184100008540c400310146929140c4001805102d00a90350b4a5646000242c10183c0707101d0340c0780003403410102e030f034400c2d80c10402c0200015165030b0744455555a0341c19000c022944641064003241c1f241d80c0025845608850b194442c50030882c1e20028000149014080f030622203035805c204444402040c00104140110b90b07020b05000c040505100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 326014280 1250 326013030 326013049
    0x1090f05030a080c0c0a17160c05030601090e1b03070806010308031509090312100504090506041703070903060f0f140f01050907050a081b0406050406030c09230d061109 74
    0x24040e00040165000072900801c02105441c7e02c10b518840170400c41000e1043d5010f10624110721841c2c4020100c1401401c40e22142107a00c00c40c111101c680c1c03030310400c60690700c4c00042e1000c0d81e07000f80800040d0514030121200c5600d0040c003151101e40e039502d0390a1800d002a401600c0a41c40003003400175031a503a034100c0e02d0154040e01e4500c2e031b81c10b02a0500c0d03541d204c2d83d0407480c1d1441c4050082200b03041c070300c00d49200034013005005000e1440241451a1101001d84086460150382a0301054a00c0144103032480348020b0784405041914503107032240a04000d420002c1010340e2040100c9510320300344500307095100b580e01826602d01d4038051110070300c00d041c2c104134130940d0894100283c01f07034030108440c03040c1010301e02540c2d55100c1c40880c80e4008440c1c0741140e000d14011401050035a80400a041200c105640c2408100b00d1040266041c01c840d010b45889440d00018420604001d800b4494100c0030140c5015000d00d19516060300326900c51087d10409140002c3c00401881c002120b03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 326015530 1250 326014280 326014291
    0x11090c03100b070f0b06010903150614030610060f052107110a020f061b030301030b071704030e041d0f0d0e090f060f0d060c021c05120703020c01090f05030a08 70
    0x100e0301e0410f850711104600c0d030f00c01c0d2000346080190b5001480e2a44141680c0b00156070121081a10051080040c0090040b501690890412458112800e8500010001e010780d503803107808241d80d800c04001315044c11042401805100040150300019166030f2030014030540940030420725403c00c0071000340303800c110002400e00f55101101e00000359490b0301a00e200c0b15000c0703030103030356422514010010070020340c8171400c1c02d070001000001c14024204503881c461f2080303a1f0b9468920110f0408041c000c2000e580140c0002c0001c0b00061241c1803c0d400940b041c05420481d504001810700041d1400d40c50181482c1d054000c266803000a5800500300403c2c55000c4840c281e4070b01d071540d00000410002441d0328440c00f001141040c2a8645224000810f900650180061508039002960301d0726a84040360201c0c080ca00100a01c500c100141c41000d89031303842039005904d540c401200650841c815424032550b841c202c442c0025480c800130010240b048000e1911950910805811148020704 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 326016780 1250 326015530 326015549
    0x6030a14010c0e18010611070305070815100e040209040c03020d140106061103091507080703050301030218040b060d05010605031504050607032c010609140a06210201080411090c0310 80
    0x21403041290741034021415146d05140080c20b240304d01d03009914061a41e4000b404901508801041603640442c200410403100d061607101038403072000c5c200e0849a5441031f82200c045801c042001460002e00319500300303001e40205c8100035200d0700021502d015000c0f0895803992034846103c14903400b0700409000f02130509200b5104203d8035016502c034820403446510690200b4082c481741d250748001d448200b82c00c51145034450841d0324014040d40d10a001c10f920074219541d0a102d10383da1040b90034403e070f600030b101045580703c40e82804106a500b80c0c0484081d500c901021030240c4042021f600001c54aa80c0e5008504250602604100c0c0103000c2e00300f01410200200c0d2003c5c00020640074202421401d501c19400e5120b1840c0108080e8025003012420b00701d500d01d507040e1082c80c0501500307100d6410028590f580c000300a45541c1d2602c100b0020384045c410001542c068602c0583c482d006004074080108904002203102000b22074900034110040248034244030503000001c064082030304d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 326018030 1250 326016780 326016799
    0x10b090703200c030d05071d030c15031b0307170105030105090c1003140a0911030a0c140a051c0c0b0307020601031e0c080c040b0609090a0506030a14010c0e 69
    0x511900e5038951220350301c480b1480000e4a4003401d1000c000700da8004c400c09104001604090380005c01100c1c200c02c030342100c0c6105807a07401c90342c5800b04081c0709040008280415504074003070814802d0700020515604680000440c2540318901c074015882441c050755100c040e16081c90f8200c080403c182c004078000da1500303041010f00000000c411072205021940085a02043c540480280c580460030021040c0c103074041c040c0c410050781000c00002d1003440f64074007188114041c50750f141c0d201400640b0f038640440d010004c051401d86054043c07a80038280d200c110391541c0210b00159990016114403160400c5020103001c0d0450501018088608066245050400c0002e550720818040a80151105103008c8001042c0da0300b81028a540f00046444095643c0c154507103a90000003903034020b1b418000c90700442c0c9442807c0300c86200000f052040f0035158840b1100045c100108003a0301842a8004640818135800c00060041c0c44070b4000700b2514031845008000394201e1401601561215 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 326019280 1250 326018030 326018051
    0x4170a0203030919031e02090703020313061805070e0103050d050403083403110c04020408190303060b0d0b13110316021e070e06030c03100f06031202010b090703 71
    0x1000b2949000f408640b00d0b90640c001c40101c3d0f032246526440100404060121a030007011401c026804050084039540303000c4e540c03604194103901c81212030748104d010800000000401e01e03400541c3c481102d00f00000c2c20030b5a9601c147c60070880e504007880340000d0400420804c4010481c1c1e040304c000b00d00d071041c1881d241d661040500d02850000c0c88603007036100d0b41d0400e440501000c1c0c05040300072088008203001c840c10301134038035280c4441004180c09440110b00b41030500303008440403203d05100400c29405862645010560214408c40406896a0000503441c030b07244c02600082c500c3e01400078070340d40010204207002203000000200c81d42054045d90700b411000d419654000103c84440c015862440d0040b0300b8407814030142a042c0840c00e01112146000064034000c0d183c05a007141c0e06619100c040603514190300880660583c0850030403040c401c01a00000d4454450b0000850002d440c0d582d820402550100d5000044c0c0d03551000e0001854005041d942000da581400c01004680 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 326020530 1250 326019280 326019283
    0x312070215030c0706020d0b030c030d0905150d1e0b090f0f04050a080c0a031d0d0816150207150b060a030e0a060c02160b0a05030f06040b030a050304170a0203 70
    0x801d107101c49801000c0001800061003000b2586aa5400745c0704558460744030001100410b4040000c60003407103040916041410700080c0d180c0118450f4554441d0303945000704000c3c1a01c12500c1842092005022150345200a4000c01c03142c0c140390b90102909048800618045035178018400d03214500300c409015414000000080e044070b480303d9000090f075250305029182c0810858001c00039940010590030308400400d903481e00610030740d940c1490141c40214613510104ea1041260b22030310840d09000010310f114020588681301071a0201c0800342c82e1502e03501e0300001c80102c60710f1500000c00c20100400e0300072a43c841c8441803820003000740040081411401541c00700018196104000c0e00380305420014520b40b04c2c5d04c0713982404004a60a130003034131170800904003113025401101c0072551b00724140565004808030398541c0e00796907075808000c0d031214001d0031080e0895554200c2c1201d54500f4014a1080d90017000150b90f940c2c6412480e0b0f0302000121045a0039421910b14100180e07030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 326021780 1250 326020530 326020549
    0x10b10052101060c120519030f0609060515071e0c060e040e0706050d11070c030b16051204020604080109060516030608030d1d1b100509010804170f0d0b03120702 71
    0x130482c5ca01031040403411003d1300d503485a0601c0120040f28200300201c0b03d507141d00450340c0c40541440900886a989160500765000d6000c0c0c2540300c1c80488603d021040100c002e00206402820600380707072080d81c42801281a02890155041c100d0030106000341c030f400c801102c4400e2001e0710100120a5030200941d150311490103074100304400003810b03e91800081c0c102c00b250500c5100307015980c49440c0f0700030f10f001d815072004581c3d13684c070320001421010718101a02d1b8900c01c1515002e1802046214080303000d04000c1c808c991201c01800080343c0c4c50002d100301202d00c3d100300f000042a042881c00d5040c10741c0071000f44001c01d07082801c00d11a900b004000c0d244017440480c00420301e852405103a03868002c4003103100d1407920403420303490741d4903a24099075a8604000d541d000e044c200c516404403002e10440d60607602003180310000c034000030211040280c5882800844078145a006101c40c0580d6100c40c4051209940310b0b6a201114a41800720021118801c20813500d898201c1d8040f942994 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 326023030 1250 326021780 326021783
    0x30c0901050f040e030417031b0703080f07030201060e09060a0b03061e0a1107120f03150611010905010606020706080f072c0d080a08060a06090b0a02010b10052101060c 74
    0x6813210180740c2c000008200360790107444096140a400d003040d046080d5039401241360100303480030401c94040c00080101c1c1034002e49030405421854280b002c00c400d07440b9031040f00304504543d0703107400001d04131510b40110380c043c4004001514040c148034664009030f441007030605200c1d07000901440340607a0035500c078040c0350103112100740c43c40d612440d80d20010019a604008030340760000d0040f00f00f20b02007244254001c10740d150700c40b0038542e42c00120111007110008080624080d0011303c6030303900500c0c4400080d60000700100c0c95600b160303078003400d4810030707030090000d0b034024001400700b47d07008060f07554170810303035003000d0f0b010314100e032000380b0552215200090903196a590006000405000522041c0010300224030103007480c81c210166601001d0f04800003850200410128a0103115060071914250b0b80d0308201802d098207481140c4c808109001550358500100310346841d07400c040d45449000740c0b41c540e222030800e584003039184990724105c1002e1510320010322040b504642d8500105 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 326024280 1250 326023030 326023039
    0xb070f0e0f0114070b040b090111091201090c0b031803031302090402010c0501050c190c030c020f060904090f11060705060c160b09011d010b130506030c0618030c0901050f 75
    0x280c02441c0140c030700110020100c038040320000b444000f80304081c101c203401144500035461156440031402d070b00703c0c0c0f206803a0b030250500400c030307040d180e162103400008086104d41c00051401c4d410350314080c2c00821503003c412200c10201c20020303403001c0d220090000d0010b0320b0246280d403600742d4620842034813840009119141c0080850103692044c0c01030a403450703028008020b141070403001307042d50b908044845029401003a400b60036080c441e1050070b03035007507168503030a07200c5072a60308101d0022007081c91250003500030300150419958034091b0183d01070085041c4240360740a420302ca0764200c07082c1c49560162204112810016800041b229802001600c0d00358a90101d80c98007011070040c0326010700040410b00902c0500319041d0710070440000300c0503c0703004015002c4a9a801c0c2c4002d0800964402d21008841000502c1900b0040e4005401000d550301c2500c800c0024030550405024021140040403207aa0642804c00c0900f9012800701e0740c102c0658540380c0068600c1e43c3d005a070718043d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 326025530 1250 326024280 326024299
    0x405011b06060b0d022808280c0314070302120703020307021501080f070f150e030312010303080703140f061e100507020102120906070201180e04030302070b070f0e 72
    0x6001c1c20341d1010001d0403100d65803941d14640d06040c04041d42150341420100c000c00785501140c0120b1801c46000d0740125243d018403551101c0300051361665003c61200805003000054000b0a1103100700e000d00031a9850005541c030b08c00d4941a00f0000c01000a0306151041101d0358124400a0040d030b403042161070056034907640e4501c101e051010480e050b002055030240081030b0080007150030303103042e0161011503041c266541d685108100c2244160b50001004102d1503007214422080714400402c0a812039140000321180c0d0600882c00b40e000b0303070000307a0003401d0061444d454054204580180d07544070b555400c18001d604140c2102811080c42031510304c031881941c01c2031551000c003d15004004204600c0e00d50b0015086e5442080124014003c5200f1203401d088000c0c203079418400b0150000742030000c6a401580c54490302c0c020040c03601c40c188000560000b202d559103129a100350780150300c0304e01d07904c7e224001c00030146c8aa024820590201ea80d026480040c00310900d0040352078669 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 326026780 1250 326025530 326025533
    0x4030206030a021e07053a0e0d0501200901051801170f1e010e010b0a0903050d09060909020715050c0403020405011d011a3a060f0b0405011b 62
    0x9100703c0c0d80e4600804d401d80d002d07081e0f071303d100703006044140d00030002d8403000702d646001c03902c4400018070007024100010507038140d0070392141140040100c0a0506c00c003010700c1240000c444143ca11011103880e910746a04403540343c140c00e481c0841c00341e166281ca042c0036102001074001d000700f0004040b4141c80091183e090b80c411401c0c3c050f0300745080b0464003207040003040709403412812070340610000c90f40140140e904013030b4140c1034100c0b408515071403c540d084c01d402103281c1c1e00c80f08518003001000e55010003ca407040c08089112180c681b00c0501c190b24200300070300300940950090403454810700a8402054a50351416008482010001050385e0780c2020b0103207900503608007a42291074440003003000d0f40c80c0b01046803a5020794040080c00d82e0799280c01c261000100080c0e00320004241304850445d00210720252201108a002d00301c00416100700d52140141071801c00241c581b13a000801c544014100d401c0003600307558201925141c18080081d0440c9142982d140c0500c16110b500e40 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 326028030 1250 326026780 326026801
    0xa030c060305101e060e060c1e030c03030109050601022a0d03031b17010f0807030f051e10110307140d06120c03060f06050108060405071107061d030a02060403020603 73
    0x5011000a449103155a005052030803a013a4040e85020440507280e04000e444c00c0c6c07007038070304624a050042c4040c8200c3c20140d92040043d6060050522060040c080c0c0106d0900140d03010701180398001800b49422000246040c00200d0103910304c050300240200c40007aa405000c0d00f1100560b40800f0700c01c981d1800310300508000f0980301319407080c0e0200711070b079550282d032070710030b84192612824442c0d803a580e44690001c3d140c0b0034180240d0002800700001813080208035881405401960000000d540010041508054203070201d40c121120300f920840e51403107004400403039440002e06503c1c0c00c0d00094404011101e1514521038003080442c0000415002034000d03003074055003664858075034a80244821120702040303a4207400c1200b0140d1150041c8600c104807941650351019176112842407000810000e04440c04000400c01601c2d031540c01003000e28020106036a03105620791400c190407103c9400d100f206031007a0001580c0d00007580c0d92005a030141c0390100c034010b035241c507641d4451 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 326029280 1250 326028030 326028061
    0x120c0203030c0d091d0712090b0a0603051605030714030f1c090803030c030f0406020d060b0a02070602010b0904141507020a06060b07020109150512040f110a030c060305 74
    0x2541403200140740340b400300c0003040314245000161101210b083e202d2290b04440929214444910803a460010382d02c64807521690380803c0c03031560006601d4200c3d454072051084100d520185454954100b0420040100310250300d500707030711803031107112410000000c0d110881e910584202d1025482c04c124950741c2840b405030310b9903a010490710810f0001007889003241170300c80070b1400318111346c1001030b002c43d000c41101e1190726a40c48440c0382d81d0328402d101400880281040e90303243e90902c140024000503101d0b000152036040c0726107440d440364100c024504000394000303904690501c5e51031015a100d0349041d0382c0140d400880030111414101d8003510b23190511040902030740d22541440301d1960046040c0b0810341c014441804025203d8140b02250b2185030360090004005000c100942049402d104400006500d046850300c034050745803040c1e0740c0c002ea40551b550350f2900d80e1482005408010081105015280c441d02541b5680303030a840300300a480366400341a210400251401e41e0185d22 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 326030530 1250 326029280 326029283
    0x201030c020111070b010503071211010503040312090302060604050604090503090d02040e070e07020601060305091c2c040e060402030303131b060807020106050a0f050105071104020301080f01050a0b0607120c 91
    0x75868911509084550030705c20320425000b401418000f2a65400d0240d00d00040e641003640040c1451003040111800d0340010070540401080a510114007510390155541040c00380e40140224140401000300303c83c8040c2205110f94508902440000e80110588202c000102c400c01c201c01924000f0401500000300c06120340c2c051020049070490006100c00d00407030075a4201c40740d50787c84403415400c8890589081c410390b40002c850f030482a11036101c0d0700200211b0b241c00d0b00008208a40516072407018042000c22410300030005174281480e1103038800402e401d40050206040a0300825100c0c480641401421900d0b040610248031484c401d00c603403800e801d180d5116243d9290002030201605917200401542451130005152801c0400b0000f5100150703031320758000d80342600640e041c0d4803040c812941e40504000d0242159998400703940202580ca0280c0400b494002c50342d401c54600502600c407103850006001c800391600401d0b1820b16501800030403020742c0040055500b0902c0620 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 326031780 1250 326030530 326030561
    0x150e011b0320010c050301090b100e0607031403151c0c0303082505030414160b1b07120b0907061407021c120311040503030f0f0f0c0303012c040201030c0201 69
    0x2200a0303e170303101c4011412039425040c10401c030120325007004803558402030340d100040c0f01b0041501c003d00d00b01c401854101d1107810226008c0200c6071496441d50403c8404264201d00400c45800b14140385184a0b0304412410b01d00e1070010040e41c1c0c044064481d4040942004081c0e8001208000380c1020a420391100500c400540004458000e195620480703089030010341d0b072500c0f0b030440e0200142c10412100c1c1036025aa8031800d01040300c1c41038122040c000038810300b00c01d5940b1078803011300c103220280200100340700b000006420b2040000e00040c020782110b900c83c500400c81c090740902c60b000704000c0c010f4041c0d555500d07800012203001d840f0489420010740c4d802e9080402c0118001c0d03035008602518144411007480301c038144680604d10803a41c06030020420441c0380c51034080241041c084030740c0603e042c112030440c012402c1d00402078001c1d580d80000018020880c018849108081750721210070350108842003540013b0b03e014000905260300e4510795501b1900030b40102c02c2e8a450881d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 326033030 1250 326031780 326031791
    0xf070c0c0e0103110f040e0c01050c0a0c030f0b07080c0f0a030e0105130c091a042304050d0e120d0804080f1303020a170703030c03020a0c150e011b032001 68
    0x405076400d01041d1013052103149801c075849101d080600400e031017400014050404901e01100555040e4429000d040060003110060400a0040720440e0043d501072042c00c401d0790824545410030100180008041c00884401c01007403511030000c4a210909500031940c85614a00d000c2d00030f13110101d81020f25500304030800c0422180e04510048440c0203d260701560381c1c1d50125881202c0d5043e42100c0e0000b80b1000480803030a15401036600c6584c018906100e0400010a08103001c4c0141d81c11603030354000700c02100c82c0365486000d500d00101e084581e4881e4240c0075103034903a0b8403155250002401400c400180c01d201c0c260051302c031b02016096209030785101c409003034034108500d4041207216031440500400e200801412600c003404012008000c054110b071416100b80d10074100c22021442481128400100d403102014024008031b0049a0105448500607041101c0507440c0f50400059081090200221410005090780c0504003940c5041035506035021551101c800c1107495820203 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 326034280 1250 326033030 326033033
    0x30f0204140f160f021b0a030501020403051c030b0a06180e010902040e010b031017031e04061e1d031204030f0b0c0f040b0a030f05010e090d03050f070c0c0e0103 71
    0x40e15058428810290f0016040d8000c0314207455500c000343c02200160702441c88911105120701003660b0310a00289161841ca80c0d81d56114260b900c20340003212550801700150701014104110040c603041c442c1402d0041c0215940801c1444209100d0303d01001469030816041400c0e40c0006000382840c00d601c56442d41c0c440d00a44044c0d803152003071002040c5a00000500b00080d139080c0e9014544d000d05000080f8501203121050b00b07048000c004142c0410800001301190304503c0f6142c519034440380075111441c0c40c80203010845080088000c200e42e0990182e0b080e0f81c009595211801d040700d4a1030740c0c070442008a1301d001e91034200260241800140131041c01881c4844100652059600045550700d4625203543c40c0900f003c0034155030010301c0280701e0300008801400343c809003480c00140c2c11507000c2d049401d03684281e000c40794011515092142e502c0c07081c40048180c4034141824096030030303d005019043c42006016404202d0040394450811038030303803180c0c3e006201c10b007805816941c4a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 326035530 1250 326034280 326034301
    0xf0a09020f0a060e0a081606140c0106030c1809030c03050a0201061d01031b0f030803060d061803020106050d0308061207053f0a060926030405010b0108090601030f020414 75
    0x5081172160010941c000307001070b0002440700004080e074401841440ca8003400703491800000146101405083c04003645050007403080400446c000c03210464607614010001078020750713030104d10391071702d007030101c6030b008207401400b0f80d12520350500c0e2040e903810a0810880c018440e9421000c214101c003e10300d08803c600000c40e078180c1e402001000e84c145100c18041c403040300140718680d15020110401c0010407030714405940c1c4204081d02c1540401070503580e15088071600b04441c4c9090400031211030a043e824420344004e44426609416003140a0700d01408041c4001c0449103e003c003184d60000c2c10030284004d500916010381020100c03241a60040590121410742101150141c02c0003540c640807e10403402c2c0b021050080c000a01c2151269800341201d0074096a00c0d4005032107502d50044003025041c0d103135030b000641680300d003414541740342503c3c1d004130f106041181290a00031403480204507070b41107030360218688004140d68030105020382002c01c81d00411060032004c10180b000c1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 326036780 1250 326035530 326035547
    0x14030f0c09031902040b0102010504030f030207050111030c3406020304060603170414010801060915020a02030f010204030b0124260a1406030f07090209010306080105011412060f0a09020f0a06 84
    0x708640c28400c180c00c01b0012400c17102c0864014000828080320001d07000d000354000c01405020b08c0011407810340034040440681d00a460300c51210034001008442d01603822500d0030308410762151100003003c1440c681e5140400600c0250a80341c2c0000030070304003e15a03000303030300841d48000c0c0c1c803900c0c940900703401900b0703006441108034108801c000826a0341c8600480d41c166141340d291000104c1c10046841c2888540d0400303202507200301506d04015a8041140a203200c05110015944a003149410f144035181a4031168010b07410116004440083c0100c54103844800c0c580702c000c00048a040044204103224907114000412003170040e080c0c030342d8101da40300310106000d02c41c8640b95001450fa54a4110b40c404109400601d418070402d000380c0c0007400d911390145000300d03203070f031311040389608485081e84125400810840341c40c03020b041402c0403135805200c500c0540b241c1d01d49245555807040006101c080c00c69a02c0d075030b0104560791344160024400c406030070341e1600394540901801c01c84 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 326038030 1250 326036780 326036783
    0xa020a030b0f1008060f091501090606090503030702030a031803060609052d0a0b0303092d1e040c03093203070f022419090614030f0c090319 62
    0x1000000180f0700c2d0604041c0c5004a07a4001c0c0103081550300c100031000b5409000d01040707480e01503800c0c481600050840314502070404001d000a80740d240c02009400050b07950300850080d041800320303902680d03010401c05249500f6040c88810840205205c0100d01e0403504021f00c0e0754500b1602254203c0c15a10044c0300345415004901c80c880170501c2241900309481032260148c1080001070813044060308000400310000c1e08803400c1000f0540040d54021441080400880c001d040d00e200b100d0b83d140080024039419503001841004000c10307600c3d00100e141065004640b00d102042820344280d00c41c0407586d4128600b03008211542c000c00601c8007a80170409130074410001d50580450010017107030035070766105502d030080b203c290b424007019262140a116070602c400c0c07c1414010f05050042400c0803070080702c1c50000d061410701503c00c0c0030f560060400c2182c0d40c24045e01c4044100304503500140d42c005841074903614050715001c248203401f030090b0580241d1040c1a00859602d0000300e520307 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 326039280 1250 326038030 326038051
    0x1107050709050105300304050d05010b040c140714070510080406050c03101403010f1d070602030a120906110d06030b06040507090512030d09080a03050a0c02100c020a020a030b 77
    0x303913070350010810400c1c803c040d040600105014120002203245031060184003542055a0138160344000040065544400507a050794403540d03000920701c0e00c0d101c4c500c80c11596080c8126013002c0c182c240d41c1d61f80210b034002010b100352340301030940c1001c041016000509004200c6c5030b0340c8243c1d4400501600040e102110684d0401010070b030411211800d4074820403c108201d003c0b1894060281e031007000411036981c065595803850a40c3c9a42c41c000c2c00305d00c1106c0d003503003134042d06540b100038500340c400e03400b00c0c4c119001480040442c552200613484010301a200105016606050030002000801503925a1035000a4100c002400c3c540141e02264040d40b00b04503e43d44040c180001d41c2d07404c694807000030300e80d0724041c4224030700945400e6811556100300d0741426410644881161240030081e54840800f0403551303210b41c0c3c58040c40754080140503040c13128244030000a03640d0b01c40115002811901c03685031001d898400c00054425607001422810a41d03a00e08021040d08000d46000a91 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 326040530 1250 326039280 326039291
    0x510140928091506081009020d0803010305030c071203050d1a03010606081501020304030f120903080d02040306050606090a030215070501020319061508060118030b04030e0906040e150a1107050709 86
    0x840c50038484c9004032044040506034940c0c4100d140300007016030103012030b403002c0c101c036480011880e90006140a10312a00007941d03202100c0407130501e01000f980c403032034144a00410304000640c0c4042a561000810800030a07042141040c0d81018929402c1c03994040d845c00c000055600e5104074440e0241c0c1e541c104002441050300012a2a4410790202520414000d02e600300000c0b000d22640505e4683d501d0012080e945030754804155600142c44070f00242d40100c1d050050215038441c2940040c001c0f10020320304811270000c10b482060a20000e4441c41c01080d1461407813440908964240e60300c680210354a00d0700f90702c0081140411940000700c00c0c945280801d1390b08a12014881c040500c0d2920001e591b1024011240d03440b0041e496100e032402d004d00000003a1401f02ca1134000c034401e072602d034000455101031001015006204034460342c00c081981d0706200d0081200d5620f49105080d60f4132558074000d5610141c40102d20b0711041d5100003628006002011070a00180c5000c41014080c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 326041780 1250 326040530 326040563
    0x15040209090a0803010e130f050a030215010503100b0f040606180501050705060c16060212240604030209040c050307031401110a1d040b0a18051014092809 68
    0x5560401c1c001c01807103801d0410061004240586e034003984070070840c090300c0c070035001c5a88820007458250421203823680040e09000c02c1603014080610072030420401d524541d803400300080c0d43c2c1d503261080d450a490b661004140140c407601c00142000724043c106001f42543c940e4001c140340b01c00340c481003054003050004a81584a40205c0d030801c1d41040091055440712040c241007a40000090143c6a001c202444002626030000c0d003040400c5241c0c02001d80340c80c14085150404803520f81c0c0c01543c0a00d0f10400b00e544a006460689406640c010900e40c0d4914000c0711501c81c44d04141d13494466044000100034105100209800a0303900030b02c07610000c405100c90714020860020049105248060760410f1100d01c030119109000b0401f10b09410440042071464a003a004540b00310a1068030084402440c05000d40102c250840c0002c01850103d00e904500340c4140304c03610403002600403030713200303044403003110150440c001d1444080200000004020421620115600e05100a00c041c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 326043030 1250 326041780 326041783
    0x110f040e150a0515120c0310060905060f060a03020702041509060302180f0711100507030501090605010915030506031203070f09080c03100f021e0a0201060b041d040201050702031504020909 83
    0x14007a0610800c200c013282e20070780c05c00c101d140011080daa00391084616903a00355504121601c2001500707500003e189044c0703840042a120020442405244007240850b03032a1a45400c856060800c1d00d0010784608003480024081c2071040c2c004d5500c22403850001c038007101d1962041c0f044900c00c441d8171520154001911414844c1241c14802c2c0c102180e000400311401901c400c0d02d0700b4018800c0d5a4400301016400c82281c8080d140307800003960350801400b41c80c0481c8100800340c40b09081204c112407500700001d207000f09041070b41081649800204900da1000c00200b8440055418999201e00d070041c0000c100d80004c00000c400100b02c55070002e001100499400070040000d000390800c40550041348003c3e100b18000a03c1c0e0a500b001200c48441c9007000c100b070001600600300303684800100c0c00900b582c4150b0000404580100320822400700c2c0c0d40032010410120310000720b1903503134030300058419005a100280d0580903030318803024a00c0248002c1441284200c5080b80075844404030366 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 326044280 1250 326043030 326043041
    0xd0206041806230d021809010c11010603080301090c030b120c01092319091404050105010611030d0b030a08042d060c020105070c0815010e0c0304020607110f040e150a 73
    0x605500f001d40140d03561900304505a48401070000e042000c8a01c2140400e8200150032035104000ba5952525580c0041e400300940440c6581d000081c4042d60031a100c6801520040c8110b03c0055036032445062041e0103a001464090350013408669008070a04480f500c0d0303240f02c41d6150010702444004904036070900f00100d400e40da1039031001c884418082c14003d4060b015160400d000000600000c0c1c10f40c0c3c14003e0405464000f040784025003014a415803c4d904d040c0c02940074003028600001400070b0010584000c0d040704403002c6085019080405d042c41d01d080e41c05005640001008a103a51030918042940c41e111686495164416038410003202000c5c0a20000103940c0c00b020030156100d10b000e000740318055040844a02d98a0100502e04508221000d00080e40c2e9001000407125417000d1907400080c2d901c1080c610720b80f0364002120f038030807114001c043ca0201807103e11907845450620402d10030140082080310f10103100180c0d00d20465034040c2460040400181e4081502c2c0211f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 326045530 1250 326044280 326044319
    0xb010e090a0f02040923011d01090302060403050325030501290d02090316090c120606020c2205090c0307060e09040f050f060a06030c0b0a020d0e0d0206041806 70
    0x140c502c11240c1d41d0030000905504d240903181d03120312581040c1946203c0c407803103d00e4400c000000071a400405444030304c0b8440882032503c1030740b601c511440400d40109403160700c603901d403030969500c0da5081c46071039616204045c40342c140200300403002d2200360903601a070305035410101d00003030000c1c1c1e021a41c140540d0151007510000000e2040c0b0015081e00d4018280c4a08020300740d6114078041001c00040100e552f0003500b805407110a60b41d01203810813007207108100c41c1801400701c0740c1001806961000c20350046401485400f0181c804030b60384090202448030b07101010300240c00d15404d030540d01e000107150b0a109001c0c2490000ea21401440500846074002d00190b00782d50302c6442d65440c45c0204802903460780200110585007000c00c0c84058032501e0310f040002103042c1181400d1400b01401d0300128503078101085a00340702c40e0001814106070044d0325103a0303401176144010460f04100709400130741000010401041c25400808145c040c0c103025032080020355038070407a2041e42c01d8000750 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 326046780 1250 326045530 326045543
    0x1401080d050901211418100e03091e040e03120105010503070327020301050a06061e0315171b06070f1704060909050f130825080307200d080603190b010e090a 69
    0x301f10f10074524035009400f04a1402e0305a9040011340c901084440424045420005020045d40c085502c1c2c24840c00820807040c000450800340301001404071400107006250500201000090186100350001c1000301c4283c040c08682c04a0002200380301460604103c1c0b1039400c08000030560301c01403040d041280c901d075031085c0c503000e0258072181c200700c41040840d00b01500c50780184094202c413204e11000740b84840d4421030540b6050003a504241c903030030450482116030414050140c1d520401d507404140c0040c440ea510802518181c1c1c1500d40784081041110000314001603d65004201c240c11164054030500003036440d481c44280382c0c1c00480c1d81e0101031510b28030020101d0828405401c03102080d07501049240c502001460050302c61a408441034a800010000020f1303011070045500d81036030f07007a030700140c03514540c0584403210710700004108008900040c0c3c1650b41008000a40c1d0100c0750584411840350502054040003401000501c440c0d900124032913960002d501001d0642012 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 326048030 1250 326046780 326046793
    0x204061202101e050309150705030709080601050a0303120e01110901020c0901050d0807031407120210060f0506070507090216210c0b06041d0c041401080d050901211418 74
    0x8044d01c450300003601c0945548100b658680170301100c0805c06005003010380b44c19481e803401031001040345903c0c0c0c222014a030410f00c010800d0381c461000a03010f8a40c1030a000d290031050300c0f0040c0c0100840c2420031405d40c02c00022038100e130f051100800702d404081e0b09a43c0004200418003c00c2c0f4420b21500d13400c61003030840b48002c16098070290042c0c0d4031070f1800b200f400800580314203042e0004502034910481e5000d00d10701540d010001d01e805070348410405d0202a15202000511b050640f04250080c80005140307410410140060400b801265004545542c28200e20f80d00c150b5141508544280800c5000d46d5843c8140307000402d018101d0740c9012090003150341d10355498401404807900143c4a05180c4001242ca604220701200988000c000241c02802004151950b91690b064004103000042c00104c81c04140c5400d1914507007003090751500902d0048684101d034aa48420200341c0129220070310038550008150390aa603a400d20342c50700d540d0fa155401842ca40002030003a4842ea = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 326049280 1250 326048030 326048087
    0x601140712080c19050d0e1906020a09030503070803150a0b030a0209010c15050444132301111509030d020f04080f010c020721020406120210 62
    0x3244401d40c05034025100320f060003403648084c0b40f10b42d182900440800c00200d1509820a400d00c25440c1c480760080062924049802e00e4610700d0120140c040e00803900002c581e04100d010715032400055920000b2296910030504000d4420380042d0384080c0c4a64a03500c1c040b00610300401c1d010f040d030790740d071001038a991255800a4001e5020b494150306002e802c0d420b0101081a51308810f0703101c0b001050210740e40c945441d0a20f20081411040c1104045054512100c407401d0141c4017903803c0001138100c84031611040c840494060a61540381c4440030480105041076a000c417440c15464440e60000c00f0f4908400549920b00c240d401000309500c40101a000078000342150b503006140001a603103000002c58950307099a21424848071078400018041082d40c000304244c0c8031140c441002003010702c1e04003100079181e00c0f0a21802000d41c41003e00d8810b4413001240010000e03a00800800c19150f90301c0300b5503840c01481809a115480340000031035868094001c181c40f149903a050f802805101 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 326050530 1250 326049280 326049287
    0x1b010501170120131703070b1b0a030e121b01060501051215010e041506021b03061605040807030f050c0f030d140c01020a031401080a030e010e060d0f02030601140712 73
    0x1a003000307403941d00411000945d8401c1d03101100c10900c5810080c65540350281402d05990038050680024020001c030300c02c0036424500140c0c0d00c0c2d10528500032600c40f4850798040c0c6010b46e1a1004403140c5400101e50b4882d80402c1820410821950024000165104012b644074018660301088424100d80028880701080707508005041d414142020b900314000e0100f011581072403480f00038491141c0081c0200e540400c1030f00040d1484540417040e4104442c0400d44420001d403486406006034031940c3e00c15406034054a02607c008406c8400c2c1a9903414103d00610032024251881c0c010f050118000b42800c0c0710549400c07001500810b07003110100d104882c4194019510520071505010142c0450820300003410000420398010a5180f0121800c105404d03041c3c2c41034685a002180080000303421884000e900d42003401c1a00013180c0200200d0864440c10001d01d003014074004540100780e40c658003a500856084e6614650b45200000051051052a80c041c0000c0c0042414a00f580d20 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 326051780 1250 326050530 326050537
    0x60a0b0111010c0e03100e0a030509011b06050a18030f0813020d050c0907050304050705041107060219110c01050301180b150a030c0c02011b03051b010501170120 71
    0x41071604244201c58481c900e0308403002030081200181d200541c10704c413494100203810f03e201802404001403901011060356411030401c0c0201400400700c0c00bc0e605130701451407400e0105028445c102040030320b18003080207007030840380070803168a000e40010402d440c0c7d130402c0d20120381c1034881881a2980510030344080d1001440d42c00d01d42d184060b4000140c8031b486208011910a00040c104070100f20208000100c0052001d010014140200000704500180c2c4100f185c00aa8000071015040c5154240b10300c2590f0001d41b08a0000031143d07003000d100b040428029405907290211600304610507074403414400f007901c0c00140184014411001602c50b03141c8890b0000c480000c1022780c02c1c0124003103408403c1039000038031012440300255034041c0127003089103505141a03045a4056030004c1d1111442c03007401e2008101800c0741c5010503000d00c0c1115080601c0604845852981c0500180a054240500b501109150b5002000ba260500854001031000c0001800c802c40c1e1000e615001e81 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 326053030 1250 326051780 326051801
    0xd0804080d0e0a20090c03040305160b0703050c03010b04030b09030712020f0c04111b151006020f03040e0105011d0a0b040501110d051b030705070e01170f060a 70
    0x20401001c100000307544600703042c149050002e400e501555090941503101e621039a403007218820103400889a58244d58540c0c0a11311207442c9490b82ca072424121518021138110b1a440d0f80980002070034081203076a030f0340c030940319039800340b10315a11203400092a00003882603030290042840207100294603458150352000707541c401c1f6406c1507026200c0f100c451030122803490150b0003035010b00185c03513028482524000c1c0f0a07201449081d0003502100e05d1845600f2a0104411020600301499481844030342a00e0b0340c00e101c1c2882c1030608910854640e41c01d84031f08001b6110303101e080003031080b011040c0d50407500c1420031510160b01c0d100055640c115070240c480003410403c41c0b10340041d0303501c2079864003a00f2001c101c140c035207081c00009000507422000345050360f03000d00303005a02d5a40c85130803614105502d03110051501500490f09145004108009040e8084da0002181c2031801800300e0f8100c4110f82060b1803100b07280144992140c8031900b00c030190303400040c005115048503030403521624 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 326054280 1250 326053030 326053043
    0x1314011103030601110a0f1b080607021e0c040f05010f051c1b1802040501030f02070215160f050c1513060c0309170a0c06030b0d0b0408070c030f0201020607080403020d0804 76
    0x4021955540b141f02d800f410301160f03a0800090b07203400741c50040c808034000d0b02200c0000e141034101240d020359a42d042078030174110794512000d01901362000b13203c5403c900d60040c00901c0150201c45142c80900400d02500342c046503081c00000d441d2515903440301481d800c0c238008000034525529150f00c221a11103c6c9140000e41002c0003440ca0310003040c14020120010005807524204000102a114103422050103a4014440f00000d41e80301690390001021543c4211703918800c49108144d2404c0e4580041c04045c20140d14109100e4049001c030042c101c1100c0800c0c440c619124000040d01808401050b41450a5800c1c86168003800b070007c141c5019040410465544800d142c10350140044200144c3c1c00103002030041107060526403000c0c200e141002c0c8160a2100007050050b41d81c004064681c04070074021505100c1d059046544054200b07440d4481b00b40c4a041808280c1608007080b030044c4640b90018141522900c02e0f03902951b03040d030284c104500c01c0142110780e0032000d44240c840 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 326055530 1250 326054280 326054293
    0x408031308070602120f01031a0703180813050409050a0303050a09080408010e0d050406050f0d0b090103030206150303070c0e04110901120c0b041518030206131401110303060111 78
    0x2140c00100900b02e140e124041c09a43c2c0e1040c64401121060302820400c1040010070051001402d55203c650589503c40050f0040d5900c0c11022405024040c400d40c5043c62400b52800c144801000104401c1c55100f800109607079440050104640e240c440280203504046080c0c00000e1090300400d4000089407400b044011098403003d17455445a07200c0400d5039920b5540c41c0780c2c0a01409801060562420514202460400041c00600c29000014034500c00000c1050078200340754000c1902030009000140d0a42e181d02c1c02a55840d0250f603000400c0c0c49040f030a482c6460004201c4403110f601c01c404490440c600b0b42c81030280b02018004881c10500f0303412300b030115203410085038000c3c9001d1a400440078500d0901c1d84150741d041e0030003d46031504220038060038a01641051200b42c807071401072800b00c5540000000d41030540c00007036100200003842800300d070703400d00360b04251100c414180000050100c010b4550030111703070312900150414030020b0a550702903215158044180400c0c1c405 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 326056780 1250 326055530 326055533
    0xc120c15090e0f0f150a1502120a050901021b0a0501031a03060903041701052a0c010608061e040b0402040203090a0b010801090b060d05150a02040902031006120c0804080313 76
    0x7011003080303451044071003c500400014a200a420640010555101000c032000c0c11010584103015401044c10890b05104c00a280394400c11540e0182030036258125101c085500009107940d015019003401440303080c0c541e4084500e0301003911107909004002e521200c5c0307003c0c0150040c1006505084100703d0210399048240c03001e12411b481742d100ea0000e1991541081d00c01c0521070041202c80003640c5c5070400f0400c040700d0b0380b510a402ca000101d0000c020320069003100a0b0383c40740e00010012542486400610780c080012a20f019081c44034081401140c401c1d080ca41e0100200c0303001c1c040e17008203400300300542030542c020350308060808140e40d41d40101d03803a940744086003030b48444181d07991102c0060030f202040f0724094000000300c8131003064005903100c43d540e40780f64201d6050f8030b1401402040920101d0340c11103004048510040d520381ca403082d40068603000c64418140414507411500010355028070400b4903150035a01e5901440d262629454256000181101d03841c10300c0c102e1050 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 326058030 1250 326056780 326056799
    0x15081e030d05250816090503060406050a020705030711090a050702100c11030f03180a050303041b230a06051306050904110708041e0608070f02010b090a06030c120c1509 74
    0x2008219942c49540540c100381c485c0190300c080103221030041100010080c406503802080c0103402607082400032589841ea000c54900a21481c0c400030141e100c00182d4034204264552500f5491504680f141c14964034100c0050654004445520042c0c0000c14498400420b82d40615200a418501000400760b81d11034580785038040d205031101c50b013012041000c04240100304010014498015080d092815900c8550b0303030102800082040e1846400190321144880080b0010906840141004040d0142d000c56440c24101b000780208111240401c0c1607003e501254214103d02c14014403462412500b1142900106403441d48140c07112050440c030301148000e800000e01580b0b1310380d03a032850080e011b485e10544610756407241d0000c0500b00300c095046504640d0140060600c4a51328401303510803401031002e5080581c3c040a52414446c2411580d8004400d0741e03c14000382c862a500d81c6031568105021000081107021600c6061000c2302e021955a5404030722818a141d1442c0c6600340d42 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 326059280 1250 326058030 326058091
    0xa030905011d0a060918110901080c220501020c0f030d140705060a0e1b0f04110d0606030b01200a0f1505070203070308010933030615081e030d05 64
    0x131400111003100602815082442030440c1c00d4003164100205014508504280c4c022411030754103000c141c40c001040280e00d403040300c00e104042100303450000c00101c3e8041d0203c00e03030700959006210306403801c00c05060600081d00741040c0280100740e001801c1074222108002004110340c8072130280031500005104001d00c600034040e0f0706001c00c0c0440040c3c903a9240c5070b9201032003c1c0c01aa03a01c410000350300c4444064600e840140c4020031200740119101c45240710380543c0c8444207103001300020341654540c0c4111140032090340c400a029007061a69036550142070780324a02d60b004a880c010001c0c41408040b151540b2514501072000318146814084540132640310015800001d005020154440d8601e03000d401848410004803090010001000d4041890004203079400700d00185407050040682c1c00640d40300d5018081e42000c10480c40c02800c29104500c130620036041c642154007010004440d02a0284004504258040d4500400342101a00d424010034281421055060324032200 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 326060530 1250 326059280 326059289
    0xf04080901110f0c030d0c030e06030406020708030403030c1d010e091509090c010f0801060e2107060909060b0306061210031202030c0c01111230010312020a030905011d0a 75
    0x10301a200c20500c180f46c10440e42d4002041005428a000000660401c009440b010801d842c015260750b598a0201c00903c1106d0004c0d101c040040104401c166160300020001211690303160064014000b100035840001210540400c51112802800c0d007880c4001d10707400740c0300c0c42d030039510210300c100890750a0b4403c4d6a41d41071a0000300f1058143d50b040951040c0345000c52030814031540c0f41450081100036030550b003a124190200e002c0b00214102c442c10440011503109a032040d90303854801816840d078510440105604000740010403040e808140d0744140d00203403800b40341a4030721054100c0c282c802000441d54420550300803000c42c1c81c5850f00148044960000d59645030164011407800f0140a40c1394104046010240e900da0800320310170b103070000234080081e20781440c4055628804500d501c003910800c015408404403504901903281220300a1824901c50107407690100c0c4c50702c005100c003038042031004904201c1541f092200c4000708000031409a0b2400800000600b4a05190701 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 326061780 1250 326060530 326060533
    0x9020409020613031208040201080c0310030b100504061502060631020a080a090c05040f1121010608010b04030b0601020c131d0c0307060e0a090908130e0f04080901110f 74
    0xa008100c000c42c0c0d0305c50083e500e0304211549240542c0002c1c050704008040d00c600743c401201007810220184d4070078026642c4a02c5480240c90030701090704c103505041c13051521490406200003090000c000400140d8805a4040c03d0300750b42d0b48041c861130704410401a400c0c010720421041003000d4910321050b0504810303101617501e1002c81e000070890400a004a0706140c1390104440000d6200c0c4500004c40c2c01c2654085180704125031103000a11000000760302400c40001c0d042c48100000758921411000002d645030700707907240d8000304c562103824000c0741e942880030001030000c10307940c1da182c1394040d00504c102d0308840100d10100c1e5002107201103c644691300c400703c07282c029170780190780481016000001c0000c01c6641001a548030300d18801c580500c00114009603980d161041d1000241019010912501c2468a02001c45900000003020389014205021880680f03418407a4010380384024659416125074803012103940c00000d0301810300c9840b2003200913003e000d00044840030344910 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 326063030 1250 326061780 326061817
    0x160603060e0c0a020c040b040b0a15020105100e01060e3c12060f060301061511010b060304020d151503080408010c170f10090219020c0102070612090204090206 70
    0x80c0c0300c10300490007600b03420540340280600464650b0000d0411020030080f0f401003030443c402804500200110005103401c5440c0100100b458071090f075074100c243c007080c0d00800036036446541e290040e840c94003803690900152401089003d02c60010304980010090039446011142070341100c869007442d85164440c80c00f00c0300e010420303a4508080546907810750343c070a000c8581d0340d9100d40b1640003d00b280d2880d144240490025102540b00f407025245154100903500f600140c00791040d20400d150304c105600b4031416004074248101940c0c041c55001d0b24040c080c000981e0381c406c01c03000c07150748110150b650301c248214211001c1088001103028030b07100b95940d81005031060940300040040000d1190007401c49000e0484c5c41926070384060640c0d401005078440d40041c071070900e405d40c0100001400440c5e041500742c100092038418640380d808840705005680c006a0712020144118000304246950038551440d0a4002c00721040c4000c100046401150b0300180544e00094482c106204404 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 326064280 1250 326063030 326063039
    0x6240903070f060f020d020c0310202b110a120b090109021b190b04030908031c050702070501020d0f0507020a060503010509011a090f0607050a030809120304110103050916060306 78
    0x1070100840042c007d1026144000c92a00440c0d40c513401143d45c43c40c10f640c1c03108110001606001400264484091040d644144894072200140303540c0c00850035061010b00c2d2524060840d10070380d1060700c0030340034132410000200c03802c0d9950b160003141510706540341c0007068041d60740e000343c0c20f0280000010042e10340100c0007004a40840d03120304607080d42c2c089420401d0f04580c050410071016404804030741c00d60b68034503084030a01034070343c4004000c0c803000c0751a100410101c480004490750780e000401581e900c4c00403c0f0303a2084544150390240c0c1003441e054104500c0341100700b203450000c0c00d10b680b90811690201d107041079030b64065400a031012005002a1400d8100140106201e4540d007110410600380e0794030031308c101101d06108007040795942c20241c0320101528142a005029580780221906020b030041c07030210383d442040d000d4040c00722412420700060b640540c1d000320b2050240b89200d0010740c001e1402810540040c826695040e040030343d9800400d014040340c0d58049001450b1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 326065530 1250 326064280 326064283
    0x30e040c051b0102040b1819180f050636040c03050706140f130902030f07081b18060721090b040302060702150408030f030f06240903070f060f02 64
    0x8101642d1a42d004001c00c010156a180549616690689500c0c0c81e100040002681c000011400c00812003152075000600c03080c0c1580317101c42200c0c03224043c07001111205180d0211441250025070004081003c3c00010510300fa0104803100400038080c0417000320780c0d11000b024011603084138250f1a030081481041130900c107080081403641040e10342840418080203003409507c0940c0840100030135402c841e0040f120381f00000345200f51046680c0e00780ba8458141782c0c0c070308440e100040707400d000100c0c01d420032104042800906020103103062807100b0a44445003080d000710594498030511000b07021031807aa04d092030fa20400040d005240200103000391030410f14743c1c043c2a0b0038609200c01c10150f101c8a044540d00f560407130b065500008141d15191490055420401e00c901c00404c483d13262903d203200031401205040c045036529900c207400c1022103030000c00304144c0c00340405c11103002500f03014050503050030001c041d184160b07103c03110451500400d0340048000b42d003242041000940 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 326066780 1250 326065530 326065567
    0x609050106051002030313030513080a030e0f010504120203010b2106071815020f0115030b0105040e07030f03120f052220011101020406050909010b0304030f0c030e040c05 75
    0x1000c1d143c444007100e0750b070400307500ea0100500b102022050a4440c02c2054460030448500c01d0252000d02d03000c545500d4280d6445000d0310040b40480d640d034501c01598900201e0400000354165100c2d483c0c00d051003800107080088000481c0c1641d01e8031a01100c9a40d2110070042900118902070402c0d084480854074201c4040c0401090100006030804415115082a026100046c40216002581c1d9404a181c10301603410480b1380d51801e100c103041030000c0c02c45030080301e0040c070180c0841e03601c8408000807503c040403a14425408007500f0070000726100c000d020f14a00a082c89080b10b01d00740500015540c403904001a095a100c08200c1054549460070340b148443d6480c9021801441c0d54083c0504009040503100001c190107802d4140c1c410784074500d403224840025500d0320354501019101d504042c87c0380b4070448200e800444c0c10b4031041e055900c40c1c2d40503940d90002000b03810056516803d0f04500358100704144200070459140c500442c5041c80700d560b102540c031406002d01c81c00c0220b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 326068030 1250 326066780 326066789
    0x901060905030d2006070f0e030309100f090e0f01060f08130303051506180a0b0f0702100306090c080103061104050102120306031c02060103110a0b0304061a06070609050106 76
    0x314a034814020781d1000509000080040c0c200800b21029504180c0068040c41c008030a09214074005c01000945c4002042c0c0c016401e52607010460103a00105601d0b0301a04040580084804d052100317003604c6040c0e154190481e5040804006440700c19456001000b01c0f40c2d458200f0900d0010071120303620011080b07d000a0785032070307405400c3c03030384440d494185160030103001c05031117a01089a245080b803088a07000002003003207070380b000707102d50003d500790000c140030340b00d900480d200040340d0440004650f2030035121a03c807850b10140d9400c201c1100c0001038400c0c2010b5a0b13100100f1102518840e070044120f0302e45903102607614600c0c0500a075100d036039811a400c1e605020420540e6000207000c118008141d0a041d142d40d01c05011034600b4924058501ca018040c19213600030a402103400c1c1e05990041c580c6c511b0b040c102e8000d04c980e10a0174420605242020400a000705045600040c072000514211300131040060300001e0fa1900300000a5032115610b206440410409108280050 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 326069280 1250 326068030 326068037
    0x2030a02060f040816021507060f06080a02130c0e040f09023a05150f2505030a050402010207030203030c0d0e041802130b0a1203030c090e0a0c14030a0b090106 70
    0x40c07a1641d904a11030040124040c5d038014981080d40840d512001c04404460041e0466512001c0c203040240113417100c09001c01d0700500e0400c003c5100310b40030840400d8550054800451040441600c03802030100303103014010460107030301103015580e6500a20207084502c90b0081403414440c010030202e140c0c48180313035418803101598681100c25006800c4aa030307041420400b20500c00c0c5c14040c2c288011609a540750003901010400300c0140e48000074024080c25a91005084048014540c01040f01721040040341d820b000041146140f80c0045a01034410301c140e0318500e99030340c0400d140da04410040c0d03a045d080240030f41041540b01d00b417007401d0481200c040c80305101c41e01800310240008680680101d10b91140d80c69100784075000744140c110003812010039148da50030b400c8444502c1c4c10080b00001d04000f807031242240b1030000c04043c0c40700c040e0307241a261605500c110092112608171420b11550009009810710b448000e5403150028040101d00000c03d54200055082e0581014051 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 326070530 1250 326069280 326069311
    0x408031812041805071209030e130501030b010b030906310309080c0a0506070b0c04030c03030905040b240904110316020d0c200a05090a090606381902030a0206 70
    0x1055807040030241003035507511b4000703030b02c080c0303810120384141200b001d807030f00f1201c05906056004800d038085030403a4054440e80d40c10340d80703480b0041d01508c0152420000380c2d00c84008900b1000180554400b4880d501d00c040c082c0c840d00ca400c40100e0745928074107602182d0b08550400107900280072007810b03647c0859035510628204000900d19000300240901020b14150018420110550403503001d03640001c200c0702d0055680c50010640b40c4e171402014001c500b03000070982c040c1084e800311000e01107030b005c00807614bd00060302c118280d0010070403507600c0b944070f242d820540655840254010140c40c03016140209600c5406480d01d8039100d12401013002c44040c29000c201c4501000b000d00e80c0c001d86081c08103031600005010816203802895100052078240142000300e94801e100b003a100d800240103007560b9501401c1400d90000004ca10200c5110402080c04c03095409501d86803540c0e0411030605492149065011101840c000c015900004008554603010890645d1041c00809150030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 326071780 1250 326070530 326070541
    0x706090e0117030f0c0105090706030b0603040609030e0a080715050a140a02011e0b15092119030c05010f1514010e1302180d0203060408031812041805 66
    0xc01005200da1192024020500c2d4541c07070050045504018401c0e908640320800b03040a00d00a000584420f2240d104806002550750b0207030082d02c0d60140000d04041c1141d5075601c8040152103000e10440410441c8600c1400f180d6411b80040040c1101e01e0090040c2c0e401c1800b400180411107082c602805010f00c103120304a80e000301b4001644030b6800c10780745c480d00c0e80c6006034090194002008414140a100001185403642c45081e900700c04440072402e60b2406030b03107441c070340c07003200d0155400c40c0b1402c1d802107408805048510344140321900722084c42c0c2c1d0400082000104102040300080c05c160810820301c2005d014180c0100d40b8540d00f0401c6004020415200a28a03c10b61011041075a40715580380e0003624810f03007504014200400424244420b80001c0d4020604500080362001c000c03100c030308102c182e9544042c0c1c080d000b80050b0f1100c0c0c0f11018250401002000c40c0045028001c1e034510091041048001650494903203407810907146881e00d04c8105140e090080c40d0004000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 326073030 1250 326071780 326071799
    0x6090e06010b03060f0d0f080403111f0206010506090d0c14090702010209090402100c050607030e0706030603020603130807060e100501150806040f0f060b0403061404030918021b0f070609 82
    0xf240640200c840c40f0f0ba80001d894507c14048044601400d07101d0081800400d0200052a0030070010041341e40003c900d1948165075415480501514016406600140514200b402c0103011403440141551031400082c1d40b004a403100c0f5402081e81051105901d29007418a4007910360800d003240025070070020a500451030a1400900107031203070444903075001e5083d0180c070039007642c80d40100c1078454a2411006c0500549408801080c0612803514000b80e203030b110f845964142daa0040820f460354641d01039150b022621904240d405050800800000560600c00c2a581c009540003500c800000c540d1400110f40050f80a900881010800403c0680d4000c1086604c100c00700c03400070718508d45804420007081c80c0718038241030074501540403e5540305030300a03008803442010140061030032081c010b1a0001e0943d07000b00410040318042c8640141e0386003040c2081c0fa00c0300c00604110059010b0880c2e0340442d6a1035056420070240700106203002d00c0041e004e4034441c02e203c544249401d0154 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 326074280 1250 326073030 326073049
    0x110301060e0f0c070201030906050f0f0109111210050607030207050a0b03010e07031d12070b0a0e0a03031113140406150c080903010e120a0815100c021306090e06010b0306 75
    0x508080c0004c2c12a08682c02070303000c0c0300a1078000804000d80e14004030410020101500e0f078200c0802d074100005030010740ca00030000880c84803215241408500f01c21261040000341164104d14030642c00840d0980301c0300054030003540079500402c17100d0700d40420300c03000009680016590300000c10042c00100f41c05001960001c409240001e0f441c0085030030040da010005040581c2401050300002045407003e0143c90b2090007201410002d49503003501d01c084601a002c0c501050f0016251440441c0c0039078098198903444109151400480844140c24060160081c030241000044070950701c0c02d00384109000b8017400b125085241d0704030040940000a01c1500505002e40011481d0080d2000c1d000840050300100407a0489416102544104c1d00200c000c4000585503400040c81e41251080000d4ed025002d0a00001c0c12440c60086072440201c1600380c0c0c10030014094141800030300c2c8140d40042001e120001040d03074074050000e0400d070069100a05000703091091005a5a07501841d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 326075530 1250 326074280 326074291
    0x50d0b0606160b07120b102106030602030c030405010b0d0c05040b03030f16051015090903030e0a0c060219080d0b0109030f0b04060b030609070605030601090b07110301060e0f 77
    0x20162103014001054541c55401c00b401007103c451901440360310303500030100985800013020b042c080300c01c5010034801c1c00c151080c41c100006d601c40400d112145c6e486030441a02640515002c240942c80f0f4840d981070340c1c802c0d81d01040070380c0000200320a115080c81904c85041086441383c00440e1680c0300c0b1102248036019584c441c550300c40c0702c040076640800489030002e131008403240e01c543c03a02e0003032181c04d00380200a803201c0c042c88050280f11300343c0344103020b001361200c3c402109003802e00469000811300c2ca0403c0b000e046e5a2000b05441600421401485501c03c0303107010205810010000c1c107000c03401e03882c03901c908258403880d000181d000e001c0d9289140d0000b40041c0094401d00100c0300a003496101910600514090200b0b220048200074401d501483c0c0602031a0401c83c145552420102c03104c0c901d680049900f070084034452002550080c00514010007010f031103842c030a08550252008851105180032840700380d00f020700944008200c920701031035462038040720040500000505 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 326076780 1250 326075530 326075539
    0x170106030209120703060917070c03030806011b1211030f031801060b0d09050105060604050f0f01031127030d051e1204050a0209011a070605060a170303070801050d0b06 74
    0x3481c00c2d0356150403035101801c240700b8084030040ba540c3c2c2003003001840700c0074040e82e500441080421003041148110740800d9404080105c841d032554804070380b6510060045410401041141c0c02d020503480d143d15841801010403d42a01c00740c0000380c01041025003031a2640c00038032078031043c24200010740e0761080d0012551030100b051550b24600410460304141c40d40c0b940412552480c5600e41d10001070301b40700d00003c02c002d8880e28104200d0303000764031845520035041c0002c040c4a041640044240305030604011580424102031080f45400280b15941c82081c4080e030700c00c0c2040c0105036809030107803c2d400b0300042d0810303400052031841413a1078920300102089192103d0011202102e19070b408a84030003c15003014038085407070701032401e02039110300c400c4000441d4060207004c0241242101002c0b8902d001d5250b0746010252a000384055480405c8050000e080341e03000c1000c040c4100c0d004081c50392031800c440058034408060308a94080c00e0300d45080380001d200d208010360480700846 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 326078030 1250 326076780 326076787
    0x204150e0108100614220b0409060803070c0527190f0c0f05030702031c0911040c1e090e090606030d1107061d0d062c030702060306210615011701060302 67
    0x103c1030101c01b2911061140c1e0f143c5045000605c00c5661000f810640d6a040014001940d031a0200c3e07550740590300018000c42c012040421052400c00300c000014100144550300300c000c0500000c00b1403100300c90944064a442c004407481029a100b04101c030f10180100300656003020380c0c01456140d60721810014410700002164215000300140c0701142c040c22310040207800f2070b5403054003030700703ca80d01125844141803550300a490140a416008000d655800080480c5884401074903400d06c0c2200b0140032001d1000f25010031440001032240f031000004180074244401450b2500b54100261010800d00c0c60601c0716203103001c1500d41c01c0301d020785081c211140004119455100780d00000d00d0740b0000a10502d01000030b00d406c040c801622010080c0c00b1000f080080049000310310b941c40031942c10410042e030051030f081d009507410a1018103044c2c4400c0c1c040c0395200500700b03107800158461344003404000c14040d00e4152407802100c08e1910580c000716003a00f00c00300104c1806114140364010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 326079136 1106 326078030 326078047
    0xc1a040e070203190e04020d020310030b091c0c031103160c060e0d06050a0b0a081b300f0d030e100c050706050601030204150e0108100614 61
    0x10340c4d402c504001c0011046800d0b40c800d0b000745070310541c02c0c021802d1007242440035501c03070307040010440ca009082d41043d1005c10b0340201021540c1e48103500300030014005904031039003111a820030044c885214a02a650540c2119240a451101203114000d680000c58101e20383d501510940d04460303203c282c1151250320103850b00d5082001c9026000018500e41d00043e03100601d2540080c000c40c01a0000e440781010381e10604c203640c4203641d4a8115080c10701c6100c0651400c481415000039241100304040b4280d15249500c980c0322081e09000b0001400070582922000040d98119018140042c0090031808540b00e07051244031400040ca51175445000510032039034441c07500b84829035540c6030282c2002420603041503020f0000162502d08069194402c2c5404d1700e43c2c031000b21001000412004009000300070366a0301990801c56180c00c007080404255194410a41d00c0100 = true := by decide +kernel

theorem cover : BRFrame.Cov 325899280 326079136 := by
  have h0 := BRFrame.cov_init 325899280
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325899280 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 325899280 ≤ n) (h2 : n < 326079136) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
