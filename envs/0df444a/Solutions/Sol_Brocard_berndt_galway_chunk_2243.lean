-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2243
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:07:02.625989+00:00
-- url     : https://prove2.me/submissions/bccc2ec0-a016-4b19-8051-4e376fde6f3e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 403237410 ≤ n < 403417266 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 403238660 1250 403237410 403237421
    0x70605090a170c130204080709020901020f01060302090c1b010203160f030506010e040504020f091503071e062106030b04061107021f0c0f11090709210c0315 69
    0x81d111a04401d60354454028040310981c1540c0582d088640011414075150404144c295400d840150030244c84024030307070901c100c3e503100c00e45555001a001d045960140001c1c0c681e42409402000003c0c510780110340320482c010104400000002009035490806016881003072048400854403072800080e0600108048680390f008103030300323001c1a40610310a00455208a00c1a9900071002c442901800b02034100500b0884c0d000440318030145140c1c43d88070b10203214201d18010103042ca00c083c400d241c2001001e030440c0884c4854110918000946880c01e0000c4908610f0030103480e130082c07a40421a4148042c00d071943e68102100001408015022980030300e0148404200a42c0c031000e1140c2540704040000790000d80d1201c0008441c40e20304883c441214241c10248090301c2599030300354070b006940c0c004890769032000c43c0c00c901a040c020160b83c0d00c444942400d0302c20a0400c441c148902c041c80300c0101c610648081058200100040510021030380006082c4400c010300e2001400741c003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 403239910 1250 403238660 403238677
    0x91505043b070f03021b16030b0a02040b03041104060503030c010e011b120c09180203150603041a0c070c2d23040213030f141501180905070605 63
    0x7040c0e400d140745000104503445000b40300c95200c44000395000785040c1d01079007003804000c40c401d50741c0d4020002e0b00f509100e02c20b1500348441e000c034582401c0d89800884034030b0281130302c1e5080b03205101c06d000c8440c980086035045904400d0b100030002d00c140000d805001c0d241c200a415010100d1815181c000540100e180901c401c402448007500c046210360400382256241000621140341c1070b6039081c0c05502131044084140b4040315500c0d1100c440801800341e10700400c81d12580002085101101d80006081c1d698040f01c1b0180703035080980381d94404c5000a82c01185030110540800c040002d070500b242c11450744070402002a40d501d16000c140d42a40500980b00d0060050403035022401c1428000d0030346100ea000b040105071284031a803a07484a0212964002ea4208189032240c03212080ca200118405c400c00c801c0340c0d155103032280320017458040a0001d9400f10031507410802c4401600c5055401c410004039803504100044c03400740080280203030050180c0000401e65940c00f000a00340c51 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 403241160 1250 403239910 403239989
    0xa02060c0d09150801030213110310090b0d022107031b05030c090408030a0f0e01020f0405011202030f01030605061c060e0c060319090f15020d060b0a09150504 70
    0x1540e49410100180051000740c100181e0044c005000500d0300c0e540c844020f201040000480c0855000313246c3c003642c0151081c01e84c12403564420440c681150103286141881541c085030b204126501081d00c0114120000000d0380c20450345122049040050500070b5400446100c3c6818094501c0d030312007042401840d029002c2d4040c2d0340850b040c50041c02e40074580c89041c140c51941c852180000904020f42c131030302d010f85c40e000701e0b8a09010900103040c0204000d1006591136252400161187c802d00c2c0007469282c0c014000c0001e070b28000101c0a0440c0d4100d20085072a54034a0009201f029210140c0300f5130100203501d01041c04a1640000c0c5404040d00171130f601d10310000200440c6000490b4807190040143c684078204442ca03800950b541c2e4840c179616044186650b40b20030044191102a846182d804a121504450031780180001015501941c5142c24013001c0002c22618090240074117500503840100340d000d11881c1110001c1c00d0a003212140c080c108506030b0b092400340e0b1501600c1c0c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 403242410 1250 403241160 403241177
    0xf030315210a02040b030f060f010905010e040f022b051e010e0601140a0503060106120c0c210504080316021002030c19030c171e0a0f110a02060c0d 65
    0x62404a500308411180c84010315030056030f90b0820024143d0320b00c026416000c0c080d6803004840081107114019004c1c0d00d04182c0541c1030950203400c66205030300c0000d0b803134040818840810328125095039456010b48020182c140d07503002c10400c02d180d20080c980700e0400f44904a081c0800494012140303c1c3c3e104000d450980800b92940c2030700e1480900c0806030300008010444851003000c2020103150140a68800d00e640c0c000007030034080264000c00125084045500c000e03c400e206400c01d58580d4149031422003502d860700742c850b1484210b4400900c00c5130024400300350040042d68000c1c0358000469070f07140201c3c08081078034031020740304900804c40202c9140b145400030054840d82c5074603000078410014541030501001c1d07424102070701840621440207000c84c0c040480c403084c00074244103403507540d0260004440301c0040303440300880b0304409201700c855040d03111440400d83e04d1507240c60070480c5401c04c140d50400858803402540000001400700000d80041121403074002141c032098070 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 403243660 1250 403242410 403242439
    0x7020306010b0f090405091e2503171602030d0f02060c0702091605090604030f050d0c05030a0c1a010f06120203010f030f1e05070f06031e0e0f030315 66
    0x10320f0300907080e500c0d40015090202242a0406500c010707400340260301110241c0300c010503604460000c012580744d81c1d070820100980a401c2210000c140c071840d150844034034604d9922141008543c851003c909008001484400000c002d8686544940c00805680210b0355041000d014020031500322000750003400c0014a21016080641e5081d94003c0c003542c500e640c45070203501407111030012040520800380b2002203640c0b00c49010f0310142d0321a801c0c4540200150501900d404030b1080340100f0000b8020908000034000704c255108105282084010364590381707484001d108180c00c02884c00701c0f0110000441c4030809210404845150301c2d0040440c2040940005900c024010300020000e4840200000740d05000d044030094005c910a400c26221425403084890030010161083e40c02048107020300511000084001d10850070300304002860380048810010703000c5c0130078504503500c5416942c80b03034007403080c1440c011071034060b41d94034a41200781c01d540e819007003201ca018940c40c81c10360300b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 403244910 1250 403243660 403243679
    0x3181b090b0a030206070303020f070f0f020103050109051332070905090a0f030f050d02030f01050102011a03120a1e1d0907021f110403050105040204200a0c031403010b0702030601 79
    0x40030f480d009400c040c544641500d003a0069131054142c100080310810500c3e01150303161590703d10461145050b010005024000101592810b0704054000c03450031043c001c00089100d0107032152903014802704c4152605908045a00c03401c229030340400108500b14400400d00810b01c00151081070b02c0c1007116407691a9101c5d44e64800c0c2000400c210b8510324034002180c0181c4280c80c0c1980b0502d0007511f4032684600e0103090360410b03281000c00710000c00050041d582c081c05a068480310012402c5010f0389100006951a40b9003e12040c0884000902641d0280706038603081641d000c840041102c0748500c070380148002c11141d5000d1901c0c0c0c450a407516186081c0c9100340c01131030310364020044244540440d80b0030700035850452041d0f560301c2e01144910501c40b80580002d6001d0400080c81d4a0140144010b89050f90588243c440d201e00101e2071072103024098801c02c144a1800644800381860300b941c440715000c109501030240880001a140a82c10003400702501c00d6007512080d0f640c2c1d42005 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 403246160 1250 403244910 403244929
    0x13090507060c0201270b07050a03090623071119030510150506031305100609140c040e0a0f1e0c1103031302060f0d0b100905090703181b090b 62
    0x24001900c11050444046081485c0c1854510109859100b02e40d161503800da07683c85118211080d42080a4074814907410208000040020741407000719615805803104584080c80985900480003042c0b220500c2140340c03000301c0c1c2d900050148000303a1000071108003141c2e03240c4030880d500d100c1c1d0302040f032148609016001d04200c0040e00d4051b45400c060402c00140c10081114104084460408011800c2044000071074002e4800002e080b0342801c04140a076a4103441d481c05204100c1d0a001556204104035021a90740c50307903810700751b142e510088016245007080c159245062040c800c04980b4220b21552035000202c034100f1186c2c014000a50b0501581200141250028000603000e24006545220340c0e51004180a00c1c003180c0305240c0d241a00300400c801d070940c1c4e842d002c007101030a201c900d0450440042c00c1c81d001c0b8170700e4600000e00310701c0010007100400d912215803d07000e803005815500c07041da005c04443c11a1503c800c9600d0f203814184aa503401c039043c072901c101d003402c0c1407500 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 403247410 1250 403246160 403246163
    0xb090c010f03111201061d010e0d060903090b0403060c08060306070e0f060c010516090e010e0415090501021813110d0c091505070203060601300b13090507060c 70
    0x144200035501c000140c004103410400a07080343c804000c0070b41c0b1100058502400780c02d0700e444211202d1804e04100d5085103101c1d51780ca05025810440000c04e96840048848603507000c0300220700303011686001c50381c1d681d5981c4203051854000c00c1c0402000307400d4100b040011651f50f5080c4482d0f0301c1c602016070382c241c01d4a2200100d02c42030300091b040d0404602d040021040901078a00d403034608803040d82143c408036090601e010b80240044100ca601020100042201c45102071040d4140904114560700180c8014201e8441c60700414025038650801c0301c0c0301e03801c40b000310f444060304901e61003981145500d4500c10b4000e00354540300604540b10703140c0312001842c0c03850700b07114400010b180101a400145000d0020060340010400b40c50903860741501155079469444003042d105142c604080600b08506000c8403060800c140c84a00040d03420280a00341c04542240150042100400c593398a550300066608000b10aa2540742c2201c4032451040b400c89040540c1e81c00d00b15040d2040250 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 403248660 1250 403247410 403247417
    0xe01050f090d140307030e12030703020d03090c050901120b010816140d0c0803041e05010509011d1005090307050301090b0609071e0306060f020c010912050c13090b090c01 75
    0x286945800d01c4000005110b03c01c00b260f0080303800300303440a031a541120004900088403101c0b0022181000403100c180c100c0c0420040d81004415036019441c1c000726641c0408050b0342c0c0701c0c00c00501c41e000d0802c030010940900144403a51b190380981c000d801c2d90300404c0c0e400d0a050300000400340343c0003920305110f20404016511513802c1c0b10305070200398034103e84164400c4c1c09882c0b6501040b803100028000b000c08400460352503262400462a41d42c182d80446d2500500c04420007013641c020044480c44102441d000011208050002012211450005400c0303100c40070700e444038542044c0100303800c06e41142212019a5100c00301402d0300c007210360042c501d03c41807001c1007440c2002445e20750000b5203420200c3e40301e0116521829203140d0400440300003900c0760010080b05401500d8240407040d28800380002004003000a482c03100300d40f00c0c0e00403001c200d00380a42070060034401001040c00081c06c0003d86810b00c0d4401000d040328410585203201010040b8240920000300d105d01500e044c5c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 403249910 1250 403248660 403248667
    0x60501031503050606130b09070504030b10050f010807120e0c03160308090d050304030b040510051609030311010b04020c100c2309010903020d1a15090a02031003050703080702010e01050f 82
    0x1c0c0a5031180d008440903081792642c085501d00d6640440141c841c9c0d103140d0f1016204c42c910704040c0d41c8140c1c0074104d4520f24001300070078001d9031180510680e035500c007030030314106544648074202c44003503d150307581e20410310b42401e80c1c8a102c0c0101d00804c5c1d0385002c800300c0701702420501003800c42c15043e10004040e02801c06c900c40c0700d420708984211907680141d0640c2c0c10f0565036180e60201e5001207e081310643c000c0f030005000580c0030b100703880d04800a1014030340000ca01c0d40c1c000e0140c03040e9020203810b108840100c0c0302849025041500200740c040c0043d034540d00c807280394540d00d8031074003040706e001c6080c8452441500d1040c46445480500b034040d8203a00341c9030030004480c55029500c400d0410004240c040056260b590551a055104440540ea05005043d80034070511001d4442a108560a49031401c10383e240e94001d904501510302c0140c0c1d0751560801c00d14010210703440140f5030b019000c0d0010034000800c1c054410b1a000383c98440300c00071010300440c0d4501c40d01d6000e00c124801130 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 403251160 1250 403249910 403249921
    0x20405131403040b04170c36070206040213180807060c0302030601021b180f06090f06031509010e160801050109060308040b07020f15361c02040903030605010315030506 74
    0x840d90341124248410075200c45e1504a0702117803076040345023000401c1600300c1c00c03042c0d1450603651641e40030354449042000c1e0340c00c06100003500c400000c0c01c06440f40b0f090501c412a030301241c0c0c3c03240140c6078501002c0ca00b80d819929001c0341c1900700c64420350703805241083d9641454024000c4a1086905034040d14044d50001051440c0b800411038154001122203104030342070260481c07540c000d88103040c54070514580f14040181c1d0000c0204801000c0c1440300611501d40c40006201c0c01904480d00880440da648404c1c0c0c50040ca454113107280c0e94800d003040d082032004400c06840c10344802c00000e102d00c2e03880d01080001e848035440000e0050364100810010072801d0005004041d00c000c0a00b00980244000144414507003003202d80e06003400035501c054404e1103003100f8000c141103845008642d0003040c880c0405885044210302948868003400c038100c2e22450b45004055000380100140c14403410000e0042c81d8500400e4086450403480142624000c00741d9000c8950200090019030f550 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 403252410 1250 403251160 403251179
    0x24060907081308070501020409050108100e0613080c0a030e120a0206070f050309031006050f030a020603040210091a0a09060804150c020304031502030f010b070503120402010c020405131403040b04 86
    0x40030010f48082c2000e10074a00001c40130f0000f00002d1a4941000c9030b1075040548590502d1032002003030391154545805916280070200d03803540d02049101d1004081c0c801030801e030b00f482c4550380030a40e4501500402a003050713004013031a0700840701540e5803030125a90b691066503c0c031080d40c01a40c84036042c010140001c0001988881580c800c1040d2802d004414000c80c0c40c1c41041209002c1c0162180c04c2801a41030602d80981034040490061070100030540208030746210203880030307002d01781d06140259030502842031800104145012100040c820702c40c8925a40c0200c010b0310005401c1c200c5c0080c2281c4189040d50049801c114000c448502c002940b1004108080107601980024880000440c0c40102c40d603041400c0c1510243e92458451383c3e074240500c0580040010b407009200c11800700b000041a40c40030040d4240a100d25140c42c00161800041c1e00300007580a400c0c0b40c108034500c00401003c4541d00c2c4070703c0c2088800c225100038180c40380558054241420014401006607280 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 403253660 1250 403252410 403252441
    0x6040c15140f07140705010f030c0c0f050c0a181a03060a050a110d02031008010e030a0806150c0a0209010b0c1b0a09020403080417070f12020f032406090708 69
    0x142c0109460819550303144001e02948a00c0825550442c100c10400d130750b0841b044a42c020918079080228040c030034406443c41201c007001030545021701c861070041003001c00100e628007400819103c42540e9032800c18520790420340b03c801c4a5410310b610b5200c0d050a034072902009010060140c001e95450140c5c50000b404000d100b002e8440d120400c5480080308030004045111414030056520f01d800d00c0f24100e4580598030403403150303140c10b00815880c40040280c80584030940b9107440b26441d034100181c49003104540f400c031043c42c001070804140000140318500c03107109885400c40c0d0b03070380c850020500380200c0b006802c01d9080181c04103800021a0400c01440e08011300b2098495101c140320b8040341c0040d04101c0d002e0800003814001982ca00e05554144403640f0300808030750f402c0000c6601c0300281d611400d04890841a41c007411590b900c44400704024015041b1360700e8002407030604e078005110842c005071043c40342001c00c1d404e050942c00c080c8603908540301e403100c51301c510644814911 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 403254910 1250 403253660 403253677
    0x90c04180b190c0c03090e09030307111c03090201030b0306040c05060d020f03070903440918010f1205060408030603030d09061508010911060a050c0a0506040c1514 72
    0x340b291041c1462031080d912411120b64804080404919018000b00703540d0b040301c0021a01c0008102505100104480d030001d490310780211840c40202c2d0b0f01e440c001c041d4407403034050745202d80343c015555415030000d07000c1c5000741e0781130140e40c22250a05480301400d960280410f15164024030585c20820010240400708a40051501d40721440f20784050f0416a0300d140024200c110405c1407013003111001c415000d400120f8400001da41c518503400001c2080e8031401091140b0024042801c0d0b20241e07861018064135030612842881410440103c0901415600500c4900e01181030001644000310040c0d200004216070344858850343c40d00e0304000c00480d4544410040007000d1041c03030149002c01c1d48114000b20746039036240410b118025860300702d0700d0160b16102c0d503400450008404002606002d4458656482d644a0308a5031880340b442c0b0b0030000e10540c0e0a020401800141c1b1910075070046010040d40c948400c01280e034207820001c0d1800107001c11011000c07901483c001000b044 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 403256160 1250 403254910 403254931
    0x190e0a110a0e0a050405060c03090c2709060a0f020c03040b030a0b150901030f091e020f0607051e0c06030703020901090e0f09010506060a09030f0203030708030c03090c04180b 77
    0xa0360780c6942d400351410859440d036019441d08140b0007007120401404d50482410a2140e0030b620f07000b081a5502c0c0041f2050710b01c1070000c144850310000d144210155200340103421000700d440e00e21358aa42c1c620060701c0d043c06561034400c88031b000071941c0c401c2e147e070854010081d40c982468225800300b903410150640d8005559030b0103299280d500e0039018141d203064000c0d515128404071001608490400744c2040c602030404e03605100080c0b138042880071418050ba040300001c030181c004201c1d052035001038540c120b44002036010900100045407584020a200d010010b445140c098580b504901106e880d04072006201052100c1d010381c0207440010410300d02200110703991480000c07144001d0f00c102040c41600c80a00000e80401e001d000d82c068002c0d070b151803400c4d034102c0c0300800b18020391002038900d011242070f00f0b00b103560510444481a801168444d12424040120f0140e40c1c0266900c40749441084601c0c0c0042c05c0a000d034034049404450049600300c41500c41014501c8003c0103103051 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 403257410 1250 403256160 403256179
    0x10090302120f0d11010b0306071403131704031103030405220f0c03090203160506040626040b0907080601260a06140114040204050a0303030207020d05060f190e0a11 72
    0x48010884562018110f59a40c0e24540744c01c043c45084030f50f00c01055020b41c00110800084540061a101940300d800301c5035552580d41e40759540254000750750003024040c040c012008507602d404c0140c030a4a006e2088218840c2c6542d00b01582c83c4103502c50250001d160881c00341940c4010741c0c41107000900d6280c0803403030032240000030048456401c664400310b940c4001180650074104000b10143e0650800413010904010019640e4040ca1151b01c00700305d032440d4403510540881090041d451021000e110701c1e414a40303424003119008031003c90041c4951030001584010002e1180c0c120740412243c91401c507284004608443d15100d64920340c0c0c40f42842032400148544504c01e000014500000265410000c01d040c02100d000b112038802e90050206204940d100a200c0084a40c541001030781d43c816403011a01103ea038003000761407070140004002c1d030109040b498520852440320b40d44100c003404103000e0200d8205000070803c65010190f01c0c00015805240c581a50701c009104052 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 403258660 1250 403257410 403257433
    0x1020903280519030806031b040f02250203060919030f0e0916020c0114190e180106030c03091a09010f0e03070c12150203061c0b0609061009030212 65
    0x15000800043d03103002c4840c102004241940800100e41100045015061400c0800002c20394414046a024407403139035805a02c4d0314200707071340c1210f01d02d00300d07050f6002c1d0180d84810100342085410200781e00a002d8140014003144003c211100500d40301c0000c07038200c0849440c03c642c0b03401030040c00c90a1000744104180c0950310860aa80704882c0442c09086014030b0200080c10702d100b12100d00d06102c1c4a9060b29074045030314050320032119840d03010000c240324194003220280074036a0a960000e000c00c41c090781c44402400442d050b02d0441d00c0c1400008001c0340200d0890303208441c09860b032001c00d8802e43e40341180041490b00800c50b44004600c401d9545400300482d80d045e1040d513030751b501c00a10034081005c50300341440107041d6500904203000103525800f9500c04014400b2820f80d60000001d031082d07941c514102011000c00f540d000c4007200d1807900124000050392458480c4030780900013000c902d2319035400044590306a9a412410b840c6500748601c2c5035039039000300164020004c0380c65 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 403259910 1250 403258660 403258663
    0x3120f020f0711120309152d0a03060f03020a141908070302030705060705070605030405010603050105040803040b060f01120213230901090203010e072d05040f08010209032805 77
    0x684280501d020014443c42e000070800074214002d04d49156030400e10503104541d5417003007002c10b005001c100c0326aaa8900c0610507111894110200c20078441c19010052264007090240824203030b0764904000c0303141c840040d00f00d800001d00c0000d41c0201503043c02c2c000d88900b03000101c41c040e80501581489142140030b030700391940c250000d240561002c0010025850304200c0d030b10007840305403402464400540c40b83ea81b60520f034082c207807d00070004007060400000b540030b54001e44c2c204008005030b080c946010f1040c0d03841a182511340b0951400440c0351498070000c48880224140c44480b2058010701c4c030000030b5000340b40ca1700000c4244520008030701c40f00019084030155048100182d0000220800091030411707001035042d1407040c0014400041405e04031500700040c0d0030718441d44002006601da50520500321200700240790108455242e410a0161080e5a100a00e46601a8507084a40d00701c0c010300742c072298581d0004080b956600e08000159196411aa8103d500540d060301c95a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 403261160 1250 403259910 403259917
    0x507020a09020c010f2c0f03180f060a09094a03030103050c060702040f14010f080a0b01030b131a070e0103050403020d110c0406030602070501050c0703120f020f 71
    0x1440d00a40000e45030f0004542845007a00205810400f080880900c14084040c0f81c01203c01010b500850b14900c90305090400c8070109040081045035a14581e01c001c40e07200d505507c0819005200301d002020480c68100282d507a48211903417a6142540307070400316809410b1700a1041c0c4500350412030b800f5801c010b00903102da40c804403110711a09008403000085010341e0300c1e40114164200f40014000118013040d00c100d825801c8922548590460000400034242c403401d4a410a14001030101c05400e0101c02d54120740366844401a01b41d0781e0380036503494050040c002003034111040010b10002d002c0807641c07070700034074508079803d000c00040d540e508900100c00048803051030032404001100c2da003d05055500d034020f1a0078040b90402d503401035503c180c400041003d10203945910955600304004d802150500100148102580ea0502c48000e522070712055030603508100010390400c45070401c8070500340c0e01d982e0304011081058441d0340280b644464001c03000d0b800708020720048190f040907 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 403262410 1250 403261160 403261169
    0x110405060c01050405070e0105031507020c091f090614010c080906030112060e011104060807030905070f031a0c0405120a0b1504050709050f040228050301081e0a0f02010507020a 78
    0x160f103081034140540340c22030703541c0b00304041d059040040c45103803008101d20020342c115005400c2d00d512240c0060b81000d8412555941082d104002c000c107440b20b4610080d8641181400d082140381c0b02d50002c000c0d0792150043d6001e001204070940051b51082d010001282e004e85009400c5c00c0f50407000a1145d4400e81c8a02c0fa081d0494441105112051240083d500080700c001c121045048203020a0750049200d00024403241d40d00085659003c1e4100b640c07900d0f070000551302202e440b816180c020b40c6581c0010b070340400380080460515001844030034080d641e2905940c5c109854a41044003103050024104000d0182e0161480000e807810310b528000e03500c08110990040340c92080c402144c0c1d00400010402c074480808000e29103440c400c0400c8944291400340c0c0e200c80c607010321850560ba84003400101260046c0f110441c030381c131202540c162900b003000d0b21128100c1805080d80380c00c04108139100307608036415803800150406401c0d000c55206040040c20a00103070002240b9a149911 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 403263660 1250 403262410 403262413
    0x602010203061f0e010c03030209031e0f01062102030a06060603020913051302090604061701241a0d060923010b041206050702011107060c090510050706110405060c 72
    0x1842502d141040c203003800c8195160f9941d02141820f200180440e0003984900d0510654507080400e0500c01c0d0100c401185010301110310340b1820107055041180c40e08a581003500807114100f0380c0358130602038202151400058a040106a41c08426401c00002e1089915100e200803210010704503026800041449440c0103032110302c0d04040c04400700d100414020854a8441008040100400e40501c03031901070340c020307850390f8071030700464005e201541040b0480f03000c2e55485510070a05400050b80581d07030300c40e2003690440844c652440b0006501603400c0440d0400020840141e03070002800f09481d2005000c8bc42c1591618145c003111070300e81c412000d403c9540c408481c40200c402070180141309181c2c0c2c0742e2510789005068000d03d041e660b4000c244a417581c01003184603100b5003041038061440510280e0315003061900310018122007140740d02041c9422400a594640a00c48401c1d4541d03e031603541c42c0c5150356454000034644c400c954080e03808180404034103900e03003001a0124585210 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 403264910 1250 403263660 403263667
    0xc1507080a03140a06211a07020102360f01050f07020301090212030d050702061b13051503010305010b06030601050a0309051608010c120b0f010f03060b07080306100e0609010c02011806020102 84
    0x1c1d0907002c108080a183c0031b9140c03d58920300001c15086640c0040240c03200c16688584401c40e08901920039807400800603105883d01d4903096001003040c12914016007500c03112030840d03905220381d665017260b45034049031052240c1d0028182240040c040b00307100600000c0c4400060740041c0c65035200c410000030607803000c900462020924031070741d90081510300041440d441c00010641140350400205020040046920440390f001c0598240c0a818001c0c082d1400c1c0546030310700b40717a9801c00d00c0150742e070b903080c840c13030306020f08103001102e000d108180e40786403404189404c1a006003a480c4000c0300c40d03104100706944003c00301c00740580508820030011940340190078008101c8110300160f00f18007032178621100010798480040016039075084c2049010f050f0380c4801600201401d03400300340303070280000300d6000300a0304100852003890101c42901c0380f1410110202e035400240a40250800c1007001902c1256008a68100c1c045105140501d00c1d1031410000c40300141c0c05500250160b90080b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 403266160 1250 403264910 403264919
    0x3030c070822170a0203060c0a021f02190507030219050a050109061a030c1011031303111008100b030c090d0c33050f0408010c0e030c1507080a03140a06 67
    0x604640c0107003c0030600a0182072156000203803508005020480003840c00201040081c2c028040c0c4401003070b01c00c2e04074207240700300c01c50180a036006086c00259244880070b00302c8101c0c0038005641180c0d401d503004208038100c4407030800c102c0c800701d0b805131403d120300014440001d20074000d4062041c8541030105800c0d28402032070240140f2108164429000001154041d4031054001c2c01c50071040c5c03904422482d50146143d0a510401a0218105545031804002d10241044001c0c0d002020745001041312050401150056070640d41c5445031901c0010400403003102c0c05c0039507001300c4540d07840b80c5801145400030745c1c1900d400c1c400b21001004040200700451304a503d02d028401050054440b01062200055200d62410014404d100c0c001c6040c07007030036150b0001d542c0030f03010610003002644401a006801880700071b2a8922034420440103148604000e141c0c40942000310044a05060059807081110340010704d0b01410155200c0e01000c1906407680000e0050150160009119041 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 403267410 1250 403266160 403266179
    0x906120e0109051b040e0309091003050601030803040c0605120402150409150f0902091005070507120f0b0916030204050a0902060f0a0f0201050c0301060c03020708071d061203030c070822 82
    0x311391265115515020504100040c08001c480740641c04548030603880d030311404a042c280e03206410203460707072080d2400031081010003c0103600503401060580e00e0a96a10303021142407003045800c2c1d00012101c80400d0040c1040d5641210f40718400040e18106905c41754181d045600740681302400c0c2c0c1803404104280303442401e50700041e001142c000d51400b04213a02241e5420566102101001000280308013445001d120b80c9000d420420032003102444c041c01d0029281e41d0b02882a5140c030450404110803c4d00068154803c811401c1800e20803495502000b0060100900016505840b1010070780180d564400070309540c0e035280d0780e03603440f06800c000c010704003825500c014041d0ba2402c0e0a0228200514050b64116401860071213a2383e252480c04901b031428940c4045000e02c6080b038046a02c0644041440342448040009000c995600c0c2c204821245403184602c0642c00420220740c11562a000400410b406490094034110401030714a224145c42c0211942c3c4243c603800510035800c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 403268660 1250 403267410 403267453
    0x1511040609120c290d0c0e0108060901050120010504030c0302070e040803040b040807060f02180319061104120b2202090106030f0f05040b04030f0f0906120e010905 72
    0x808500e445803080940d8509115000a02410a80480c0c100b03858605544040441284d9a010348946456501120f03a001c06044c0d508040341c08074183e2968441e10394401d18000d8424100100324411603442d0600660f0302102183d1525040744c1c0018040c0c400000c24003540d80124070990320a0414080d1f0f040007814403005410101c44820308005000109825505594015800c0070403084291191f00c0d20500380e10030b200004020a040c051543c0d0100f034194050012100c3d1400b1300481b0070b1000342010380390b806001c1d0a9501041903403642001c600c40d40d10824051030302000b8145030a07100c80e114604522003400c02c6581c4291a010480705006150028019030170310414a1078840250b0300080400005000b240101542c46903808245000c5030050310050f0b2480a003000701e0b0415003070060303000d00220303410381c0890399000d0001c08880c4103400c022076881140d901c00d100b1500f07085003110f5400c07042070005c0c0003580302e1481030712480c0d00388107548040380708a0040c454946040c901110414 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 403269910 1250 403268660 403268669
    0x301080105010e011212050d090f2d14011d1b040207050307122001020c070608130f11040609020a140c030d0f060e070c05060c0702011403041511040609 67
    0x50f090780100b2240c50b0450800085540c01b410303451000b0b0409104580c3da000e4511400c2c440c1d410001c1201c2800221101512620701502c0712100c4d80801d00b0f90640d80e5101c0c20f511800c40201400d8010218501065803400c4200450010a0140f59408404083c8420400007202900050440420441e60107000c80c1070440540342541804c0d1240c8a5071346070300034094050902140315030501c506a00c02e0b807608241c041c11350401e41075040c0c1c601c0107900071341001410030301612503200007081990241d812107114203d4044c80c3c8a00b00070790b03601c00b101c10481200482c0c581c0030002200e40701e03070b842e40501800f80c81d4050005850785e0381007000070180074681e1a4091454410001100030000200c00c0b01c511321040c3c2800308025003201c40b0700000f000c1d182e00548418503104184441039234480e10031900c0f540220115003054480a0400e0080e1040f454009c1c0450070218140b41c0581401e00a141d00c03502440d258008a02c0c20304061058030103590503400c1d04080000c042c00f5150308602d240b000f91 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 403271160 1250 403269910 403269929
    0x50d0608010b010e22020a020d020610030c17031c0e0610050a0911070503040e1f0503030301150e0a060201051b1222051501060e03012a0c0215030108010501 69
    0x150050001e04015113400c84d0b02d0140d0b03400031240319003124035580c614403038856480071581d80c132400744001c1d118400e25003444014096503001c602e084a13049003079800e4a400410650010b440d210060040224000c44503105000600294480e1440c5c0040010440e4410001040c06851a03003103504110000b0800c04461340900c0003031000e80c58084101c0c050700c0700518001100c1c40c000384a42c025003e06c0c20024001d1000283c0400da001c0544000340c002e020700e460401e03906000007100d0303007000c001d405400e030190710500041048103001421582d4903078450410509200403000407580380007181e0071100241c0c0d1203070103000103403070b1078488401d1a0707000c02030f06030400c00f80004448103804040c0070902032221400700e020b08061100990380d005130b480390440e2109601d000d15106884024890500890001421003c0d20308044c003035180f004c031074021a00380e041c190400808002075500704680800c03d806014400507125404c0c01007404001c209403e813290303d0b06500740c0c05d4400580090030b21 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 403272410 1250 403271160 403271171
    0x12300a050a0216031101060f03150b42160203060108030711040e0f071806051e01030903050c01090f120f0212070203031c020a1e05041a0403060c050d060801 69
    0x140b94054003c071840740e0345440d0568202d415040600d01401c00b1342c02142e0960100c0700000108020407489043c1030240850600610b103258040100d13070b00e2016000145042050252907424144009200c000d0401c021400c1a104806031042c0440e009a903044010b000c0c0c0c1194078003540350400c03e241c014403500004500d8030080782c0e03402291300d003a452158003964a90702d2803034104405006a03040d401c100e208a0300529a42d4000d03040c03506503520f021060500e021300104d050304001404082c5c1c2000080800c081213a031400450041110700415410048280405220401d083c02009a014001c000c0180700d10154108001c00c820407000320700c14011042000c860464001c555441d83d06201c0c1801c60300d07130842e400481e00318441d10b881500d250542036000c070031b00319459001d006444020f5440140600c15401c1d2102c0d42c0d040b6508800104070144401c2040f03016404a52112002204140b414070b03a07030f66502000c3c0c440780c1c03c00320040346021903010060815031040f48020214407000744035 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 403273660 1250 403272410 403272427
    0x1c02070219050105040902030a0b06030709060f0e01051219020d14010f0e0105130e07170c10021009020f0d030302040e0f04080a050309030705060c040603150812300a050a02 76
    0x152291b449502c0c0b825401000143c01c10030107034419003000c54043c00c060303940d140c040001403100606010f144042081e1081c0f220a181c454001e031a014a8181c44080c039108100240d2000700d00014613410038003078400300c10503e40d49030340090000c0c650842c00103d0110342e8911919007254058011000d01e5031812001c00c03014410416890444a0a86030111418003684008016210010314140d80384104040040c0501d14151904440c030409019100d40c031701080b0400071542992903181e40168409000892001d10320340c4104e00313540c80101400c2a001308500404c5070901c030254103502180e40803904104601c00700001c1c55001451a028540925095031401e00c1740c09000340503810171401000282076600100121003649401008413040f0b440d1240d683d440b40d82c014025900000d00344001c05181c041c0420174403054680d41c0e00540380112440d84860000c1c1c0000c21240c00509490285040c9246100081e944010f1300e020003089a161101590701034844c09012034100e148100150203 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 403274910 1250 403273660 403273667
    0xf0c1a160809030316080406030606050c06040605061809031306090b03011a210a0c03140609040204090c080609011526120c0606090f040f171c020702190501 69
    0x203000c0d03a0711045482d00c1d00c0c0d82d180400c2c910701070102c54030300c4140c0b80500541442410000fa00440c0e01c036550500860f919a14100c9950244c06000c0d209507010b840803600086c01600090351014001c0c00429a0030025120030035081d20640f105078403500001880b8048100002d54040503010500b0910740705c618202c405200ea00c0144038000c100c0f4410b00d088518290644102c41c46030b18010720245500d0700c5ca25202d600e035081950341000991512032101d420380c0c080d01030000000c0751b4800c0d80101d5900e81d0184650100000c00032640180c0e07503100a00040c5000491602034000d40008226529004124034210356071402074030400700d4000810410010494180c15598007460010401e45031118011450540314520381280300201150841c454400021624820039084804015985544d1624140e20b42c0a4602034000c55280c0b480c2d20102e0f0203e0f42d80c400e030815a00005140510300795003000e02a013080b911302d90751500001c82d4019403500c18460000708480c1847c1e0703200e40d40b030100041c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 403276160 1250 403274910 403274947
    0x9240902030c03070503060c03130c060e041a0609011409030a0308090708030f040603020a140301060e0a120b0c03090a0605190510061b020607020a0b1b03030408030c090d0f0c1a 78
    0x1582e016230000001203c1008480105102d01e61001e5000c824986402000e003100d1568918580240c0c50031000a49504161b040c1c01c0340501d019180c0e500c1c186c50b071001191600250021210030704000c1200446a890030080440e203d4003d60b02d0b0400303818121403417401e01c400b581c02f100496200307100304003c0719070b42000c9030100c410381d040c0142d454041140581c0c10440301c10340340d0500ea0001c000010b11030340080c8c0e05204450300729020310000b80c4400010341d2100462002038a80355903180040d0403a10270f20700858005001404640030703400035544980944400701d4010504030384052034000c0041c1c040c0205900840f4001000c8009400c0440041140c9080da620b4107484040e07039000070035515044112000c2c0c50b0080c105016807501c80d10400601e5110002611402156820a203c144d9010003520300582e030240b500340c03941d15640c40030700b0947c2180038815403061a2400d004005a00700040e03481151003285403466040c034203909840c581e11404d0b2040c0d0800c074104000e0140c04e264a008 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 403277410 1250 403276160 403276171
    0x81f150905060d06050103030f02120f0d050415050103030c12300e0609030910050720120102210114010207090905010605030d03060509220609240902030c0307050306 73
    0x20a542e0b42000210521042040034242610f00400401490380c4282d0034041d80d00943c08803070000c2c2050780a40403d200d1421400e0103481e060110000445c115046241c10501403098001101e0305403001004035002a80210082070050b11603104000b40c0000000200f01f0034245500300c01041daa840c4201081d4645292280c140c00311820340c3e5012961040101c220150100c40381c9180609050380c4e40d502c80000c4600c40c54465146154140c42401120f020380e600a009808410a50b060014a460200001580984c202c419403041c41d500344068030f42d00c0346620b94802e482c00004010150030006810a02c61019810030b00010307a40c0010302d500480e41d510304001400d209500b801d5005000a421942c0d25026440c15032043d03590581000058a0b801c4810211540b5042000601e0304040c183c0315618040b4035400c140818680da001c04441405a94901d5211403403140c02c03500d161480c00c174080301344d50314282c031000d40c1800c0002030001c20003540200095400d04000950b40d0030f00600 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 403278660 1250 403277410 403277429
    0x506040b060613030f0b1f0e0919060f110405150c010f150e070e101805150c07050a0e04020907090b0f12070905060405011d0604081f15 60
    0x440c00e60307142d2034110740d10f1129001191105607180e20b002003426080703200a030380c0301c1c928502050f0001140c0c225101011104105901e0092402d589921401d40082c0b1041c100d01460300510005440300d048506031074450040000d01c0c42c10582c9084c01c9840c03009030140508401d21042c0865101c11561002961084c0019074490002d0342c3c0c0b07980503011840d403004100e030602c442c1c00447d8243d080c0039000e4466480101c0d48664400c10304a41001c0c540e1805030f0b00484c46900d44104501954507480f010078440005e0920580354000701d24500d02a0300104004140000c1c19078000e0802d000c004040e140455000381141e2400c1d5482d044c1c10341c0078001a115554071004141041d0107403200500902c211105240c075000c90380e800c00d199030455041e142040e92844001003207144506003800644500409441c00d0504100044a002d4107207410200818940c03c4000d00315680e1070054802800315000404607000d9042e0310f0314003007080310000075907581040b0100540e40002c0c2062402e4501b00392 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 403279910 1250 403278660 403278683
    0xc090a1505030102040303030c1d0d08090d120f12050402030a081b010906020a09080f120a021e030901110303010608060d08070206270a0501090b090a0f060c0302061003050604 77
    0x100c0000391061aa030120740e1540c030016000003016015041002035040903113407a140d81c81420707800c200ba00c1018810703680c800b01c0302c842c020000d08007201030801c260f00903001c05107580305e942c3c641080424140004022507103011000d0081548011240c1050000e20400c1c44941400d03404280d4032414a14000e04030100400d05100c1c3d401e10a84c4550303515102030003800088080d04200000754080f08005000079001c0901250216000031150a080e10203001840e80c41c040d080030128039003250b8014001c6014102d2090207203030303e0003441d14003240c1c254065030b6603d0305100050021082209950340390780091004105d85900084a240d2102050b1044400b0215919099102d44144803009502007004601d80980240981c4420501210500039810940300d000400002c00c1c40f5210360b40c00a0707000340d001d01400704550050480e044e4050b10340c010f03c5d030700c030040801a0650354001100003686000d00d04c0600d0781c10041543c0107941640314080c0300d13056031261521100010310162440d030303428 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 403281160 1250 403279910 403279931
    0x4060e0f18040b040213020c0a0f020406090905060a06090c0f210c050306040e010501050607140c1f030c180312090506161401021227011a09090c090a 66
    0x40301c001c1045001441c582651405240960035840190b40581c011180901c0048030f01e03a284c400c544c500b501341e8004082c1c2004940e1901a56010b2803001c83c0c01c90303159840011400d05034010812200d11840291049260140640b411542103900403200c05060065201100390005c0069207042002d18002c40b50060809211010842c40008000e4031464084016140c41e0b100002e1030050008403010300c0340140d4120418240c82e401c0c01190f030700c803408010000c00a544029825030300192031041d5845140820001211600902d460a18520481321902040c0303038140718900c2c0303148560400881c0b422402107040c11203482400010f045c0d224500004036000c4c003d41c4840010078008100319640d103188a1540b080c0d91211030210b4030943c407031825a40011042c003d50301401680003890b1040d07505c21f004410780002240c02d15007061209080c00e41019400e004441d0b00700201c0c0d0804808260010601480340701c010708041403a0040810b01c4007555424207038942026400e0808181800e01e03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 403282410 1250 403281160 403281169
    0x50406031b0f0f0c1211010e01270c15020a03110a11090a1d011a0105040b09061303080a0903020907230c0102130305010e060612030904090f0b04030305010e010b04060e0f 75
    0x1601002d88074901e2107941c0a501c0d98841b043c00c0c2a84020b02c001c0c03045652521b07465007a40c00d502c8000a409030781031110030350045203c801441c1140039125480019660701945000b2568070f0608000581003403401c1024550402d4028011114410007060000c4442d11800c5403086001d0640d0303c564003800c085015480d05402c0b20000b4441101d80002520740d91002e14000c0805000340e600001c4c1e4401c2000456000743d0607101181e03500b0006610b40a01c10042040036440007900b1a03446001003004804a00f049015040c82d650f030f5100c410b2401c0c2580104a209030000304034030104501092440b0800c0c8186500c43c03078800c544805a038564401b002518064007910020342c0c410003403035030000140201500442803c6038000103884164440c9000d21030703190210450005554030401070b120081c1420303400140d030b41e406a041c00e003484c0c846603280105907400340ca080c2c00183c0ca410042c854201c0d42c43d1203174014901c2d1000949841d00d0002c0180503000c40c8001725101c2c0d4403281c500310326900d5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 403283660 1250 403282410 403282427
    0x304080a030c0c1e060c031103041209081b13021c052d0f0c03160e060d0f05070206010806072705040914060106050405011b030e0907050406031b0f0f 66
    0x9004c4414000010480c502c81c511124244080d50803034180031307034a040a406846942c00421002c8189851944d5640302c120300b0540c1d425208081011102c2c0008544c40c003401116241d0244070b03130703c3c0c2e8030f040c04c0d0040040c0714201c0900982e800b0310410041062100540599220039080b84000c545035441515401c2150101003040301c02400c41c03403140b20104401c411161084500ba10202c960761581018010740b4001160518901d451007015008402d000342c00f5000107030b0303004029501d410b4446001c0003c1d1905500e098140036107400a1000d00354041c4890790250200d2030041074030303290050b030041c071070141c0b103661400308440146259400058402c000000e00030143c020700248030503103080503180381c80750b90a0542e40249800420070034030074000c4800310b0b881607480f1620100d00c11500c0d1030106e42064100d0500c85000d151210310344031034000078491115526810340350f40c035100b0301600780c504c610a40180c07014244074042d00240c2182c400050034140c1c0c03400903c0c5480302482a9003d60 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 403284910 1250 403283660 403283663
    0x8041103100e0105010e0408030106081f0b0714061504090609061a030706020a0201021c1206150e04050f0714120a0617010e250f0803040f0b0304080a030c0c 69
    0x3502588068000982c1c00440c14100d00c60002c002503030b0303030301d041c4101c940064400410084040004000b9140320388816604603404146803107010a0002c00040300324041c0d440f140e041c440c013203420001d04c40a801c001038100840005001f55260111108120300340d502c1c8440c0c0301d02d0b59100110203004881d404500a03507440002017194856981030000c402000001d0144684120507001c140c0d944041144905240c0c103030001c2580c00b189030030442e4008032a185403401c00800c00070000326501e00703000311401072055407030012200755482c4005081c00390342c003043d5000e641004144050300c3d850303012035507001380b00f881e0041c2050300c4841040c0480c0f054100118626081d207040c001c2040c0c05600040c05c0f00d5004519101941c10300d590341d400d85045400301e0344650041e0107004219420368104180e821080c003905445291209001550412260080c200551020400b44030030022080c0e0400038000341d00d80e4608619040d40c4040403881100c80000415032110140320003980540900f00005 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 403286160 1250 403284910 403284913
    0x61128050106090203040521090603070c020d031d04020703050f030403090f030b0603150405100e031603030b03010e0102040f0b0a090f0924050a0302060c030705030a050304050d051908041103 84
    0x50f9580601d002035042550140c4d618002d032418a10345940a0001580281201d8011420815aa01049415040180a07600744503200c200080143d8454001840303040c440d4135522040324124901d6880920350041c154001c62040001c80c010a0b049010340b40d1190140c440d040c1d695031140b9045561185c41c2d448000c1c0307008031100200c1044104000b15104140c181c08071180e40c0c01c0881e250340d5840058801030f043c0d0b04007460110100005401155102060000722840e1010002081201203e581c400783d0020750764004031a03081c9070030300075040b28044c008020b41c05d060411041d07140d5210144111403940c8400640450100d005058100c024031200d04004540d956074000600509003409514032041360142503100c545002d4900003040d14809851040158119400e000d860350140103101c10502c0140811000502e0030070040007018a01d0755400e450303003000d05d090392500c1480100d410a00c1070074400c1c40c0c480c1d407002e46a403125400c64a4030181c80d032a00e041512a0510594101f50075 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 403287410 1250 403286160 403286171
    0x6070206131a04090b04060e0a0c11100e0601050306060a2102040c0512061206011809140d09090207030815060d15050a08030712050f220504060611280501 68
    0x2035a0456016000301d64095000384085c0e090142040f00329801ea00514096620b6903020905034061342d440074411098900380340c0c091966403240070b8034200c02a40b00d80b054940310301004400440a00c5014010b1a05400a00d030f10705000300041e8502c11507014046040890116040c10344d10400209400241c000c2e004004c00c03131120000400a50200040c45404900040841c240381450810801c0012400020701a184d0030544405985400350b0703440e54809803242070301d40c00f04540807015140480740701c0082205080d064805801e86016070300c0000035034410300ca0100401c0d00440c0329940484c001032400032100702040003487d0760045810000c0c8041c50103101c24041091880000e0a0b648119107500c41c5030b82d600c1d030f40d40c2c3da4401e9010081445110014100c0b0341c50041001d011914804801c85080c02007a46080c00342c080c0340b0081c280e4146140004115604003442100050031141c03a0000f0150000401960703100020045800d009248009041040b607181c000340361310030b5200000380300 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 403288660 1250 403287410 403287449
    0xa0f030b0109050112032001060504110409050c1305270a0c0206100b040b0a050c030a0e04110309210409060f080106080a030f030519020c031b06060607020613 70
    0x104400e09001e03024410345001d0020601c0e0203410105804c00d076240d6140c413028840c035503000049003c1402c48510380d42d00c0e41c03008030b080d50701da020701ca03920b01300c005289880b01d00d083d401d081500e41c090944031000380200004134402c1c4010186005854064461400c40070000c1122010582c1800000c0c040000d003105001c015404c90b00300071001e011523800c981e41501d4011841e4400b20340e45c440c9040c2008100400c02940d0010300103000b16010031309040e41004008942d20703065501c07021440e8009001806071208070b00c0c0621924882550140d21682507141503001c0c2e690b9282c003026800303c0001d00c4a0318441018040c0d003214003030f1410701400d00100c0da4800c0c0064446d8444e005243c5c2c0c07542800400f00e01100c000440c4581540c140c1d0f1151000b0341d1240302500100005407041c444543c04140a04440340240014200e003401d0400a640e501900307042d510b246030103144c0c240c01d160001014410f040d1f45807025a960305404540301640c40c054a004c2e8075100407180d019a007003040187c00c3c2503 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 403289910 1250 403288660 403288673
    0x604150c1205030702280c080601030c09060f09050612010c0f02191707030504090510030b160801140a0905130201230a112409070f0e04110a0f03 64
    0x18918855095040c162000103402da80e54002203541e600141d0008a00109280d05200c280d50120120242c108400d40349807221100d400c2541c20010455120740010130410840301840f900a20300710b5820400c842c10650340d890300a03031a10900347c56544a02c00f10b000c80d0b50b42c10105003420104402004104801c1c81c0c0a8136002c1c104000d40c000d0f0007030184031800001054200800ca40d40300b403440350b094500b141d80200740d40240030180c080060130300c0049201030540c45018011410b12a00b40d24217071a518105c00105801428134080f9510340811940d9660000c0145056420015400d081c0c0d060110200b07000c000c65a02150341c031402c00382800315060543d0200200c103070003030b65180a09004400d05000f125030482c004130b200342040041a00f45441441d40d038954160090603070b14071000319800019054504c20308028142140d10a200e000081082880d0040812581c41000d95203000c402c085500b070028409404000800d1100105580e0f5421003c05061900040140c0c1e40c0c84e8100381 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 403291160 1250 403289910 403289927
    0x306032a120a150c020a0501060f1503090b150409210f260a020c030a02010b04060f06050f071b0e07080601080c090d080f041205010b0a1d06060415 65
    0x1c1c0101c0c080d0320710941601011031040202a000040c0c0382011565039203500c020314031081050110b0041e43d030a0350015100780100c1d00280b100380080a40e00342803104044204601ca132481c2c0a062811801c40c00240e100081941d120360024106514840d02e4400b00b0003610880000034400c14441c50a20054019420310702005a03042d500c250a4417a007110640c0c645880000c00c41c2c114000e1406035810480b03100304980d1002c200303900176040c9460101e016185412000c40340340947d458004c9044582060f01c210780040119802d0b03181c1c2c1c0c1c1d1520001a0241c41219079403c054140040c8600a01156003400c00364044545800c02d05550b82e841d00225002c000d680c603200240c0c1000c045004c03907100c0e0301c00d1802000f0501c02c0300d14040c400800c01c0030044c400742049455280500c1882032450802c00a040202148405518070b14002e2420508544040e0301e110300c20310000001340a907041c003403c41c100a198407400c0100c907840d40400a0180e00903a408803203001f025030610100690b0041c2e02 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 403292410 1250 403291160 403291243
    0x6061c11040f0c021c260703140a090203101b030b0a0b030106050a0801120b07110106050306090a020301060911160f05030f070210030b0102031c09080f19020304051005030603 77
    0xb0800d8203400c41800c44118071b00b503201d1020040010b5100308005900101c40750445401d041c0090041c60040340300002c4001101d05101403aa00c1c905281541020322007143c040b03505030820825142001084800e5017680700084042540e101d07041c506545079453700e440500b00c54045e5075107a42c1e4425000f42954803002024000943c07410000a01d01082044000301c69486020070442e42e60300e1300100c03650b5921850f2904150740b00e040004d003d480c00e014150286400401510407412240103250940c1c52503400100c605151981d86d41550800b1426622141e6a5000c1210f0501460070108031585a081000d00f8134040014401d034401c01680007001c042c0d2003035520300f090084e04601034003112000c0050a015810030868260401c8895811a03007015a0070800150b607251a00c1d150260b1700a41e0810b680114001080345200c0030503d06035038800c0191005514090405010800b244041c80c214002d2007404004645207039400d11400450b41c0e02e80c070801340741c2c000b028508400790f41424603 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 403293660 1250 403292410 403292443
    0x30f0e01050702060d0b0a0623090105210a0b01020a0c0e1f0602100615080c030c0705250503070803070b180f28020913050a140c010206061c11040f0c02 67
    0x1e00103212382c01404c506a0035001d01010181491003e0032390310080e801008403c0c10810200a892001d8a140b02403003800304011641d00c20902c1c000d00f20b0800c42e821801350b03038155400014060002000b500c0c049040d1000c50300204002e440300451001400300d014101c21150407444400b094950340014514500440803500340f010555039000f55818a440103458000a071980000412800304c0e0703001150403411300599603242001d00d88070242001440805610440c9580e07107250130301c1e0405140080039101c201c0282c0795240c41c04214544d00e01c00c0c607038024920030200300001c0f060040851190744603c0404155001d0b90f002da4040780c2c840d169401c0902e041c2d00047c0095400342681500d05040d9940608041030715201d00da00c000f00140c0b111001ca4442c07080031099070008441c0c0d006002400e0780c0200400180044c000003909107040141040d0107010080c0c840d0203540045a02c580f20303960000c1c02c60b08020412008140038100c1000c0da000050b041810340805a6030010350074151422600 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 403294910 1250 403293660 403293679
    0x10506181e2e0c0c050604090212060901060804030309050c300303090a02040e010b0d0b010918170304060e06090a060605030105010617101d0f06010804030f0e01050702060d0b 77
    0x20440031005802c0425451034902122070748102500034a8001c003031900500801c07502c10b5507100054441c0d84190000700300d0b99008a401010442c41c144519041281169210380c2581010001441541d00400180800d9143c1001030705000007804020316003c80a0804100400800041c01244650200503061040d140c8070000c0c86840c0401038900034212440500500300103602000050292100811000e5513515054030040d91017440c83c041c800c1c81000f402503a903241201310812100c0001582001c402c1c030124540010341c015078220100c00802c1c280644a03280d03402c2100080c42c920b8076110440c8982c0d0140607010100041d405074061058a05000494940c0c2c02e150903070300284207000105c2d01c13101d141901d607512040510b034060456044441601e560300c0000100c01b40031440d40e9091000001400354803201340c0745070741d40050300b800d000513942416503005109040003000c510400099034070444090b03103d14101c0b40099001091a52543c180c1c40b01c6500034011091094824070051 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 403296160 1250 403294910 403294939
    0xc061b0c02010f020d09151403010806010f09060b0301030201050c100507110d170a200301090c080c1e0c0c040e0303060306060d080430051c03060b03010506181e 71
    0x2a4007a00c1c40c8640da0341956142c47c152200103201c0385803441c035003844240300846c11042a034801442c000c00c1d5042c001e01d1154035024841d0a18a0700744c104c1c4041c00e007440c42c2030155003042d5044a046a5081c03070625030310b80d0740c0b400c014103100704400b200c9012400c00c803d04c42c680ea030000c68aa0002069401d480301c0644c2c128050301c030075040000350117454001c600020300254541d4801c061201405090880381d41d50040400203035031090b080b031243c580d50f90030320b410215407240d4000e610941480c00d00385070942420512101854400711780703110200c002044000f1007010310240c50501d801a00c207126070160351032050b49903041214401d00078841d000c005209231a040140500b029040b0b0200ca2416081010861080108000801c5c5500c4a00e5031021421040805480342c6805040a880000405c000d445031210214103101d0406041c11028021191007030b00716411503c040b00e20b80d0303407500000c0b51380ca1405850010030381d00c00720070300500d880c20100801d15070948038200e030161a582d650 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 403297410 1250 403296160 403296163
    0x13180603060e01020c071802090d0803071404080a140c0307061e0e0d060f0b0607030302032a12041e0803070f0201050c0d0915060803090f0f100c061b0c02010f02 71
    0x440c4402a440d500052081001f401c1104107950031811003200580340003084c4010540d0880b020004541c2500000100402380f58860740c0c400b441445a048d0714600340c41d01c0e0619a461840d0900900550080680340003020001c01c80d00c22290030140507106003070340d80e85003c4e160700019041000b040c2c01005032019154460128121750480c002d1a00f500d8070680c1c0c0300c1200401440c0701100d480350352441a8809a91444041e1079903500c0ba035070160396031400c852002501e08529030305900c219008010042c1c0141000107031541c1d90201c00c0508203a540d541491851040d0316880ea044032002d601e5124103000c081c0c0004d501c13500003625104a200c01001040b82214021122600d81d400284668012800181c00c1107901c18052182504c0311050510442c0407a01942d1280c510383c5c1c030004500941d82404207000350001000c80750200c40c0c3e080740c00414800c3c913106087c54101316003000c5079400c010060b0700040008a0031100405a2001000090300c2e88000e8402039001c03580300407180c0002c920 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 403298660 1250 403297410 403297417
    0x9080601060206070c110d0b041101081b0c0102040e01080c01080c1e070203030915253513030312090f03110c040f14101a13180603060e0102 62
    0x2882d40209a42c0e40d4940088610b840228002c84020a60740400303041c9944251040420034010724601045040a00e480384ea407000585200d41808403450801c81080403162038007644180f220380d030940c1e68400c5070b05180288a035801c00504040c0c3c40001080b4600001500a4240000c0c1c80f00303040d94031030301d01e01d650a0003802d160607200025070a5002007915001b0241050fa440038084900700031510300004c0a000d10901410000d00c40480c0b00b44181d5524802a20140074000f0700c014004443d4880c468542c0f00c004031280d607903a0381d078044680c0c40e0211950003103031000b14000c192614034414101400c000c2611003900090129a84c0154409841c45036080300c903401084110304c0a980e0780c0540711003a050660407028014101c040c46191118040c0281e01d0b5903c44000510303280c4070380c890141803005489050420200f4009010150010b00f140d0107040c0c00104460b182d503400c508050b07503500760350030070f20801141c00c840072400390b42508001c054a100700310600c00400240c07800342c02c034017 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 403299910 1250 403298660 403298669
    0x90e06090d14091309021f050d0b0a15020102030f010e070c11010302210103060f020702030d141603200c010504060503042306090f0601030b043c020109080601 70
    0x100100754060103a070040c0480b0511048904500d420801c1007400a40060071031110700c0555500c0311800011403030110640b40f00d054112800380ea03100303140b450091081c014050b607820410764034001c0c2500c65550009040c0200301d4400c418000550102c03009001c1d401c02d4459180515501001003404603540b00702502ca01c1880d40c5110806226880b0b00b9101a0044107a81c14035908210400f482081480350424013440350134840031651461804200300c0c0d001d400079000300781c41401046c0c0180c0d4042100c180b409241d01d000509460070300d10380714080c8221100f1b91803607090106a54105500502601100396150102070200c1c000c0d9601e06882d01400e442050004204000c14000d03940910040c42d0018001c0c11408008585080501004906140c1c100d030310b40d114508005a0030400c003d43e011102c0c7c0308014140c2e0754903550381c040204001030700040001121110365800f00400c0071084490ba200b944c20b000d140800b25120101c00c840662081e4002008000007140b13009000a00c0c90495 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 403301160 1250 403299910 403299913
    0x51e0601060c12030b060c0a021201180803100510030903081513020a0513080303010807140d230a0318230103051f091505241605070f090e0609 63
    0x4072035540c905404000822002e0f007032507610241d504182d118031000d81881e1200100030300030107001d80100500002080c0079101c451b814004100c106100e168040d415160388680b401d40c030381d142d42c0384800d00d118030b81e040150040781c0c504001d02a44e0b4141c01c8200618007944400e82c99880d8540041d040380102d48450303402c8070211107160f8002c0142e80c0100545031407490305a003089402c5c000c415040d40640e0140746c0d580e2022005014005003848250018010206c24040c4140e022011800c6454900d9005c0e10b1070320f0110700c400e80780d10603e151100380f09480301601c078000740034500501050380000056941080c400804508c6402d050b140505060388425258446007150740110041e0100410142e40c402d042d04c1c070b01e040e2060364400b600292080754808180d0840f175600c103d009401940c01940b082000205000c0403110707117809a41803030200f10f401c955880144803035a41e068440d02c001440c0d48521030000031403600342000e220964040b98014041401009811a6035980503641641207 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 403302410 1250 403301160 403301177
    0x402040b030d2703020604170705060316081005120604051e030d11070b09010f05060406060e01120209190e090102031e0901110c010b0f1507150e0307051e060106 71
    0x410100c840203000d0724a068a4410f2603035200c3d4049085074109501c564203074400304002d025880c2062145c500a4002074030f0140c15032a00301c500b110f40307004032041201807090301c6010660202c00992040d018000243c400303021506000c0000e55240021a400d45460240c450a1000140030700ba090717041c14000c20066007000504182c800003400d4a1040102000382000b0240009500040b0783d84641d82250000840750028001c49090718402440203120b035180040c18000143c02070411828240280307414041c40da0300300d034094000c0c41214552075208101844200030010100000f10541d400300408025584440040c0ca090b40000c0e070786140911030f01c041c410582610320746c0850744280c2080002c0341c1050704944035402c0780c1c0300074000344240e5184d19144000d801c0000b441039013504155a080e0726444400140c072118090850001c0a880c160a81c01000c1040d681000a06100c40c5096075581c012500c0c0281e80c411611b11901d503140740100401c1d1408001048060498039980c440e03031074 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 403303660 1250 403302410 403302437
    0x1a0601030c0c170c010509150705130303121d0c01120209060405010503190513030816082706010603150e01121106120106020c0102070801050c090d0f06140402040b030d 74
    0xf03610b5560b0301a5088048107001c01c451601090041074001c60094000d031451000a00c0901c82d1214020409018403008000840300700d0b81005000040300d405240c5016001c0480504002406502c2c0408610b61000310f1403078132014010900095824003600e0b440003121a103640700c0d007640100c4038030b107600100a000070815540103a0055030320100034001d0044083c1c0e9100741d01c080742e401703842c3c44000c0381c6031700c2c08441050b42008415030403080c003909081420004140c02071200100a0002000081920100d40c0040282105000d030581010030381c1e000d5a15207000900416441445050b0010320680009070311072700c0e5924078161501040c9240000b02c140c2c03201c514022440e014150015000c2010015a02c880000940070700b0541d070280c0121820b20000915020b090741286c5c555074905400d00000d402c1100c119084c124003074074200d12444070741c10704152000b0000c001a141d142446000c019442c01e0840262085108131000c1251103401e00034550346446503444000458502d694584 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 403304910 1250 403303660 403303673
    0x605041503021903081303020a061718072408011707120c0302041d0c04060f170115120302012a030506030309030d0210050603010b0607030c030207050d1a0601030c0c 73
    0x504000307115446160603680c0c3e85e2242d646038000b0017420750b0484a11024400c516021340c50900070b0010b481d00003c1203c041188880c0150b002e01600b030031001902001c41401c80901101004200b5180545040c080c8000599040c00403035080000084a41c0008503001c00710104c0c43c0031030b103001c0c0000c01e4910f00300211244290440c800640307e441c002c80000006998074001c542e884840c00b80d101c40b440b00da106401d841c0c440c00d03c1610344160706049003801740070703604100002243d03883c00800f007003a032070341d10303d0303801490311081000d84041c04030740c0403500080c0d081c04164403600c641c0c02041000c268821340d4980000f018095151001a0745030b03068010312a81005e0707008076004058a142400c1100003a02c1c016100c02504096080b40c44003283d803001a00c6026407140d0190024040d030100d41000840ba0320035600006c041c09034280c901003d05108200383d001074030002c4c0440242d6105420007043c92000c1c0c01400c0e400100150014001e944a80504000140d0a80302c51035613014039a00c01 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 403306160 1250 403304910 403304929
    0x806070912080a120f020a030b01080606070206030a0906092603070807050304031119110604121212050f0f0a0e0316030203120a1b02030705031b1c080703060504150302 74
    0x110400201304500341d004e00482c03042950050030a4001a9503210622016041e02c103039500503414004c079071042107184d44907041120410fa44c100c45003541c03995048810f400070704520300c0c05000c80749002804020801c00d0500407041c1500c0140e82500d0314140b01d0342119600c8116013000c00241c3c02004180034070300580c0590b0700284039042240003024448690341c40c048500110700b551139146c483c030b1001e00070300043d441c0d107032321050703568a01d00340c1888008500c1e140008c100078050782c5154400c009840c0710313204900c0b0303200b02620180500c2c144880064004c003000d640c05c0081901040c0807d4003954070340300c0c0502e44003452001e10704145030302c07114551041c11030384243d05501007084201031195034200d08030310660401c200042c80c1d02c3c46044020300d801c048038040c0155401046000301080c000000e559008449a00450110900341c01950508600c402c100c810b8145805159111680182c00e440c4203000e5540d0420049070f4410821084c1e440c442001c2c100644502024005414504c542c3c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 403307410 1250 403306160 403306177
    0x7080403110d05010e0313081b0904031701080307061103041101080604140c071e0c05040b0d080a020127021804050111040303051201231002010b0d03030501080607091208 75
    0x4282e46a8040e1580381c203542070015240007a0300002000391821a00f0444000a0580c40008000542c01c51801000b0030140d4181c0900c2001c0c08d0b00090201841540350088000d101c0c00454441d503914910f507543e03a00040340898074141804040841c5d000e460b400d585c419500210040701086448005580c8004060012500580c070340381c1d9990f80c170013508600c902481940141d183e460569081807640240700b510b5811f80130000300610004601903042d000107460085800041d5400760b08001904044d00110003400a100850507500b41c0e0380641c404038844c41303c00349044102c106805803030001c03030381e00c000203600005031420303030610031044a000e41d030140c0701d9400001e0b051a41c1ea0044850f03001365100b1400203400085103000e09208a802a0040c01c080c6004400c3d205000c0b04e0041e011088a280c90088402e898058001e0b4803d411201c464000a03024810640070303418020058002401110044e124000c0418001480350340300c80b0841c1c12041c456206d40103280c6da40d00207988418070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 403308660 1250 403307410 403307419
    0xd030b030f16030209060306190e010618021e0306030a0303090524010602010f02030f01093303050c0a141002011407050703020f0c130b190803040315020708040311 72
    0x84034404a2410010340380060840b002c1e40046900e10b1040020001008003030501a4110409110340d06100d090044064038100d1404280551461907560041590b036201c03400c00c8a2803e54011500c0003980180101c4109172411400351020200c103014611041d0b9a05415a0001100c1e01c0883e01c40c4d0300280150384501d050300c0e011180d0390040c14842003108071492400741d00100402c0b109809102d400340203e0321308019400c51030107008403031207020b0510408803401d44031009122101c0300309800c1041180d10504200c070100b80d0faa0078031022003143c0422601c0c3d100706240d128052a001c068103007100c000007000c2c180090f14105100561981410701c400b55034a5420032600410b243c0c824030b2143d40c081c4e45d0741d0746400c0d241c00c00a1820720740340102511500144400340258a0f8060400541c0031440b01c0498144044008500b0489070201d59009225400c1c10200d98820f0110041045a01501041c000250380c40b20710000c9200c2c06100421a80080004000155042404450003c0002c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 403309910 1250 403308660 403308673
    0x3070509010e04020a090611190b07020a051509010b03070803040918060204180b120c0103051f0b040303030b0312070209100b070501060501090b09031e0c060a03020408100e0d030b03 80
    0x70224042e03070402e000c800003086c5038070b0045c030007150b0002041c0c0c072010403030700141403080b00c2020140805801d203a0250a0b08041c50004007102d00810409510b030b07500030f00b1941007450000008004039410ba40042d099405c00050003624500082c440b4207030744040c405546090300d85981900105428540d95040d00b0308103900785c010030400d10141c00140b0217401031200792940342040004683e00903461034800ca0380c0001d4102020000140038103410b4007030a002610340c83e40c100700b1014541410017540700c9030302400c022030403400103009001100c4c420f4409000c001401020147c4401d0328160b240c03103405040c0404005850040181c54025294881130a602c940382e40ba504840e40c80207a09951503912107408101c1540e0100b9024010012003a48904101141c00007a45500d883e590424072804c86c0d80305008040001c1c041c002ca24070008005550740d144815002d0040e400510071960a0b0145507040d40c415000380c0950f840c880e11070005040c1c40903c40320168010300104000d19010320410 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 403311160 1250 403309910 403309937
    0xf090f09051005041506060e0108040503040504060807030b330d061d0c060c0a02011214130b0c040506070303020d0618090b090a0f02100c0510141003080307050901 72
    0x622002c4403100220b24003250390302c0e05091404989058201c8240c8403031400004010300e030390200b0100540d07031003441d08101c0350701c0e00d040089c65402a500155407261400070001021000040d0345400c072840bc4d0382030340e6281e50703030300140703ea00303c2010054803104a480c1404003032205a05c031b42c04208078000d103a60584203070358035a0030841e07250164114501e009860155006181001820704140c1c2c00c503400b0380b07045401010705850700414113009050001c0c1016111910407641c109001c0486012140221032a000e00000d001854640f416600072410a01084140944400315002d68902404151070510b896030704500070b5101c540d18a800c1c81d62803c0100e03140c92035204100b00140c1d403100c04211813130242803c80e1114009800440c09034003940c201c0e000108075605140c20745804940780107001460800a9810340010b107001402c078020500b01d44001e000b194041200c050005030012a00d580e10313403010251b529503001c0034054140900004d00d4003440340f0b000303042c299410b24000303141e030104 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 403312410 1250 403311160 403311163
    0x81e100606210e0705130204030206181804080f07080904110a0e040b09011a1b01050406050105010c03080c03060402070f0f031701030c060509010311030a0c020d02070f090f0905 78
    0xda42002001411180340c0020014010010390030b010b00c0031900300308090700300c8619070f42c60035148031380307401911840d80710340328101d2507410b540045802410b1151384800280e8804003e008402e0098804c4803980b146815130722100a4030b070f20495004516500e4442c4607110035000b600704c2d81e401c4982460402c1f2884050301c507800f0340203070b0207402081c41da2108003c0c5006440c1400803d20301d80142e2500b003a150503a0ba400c0c10316811590741c034518151400102c5403c00d0305210344460314020034090303002e00302c03002e43c1580101d11542c000d070010011a41c0340c0e00112959901041c003d400511014041030311603220400171604400c0082c40145170030030556400ea104030241c0c4050706d05c91402d1403020306260308002803021221104280985a60442ea2919040700700d40c09500c1c10054046418800359001e580081d120310281c0d4007150700e0b441c00f407941c4006440e481c516000140203a1440e0040c1da4000100c12040d2070b2000d02c051400d0f0b042202090080620150404410b074441c00d906011800 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 403313660 1250 403312410 403312421
    0x604030f03180902280302040806040c080d03020304020f011206080f01020316050304020303070602090411030c1308030a0905091909050706021b010e0d0c0807080c1504081e10 77
    0x400c2e100d180c140810503a90300c20807409035200801150040043c0e00c0303102c281e507840020a84103420a2244511450802c400030b0145400004a130303c202418003052003c3d01c9601c00403256410103c1d915401162003ca080e80400da80081d0042040312030303144039602070180c2c8451002d8186c4005070785941c0f0000c43d41341c0f8401111218490354000705020056003026041d02d000c03a003500b4110303e51300b480e501083d52840742200c0501541d42c0820320841070750361600034410304520711440f551641000010744d079403580700e40c1210841c0106100c001548403004003d903280c03204191103c01d5034515020a004440c0001031403640121100c6c070321119030640704e210341d0f03e21303d019800400c1c000381170050180c030303100b22904038004000165100d100305070782c00844006402c0094464540c415502c0c03030301600940c1641c10415050240d0200030918440025200444e10404c43d0501c3c0c440400d210030602c10b21039030045008a40041812070300414180d00e5004602c0c91a01c1103410410001c10f00700d04660 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 403314910 1250 403313660 403313663
    0xf03201507020102060112050c01080406020903060a1d01090309050f0301090218010e010b03040506180f1203160c05030405040e3a110607140d020408010212100b07020603060604030f 80
    0x110109401c015940d0420507103003d07014180c1e120240e201c0d00d445151381d07034000000c1c003810041810002020004140c0583d03900c1803010f012103065003005840340c0c015000d004c07003211400182c2103d20514400500800c0c0101c0d03015205c4550751401c140a01c4601c074807801240c0c0d0150340752124100142c80e100b4659650741d4611407802d440d94103154030075407003401c182d01c01310401360203109001c0441c00c007107a07254201a00f8007407044d640b03009010700740c2483d0000140344410300844844050300d1f6141c0005522032041b2000e102c8c0000000360054454055084c0040d0580e8000d00c0244000c3c205540000554035400301207039903030316a16804140d01101030000b00b0754116800c0f2100c8400344000e0400083c0381d0b040c180f0001c0341071a14401541e500700181640c0401c0f81c400b2095103443c10701c00444040032011201999200d850b0602d0754080d43c8000340074150001e409001813800000c4406070010303240b010064505e880030607020000b25400c01b41483da8000c0e0200301c008000340c000c40040c078049 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 403316160 1250 403314910 403314949
    0xa02070b0304060b180108030d0b12061003030905060412121716020601050103110726040803040810020903071401031103280c02070e090a0c06051903060f0320 70
    0x40810301d0512a10007400054a0045017461006120080e8040140c490594070302d0800203280c0742d500005204c0f040c000521700070070301a40003031210604d408a05e120a4a01075140c0142566403a801c0c40303502e209911410f03403290340b00391002d0000781c80588038451008079481c001403498130040f0080c8074403a0039100061011405c2034101c0b002e58050100e2401000c0900b8108081040c0141d4100288580c01004200f214811400c42014203108101061444440c0460f5101c41d1200c10055032944180115406031080250750b40403c2c0c0346008880020070083c1c040c1084910b001d800c0e40300310b0041810941810744031181503414207004005148144072008001e02c51036980010755408401d10b000703242c0c50a0801e07441100d481c3d0002071310000c441186036500080d665102845081c490390b00da00404101d090903001480e90350000243c04100c0a8a02074000d5120b44a1304cd01101e00e0341c464500d00307c00c103820401c086000132884c1082c040c00c030000320941c85445000100e480141901d03d035600c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 403317410 1250 403316160 403316171
    0xc070807080f01050112080c01060e0a0608070b0f271009090c03051b0a020a060c03090213091e080c0f03030a1104030c26070e0a1a0f060a02070b030406 67
    0x103491007040b01640040300d07503008110650400705900b2440e00c1c41c05d0054100200085c00c0308040d1801d500c114001c262000c0c0b04992170510307515000191045105d9155144a104404181981d0800845001a44030b03005030b17250541c8008803200c0503401c59900c2240415091082c1940c1d1200c40d25804550386a944d0700040d51b003040040b070200c410005411080600e082d00308898420a4265802014001c0a07242c1c2c480c044881c00300e181403d50036004182900300402c69400503015003000388824070889a1050420350114148125106843c000d401c0400e00303c0c6080c4411070000b03d03000312038040c004091800c505102c01c146000c0040c81c840f115540004100f00819000d071040061843c03410380483d1800f8503544030b0545840b400d00550714444d849102851150160a005c00c00352000e034401c1c0d8424560754000d4140046040b984880b40c182000c002d418100c2d4554600580c0c028018144103d80514a050026540110340004203510901402258541c2e8202c0554811031150001048 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 403318660 1250 403317410 403317419
    0xa051c0305160e043c0b190603092a0806060316090506040917040503060f04050616020304090e0102041418070507021c050328051b030c070807 63
    0x4441c0000c00c9480a00c440301c220602c101c1d4400e14002c1001000c8401055152515589000d549003c01c039603041210301740a0b4020038181c80009078107101e0004002c000141c1903a0900c02a08261401011040c110b42828003050b4080d0340425051809090560321110801e05107811707000c01c82041441000c0154401c0080c2c2d907041000550002065010b000c69402e00c80002840551034010700ba442a02d800c0054507039107176a03128001c81c41c5c0080d0101014418240d469040c0d81c000d000d02d5020380102000641c40360b1010700c54a0280c0e51240081100340e031031100b031402e203820540c8010b0860208110018210300b0780e0140e021400000030006a50700d240400010601c1000c0300c25500810510010b090840d07016a20540d0102d0300303007070242c2d48244a200184001596000c00c0c0c1d000d1240071110803d20034000003404001c00c0b4001c164902c1c0b40500c0d00402d8007484400e0b45000150104110b801d400d20201081e41815032007000c483c10710503603041048c01c1000c66007050845078007000c0c0401 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 403319910 1250 403318660 403318667
    0xa150504020c060405010b0a0b0a0e12191205070c03060902011403100602060a0c0915020a051f18020f04090303020c06130c0b160305090d02030a061a03010b0d060e0a051c 75
    0x14007c4004072200162540391450024440c094140c415060182280c41000a5140c046194000c0a400b9095502450440500f04c200b10709240c010340303403040c0c805000320ba240d02800846141c41e0300b004000040d90310f555540c50240c519104100c3c10490702d4110740340360134401b50166006501c100c603d00038903820040001c6c9890f00041030f005a09040451543d04d041d0041c208030180c43d4507081d911010010300c4001d030301c0c080c03e08500034580e00c19000195214403d64840c084400d49032681400400c020010001c00070701000006988407000c0800070b1454903041e8810180c00d4440e04015080489010103181000e00450700701000c10040f1143d402080b4094000038050300d00c45148606003089112621282410700c0001002c1c0480000c40910b1507440b60400c00002c1c3d401011544954450314040000c0c0440c2038040b40110810718500030107283c18080c0e4110b1241c088c1090581d01c185859480c0a400c940d6500c0300140515003c1c900490024010080040c004000300c0b0003201c43d005005 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 403321160 1250 403319910 403319921
    0x1080d030c0c110411040b0a02030414040c020607120e030c01090203010c05030702120a030e1f0c020f190606030c0e0f060a1d0406060b040f0801060b0a080a150504020c06040501 78
    0x1042080a801403203000140c00c0035484280c203c09403000038403a003100c03140419901c035a8102903440d075004191443c0300c981c00001082683c428440c034025000070002440306550003a190030006d60002c000160020788280c0580700091f002c20000b1441d2501041410b0440d40a800007a005944440550f010742c1000d000d00d41a4606c14a49980f4600e44244001d4a0740081c2c41030782048100000d40903151440394010365110030400c000d955440340000c0703000803c01504040c00c506c0c40e00300003000504ca800800c0c00388407a2400c0c6d02500001000040804011180304412140c9a40e160703800b00115207000785000c0900100e504d694003a003407240001140c07800003407840d40f08024001003401084e44404080c5421244c035400704107651102e180407000f81000d070b0030100c0756500201e00000c4564031224154100c802001c020010581c07140f080c50010300c22901c0c06c1c40070640180104903d9210b41e444031081c8070010f0700c051a20341c1ca4800003400d0303902001c800120b030b074003441c03c1c070082c49420300c2103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 403322410 1250 403321160 403321181
    0x409050a0b220f0212070c050601080f10050903040e130308010e060112020304150c050717120403051602030102040603060305010b0a14060a02190f1406060d020609040b0901080d03 79
    0xa40040e0882d5842c2c030410650345080d160322941d03c41040a8580740140c059070440c0c855100412072a1405503001040403121410a42d624446c150002070340e40c10104420841500d144042c202401c0400c1c84440a400c015280c0e07511f510040200160f03140c440f00205004d600030450300400000f00d418000d08414040c0c11521680d0616014052160b0300960322041d0241048405a00e99903281800307000c40c95610440c0b00300d98200b8080116030781d030250040031403503c031f500b040c14403890b03580d210400750141d81180c0d0000c4a02e4804200030a00030320180055540e0030484444075102540400d0136a000b503448940801d071544410f008025080c00f450a040ca800e45903490810301c1c15000d0305000807054482c42c0691000140707980748510078481e0740c03120101010703d0081102c0381e10b0020035a40f14550b043d1034810344c00144e4104450003043c1705000e1032006014011a010030f07001c1100d00e6100c0001c190f840b40d03883c04240241d8850240c500c0c02400c070318000e0500f051146c04080c1c280c1d002d8024 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 403323660 1250 403322410 403322419
    0x12051f080c01080a0f15030309080f03091005030c1e18040e0d120b0a1502010606020d050a1817010c0801060905060304060914030c0c0a060e090f15060409050a0b 71
    0x1014040c1e6400f01c00c4a6004c50441c80108080821514100c024600c0064007541c05404110100525401100300012200340700300f00c03034000301400c2203903459000c1d0303240c0035502511103e100d284c043c0c801d0001d03541185142074103e1a08054013842d4030000016901d0b080440000315060390311081c51130404109502c1524103101c00384031050a2603c801d00344007544c0070300050f4800c070701545c056a840542d1349007025021006039515080c0c022282000c0b042035000560801101050071840412140000c409907202d490030310410350310948581c08401c02c0c984800202c0000052130f001981d4105400303120880000604143c112001061404160032000c1070081c4c0700e0b01002203840707050459130300c1501703e2000a180301c02e601c8c2524484845c1c2007010490b00c004251800c0020020600ca0940c080813512140d4440c0d607200103540c0100800020b96200031040300203110030208030f1075030780d00c192010200400b0032041c1c0c000442503002a0011102681d85004100c1550610300c1000d903002011034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 403324910 1250 403323660 403323673
    0x9061205090607031e0207081806040e161b080304020a080106080703060e1204060504090513020108070813051c1b0c06211103040b060f1c0312051f08 66
    0x384682c1e03034002401550406541c0c1250a801c0c0c04428201440030000820035591240c603410100c4c9079401000c56001d40180d10081d03408170340b51800031a000c850030048040e08517034038000d51380038110303d8202d02028000c0c0d00141031848411f04040c2000544284402ca4407410a401440100c003443e402242090f07140c0f00040c031400500050319011690f00810101d04207400442007800c21039198400c4000c900046000305010b500180034105540c441007003000550384400320410780202c50040607002c034080c0008100da00d4030440b00341c2c0c1d01c02c402e41342d039031001200384d90380c0c03072800006040881c3e00150300030340d03046100d0313010701c0c0070942c0d00f003001900f14042455191010515410f100d454148001344d008010241c0a000b030000c0c441c40041020400c20200d0350710420346a00888080b101f40c2d604000081c011708c0c0c040c4d10311424000c05051030070404100c40b0951484080c00000b6014020309100c00618002240121031117a0007032940c5c818180c00a0f8402a801001900103204036003208 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 403326160 1250 403324910 403324921
    0x1a04120806042a11031b0d0804021e030312010e1906080309090714070804030209010b130308180405090a060e030403080a03020a09120b0f060a080604171909061205 72
    0x7411002e03941d0340c0c04451000c1400404044e03030307000c030140441c480c2400007060380d500c12064400b803500c40c446800c0c01d441100000c5c200440e1001e808880080d8030100181e08450462110828490f013508003504803450181141030321046640309038440d402c002c880c18100a04c0c80030a481e0401d40e094a050144001428105416124043c0c00039484c014107011000500c060b210309c0300361750910f150340c00c5280c0e160344905242c20254414001640103a00c803900000305240c04108032108180c01fa14038104d030718115590b01442c0d601825078003400c1501c071314056000e55a00d2185078025881c41000708005907072450901c0c140d03107220854005581051100304041240401141c1e042c0301c6920b0016640c038141c80c0107036120074080d0032200010388102c80b80400c004011071a2070103918507951500b2180c0e6160100090070f070081c020003119030082404074000400708408082d001559600050800f040740a5400061114804060000d45847d200f004a40d23001540b241e450a0b02402c14006803610 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 403327410 1250 403326160 403326191
    0x19060806060603060109120c0302011d03061902041a0c070e0f0c07020103061d100504150b0903010f05091b06190f0c0215090f0402070b060108041a0412080604 70
    0x510960007848000001004da0f88030342400c074090021002600b00018540c1004130030320135980000c0740454409200f41020003405150b0b070344401c00080c010b000c151b840e4039103c00d5604080f4010364056400f800f000ca121501c04004580340800d4152658485144105541c030307000165000c006400508428041c1550b018a4025440354440800c10b40d14252440120f005210560203001c0d41445220700000d80030030060320500643c10700f800d400c610341d1070f0001c000032203803500240080402442810420250074002030070f00100014000902d4404408514050360806c984503030480e0081d8805104001078010f0300040050103a80090901d064140c480600038010011081401005a4012043c92007007070488140d130f0340a000040040180e10418150f60081e942d07946c8901c005104001d083d040078829528140e8105982c2d16494070f8810054440082c09007056a0766085103602e01208050502c10a026038410004159211100c1d00010490a07015083d1032060b801c0c01442c081800c1d1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 403328660 1250 403327410 403327423
    0x609060e0402090c040911030604150605030a0905030d060305070f061d120f150106020d0c0b0408130306020a050d060b130303050d0f050906060306070503161809090b190608 76
    0x24142c03440f50550b1907901051166024a61260900342d06010041c4010b064290181d40140d00582c0c1c18011900b2019150110010b030b0301945001480c1403001a90201c081d4021250160040003075034980400381c4481400d03034000350016601ca03030115900700100904072180500618040c40c00010034030510308440c01e03884540c40b1035031040c01c00c86000d80c2061000c0c8800f013440c944036006c40398000c5140801d4049603e0910800d400b40c011030f805085020b01400000340d0969000fa43da031170701c1e6120707507500310290024040910303884041c0d4000b100041c03092005041d02e01003a114035440344492201c407429254140c10040c9014000d000e602040c00200390340c00207a0380d05080540d243c00706010000001c21015002c810304038141030602c16501004200e4902450b4107505681007a9603401041c0c4080c802a903d01c00c4081210b0070100d14644a0820604c401c0c09007445800d030103580b400d030b030400d41d91035090984600355140c051081d11540110384a428038910728080c000365203090300c0c160700e495 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 403329910 1250 403328660 403328663
    0x1d06010507030306090f09020406090c021507020109050607030f0614010c061a06070609050c061c0905030f04060305091b0a230901060504090b040203060d12030e031b010609060e04 79
    0x3201040c5042018080c0d040040039010100f001c1010307064051154010303001c40e80c800e902540c90031202240d42c3e0f509014510340041541c00038401005840c50000000f01d0090440b41155138490440740040e00c14840c99010700c41c0c0d50340108124000b0174070710080341c040e03078443c0e0300d01894008980384603608408211a00e940002c0c002a4814140e414900084001144160700282c006004030410000d07502401c0c0641c0035000310341004280e041031080620510f400c1c0d40740c5403425000e0401e4500660040c1c4162440b4006890401c013801c03600b980c00350001d40046c4080f0391211308200001a0420015000c900681d00380c0300310012040104400034401d0040c1c01e6080101c140d01c000c04189110211040a005000104550f95a042c0240142c0041c081c80c905c4504101c20003200785054000c2d6809500014085001e40142e80d5030010400c2e0000c1c0c540050548510000003100c4051000e80055000300303d014141d18201a01030b03003110080d420081c0154a486800d10921500001c1e403039009 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 403331160 1250 403329910 403329917
    0x601092007050c10020d0806030a0c030f11091029030106110a051b0a060908030d0b0111070e010609080109050627100213050616060b010314100305071d0601 69
    0x1c41d882e0a050741002000e41840e50003050307503031138120b18a80c005105d8603600865070715000c1c641c441c4002c1580350b50b0140c0c8013401c000070b03004050002c00c4c1c0501c00e032500303d4421400b132a4030403020008100c542808883c92211080d0414041015503d207420403072141900b0b080c800789401581560ba80e4030301060150700200200707609034508480040003100c4036190090b00301c500c480050300341110440440d4061601401d1040400180e10340030703100d5141510300c024040c60030087c2d18020f410080502c0800b250400081c2010f030500380c001844848007400300058508001c0d818620b01070301400c43d580c85810903038900310b02c40c00454008200d1a40150040044a010025203d9140c500310a0000d2002090284060703803804000c40d41d0041c54508040f00c0c01c0c904060b9190308100c024003522800f0110100c9000d48800090342c2980305007200081410006252900c0c04401c400c690011510f600c50400100b04c00d00500c00b04110322401403415400c00c01c8500742c2410a503007603031000362145041c03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 403332410 1250 403331160 403331167
    0xc060f150e090106150e0f0f1801061b08031506070b0f0f01090c051e0d0c03021206040c0f0e010903141c03060b0a0c150509060906010920 61
    0x2290400100ca084400c0900c8100791110718101403480d003920946601d600e00400080c0660004e50382d00f54403910b5459a80c0d01c02086018090309007221941d5550185120101a40c180da0381805040c2c080c2c583c41c0408a07035030400801400505000d503075040c03450191551240010040000c90760311070401a0300c62156103510000c680c0705e010300e10004064600c41000c2040c0d1021079680383e4031840c0309240050803a6030b0380c0100004c5520086041001400410904143c0080d10031b03481144001e00030820318001d89490164100d40840301441e00094001071150200307a480c14030075401c201e00700c808202c2c0c0c0740110000b80c00c401203480042d0601ca580d00300018942c0c0101c0401006680203940d0340c0c074003060201295100c0418081140c240180a1480c1c5e2159110384940701c2522006150940f5007a40070310207550400280e5012121851700d90f13101002c0c4081d9014203805152040010107850405250711030070980141c01c60020380e45403014200c2d04003406d64600c078510322006d095a03503 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 403333660 1250 403332410 403332431
    0xb04051309020616050606010806130b0d020a090605090c12040b1803030414060f09070909020d0c0e07200304090923030a1701050f22390c06 62
    0x78064084029522541c04240f0100340c024050701c54081c1d51003002502d0031035494000649040c101500c00d00d030045015988a854450941d0000304d28500041500a00c603074039500088010140e608403440c020b459407410000b605002d80341e0398108554100c11811b10311018201c0e82d485100403c06800302c0d83c2403005c561420703204086410034440c1c810a40e581e0f440c03d4141001c20030070301210080c40d0310410001a80c0007891400031409820414042c0481c1480d02d10024094000c0400a0b03900102c69092500043c80750528078000f03000c407622466042c500520090000f001c0c030b060922011b0582d03c070504144901204440c1683c1011400082c1c0311003078280500c1c41041c80324866006044594001c034030341790020107004040d1003559500f004181c59200844003520a10407680c02ca841c2940b071015526000c40d124081201c0b00b000840003c41d00c031441d406440a03288140e0117010900300041100c07000d1071502c0f40d100140410541120034000d8018082d030440c05001d000c85a560042d0300 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 403334910 1250 403333660 403333699
    0x33f0908160f0b040804051002010506090105011d0d05100606051c090807051006090c0302070506010509041a070908011d1e1f1a04060b0316020304090501080d0210060b0405 76
    0x300c1d52070f00030a05454528040c41d011400350b02c1806158450f120010000325614414000c451242e00c02401300e0350180d103403c0045d289000c0103103800301c0c1d000c80848001c840340c640c0d485007998180101d00034591082007400880882342075400040402c0020002220038455000a48209805007600020a90380c141019102801502c00046c0903003e04144400b110001c0d400020a45044540070060484000002c1d0120322507254010601d4010900400180c500044e182c0c2e8807901032803050102124030460b20140340c3d000c840b200046080100c0074080741c0030034455206402618086440300340c55810550744d442c6068003d900800804030a1040141002d10681030040e174444801c5d864000210000e0010344403a004a035125425414130f56000c0c90a8090740080f00c008810040c40c58456400d01a0001c03202d03541501075100c104000181219540f180e14000c04080c8041c18000c100c600d0000d04105030003510b0b0701131b9410b00200340320810748442250200c4004883c1ca6031b07414030620084 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 403336160 1250 403334910 403334933
    0x402031209061c02031f12030e0d05070f180203071b0309170106060e0f0603070c0618030807020d0914041e061412010e1207033f090816 60
    0x9000b80f5100100c03000740e80da00d40285000da220b00801030600040c2da07003c0060300c440b51045051045580d000507001c03d0203840c4a401d280b40190100014031481d80f6113901c0c0440540c00b400c080e010a004c04c210003188602c00ca402c501c81140305510710f041400e4014405e90310109030310312108800030301030101402074040303030000c00d0303802c0101e0908908200c14034001c1c02d480c0703d80ca011034130b15440028185001040c19030310507001440d046c256111044101c4006020300f00480d00181d94280b0240f03151440b5441c00e00e518401e41d1003004a02d4211402410241d18000040a108441d45c080c4070f903142c48d00056112000a03940010180f00c26030234030f010070040c825410444d610b03011020509504914002030015402c0d5940d10403468050007440c01c80300c140e16103800e640c101c00307040d4541c083c548000f0316030ac1d0300a140003208108204c60200f0056800c0e501207040070185510600240c0b811503141c2c649060840c0c0030003951082e0746070680c09201e034904540708100d102c140803080185030380d400b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 403337410 1250 403336160 403336177
    0x30f110f070905011401090305030a080c0c1231050603060102070b19020c150703080439211502041509080c0603060f0d02120a050313060206040203120906 68
    0x11214001c2c0c0d542c000000410080c0104210314940880c412095402002050122a032000084d85442202801120300010107044c001803c1000c0041c802140310800800841991104035503079150049102c68500011201110105201040207903150784007400c1d82a08482d42502c400e503aa90300c0c50700407400d1007416040410200804180105203401d001452040340d00c10ba001c407083c00b84160100020392280281d24056450100f00b10400648100360355500544a100c140c10300312843c01c2680040000030030b6100c03039420202c00c00306205d160300030940020629800c1307400c030165207241112102d0320080005440c0210b494114040c2070059412200209840ca00016101c0824640207002d1015441404024415242e8030115450038030101e0380544002840d82c110740880c1d10520000c0002d0f0142603911903585560700d4407049041c00380385a05485038015603914548440d941c40c2c2c4a4042e00040110341c08101000016140011500f401079880c0c01104e0300c400a0000040140c0308100b003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 403338660 1250 403337410 403337413
    0x40b06030f011a0a050603010305030d0b01020307020405192a05031f0806180c2b0203031c0e06012106090c031410050c0a0c0501090804080c120109030f110f 69
    0x9100d4010b40d405110321089050455002c804d1654403801c004440c0020b010103040d54204000d0178a200406a11840b441d94040c010707681805507917000607085500840354103c103030001144800003502c0c1445405500d801c40100d1008500ba948100440700300e07019030030303c2400400004103030700320329528502d0040c2c1c40c050580d100c003980f00d54000d030701c1e2a8140c46d0303074407901001050321114080100e40544540b4000c1e000715032070070941d00d00c80107400400c900b85907180d400080920141c1c80600c02840441c1c0c90070403242e080c1e07030700980d940c0449814480480e429080400148401c02c078244401d00840002403400380b01000f0760170900000c140300b0100030304900750030500008200001c441020407485140584003c0314004821800b655021518070086000400c13030302014034050340b650302440340102d00016059400ba6252010383e4040e80220041d580a400c00703900d9450000d21010500844070002d00c420405590040c03e01c1240700800c106200c0e01510f102120340c0108111802c2c10111030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 403339910 1250 403338660 403338671
    0x5060304030e03161401052b1e050c04031b12110109090510030605090c0d11030609030406050904020d1e05040b060f060f0a03020c030703050901080a05010509040b06030f01 76
    0x9000b40c003504001c10300c14040d020b0100e008881c5280c2400001c11681404110003030501e4a0300110342e41e504c0450a2505080e50341c44c212080d49180a1903082901034610006812100c0101002c01c4607005903003811a505000400031820b9004040d10102ea90000a40f8000d860070551404c0d190f480c0c0c1c01040c21001a4a00d00c0c0c280900c80322031030344004007a29082182c985880b00c110545404448500031052114001c10001e05e007940060352280011007500c0c100d940010000d005160302c502c0a50b0030843c4440190102d1809205154020380a60000d500d4a490030b00090002d0050010141c031030356000c52200c04414203a0030107103008140c0340341510010a02c100d42001054207441c25580c05114100084890410b1105035180e0f4500410190401000680b90b6003a0340c400c1040c02c08054003444100c00c10344041001c2c007000c510030b84485484840c010001410302c4401084442c01e2401c1900400150b258800c0081d00301c3d80003002649282d0700d09000c41d1a04844040c424129807812 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 403341160 1250 403339910 403339913
    0x60317030709051c030f0207082506111e010605060319051012020906031203040302031207140f0702030a021e0906040e15090708010507090501120e121305060304 71
    0x4000551080e4469200c081002da16042440f440100c140d543c81c80c030300d4000318001e010900459128401a00700d1040b5a100c03500d030381d0901d04000b807142a003503030140d100800c40100d480564544002c0c041c00c1c0350540d9990f040e804c007540d48180c800e107a00d03041c034041054403418075401c0d008540a00005000315690b4240304600188405006000700107140c50040414940141094003804540024003040c1040ea01902040451310014200d42d41c188500b480c403100109038a0082c0d0700c140c0c000d4018540711031080411a1501c40010a01030800c66240c20301891032842c441503035100d001400c9100d07201c00c1640f011070300d000e5059801951010781100f132440751050074401040406410b40e0003002c5ea403110028041030b24980c069041c1c0b25001032070080e8080e060344039402d030300507400c60480300d0555550700d2880c00c603401981c8007030014850260a010a5811180c0701480021003002000200402c1034030548804254840009400d0005840c002c42c00e00d1400d480c0140c00d00078150380d9241801e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 403342410 1250 403341160 403341203
    0x1022502010e04050403200a020a0b03060a090e03070f240b0301140f0f0709030f080909180615010c050f071a041401030f020f07030c0506060d05031204060603 70
    0x11160124002400714991581c507003403038058a805142d042d16520403d0840f5803030444040c501d0201e541b8940b007015262000360792103038900402014a84c1c4900d60304d051a02c24010303041c24540001100d00c1c00d045242500b0b000000c00c444d01140c018031404610034007490300c3c01c091006461240c081c00900322002c60384424941c030082602c682240200203094402c070000b17031044800c40300d8500703400035007000a0714405001c0455a10842d945003215a064507903a5a0b04180610b00f400e0360408804280600a810f04103c0350b0b03004441145070000c02028000c0c4543d0307400008103000c01081804001c107405074041c69140c0c03d6943d0140c140c80071101808040c0341c0d074112500c2504506140d41460b001c120004031308030f90036a41140009078884940500640140144450410855900700a09588614a6005002c0b42c600c29540c0d6035081c141c6050540c604007000d8442842140c0a14560001410000271105020701c0b20fa04076140b40d80d0b50801900170b0000b9070000d0190742d0314084941400c0203 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 403343660 1250 403342410 403342477
    0x13080412022d091b1801030e03040f030618050606041a18090601121203020304051f0e010c0206100306150807061709070e070302130b0408010209011d0d0b07020102 72
    0x206681e45081603031400104c83c4ca20741c0040d000d900e0241d0412500135401c0c141e0070101110003040c1030100c0c142c205c605160749540d00650080d5442044194280100311290181c08501c078a00030300554804019110740351140740c0a00742c64411a91a100440903130b03050150850302240c020400c00401d03a0790203481100c03403000c5516885901030240003048aa103900c00c6030b1101c9400c01c84400783c40c8464002038000b94405041920309205030419a5030100b86504940c041203a50040400c00034002140ba60a41d40c0c01080d5000359080902003003a0f424a65030004201ea404c400041901e0b1000c49a2013111030658022904034042d001000c0740e01500b011941e410b40200d0f0381050b4255540b0007100f601d0340f40a000711210716034006d01040e8494420f40150117283e00c1003140481c0d044e900c449107034841c0d105a1010103683d4000c100d0441940e040700e89600b14001028108048800010004050100d03410f8018484c641c0315001c1124103100358147c94203418140d4103140d24940180d0001071004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 403344910 1250 403343660 403343749
    0x618050301061526040f0302010b0d0c03150911060a0909020f0c0d020f0601030b09011d0f10050105090a020f2214010302190f0c0206040311091308041202 68
    0x205182c0809603609403224250313162801d01c00c407485042e112580d41e160300040c404015421503403075282814007941d0b2406600840c038811600c40c0c00d0306240d8600030201e04845100000f070740323144c4505200480d04007569070560180454200e581c50b000407000742e83d40c61194210f048424408a501d4145d51300401c001d0103008280c85c21207a0000091900700c0e9629881a8500c1968218100400009026090441c1c002c80c5081c0049420824030301203008025a00300c00b40c404d60b0000b034810141010521040c2000f01c030038401400b281d0304140100380d00c40005007040d6400381e400100c00410a070a0b00586600d032604804001d9446503492102c050701c1001d0049544c1080c002d840217020798000d108a600407103441c0191049807219140c141c40e5a9280404039050043d051000c200507640e4400130000340d41f150401c8900c0e81c40c160280280a032000303001e80c1c001c54100040401040340c1d08166030440b41d00a034003c624004510101e200c2e0b54800440480b40300c0740308000001c40c0030b031034010030100 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 403346160 1250 403344910 403344917
    0x40204112b111602060d1b020d0f020c030c090402040b09011e060f0e01080408090a0306060e0a020406090e06150408150703020a270812030103060b01020c090106180503010615 77
    0x10640b40220301600e214800b0380700d1804030a41c00074401401d02c40090310102c0c4280310009012034003400c9034001c0da6001000c0c440103070803141c080f0003410f8020011500c500c502d8401403c0356910341000c00e68403050200d845109262850001e0304550700c030780040520340c001414000c06540d69042a00c82e030042815400c207804031848001c20080d20030801c02c02201c00550303500c02c114550320015110f0100181054a5892041040c4240354a4102e08440194856540002c0c541e2505d40c42070243e450181180311098010441000f107540d2149400003a45c61031421510745884883c000f030100c00429100710390310280490001091080440c24042d8900d020000405a0341c60039411000ca02c5004980004500c0e8804c40301d81000e005001a014920022450100180c40d41da400e0724004c0d80540c1441c503281d0000062007040f9560180003a492001c0c0000c0080070b40f02400181d981605009000400c6500c43c05140301c40c0305d040e00d46000300405402001070030344400b404407002084000c8100403 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 403347410 1250 403346160 403346171
    0x306091e230105100b09180c04030201030e0a05120c0c130506010e0109030b070e03010207020a0909051c050d0209030a0629031504060c0215100e09060f040204112b 72
    0x5025040c0035035131150038003441a030301c804e003480d48110b8550000c40140b0b82001d18104502040c00551101501901c50308000a48451541c400181940c0482c3c411841680100b0f01d14000030344002541098140000c042c03685502c4545191032034041e0310500698020b4016113540064140340c1c2c007641c0030383c0081e40c90749084884000155540f04107488000d01444e04840014240d1344500c86115520100400141c50143c05800041030071005402c03201140c0e076204000020004100701e2200d11640c0440d00c01c5c1c043c8421580900319000c1d4061840506030002130095040d5801d1040c0e20710b040d403040d0208448590a40480e25600484241c80482849400f682d0401d140009400040d200c40000d50b6129a44550324540685142000c1c44107600c1444a81c082480c840d1111130f1054900d02e80700b1056030b1a004920341e14403009815034545400410a1080118580448560264054030085840e04404100d1103030341c80740120240c0d03a40008108054000700141c0d040e1154103840d44180035 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 403348660 1250 403347410 403347473
    0x313060b010e331306030b0324060d021807090b161205090310020a03110a08130c1502010506030c060c0303150a09090501020a020d020d05040306091e 66
    0x1038000184220580c8240c610f8282c1c562800080f09184092410ba00d02100f191409040003a00342c01c0380345803240ca03410030b01e030510200384d05100f44c0600e00d9003100107008500c02c41302041c411203000300c02440c0000400e8009034a64441420700404580e0107005410304014100c03180c000c008080e603010000580f000d20019103844031001781e60101940b090241c0810085a40703d00c4079858554010040c0b010500c0081540e030342c14420940000418a8050b81e2080c038034100404944a4012220320307500244940c0e499582d001e04d1442e031005028092002c1e111190400b0090400d030f81d8484003010b072200d07041c15151641034001d68011f120580480e1011801001042141d004040c440343c800d620900000300035038070780d80380f80c002c8034005001845007a4540328220151840c1850569041c0c1d0001814407640b603042200c0d43c034085051000d06880e00b1980c0e0024130354403d502c0080c1015464001031002d002200603a860303801404640c0b0b048007101441c2500c40415508000715600c0c440e6500c070710 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 403349910 1250 403348660 403348667
    0x130c1a03041b051008090c1c06153501060801140a05010303050f0d1b210501210203071707150809030412030201090f03030b0a3f05030313060b01 64
    0x76038000030700501101c07404813421940c001c40280035181910a4400503a0304e17032030790101d040c000342e02c50301c0010040f10141001019108030003180400602d2001d410440028480c1d0b1641741c1c4602e01e228107008180ca001c5c046110301e21420301076295480d00300b00203030040055101c140c0000140c420900350381d135510001780482d9001d00c800b03404142c0801260803a00d009000a0020b124a10000680c0742004250103d5102d02d0680340408601c0480030710950601642c0c01e50b21000080e00d003441150305103440c10800125604611005514202480302155028020741d805002300c0c1c100030210381034002a50b942da50240c1303d039440c07100b110300881703480520603400c6501c2481c0240c001c0d440d01380340071914401d00c070745038070f00350115542c5c2c0390503074001440d0105d540c0045020f940c0101d1010f00d40c100300290510386e0380c04004c405002ca6145a2013140341c5100841015040c4400340e205c1c1040314003a01c403498a10310080c1940400010810364200d8400b1741840d841c069001040012104c50066 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 403351160 1250 403349910 403349963
    0x15020a1103121308070f120813031e05070803131a010602070b090612180c010c0201020c090901140103080319090221030f0a0c06050915130c1a0304 65
    0x4241c200c03801000a650f40512450760540540300e560030900c1c09002d03031501c5000c02c0030200c00312541c00a407488120303401d5000c018147c12881c10601d04070320004958000c1c111181401c0d24000407440306245e4400b0741e025a007562501508440b00c1962841c00d4010b020070408580f00449003186000c00d03e81c9228182c4145a0503a4001d800402115007444803498a54020400d42a0300c54001c00c8103040c01810286030900601c101d007071604242c4005a101400e2901490300103040000c0d0850306000f40c0c0c1d001410158440056440301d003251244280740c8c0c09042507142c44402500c803c0000030402c00d00300006c51103050702118003607201c1754209923a010b843c1643d101950250b5286210700112541c040050380e0f010407401200e10701480c003082c00c8a0b0b81c10402d08103000c9034841d441007050080e54005e03c3e84c00100c06010f0404c13034980b00e00000060034040c1c40b1003180e100d281c0c4107004001c5404403040240207801d046c140755580182c039000c101e0b1700480d0200e902c012484003400a0404070940b9 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 403352410 1250 403351160 403351177
    0x1d060106080c040e0a021b0c030c03062809050706080f09011b050306030a1e020103060f0e1305070f0b03190c0206070c1e0507030c0b03010b04090903020a15020a1103 73
    0x510f881c0a107400c10030100850041c0480798800da007005950501d03510004d6800240c403840010788941d40d03800c020142407035048801c0b18040e0300301c1400c116402031450343e0990310201c4200042e0740000c1802940c4002d00c803035040200548501040030540c00e402c01c8115205031a43c07d1003c0d120780d1200d00c3c040c00d80d0b01c21268045415010380c2c1102002d40280c3c091903118201a0032034844c040507840300c403000204440314400d4400d0525808007596898064040a090300c0040d05100d545042c8034120102c000034a00d1400c44082d070a814100241800f29000a181c401c82c0030a145484850795034040d4001d1300d85212060709559846036404a0b40101c400e0400b054028004582c0c400c4001d807000088010203e50004411110b84c031800c9c0c0300a2030000c1d80e400340300100001d904505d808541e6030219009644940c030b0910040102d980c015040340c040e2066940d01086203406c0e883c0507850440c0c3c80100508405015181080c180c1a40d4082e00d0720b09415034a4002072080c200e0421340b00d00c42e1030038 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 403353660 1250 403352410 403352431
    0x503030105060714060403080a0c0305090c0603130605070305062706060c070317070b0105180703020d0e010c03090c0609050609100207030f050303010e010e07020303070806010908011d06010608 85
    0x4000c6031500302c028080c070502400402c10343c04000b62015040a0048030100d0104481c0c10501c00410010300c0307000d001a0313441c10100040c0c10054181587c0f2074000c4403551059400000003107800910320107084c6d519600c4001403059051211018000e0301041300c00c82c0c0920342e2003041480040030880e001c92007643da081041030f143c8808041c8001d03684011000661032080c1e030800000503050302000701c11b100020101c01d403154068613000d1001c090603442188604007404445603510500120640c10800354200140d0b00c042d140030030805885a603030070443c40d52070524011841078044e0410007440d84a2102804030035107c40003130354104564041c01d81c012005220313007115400d0000500b10100400d004803244181d5994520700e0075486480111015080400104007030a515007095000d404d600c120034126251203400207540b130100502400810194102184859000790100c10190032100024002d50311300c080303c5140070b01841500d06251285200010f03a480c861030179039015856001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 403354910 1250 403353660 403353667
    0x30b011502030c0a05010b240910020c0a062c0109060e0415140a09020c100b06090901031b08010b061c0b060c010e070509090d0f120218010215071b05030f0c06010503190503 76
    0x806c4c02b14501d480941c54055100340440c0c0c0040d50fa070001060b000b001c0700d540e01680b84400b1038520001b039401c03d52041c1c0350f040c01c10580d20142e030000b1700c04007910101d10307020480c102c1c14800036010b04001165080c0805007110041201c1180e203000c40c21847c42070795030450003682c8040001c12449000c0d00410340d40c0000c4c2000e507105005070400e2945290080c122414021460002030140d40c0c20390003220340c3c405088101d409100e2850180000f4448000200941000303035001c101117116000c0305508105540f50705004142e030703c1d488030b114024003414070340d160106504110700034040c1542e201c08034070070407400184a01c2e040c0700c04c500c00ca00d602c0103084d811010400960b5455489001c250034021500107100c80d5421a1010b004040104610585855510b600190406031040b250381001d00d85107041202c0c0d250000c3c15204941c0d00002816408003403810500d086001e8400b400e88107180004211a004000140a6040c0e0754202c080d54503a40940c2c203210341c400500c20000b880d0f5041030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 403356160 1250 403354910 403354927
    0xf02061906150804020a09090305030a0b12010f020a0306170d0521160f0e010c11040b04020705060a050f01180c090315050403020115030b011502030c0a05010b24 71
    0x103000310040440545010a0381a10354a44020300000c901d26030000455032020001946011100d04000380343c01c0c1810030140700a81c4004140344402000c020140341c4460040f03100d41c0f201c00411103800c400d03c000300410800c049502019501130104480000d007480c1c00860b03065207126103503c0c000c01c030f00002d0420203035004040c0c419070000c0d1880280b51340e0040c010b004050801408600c516040408403045198600026100c080c0e01d4410004000912040c4490799130480c40c51142141c0018038890b100e00c45200140113861002d08482e00180040350603010001c0000f8418010810704d0340c14042542c030400c051518100134411411001007001100f654142c40764040041048585404081d031920ba03200d10b080743d00d0b0107018006456945081209242d070a04c40d44401c0030301019281c040d6827841e00d41408082042c0500b21450990115012590f4001c104444030003c50740243c414446003424424000c04029600a0255100d0b042c1c1c1350100101c031501d9440820008c00a50510302c00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 403357410 1250 403356160 403356181
    0x6011e240207050a0806060103200706330e07020c01020a0602070203070f080d0e0402091003050901180803010e15061909080102220504020405031c0504030c030b06030d0f0206 77
    0x300114803040d40a41c2802141d991640d40c15480a8060340004026508000c400103044403100615020b040d078160070000100041602156200340e00000b02107420284685e03d0b44280500d001501140d1211050b42c0b400d14509075030100071102c01c510788000968a0090503a2184040246140187c00c500e1601001a109601910b8030b04d0000d8100c402a50b201c5080f00110041c0c1c0d0003020483d4040f240840b041ca500401003005480c041e10154140743c0300030082505101001d000c01c040c15251400100c54003003d5100100b00304400e81352045114080c1440c036141c3c0d0086c0030f049030301e00b00540001d101c034500701c0c001c104051015005514110b400509030009800b0070341c8820400036486000102d11100340050b0007941d80410b6040380441011280305c00c101a41d6104a00540c0140401c0101da600483c0310212012014115251554404000c840702d200d90313000104031900300710000c0140804c4081c601d00c2044141c0407034207006401c88065410000c2008840010fa20610005101700321 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 403358660 1250 403357410 403357469
    0x4080d080c0c120d0c09030b01090e010f090305070c06030b1305040609240c02060421140d06061b050a02010e01020c0a15081602060c0f0c06070206011e 67
    0x6540450a08988010441c101403d20b0400c8203904004211802c54001034492508400f0303c03401c04102036455aa2181c00d00101449444002a60f81c500110b40d10000e42040d1005590a03604012544642c500900a41c00541050320751041e081c00106240d8020300c614200304030005c0000e6180c0c171508000a01400c0300610481d402e07502d4520702c00000707000b1030484160320541201d4230080b07030703005461004840e000f400d0001154840024000820240409004c03882c084841c0700c1c180c03100800056524114041c41060500300000707210280d01c510740d010b5420b4940350341d25100094018801e5002034a060900035141c2e030005000d010042d80200a041038111301801030343d042c54003c100280582003d907001c1180c104014004201c100e5001002c1a40501444003c0030f8988052200a544200042c07007001c151350000341c013902140c001011f4405031803960342142c14a20700010b009480d00d8083c86940d950b0003848540561440d0079400e0002034450408500c000e42c1307090180d009082d81c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 403359910 1250 403358660 403358671
    0x5010608090601031118042a03020603060d020307260d0f02031c0f0908030105030d030e1c050f18040501050f030309040f020706180b10050109050d1505010603150b04080d08 76
    0x903456200051b1400c0248169446035015440c20003010001503a421703200d000400c086100c4501c5041c0c1400146d03640c0b02540e030040410b4515001c3c01d880e51003c04e00e0a14542c0048106403040598480c0607081048401000d260007820b860500c852404150f40440344002c1c14400740e042440003401d004442015500030070120240030030700419011100c803c50700f2800040e648072000100501c0b2034202040184560340d50791400700329500c1d109401e2a25001c0c14551004a0103d0442d014a014420400d40b0b119007110801c0303030390718a03511464103044c10b03400c0c1d0042c0c00f85041900010b010715090b808031000030b1001d4065850582d15000b0000200308104000551035401c1c0841030101d81607200b800480e242e0144405003091050500c40700380030380244698298000c00c4414812a6807084418044402c284c03440001c0702d002d071030450300094180d55803240725441d1000015409130b15410100304650345644403d0b800d0f4039581d80c0c0a40303101d10f0150480b81d6000314514041180703d00030003075001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 403361160 1250 403359910 403359919
    0x100f050a1211070c050306150907020102071502030105010f080702060c0903250e0f090c0103020d0216050d0e010212030f100b0d0b01080108060708010905090c03070b0d050106080906010311 83
    0x8510100c01c80489020ba00c142d070020001060300400c01c0725143e0b10502911003140141210720b00741d0001038400c4040304007107004035a030b0404900c503503001f50140c0c2c0b10241d0000704803489140386d0f016500250402d120300e40c00030350000002501c0c03d004440d624081d51659000c1c02465544400f00d90641d40801840e030b40520407490050003051069120f40034072a0108400c21090707207000000d0350421300c064064038800008400b84500e04000013140101102d00382030147c0c8030002840000c00070b000e0341e280402015641d8034040d0400c80d001c50700e11403969843c1c9425000503500c400481e51144581c0b100c00f000b103800c1001c80c000c10304044070749902c5801380725000c003e5a02c1340d880503280d0300641d07101c40c0700a464a003800a80e41c0c01001d00c1b0301400c00c1c07034014100b902c3d203800d006103660301c10b12440f544545e880021500c188414003200c0b101c00c002034101c85d652030784c50044014550004920f080310394901380020906511940401d4013501304500240300c0b90f42180c4680d642081e8031007149a01 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 403362410 1250 403361160 403361177
    0x130e04120f1701080105040615150c080405120a0c06020102070f0609020a170c01120c05032a0c070314010509150a020d0c05070203010b0405070c061e090b0411100f050a 74
    0x60b0b4150b100b040d01810103100007180c1c0c0e040030306d407940a6900000101191820400003072244100500003800c102c00180ba22090541080c01e00703110b2403140d0382103543c002c192600220b608140009060007290710882c032110a40d5034815040b4200c1c051400004c00c83c0074070f03400d2080070405a8000d004218001822014090359400c881a070b1041c414000c035615412680c4003800c1036800151546000300540001d010342011070000810620005050441007080500516031420710503105818240b40001c98555400180840c540e646001c1e20045821504840d0798520460060003250300034501440200b101c245101c800c1000d804004001c03020240d424001300c1281c800b07a00818100301e0540c0c50345070f581d41843c0181130945a480054501a0381844180940107030301c60002004c29400550019800c4412803e800301010400036803030840781490040c005211508032410301562040c002564100c1001043c4a80d807901c02000401082011035011350640c0618010a4403101c1890400382 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 403363660 1250 403362410 403362437
    0x1b0901180911030307030206040614190507030902120f0709090803190906060905040201020f0f0c1302120c031009050408030c1b07030b0709060816050f0409060b130e04120f 76
    0x14617000243c050b00143d11590502091110314410488042e000d0000b096042c504580c0c01400d5a44400301c484c24039640d03100190a01c0d02c240e12491181d0f0f03008001c0042c001c4000400b55854101100c4800e01d80546000003d1450a81c410301c0381051780304010b1070540d030b5084100450b102e22040300080e1a502c9885100019116200c0c0001519000c1f00000d0346003054000285441042401001581d011010426031150001038011102034201c84850003085504d0b1050041d01502540fa03c140d0310706c1007800346401401015500c545100780144080958694902003602c5046d180508110000c202050410140d90001d100c040400310300b0020000030300c0c000500e0054541d2061740c01c2c001040034443d640350b004040c240200708601d0302608a0906c0718412110070341001e4440c042c40400600c4014420b045000c0e02c0080a1030601000140da84011010842c0c3c804942c0b0400440c403000080703107200d00701d1243d6006d640c1242e00340b82451000c0405407002c00041001206020b07020308106c1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 403364910 1250 403363660 403363663
    0xd020d0b10090e010c0f0e0d02040509210a1e081302041b0906110f1e0703120201060603110403050a0605060a0b0703030b030d030b1f051b1b090118091103 68
    0x5151900c1c070f070000503a42c689120010104103040c2000420400f130750f02000752980e00e0101800b5460380440700060030b83c58100550303141458000c20303c900c030b65000c51180e201c440a03c000c2e09a485441d01c601c0009442c0420801111466500550102d030710040403501d842c0c88541015180d03840a00001181070010702082148444085948001418a039083c40410790003c041001c2e00511402410f200f1180b604198503460120f07100d401442c01441014071040c010071405004603040004480c2003102004002e01801250103000e0219007440c00c1075900003d041c046504a0303821501812003c047c0382d440202a00c0042c2501d984241e0f0000045000040300e0000e01900b4440d0b100022b40400003004d041c01c01c50601059400d02d8a441000422500c4034030f20254a0b19541100c0d00000c0810302d4151124010ba4012450f4036420140c0d40030640b100280280740c00d02e00c0c1d0100309400c092201000301668007405241c00b242c0400b41d04c501c42021b20b40005000328861047c8440c105200400b0a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 403366160 1250 403364910 403364921
    0x220311010b150d0f110406050702030c2e080717090109060c09050f0a03050a12090905010b0d1d033406050612011109090603160b13050d020d0b1009 65
    0x12020a50001c1c540c80821018480c4e400c0304840d12405001841d401055119103008500c940028024001030f41c00c21950140082c01c1800801070800342212210102e00405010f0010801940d26150300b0900000c1c0c0034084e060310544040d5510745081c20551710442d0b0143c0050309064007503480b10482c60008a01d40540703114104071395552804149041d08000700c40c5945004903004070201d16080c4042500400c0c0001c2d05a009661203011005051080756442d034246d00c1042070307501d0a030000c07038002c402d280240307100c40c0549814000c07105001d29240d1940c0300052103104540c006c100c41d12035180101d03032220000c210001142c9503001d081c40c0c84124180da0a10489071990303550100321151801104542610003c20000c01211200c06007408075481410481407044501400042c840e039010400480740c603880315603910403255100000409a041000c6019107a2040a404500c41c1004450f164100e030f00103154501188140d120076151080140c06a018584803000109000f807a5010700f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 403367410 1250 403366160 403366189
    0x3180b161d0a1e0b070c05151206130608010f0e07150905011218030c0309080d0509130b0d050a03090b03042f0d0302070509220311010b 60
    0xe151140340d024004040d52a140c20040c803007110030961445035190b552907802561024030428070140c8010080d144120401c2e800b03c2c802c240300007030900400c030f40407001c2c40850750162400100c110440300c000406000d900078820102c004500040c040e13203030a000403003180700288000500075440b902c0450960f1550202300000c26150707801c00141d800308201c2c02004aca21523102c041402c083d0000100303880f1040c41020b0410040c00c01140d03242d0015445484001c007001d480107080c80c42d91030301418442602c80300340c2c0803c0c0240f000044d488004140550300c824180c3e14180b801e15882c0401290b81a448090b1640c29a141d4076401d05440f61b0580700740075401400142280002843c0003025107a043d003156043c22024424480058104026031846010030360029050252003090516a80464110140d0180d8883c00744008d05401041041c103032042a103501c10595181407121030a00c03d1800c4403078441c80c0d40818540400d1044e00025559000940081150350441000800c0307202020503 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 403368660 1250 403367410 403367431
    0x50a1b0c0b0f0403051e0d09030f09080c0109030212030c01061d100e0601120f1104030c0e07051204110310060801052a07150e030403031d090103020103180b 69
    0x40603010301c9001080168030012150b41504140b400d59030041c984e02600203400181250000a180c0480801d4169800c0c0404244200442c041c42c0c00c0040c0607200503003050002c200c8511001c10408408610010710800c180c48407801e4920715400c0c802c45015559040940b4001405285503489003805008000c00b0741e07504440780b0380d0230424580c00d442c1000d0500c5c5041c2029040c1040384030802110f2a512001c00d09120001c0a410489003000e8001d2250072402e044c50554402c01c010004000350099034011010014641e441e84440c90803030005480343c1001c55801d0180142200c4c0d03800f00154018400c1c1c0c14000b4415840707000c68502070644000749500c5403182824040c05809204580d8040d80195260f20f444001c1240302000042040c0c141501d80400142d800074011004c6a140310b0501500e41040781305100f8103034a8407500030707000c200c0000d904066841c2900a4100c020a961200102106200d034610740c01900140740d14002d03075984508284091011819850b21130b80300382c28030700 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 403369910 1250 403368660 403368677
    0x70b0c030f0a06030b040f020d170301090b01030204080c0f030708030f030a0e0c0a03060f2406080f01031e0201030603410703110a0305030a0201090c050f03030904050a1b 75
    0x207000d2510440024990b00000b49032070b8080021a20402002d40c01c150002140000b4a2550000c9641c1e1900b9800107400348250005001003e003c9030021412540f105e242005031003030300b0004405134840c0d8441d048055000b0007110981d8075080303202904000c001401c841100355030701c0e921411034100510149100202104201d403c14150241d0151100ca18015000b0701c0c0302c440024180c80700f04e01002d024181e840c0046803c085080c0e01c81d4481e8040030b204440840c1465150040c107442c60b005000c0012408004030306601080d41015041e0f9601141c04050000e105400007481504184103034101920f4007030010100d01c010540c00d80d441101c26141b0600ca007040da01d100c2c3c0074a250703181c400ca03c40700c98203010302070408151070040d40d078041031181103880503000080c044201900064558000003560015064055002c94500c510a040325194a603551081000784da1500100b02d4064204000300300303041c64994000c5500c007081c2c01000405150303d02c0a0710120104040c141c0200d17a803003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 403371160 1250 403369910 403369921
    0xe0405030723100f02250c0f0f12020a03080f09030c0906030a1b0e180106080d0c02091321121109100e03030711131505060a05070b0c03 60
    0x44910308100203000140340840b010545516030348060320301c107100d001c583d1641582800c0308590110b850b24108443c0f40b05204501e804c40c6001c590022008441050114800003945005480c4c03480881e143c0810703070000146040d0025551070500c82d412a4840d0441c040400002c42003400782206c004a0380142d034a4007903403800e00d8a008184100284550401e40c10083c8540d07000404011840d4081d51044540039202c00000704003c0175007001c041103040c84100421380c0700f0180c070582000012402408202e0b0b0b102419503c4005003109031001542003c0468003505048014680003440865400040d0741c040d168103411020450045400c50403480607070100c207074020001c04000e1f9440380200188407150076000800e100700e01c42030f8000c00020a00c402360034050a07600d00090005803e0340e0b581c00452a022091003007070078000744285403211000070821514491000c074400d809041c40c3c1e03207609140810040d900004078140821004010210002c1c0508045c64014100b000b186622400c03c0c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 403372410 1250 403371160 403371173
    0x7140a0804030e030a050304170708070b091318020603040317180c03060f011202060c06090c0405151011010b0a090905121c051518010302090c0406080a050a02040e04050307 76
    0x4484d101340d004550020220300013001300c900703c03000f6410340d016180c49440400d0500042c0da0012120b070003031100000309001e280d0b0081501c110111002081c0300007080d1540308840810442420b100c4e4102c0e80b090050a00c3d400071a0054000d040414160f51a01440b01032560100c0c1c0d08400e0361143c0b02c03140507131542007000800c00f00f17040700600355502d0440822039503028144180841c0000101c0321409649401086a681c80c008005450f00c52a00c40d0603c2e40c0e078020360a06a005503d44400507280b01d408841001c00200001d041e409801c0035003c0850b6100c622120040c800e550320042d90007903503201c0405000500d125100407840550508060b414140c42c0824000410000c100c440d076140d24210352580740d240501e070006415203c000004078602400650f1035000b2800c496001c40b65118003966604030f074400c88036414a652601d2400c3d03450b000d98401c80001c9451540440c81d0021541c100b154000c00f108401400e150783c030100c00808020a0764140c51b030381c100003107034001c1c03000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 403373660 1250 403372410 403372427
    0xb09040216140c040f270c0e100302090105090411040b0301061806090509030301030807080d1409030d0615090e090a0615180b0a091a03010c090e06040507020604080307140a080403 79
    0x300120b0802c0041c100c9500d003110131107903251b892030140c1902d4040c0b0420030a030900001508581001401078034088402c215616400d0000703a100d0380d5210300000d0103207048003209201d01d40c00181c20100905002c10310020744400d52803103615540303624010940003405050908003260180c00400c0182c5007086450490304060011b11640e04104018004078444004603104140d200003141d9550b2141c0b0250402449005030380040c0d4110442804011100040605800318504c1401c014032641c6034011680c509201c514200824840a01040035035241100300740d002c05c414007561030341446640c4440c115051030fa1107403031005050809211450044580041081d4000d00c00c02140306283c0003d1032a14042c0700e00740d485600c40340481192840c2000c0d03c0c0e400344020b030007409801032492000c0d00c0c0da045401084403806c64040000c90300e140600a55010704611340180180b07031210349421503543e2006040c0410301c2410304002019003040d1300201070314112a5264006400c2c28900100343c2e50 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 403374910 1250 403373660 403373681
    0x6031d1c170417030c040f060903021c150e070306050a020723101802030d02060114010306180504080f0c010501050a090515010e15121008070b09040216140c04 70
    0x700420440010040d00e00342030200d84440181c0d860b552000d0100c2c13950321507500440c0003100d403010005420364205281c001a644211100940c115100c0c50310200c10100c4400038040340440b4030390540152480c0d014080844080c015154500e1301ca0310350f0015a613054070720034985640040c54006000002040b91541d07602c101c01d58500c1400004030560f51170301c10400803000d982d02e409140351070512450303a251495010701510000100f50ba40030b0740b40c00e000d1040b4158010510300000d815031092145070291102e089407140c800403101c0c1032a00a103030017002180d420b10b04000201481060300c002d045c040b0710039400814150704200a10110300000c3c1d000c0b1154034140b8043c0700021185070069100401d080c83c2440e00000e034040050010000a4422079030903c00149018148840e110650b00c1802082801c801d082c1c0c1d00c210a40c1c0d1288a441040c411b03440920860320b040c030b010780040c000e0103008181580304100644400b031840d86404030b2130860741c0c0140d50203885401d2034019035a021 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 403376160 1250 403374910 403374947
    0x909110406050a18150503060a05010623180d0b01030602030601020c0603090309010e1c030e0a080a05070b070201050909010b0307080c031317040803040b0406230406031d1c 76
    0x3d610b040340c0c2a424003140b40c0b24070300f40e94981c282d41d200600542c0644008110007000c65034907007030087e040002440c081c055400060342e0701220018811000d0714048003081040c0c02a032928401001d0200855515001c455111602c001d586011170400500c4c030340610300545005030340e400c2840c000782ca040340300c00032180110420304c1000804480441510710700345003820084440e5414400081025003e80c0c6161094568611381c0014554070001c40c02d100941510443c41c00c5e40c41c1c10703000f980c0e103070040b400418070b034481101401504406000f510900d072060604030704200c8044001518403800360044501c018001c01002019a032000619400c00c5906020034174604004d0060f410504095502031728403480c030215640c1448142d412075000b451a28180e1340c64649902c3c100c2d9550317102e0300c40e20000a4010003030100480000d03042d62005034018009624080c50000c0c254080d10b024240988040e0110309d40310716104d07092200b480b410103c0c0e100080d2100507648084c0101d501c8402d401c0c102d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 403377410 1250 403376160 403376179
    0x31106010806040f060c1e0e010212040e0705160804030b090607080f06060711060403060c0f03020406050d0c170703020d1415210d02031e090a05060f04090911040605 73
    0x4ca408902501e640d80d4004d41c0102e801c1c442100700750744481c94104600d040c001c100f074410b21003503031000030550001000da00390f03825617004a0101c4918020b80c0501f070b801540c0301c004030760a540900008c00302008070b100c14407110001c40c3c50b10b80c140c2d0002e90056a10140e6041000003c03442030106541c00055820003c1c035505001c02c0c882103410780280040d0264200007100401e11082600e040050700c00208050717a501d86910f0001c015001c1c80e40b0708404240d2041c0a407405500134020b480035107000361349290401d00021912805010204130030f00600200380003d501c0110401e4956101304420344016a940e46403010700c0c2c0846544000585040f200c001c1884140306071555210038203d400c840240071401d10801a22105480c000103130201e105507240268286d4011010304100052050050b50501040c40c01c841d0510501c3d108550290703108405000c1d41c505400070300200004d402c031580c1415140c0414804981c503407017080d00e511500c8902c103569440c1c80c0c040c801c0503002c00e44140c500e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 403378660 1250 403377410 403377413
    0x6040b07111005130b010b04061106040b0403081504020c1f020f0f1e0706060501020d03180201080a150e060a060906200109080f1209070b1b010e0102040303110601080604 75
    0x45901c2c54000c0964500c1e00c1e800440c20242c2490501d0404980042e607111065a50303d010000c0ea41c014403904010038120301420600403000714801c0d2040740c00c02c01c03940155980355021a100d0702c0c020300032102c2c0c60219030400603a0711740d4405448035a04c420014040203601d10110030982403d14644070b0107500401c102025001c80c0d0064407a01030700c5101407511a6458201070f5005804172400701c0504a011444c2c00510499400c00c50864a0030380942d6014104420228241d86c0e40c04000d404808500d0349a2006501c11700714168450001c880004001d01080798081049006a0114012034142c0d400c3c05500e2600440c541c0c000e04141c01c00c0000a86050070140042c1508031000540801c6a5440405074a003900810321066100c8140c072b07a245240b0781d4003080c1d6001800303540800302c1c2600029000c0d11300050300306c0c141c0f19104652b03400c008103c805406415030309208034025540326184103500c0b070400d00290000e14800c1d00c4038020031503040c3e1303554035100c0140c1c05009180d01c0b4009000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 403379910 1250 403378660 403378663
    0x3050609130605181204060e04060b0304030c050f06090109050c1002060105130905101d01111c0f1b14092101021c0b040f02040506090d0c080f06040b0711 68
    0x7061540c41100820150781da420a030240d20440340c00d0700e0707150240c0f050401050712010000c2c01a20415142c10100b40000303000d20080361558002c1400d040c400300041008240074409000c40c0a12401c1115420a040101207083c01c8041e80d0101441c0e46a2000030100103003809038000e039000c04d548006c0c5c03203500307190001e6440b04c040c0b003414055840303008180300a0825421034030000360007100311a0303060b1180c07049034018000d481a022042040109103502e031103040c06610700301071049001ca070a100ca0144140581c3c001100603200c15130341d0320200c00c400340942c002e4407d00032050220040300440380350080c1c4600d50003c4007440c0500100165044c0303607511240c1d1106c3c18142101624100680c44020307009104403811900c0c11003100c110081d01958070b0b00700f8402e12009440034058151825048000d81c01540100d82d440b1500380b10184840c2013800000a06500074918905040e82d9001c1081c280081a444135215420540801040c0024915a180c0140c140d26104440c0e0200d2074240d0b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 403381160 1250 403379910 403379941
    0x90c11071202030a06050f07112b0306050301060305030d0b01020622060f0203090609070b040b070605040204230f010509040b1602070b0f0c0d05030103020d12020712110103050609 79
    0x403901c1014941d802d6403000c020400d00d00b580900100028208042815040e0720300301c8580002801c0f1004041034160f0101e440d03259140060620140322003c0040c0c1800382c0c0743d624004003050359640d40055580d8007400b60000031030180010310f41e521840300001d000c0c2c4080d1009203040d584007000384885448003100740c0001452003580328005031400c0c0b40c50000341841c0c1c00d0902819001000b4031042c030b0790100700c0d5401010390310708541245a0704d41400e5143e00580c42030001900f02031000d1008a00a0303000715070b03c02e20040000a000400001800c5018200e82100e400c007074115080241d80c0d544a500c41b805000201e40340c481914050f56510119040200150200301c0c0d01000d0700d010a00821400e40580f0700d12084944403040f800491403a600507045030800e80c0303c0c10490480160040d4102d90581e40c000c1c20720340310394005481d10341c100514a060007045201b14070300024015a03010744128031a00c20162000007070b0a410004085c0d4030050800f42c4218400c1d070610130491403c2c20305 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 403382410 1250 403381160 403381169
    0x1050a030b0702010908042d0f050927060f0903030c070f06090209131b0501020c15120106050403110339060409060806070309020109030201080c0d0e0601090c1107 72
    0x258a41952102e008a0250607910002040e4520114002c00d0b1a03014090110310412544401d440464824084c40718246a40c45550b10651001606000c00c2c20145c1c06640e001c400c0b106000a401e03129400c0c11400000b459003130080d90042c00c207100050480301c490350b80105050000f1030035410100d900c14554421070800410020000641500f04603050700700e10f00043c0c004040c10b5143c03400102d0150405000d4404844801c0c20f003640414405403550030806070b030410f0313006051029610081c0312030007000421801014505000c40000202d901486038064001680e4082d1114038500c3c02d030062040010310301303101f0381040910042d0b03021826841d58ac10b5001c600c1c1c43c00f04c04040c0e824040d0a9200d942140d41228000902003a102243d81009045619440132034819a07103556048048840c060720007400218020010009507214079500364000003400d04c1e06140032501100350013103030060100f0b405107130450001049803401c5481001c0494031541070550700b8100440b4402d031551030a008 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 403383660 1250 403382410 403382423
    0x90e0f030702061c0f0504030f02011107050706050a090e090a060f0b030a03080a0209181006110c010302030c0c06041505010503010c0905060307170a0e060c0405030d0e12010204062601050a03 84
    0x309a0010b40b105e0300310503030380006170008102d03d0500d820010550400d64400344e0156003001020042916004101d6003d150000f01500c1c0c45411300340304941c0c5034802003070030082090310000840c0f080c854540c142c0c000d50908004001c080c1c09442d00b24180c0b43c0142d04038044601d4001040603c3d140400c2c2446140c0d4103141c1980d155542c0640c40c8001d00a103100c01d50010245090341c01019150600b50303002d43c0c6407000c80e00980d41c0d04c2c101212800221886001c0a41109540342c0055029801464210303001341310312030500d0280d18030301e440d111044901b1358100c1c90041650402030050310801d409404c042d8002d00c010103421a01a229890602c40c10b40240b5001000400407880303190f003600140a545014026408c051303158402600320200010050f026080108100001c100c2c21a0100c1303501030068600702500040644158400e1440d0301d4129800700e01918100c9404e20003040a802240c84483c800c500488188a8115010070040341004008006014a40d62120070720308403a480b51 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 403384910 1250 403383660 403383697
    0x4180507020118030203091201060812070f060c05030a110301050a1e08030a0519030c0e04090f08270406030221072111090402010504060c050307020a090e0f03070206 73
    0x80e812401000c0461115555101d0600350004240c1d011008045521045400c000310888030803c0a00b02c5025120b03007031050b400750500007004514400988490750092442d041e07848486d072a028203590540c5032140005000004024000d5014800c04a82c40140341e44c150456052001140c105802e03406950a2200c262036940000c2051070350b0070010304002410f4039215000701c0c40c0030b00381e40c020960301c1510a000c0060012814400c0c49a1081c60549554040240c3c0124091000804080200740c7d407541d50340b9403c2c0049441c03200109070040c0044048004100034460203004200415650703440385040c90020405a5210109a907150211a1100c281004401c2c2c019240c800b482e170058883d0f820800614241c000701841c1c0301c00c03003030003114503034002041e12007001341056080b03400074041f039024481400418855911300103050720800403a898107040e600018000c0096910500c0d00540b42c4590300c41468042c4000385c0b01e402204002e41c1402d07101d5001a0680c042c1200c191013062f000c0c03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 403386160 1250 403384910 403384921
    0x807080601051b070807061b0c0302060730110616050c15070e2803080c01091401060302210d0305062704050c0a1404090204091e110105041805 63
    0x11000000703e481c0c15011039003960f6903840000d407503c2c85407181e00701144030050740100790030038a410a02e003280c0c031088040405003540d0030000340d60090101596130901001c4140310307042c00101003c0000c0d540c52003410400b002030900802d070008146c040182c0d45c200e0000d004c900c001d1003d00350f0342051030f030401360f48481d54002c00600e0300380c500807840e6440c41d50a0034402c03000d0308106540074011082d11310300c115191440c108128901994081442209062400c01c04075072010007805214000c1d00022071111034a80b594440303e00781182400303050750b44500820462034400c400d119002b01c981c6a80d1801d20346c41c02c240c2e4642c01074081c800203050300d4000166039952618501c86460b030200500c00442c0840c50400d0440c2d913405c4400302c41c5440b0710000c601c0246868040d440803a6070045400c1082d940341c03400d01003d0b0001c0316040f40c2198840394a000012000700d07a032600d42c826140c400c2c40030043ea040400c0c4188604c61342d40e06000b1308200501c150751011443c5480c507500141d0125031170302d44 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 403387410 1250 403386160 403386187
    0xb0702031f090b07090f09050702030313020111011118030a0b0c090103090213090b011a180f0a03051c05120105040e0a0203031317030405300102070b04060c080708060105 75
    0x5400018010f41c410000c0000c4950448144000d444825040c01000d80d2900064022070310151a6039002d60b0044c40000d0041c00107800741d0040304d02c1803500c0d01001d002d4014035400d5502d8805210700d08000400d0004001c0d1320419501020f400807001041560660348403000a800c0141810516440000306a4000e902075000110080da01602e086501c68030440c9a0004119500303013210920540000010805640c0d8640c3d84072454001e141c520f80404240044280383c600228141c101155842c00102589e40342410760040d40188050600344503455405e880c00080d000419007480018011951040b405d24232140c15150103a0340011000a5914200c0c07238000a810002c2d4544030000c0e440380300b00b00d8403011008942d020102e031511003007203103c03590b201d0049000f1143c0000221301a9030303d20301d030040a2484039a01c07001381d80405140914090030390707000700d07015070f00346d003000b004e0004112082c480d441d9072420610f17000d00a41000a00140310010207030902d410403001003110000c1811 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 403388660 1250 403387410 403387421
    0x2031b01050a120e1e010506040504020307060f230a18060816031b05090f0603010503060406020f0d110711040207020907030218190501080603060f06130204081b0a0b0702031f 77
    0x5080c1c2101c6091a003600f2000c45455411700c1220b081d420000800c1c40707410305004982c0120385c0200030b00381641c20401c0441c3c205101040000401c0703d0340c03003201081565290040b080e0079140030100d40e100f03030700d52010b4006071546810200c6400000c0d81080030540c4a52107a4118004401c110a8513448081c12070140c00c209201c2d102c1d803900d40f5000c0c0000d642040081075044001e80d40c038044d00c84148100704441c0001d01c1070170b42603080702c00010001881e035401058800c00c42ea900b607007060000341042040b5a07190147d111225400a900b2092122451002000e1002158190300d4400c007a40451010b12020b440c0708181a00480d801c80d03100f03035140d82116120006020901d650840204035000c0c0c002521034a8017140001012513028100410002c0c032641444d0b8000c011501d13007505002580e1081c4250b801c0e207690910002c10202c07018072541d80f0482d01d05403100300e0b07800510304000345031040c0c1c0e2109a80b0a001c001d901c005840c0400c0501e8004001c2d524620407408241c9074001404 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 403389910 1250 403388660 403388681
    0xb0a120f05100305070602210a0c1a01030b0c03070f0f1202070f020a1703040e150d0308090c010203090f0d15020325020a211101150302031b01050a12 66
    0x5040c0410005503020554002e01100e00500443d00340559984050b40c50b03003c0d0012203600f420300451007841204042c0001d010b111304500e844d051070b50140e03c4500800386616801c0740314490740c5004000303000b0b41c5010640c000314800e01d22880c5050002000c1d10325030707010b40c1c540144000c10004841890049100450340300050b44155981d42407843e203c64161040307401280304050b03018001c03030303400300c240414130740a0388005c003c40c036103400d1503452082104020f100d121001d03101e400c07031071164030f841143d000c4052207030301c034020581085400f05080c60740d0011030300d0440d40306110011301c41c3c1d100d0442050360442540d90058460700d42c2001010850340702030707840486000105001a503401003280b140f5501019031400c120b0030710702c102243c41ea4042c003405031114035404010038500040c3c481c0400313110906d040141c0403040c913030303107541c20742d003200c00d0303448400c041d8440401c1941018416600c501046d0b030b200200d020004000030f045405001055020490f4820070f656880034503900034418134 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 403391160 1250 403389910 403389941
    0x11a01110c0405160306090603080f1305100f0305070e060d11040305010903021f0209150309030c07031101090605030f010e06030a080d1a0414070503070201020909010e0708100b0a12 80
    0x2413500303c01011004015868903000207142c0480040c1d040b030b4601c00c0f1400d980d03200c0d14030342c684059000103022030f42100c0760001c3d107000d500310f00043c25075401c0d084c1210f000f800d071610008000002c0003c2c007100c40041c010420702080714805000c2c1e80c0c50108035039201542030800102c00c5418072041c0e4286c040c0c0e40000b00039610b401c03a440185034002a4403c04000d150340f0310b410105036802000c05a004a9001540005078944000c2010312820059644102680116030608480500851801101c0d07070050b104a458103403011803950340200b20101812060425a1450424074510414114140b0565404020080100e481135034140010203000703400003061500c0f07500c00c5448100504a203141860380381400d03882212141824040c00c29827082c01e083c107054a039282c050035176845e0300061400d03007155402c0141300b00c190b80300660140a420781540d41c16403807400420260101401510102e9008940d0508100300c07a0004100c460501d81031400f45001b000c50540040a40b64000385000103 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 403392410 1250 403391160 403391171
    0x18090601030f0c1d0f0606190f17090a050727020a14130e01050105070c14010504080a0809130b09151c05010920091504111204060b100f14130e07020d02011a01110c04 73
    0x4210b400244962140d002d50f040d072b240659648840f50215100c0d162403f0840d428480030020101c441e4060601c80217907081842c0c42e201b848504843c0b591140040300020522244140149080388a032240035207000e00f0030603e001507070b8031440722606091140e0f151035032007000e9154581e4402c4050303400400601080303403000001480d21501d15006410074a005030840c2c1c040041000b0180510006000094555a2241c95050005020059520685400041220f4003144100d800401d800925001c3c50000410400d24903028080c052030200c540d0240e501c841445010341c0d50702c04080c4e041401c400340c0c82e400d0800320340458040c08800c90b103401d031114089001022115030400d803030310843c4100020482090b601c0100008585882e4600c000100840307801c0140307a0056043c2d08400da000c0301458140407045c0c24620281482d40c211500911010007409150354040001c8041e62200340000e00c1040b000c4080c848403011a00902d50402c00c0d41c680c4000740d84004e211313042c040da2007d00140103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 403393660 1250 403392410 403392421
    0xc090203040b0403020f03041208090f06040605040e100302151605030d05040b100e07030e030702100f081006020c09070509090106080618090601030f0c1d0f0606190f17 74
    0x1182c0720895042c2c015005460500e4820340d400300c12902610301d1240c03d0b005950464075210b403190000d4a06a030000c070039001c1811f15a0781d000c00b0b8030003401c0c1d0340c0d100c507500c40c1088400384182c10050042d01c0300300c41000d4203000580e600b80c441c2a22128511545448850100c13030301e1180141d07104040d0440c000010300000c030840700c0d0800c0c1c1c46980103550048298840004210b115015403013110503466400c0085104203101e6005000c054046400322130034044190001521003074402c0c0381901007480040c5c0107030050b41010003154400407540c15081c440d490644040d45444254142d2442403a0020018505c0d40c010402d4408140020b03000048540e150751003e06030380829100c4920030014026448420200002414461a1040007a00c41c030707440d607a44c00c07050352007100c0100d411101010003c10018800300c0c8111060198002081032820600a07880b0400c0d00036141901405e8104995146003181c1c041100510060345440c034402c0818a408480400d40d0460000464600d08103000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 403394910 1250 403393660 403393673
    0x705130c02071a090a0e130204150803030a0605090709061209170327011a0d050a080307050a180b0901120b030f010b1201140708070306050901060c030e01140d090c09020304 76
    0x60703c9901070702c0300b695071502c82c52800703101c0c00d0848047e081503078154807500060516070026800c07049041c0403d055991a14101802d580007110760080d00e56841e50100028a00404170542000c864144a104035060030790040010a104212004050322602c02c1005c1042c940d40c504400d40c00d08160540341d06000743c00786840d440c0c0390003820070441507048076000e01e403040c49400f1410b0003016240c0c925071a080240903142224800039152801002c1e21000442c55070030040d03104031429036a013a583e610404001d8072120302512070484105000209206003081c20040701c1c4202400d007813035000f5a1801d0710302405005604d80340c03500350191081e00c00081d5015004602041400c4440307140506c3d62800d00c074221048900205281d4072400c000c00e400030b0181c0201c941200b620315006c5a610b80f03907130225200700002e0740302c00d0000d8008015a002d2583c01090f015103044d00740b0b00320000080801041c452409800b07070742034a00f90360390541820404410311060040581c03840564a9152501b40701 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 403396160 1250 403394910 403394917
    0x90b1f0f2312010f060b0c15091504030804030f0c0c1e050415090b040207051c020c030a0812092e061208072315041a04060507020d020705130c02071a 66
    0xa44e2a04004022500800d80c0007910031810b520f50003410b0b0150407019a440c22440604040300c28000d001200d40b060071811025403249000340c6510f0154100340c40d0041548030304140003005c00581144140c00140007100c810210740d180b00c0e60341046100c58040504917015540b04035030051400350541800c010048240c021507100351400c010b8000b1141c01e10040e8402d240009000360014020203400d0304540c040c03006400307490320443d01c560700c40a01003131604116090075078003808003050500318400c4c2d203e415a0300044003800340142102c11402c014000744081c06d03404404402154a090001c416132114004011030115001c0c130800601b0440c5056218100950314038074248110f60380032050000084140440d030f00145402c020019036100d171040041c00458080201c19580103d1350f00807000d8078042d600501c0001500c2c1000007005c1d18110b0340e503402c04159041100104159911010701041e1598010f2000c02c429180020480c2007200940068000140c03055241003005801e0014 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 403397410 1250 403396160 403396181
    0x51909081b030c06030711060103150b030a0f031214100303020705010207031a06040906020c010c321305030f01020405030105010501080103110d03050c01090b1f0f231201 75
    0x107950101ca1036030801040344842078035840d019442951084002e081c810000c6074444200e291a01100c040c8280d8141032440a034004c2d12040c00759048445101068801c0d030b240c15904400511070458980d0380c2000380040b10602a09005480c40d8401842d0000d40248030b41850303514558105143c000340c9003000403041d00040e0014411064040b0306540001503101c140d84d0801412104804410ba03104440e460092002c0d0b0001e850b045c4074070005120340050301400c40500c0c0085011903d40c40300400303e4082e44096600082030382604050003080b04001e6003510032146189039140d551503078001c2640855032043d41c00d4410068140d08e00c2c4410750140060314030440007400341e80d0360351004468844007030001074a004a9201c10900c0d51401d40c141143c0c0c5071290520a040c5030ba0b440003d400c4440c460b40603903610003042c0070001d025a100420410502c026078004400c1070400208180152081c094440e2403004600d92142d580483e40060420f224024260440030b200212018081c1c00e42848 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 403398660 1250 403397410 403397413
    0x301060f15020a0b01120c090e1015051e12070b030103170f031303091505040305061e07110c090703060602012a0c02040209060c010902090a0212070e0105190908 71
    0x1440541d140c80481c0f1540e400703400c82c0d442c400b280d082800c08410030244030800c41e040302e068440062031042034022403103980c2c401009030180362000d080780c02c1603c204020300b01c014041041c051025036640d18081c0d9400c08040e0141840b108a200420145100300041c407490f840340c102c3c0000c2d00d914400085041e80d00c03400d0107014607038002100d03580c80c0c000c03031001d0581c5003401d20008503049248143c080c400c5010345000c41c0740d5543c03600012045a101c0b0f030403074000b400018092090110420489400c19504400d02c50707200110318480e003c54001070817800401c03030149004000d0020400500c00c04002c01440109142040c4078050000d0500e0310980d00503500300400300c00fa10340b4255003440e8070307030702810a6000c103002001c049482015010080f680b0542c2486101a135440f1440070380100c0340140000034450a0500410608080c0200010070603401044030f0f00c55a0941c025140d00009103013840e800b02ca1504005076a580101440640c507209001a004015580036849400701c448010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 403399910 1250 403398660 403398689
    0x5090a0b09120604031d130f06081b0f040b060c0105070e0901120308011806090608010608070f061d040905030706060504112802010e0a0503091003090b15010e0301060f 74
    0xc40300d540f10751088a0240100b06004c0d07508812038280c40b14890510001000b00c1040602c800f00c0c0011507540305164000c2d980d40d090207100d5070340100036000c101440d0802c4898000400b04c0041d21003041021003a0045444040d200344e00c0d2280c00603106056500e4000340b200d40b8010030300600300d4201d41c1690340f18a1000c8000940000c010400219054040e0f81c4c60440340c1c2004540d4a824103400070214079181d6034100080c12507543e00c1800b0280480300e002140300d038640b5240501c1d00c102904a8403030010030060810905801c155442c0c1c034151030036000860880e1201c0000e00030500414054640c0c0800103d6074100909540314900761541120f0401001000840740d11450003140303201400e07410a84c2d42140440790f2591b0f0096800203070300c0045450050194a503003003043d0f501040790f582d44089000c1705185000070314000e00c0c00451808120041c940d440305103450401a106940403560941902d16692140604d0381d48214068000e0106a5481094031039128061245000e61079082 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 403401160 1250 403399910 403399939
    0xf030f0601090f201806370503060a0915031509021905010507020f03120a08010f050108150108040611180909030a0903022e11061317070305090a0b09 66
    0x7582803051040da810b80c0703040121100120150144000040e51b01003400d00a000f1400384101c440710102241c181c3e003102410104006020704000c0351035210501c401032003000482c2d1039071a0240304817440d011000c100480302803040d40d1082c82075040900060486100c55611004540003080b103a4030a543c08000508207405220551100f4003900d80001c5003044804007600d040d400d8050001d200406648204540301c0f0000c882c0d50044144c0004581e070000100072680401003404002d120070300b0812001c1c40c061248544015107240c183d8140308007840420709205a0b80e020440d030000110189030380310b016600d200c201d04609901c0c107200d10701c4200001c0240c8004016201402000d8580443c0386086a08020890381c1100c40030500c4280d2800c11411016020b00c200c501c41d0a0351507890029116101180c02c6c00d4004200c104a065486403400000d280c00c04601c0802e6088104030391600400e01e0122502e2182050503940070054243c00714141003450011b00c40840200c400300c106407000b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 403402410 1250 403401160 403401191
    0x60924080f040f05060c09190b27030102030403020610120b01050603070e0d05100c0207030b040206030925030b13030f030f060302151914040501080c0c010e1b040207110f030f0601090f 81
    0x41d80100b04031000c0a000d00ad1240b0114912241d146550034602c00140104002207800c90f00300321001d40050b07201e401840b90490a4140c204050400002507254000c4113454010300702c3d0301840b41ea07014480001c0040d002c2881021030302081c44008103103040070040c50420640d500d014840c0b42e0303100da10b01142c048a5a00008001080300da00c10203c0c0310a0b542d80e001c003c0945c100a020304640d001d21030300f200c500600c80030700448410100284040c140e046080030803404100800c6a17502c1c0c221122860b000c80e030049a42542c4009034940414003030001d049030f4000d4509640002d420410604150058010a1014200c40810149076032046a0b0454040b503801c1240004142908002c12080c05603503c100c4155502500c131041e807a280441030351b401800c50300701421142254000802058130708410035a46980428115025820060140c071019550406000644e00c1981564003440c066241807040355140141407042e5581e075a541c0782101c01408280d44050386013490142c804004060 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 403403660 1250 403402410 403402459
    0x1e1e0e011508011703040f060804110409050c1e150c0f070302060f0a170405010b03060108010c0905010c0c090e1005100f0902030a0b0307060924080f040f05060c09 72
    0x810b60707038a140da070740382041081000103000c1041225000411000c1140d8500004071300040002e60b440c410700d86400c1c145401d5541c1c603d030016101b1b605200f50600403400c0015071a05003401101e040300d03070b090002d00c8801d03040045601c2a400807010700325208500d400002034040d01805800362842e20741514412a111500e50200a621800601a80d840300a948014190800282c01e16090b014201e029150407070000715000c0321f1580d1100c0d41c01e01d01d0b040911000d40113084013002801000403500c0040e000c1c200601846042180d09054501446542c075010001400040d008002000d80d400c40141c4076026582d0f1400070034102000700d420191020040402c40b619845d00344009800e000b4120301950028000c0080030740ca03002c1a403840d80c0c0034400c070001026981c81d0b02000300e140c84001000d010522000401589203c1c001500d05600158515405004001e850310701c1d54031031401084a04103144090858820f00041004102640c802803180f101e08950002455940c110780c44031054 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 403404910 1250 403403660 403403699
    0x12061b082d0a020d140105030703141603060b03160e150d200306010e09060106030c02032109070b030907050409031209111804050c01110c030303040c0609080a0c1e1e0e01 75
    0x28271094082001c101850446000c03903e081c0c1c16a04c12180042100f00514456041595520307076811b6510614a0304001038a20307080c074a4844a4070703514000006101504c014060b040c4140d001c03080e0040c0303a4503500c018400d82c3c0c0c409859081107500d010410888031b03180703103003501910409002041203500ba2010b0381c8106c401900810b43c50f802c0101c100c000e003a45140c00004d512085c071900c18030705028a100c42481200d50103580311842d01c41c02240c0b42a001d0762186008031810420f1100d40c00002c01d60340182c800645000c00d201740c0900c1c0c1211000008004008440c3c505440d04041107604541e50302c07802d004440c608840040c69020540c8484150b070003c156034843c940700d0020f5402451800c2040e0700c0182500d481031601d0b0003103810b40c1d204590480745040810014001d503500410010040c0c20000000c00d0315810342d0707454500d05245070052a0031005004844201c482d440501d0f180680250b02d40f110615540306000125030380d844c040c1d03800c10003080b8004101040d5003080c83c454413 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 403406160 1250 403404910 403404913
    0x50601030605161e1d030a05060907050103200901050906041e051219050c0a03110916050a080c041206020d050c0a0e0f06040b0412061b082d0a020d14010503 69
    0x124a010060f0b50203941c0445e4030548140505007080d01c0d50341844407520040c025009030990b880c0060320710341401041e410040c107251403c0d600c40c0300c440095a400c20b84100882a035559518a600181c900e8010b0000060380841c0008000c00c6803800e1101040410710b9003018050283c2e200c1c4200b0007000121180045145d015072888280c0010300ba01c880200ca00503c20398080e160083d001ca0b050034410781082c0e50031100c4000e140714900300002860f501c080c1002c140e11201c52107500041c9603205a600030b10400a0031404116000010740444005091544c2c06500442c01881e040d00a0b401540452070034914003000140c07089050340869946512694820200c104c0300810072507100854845580c01540a0102040ba40045c1000788043c00c04182c1030480c0840310318100c420b44070302a81c1c41d42e490000800700710303900c2d0304070300c0c0542c00c400c2041c81c0c00050f00c0c108680740750307502d0015400340c11800740d90240b08100d90b40d0380c02002da40035402402d01c00e80e0b40c2c112043e41011800c1c41050b806 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 403407410 1250 403406160 403406207
    0x3306080a0b060603060a0302130606180b0f03070207081b27131a070804022815180902040f0f1505030408300109181e05060103060516 59
    0x34035143d0011948424010403031410240c403034020402032120302c80e44007141a6030b40d0050001540080c0044009000e11030340003505401d01a0440f4236005d0210740301c25860001c130200e4140340c028040c040180031042c0460b02842100d2003407070345901d01500c1440c0100c525140c1e00c0c1e104000f408184081d254824605511500d80c00c04001c101000d6039025220107254400046403418020240c0d4000d1040395215911801d20b4010840395007a00560120f5200302260050740c40c0341d11581e140c0c203c595802102e928110303102c00695401d5030268458450840143c0b010403106907540c0640143c170b0040d48140c0215440782c10407025118640500e03428100c0b11500302048030307c0340000b103620500c00c62445042074054480501040c00c07502501501009511045444603c4030368001d00402d41d10714180001040072a41008410040d00c010f05103c80b403030322003031210402485043c1081e034018100c40e03076580e69050080003400295a4074120a8144641800c1d030340c842d41039400b81c04184010b007100c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 403408660 1250 403407410 403407421
    0x1e050601170604110c010608070b03191107060c0f08060a050612100f08060a0b06120403142710020a120509030c06041d010f06020a0303093306080a0b 66
    0x20401d4010503032070303000e03480f03151114801030b446001e80400d00035180045445800d0111003030603c0b03002c0d0404040a84140108202c40345650400007000080b20000940c505290030284840d1085030006002d141c00c080032940300b00e40c040e082c041501c0c410790f90700300140c4511040260b101038903c51945d00c07030010310010034403410000002d0b03000000d10b151084040d640d601030714085000c5600c41101030700a00d042244190b810300860100c2d40c030441d4040c0c40d10303035600c00d11187d0850151000e800c004486403048030500480c01121481e20581e02c0b02d02c6400c0d504001d409400d4007101b071050046144808254006000081680b0015401600d44910a10415080700c3d10b0f0803545c01164544201c049010003034503900d006201501001c809150b1400e00e20304021004041a404a9086166041c007000400c0d80418040000c641c0762030046803060541c10070380b8800c03540d0000c64586a20908000c0f4460003410000c06d422001500706100c0c0320743c2e50322107039141c0c001145d01a0900f160314ac0041c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 403409910 1250 403408660 403408697
    0x60e030a0803090708070b03011503051b07061515090504050103080405061c02031512070302060a0f0c02090106170a1e0b0105120a20070510150305101e050601 70
    0x150300003100c83c103c0d120203a40f14881c5141071810350041d40215400001030296050340160310052004604060010f41066181409500e03c45c42000c55483e50101d0703c001000020741180c8110304076001200c0c01151207c50200066441c012120040382c40b035280001d0301d0400f0300510b4109c0b030b0080c4462317007060314150600420740d024180c0503210540a40d1a1b03800d465640c400346002c1d0000ca46c0d4402d091070180c00384100307054407101980450b403081d201000141d4a485c2180c030190500e01d000c1c40d000d20300110946044040391002544903820350008aa51a48060b030401d0001c03100020b41080e88883e000b000c04c450a403003030140c03452246401100030a5035500202c240b144185843c0f0701e0050001840c0c035640d001074411283e46503c2c3c2c0c64141e0b0b64847c04c01509814192520024908100f551320143c0d00c0d4000ea51920110f0b886a01c06a90500603072201d200860b0000309a4940120102202c40109240c40741e6104104c1c2040d55006001035a201300340c4103100c103841d50070000e400d24030f499 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 403411160 1250 403409910 403409917
    0xd08040f06090f0f0b150402120601030c05090301060801020a0e09070c08090127080d05090306060f06040e0c070501200306120313060504032006030a0c1403130c060e030a08 76
    0x58845041007541500080c4404116401150088441945a04042000c50031b00220420054032032401846520121281d60780401e0f0131050900300010b007840010300544190003402c83c019419440d04400140c5c1e51410b40040c4409c0c88140c5c0d0f0301d841c4858003020460002401d9603140300040c109008800001c1c50607000300f035070010506003689000003c080ea460a03540c100b00545100c1440d00f02005940c00c10040b01c0031410041c103026040c40c9a5001181d91050001c15280c45204a00041d00311a20f920f82201c010f060100000092440c1c40403150b4080d1b403100b107007110325610f0010140200e04c03a01c2d00d049800407003610003a10f1620b4403001c11a1082c581100c0703072480c0c0030401100d440c020b50000014010035260722055119407950a06010265602b5071020b01c1ca814105564180e0780d9000880303078450b08a500010300154411422600d0b02ea42000e8110454000070511448070316503007094010130701c2005040600c1c0e4a40d00c048071514075042c0c0c403d4144d8803a51007400082c2c00031018 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 403412410 1250 403411160 403411163
    0x1080f1302041407021f061809020406080109050d1416030c0c0906060c030207080105010806040f030e090117010f0902010203030c1e040e190203060604030201080606120108030c0d08040f0609 84
    0xf02c0c250b0048080b00354550000e07901600541d010f003010780c07803d40008848149007900017804201003454103900d0007640c2c0d418415880342e03503515032005003156565400b200141c26020001c229154640c50482d1392000c032034100e00c010445021340710740d502800b5002c403040e500038211115440043c60741c044c0d03000d9401d50070845040d101e208002c0741102141c400c0800801d0950b4540e001500b09040c060b00342500c03038001c07480b41e9040a0060040c04d40004085070400c4d842825201d82c4082c1e4141140c11b00700140b01c003644404a038000058003055002c0c0402507461040007003001000702c03440101294030b1038030b0003800358105100083e2100006409421082061145c41032105001c0704000c01541c080c2d041408000181d0040c0f0200c04400d60602e100e0008400e401c40ca14145507000801601481c40000d042000b076038000b82143e00c800c0e0558041c0c90441040700400e58603081480d446c0c0c0c0080c803100c0c031907100d45248202c08502c02da03a003034040c50b08400700040d0000035450344406440d06120 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 403413660 1250 403412410 403412419
    0x90e0a120c06050903041e032d06060f0f060f1706030a0b0108100b09091504080904020a09170304030309090504110d030503010302010207050f03061812072001080f1302 74
    0x61800105a2600415103c0e400c90344c040d50340c8034140b841c0000000c2c4410868490382445030018400075078600072000c1c4100e0071920260411004422030b503501074165100a015078100340c0005031980d078140d507890540e5410b400c403c00090301c418085405000e480039003c001044031305510003541d101c1c10281d4100c400501542c5101019856140e6004020785c04400d00d07a120b9040cc1031131956511590768020001c4815030010f06056155580d1421140c070088101c00b880004107080011150846002d080058019074481d80e1501001e89000306600c105409160018240314989001004681c01e481e4552a2800f5140c100014030001f0000144103d414030703508042c9100d80e644200790388c070f401c03840f03a130382c031a580d60544c400213003090400c0d40031901a8007000e2090303501d9900414407a50010404420721200c005588015281103162210003a06c0300700014800107001e03a242c00501c146000841c02e0380402d2000c0d004440c0b450f070455240900e05107550204543c0000c520040c02075500050 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 403414910 1250 403413660 403413677
    0x81206030f010603200307060903031119030c0312021c0f02040b280206040b0f06011808031b0a0203030418020f04090b13151401050d020c0d09090e0a12 67
    0x40325007116030344d410a0b50380318103051100c0002c100510781c035008a0015406081c00c2440d02c04040c0156486001c0203061141e08901c190b02c0040070460000400010118180c0a41403401c01070902c8003862010740c0010144d001c450908203030b5000b200c00a044075041c802150b4440501c0710300414140700342c00205a02080005040c1230807001034448110079031051240802d900f00c000c035564103155090025074014000b003201003100c01c0715081e84a41c4c82a0b24113003554460380100c5080623443e508102c01501200c000ca0517040c00005410101800311b1280d02820307041e802c2d44e603184040300740254183d2003000305111b9204603260240c2c134821280c0c000b509004200500da0301da50055042030b0702c0c5039a17484900399186040000b03400181502c10301040b0004a29008500c048054010070f030b44400190712038003450348078604586801060240440d25407031030030a140e8031800309100da500041e03074100e00410658624482c5250000791400149500780541d650500c50502040708141403000c1c62 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 403416160 1250 403414910 403414933
    0x140a0e0f0c1002100624080601020d03020c0c031e190519080c030f07200901030821180105010515030103120302041203030510090e030301050906062101140d08120603 73
    0x34040d050191a0403100150796042c14441011b0702c0b03868000c0754042161030801c1c1b040698012400ca05640114a009650748820b0b42209280c00c0e8117400d09034140c45000c0c0e40c0b4030703034110616003207005805c844142d581d070361802d0040b82d11803070800c0e80c0541281c000c801c80b45881c80016140e881081d100728241401d00324890500c1d811a04a2491242601c10001d809410840182020240e0990703400350454021603070408a0130b4403034140001030800030001442c0c1081c281c070050080c190f2104103c800c0e140d00e0540604206c3d421207041160542d0b00b001d0001c2081d152105006108451202410b819a07185480300b842c68540d8480c80c0d400d2640c20000410111580503405030035a0080e140406d050402d488081c4c1e0b0940c031644020307820303450941c80d0400710102108aa0440d10708581100d01c0d922024002034062107100c0c0c0100e100744052014458000d107080c56a812204034007030818100c1002c2061040d07440e000080103000d40b408211014894001141054000d6400307012a0100d80d81c2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 403417266 1106 403416160 403416193
    0x40323030717222112260708100e070509060c010b060705060406110306330d060f09060317030a02070501140a0e0f0c1002 54
    0x42060100004100060b9807000b090803018030780340101d6452480300c154081c414200c00c8100e016400240e00b50000c030b10460b141e00310750042c0c0d031105d003420b00702d4149100c4035401c10022582a038000c107185801c1e664500c03600054443c440a420312500b0a512203c89034069058070782d21104000e48a84d1240590303818030380584a454446000d003007070078050913031559502e401060100303620050180000e001800b860040300708000c1e4815000c2c1003090b601c022640d490304410070320100c1c1c2041c12031410280540000340c3d802011480710300b198200d10782c850042c1d1035807583c46140522840b007114120341e0052078019810030942c0e245130b840c89074400c91101b0001c4046804000074025180c290112154207a001000304001d502003a00002c40200907a41003e03082d00c0d00081c55a07105001a140f034061800c0d800811500800e00204040040103124080441c0203401000c01c10544 = true := by decide +kernel

theorem cover : BRFrame.Cov 403237410 403417266 := by
  have h0 := BRFrame.cov_init 403237410
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403237410 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 403237410 ≤ n) (h2 : n < 403417266) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
