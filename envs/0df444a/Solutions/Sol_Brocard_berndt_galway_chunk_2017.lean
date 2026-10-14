-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2017
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:27:39.605482+00:00
-- url     : https://prove2.me/submissions/218e3482-f076-4748-be72-abb8ad66aec1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 362589928 ≤ n < 362769784 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 362591178 1250 362589928 362589949
    0xb011404030b0603071809020a0602160e060102071a040e011710020d09050a1a0105060705100b030712050706170103022d0307030311070b04080a081305060406030509120405 76
    0x114904030b07640e501d0700041c3c14001c0c640c11410003828850030140c04801150b11103400039200351006140300f61212400d0340e030344091501d4115064ad046900748090014050117642021060040750900c0350ad81d811008220300c1c1405002d00140003103410400c03074140c2a411801030070303075401e0700b41c54140396840071f602d0304e079000300070204107030001103c200071822640010020394110096079084440f40c509180a200514030f001c00003228140040341c1440c115045643c0d803603100d0000c1010300c200034400d00c054040d820300c06606000c1d01300000780c1041800c0b00004070301d1080e0b0241030b22508103140500700707011115902c1c28011070317103005000585980c0400101e009040344840c074400316817a044065615000200cd800d0f000e500c0c000801c26401131310b1800c600c0f0310705007030f0b80410303131610f05408260040d40300744869a03010107500c6010a003003900500c60202d044a00d08401500d0b003022511503070051b44102c00281e41c0318100640c046040c09000101000300318281d141a14000019100089 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 362592428 1250 362591178 362591183
    0x70305030912120f071e1808030f0a08090a02010c02042406020c090c0a08070c03180e09010e010507050904020d090218041a040b180309090907090b01140403 69
    0x20008046100107408004062800c811402da840d51140400840190110244c4001035840e0150010400780d07800782d030081c1c150446810301c800b0322000d1030b5002c451140001700036000c110500300003c035003100c0c180000c1140100e0b01442a581c2c020101e00100300040080079400c07190044100d000060780d0201c018000c064045401040081c10a80100c500411405011201000d880c00000d03100c0e4003c196000d25800c21681c4c3d42450381d81d28031114070741c03113104a107100003656440050b1009025521440070035003e850b04081d94400c4054030b501d041007a0300b01903004058031081001c81b820901400b551030003410000d11050408490260443c05085681c43c42990003091230807180d40c0e250320071400103800800c0030011035240304c0050765202d426581501d51a802020383c895000c05c1c1541d040c003c40e0b008400a200303996580e840840000410782040c204d000803c204841982c0e1800300e0350141c540c100107080014a0840020b0443d240c0d03006481c10301960111121b0700e40e12071400d0f02c0851341c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 362593678 1250 362592428 362592437
    0x601080406020a1b03021006060806060f0f071e021507030e090a090c09091a13020d0f021906122c010204030203030d0204031e0b040f021908010f0f0e030703 69
    0x10351a410540d0700103011154040404d210040410074580d0010783d1061510204400300101c680350803040300d1110742140c08a401c00700400641d544854904003c10340c403842c0c0d41ba164141081a61980304090000c111250161841c6614906601c1c0101617581151603004041d4036044103640c0107814080c0090000384502246400250103041941000640c0780d4002400c6040b9612102c4a000401c40c0a000b45c0e86c1d00324160340d10003040c5040c142e540c0034828900c0070009a191070350800c0358030701070240f0840c1c1448141c00490011b841c2e40550700002910303601001b00290030201c004091801802c02d1043d072a061010000042d00314641c807c0554580710750102c0d200a1146030b6501900c940c0e0310081d05803000090ac00d090301c001d81d000c1c000703480c46000160841c55500762600c14a551070707003000d00f419203c04080740000300d40d000f905480d544060890900145160a040d140000350742c411701099444c2d481c10146486c0a106034245030407002c10402410030b1140e00c41b50303280a030f00401070502 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 362594928 1250 362593678 362593687
    0x2180103090203100c031b2303100e0103080c12040f0311030106080f07060906080106200c0616050c0901030b040803090f070603140f071e0e060c030a090e060108040602 74
    0x644041c0078000c14010b25007002e0100381c1807000006c004040c07100091100320341060800364003510907a100d50742404807000d0410042c1460001480ea46d10140414014002d1040006580038001060a001b540a8000a900c42181800681c10000c2104003000d90042c00c000a000714644c41c14030700c0640b9088803e0800e100148800700e030040005030000c1449110360786111000082c0003405a05841059440c0001280e9034201500e0742c40c806e0103010f01090304810b10702c1c000103200d8001480031005108961150b182940481d103998082c45003410347c04880032240052100030040610f00d07941c241d4070f4070001d40c510344030118400c60141004003600320000c003154406e0010404164a190058241c03540d8075601c4074046c0041610059140084003140000b601e41500d20709403901c078401c40e403100302c55021400d1162519521054080c000e000d580801c2c2c3c042c603228000a4603281f5042c5000b10b80e11055014083c0428036564031541c1c0c0c0c00118000c000051b64010a6160015071040016864 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 362596178 1250 362594928 362594933
    0x30b011425020402030a0e0d2c0117090717150f09070e01060509090109020a0f032003040f050105090303041a2701090b01050609010c020d0201020106030813060207090218010309 78
    0x5881e01c6000203035000340040280940b0728425403102c05804900c4041703038401d080d28441610306403a48035a40c1c0c0e1a04003d0400d100281070341ea007101e10003d0500d4840d000c186c035a2201c1c5a0340c2c0341990105c40c40d0307015a07400d0201d00d80440e9034070225000e20b4020000405c110b0390b11040d040000f421070540c010b00c200490f480400030805c00700641030803062401d0315a15a0402407031504456440e510070151b100000984280a00c2140c507024041d60f5007405503001c0b040150003800c5c5990003602804030400d0780350309281c1c04201840c01244a110080e0316a203403030500fa4295200900b05440381c1c0c10800a2000040d001c2151882e0500c1050703002c51a6034030f0b46019402620310600c1c022090740b00d03542c001e09441040d40400c000520030640101e0503601e900c00d2000c107020ba511442e0202e55030390036000261400e941c840700c00910500c000306000f5200e50ba48400f80c0c009080110788101c00d003c0030300c0b041d50180003140141c007a4000450400b032003074040f01c28a040300c41d05d40703044c503540704e00f02e46c00d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 362597428 1250 362596178 362596237
    0x20103092315180c1c02062b0e0c0904020a1a030a2d091b0e0601021e030901051308030f0d050903090d0f0314030907140a0305030712230703030b0114 66
    0x10300e400802c09030308c0700725640141034046985100500c582003a4031545290b4586403107100502c41c1d21200170400a0f1419050249100c8050000d90703000fa40e440c00019943c440842000e4000381c418915616400d0510926040d1580c48035900100d4201001c0c1c45104106500390000300380041c100455000d9940c04c0485c80340004d00260345911406090100c1da0440c4102d00e103000d25400e0742210040001c0201e484a121468a49400c0580040040d050591720480c05001d9010000c001715078201da0390030000749558402400001003204c04910356101603150b10516500082c0e0070065441e003d030311000214400501d6000400c00e49000d100c60080c03520400040005602030003010b81d0300c0c28003081160b50b4140030300c5072529076009203904000c541000100d0b00100d0398004e00039414074800341d035111600e9100a42035010400c41004956609400741c041c030800c071503c00000d0fa900c00007400d00a054441e0b1010385410f0140c4048041e1880710310740304a40e01c00115078038540c0c108410044021 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 362598678 1250 362597428 362597479
    0x3070c0f0618033002090f0307030b070807050301080a080f16060609060504090b15010c0b0f010e09060709050f04060e01030b09010b1507020103092315180c 69
    0x1420245041030762440502d24103000402a4040c2d140c64002007204440503003882104000c43d03400700e584d501c407014402e10980150a034000001c2c4045042c40e90000440e24140c2c07994000e48006c64011305105030103802c0780d45107401c0141480c0081c81c0d90b061420950b40c6000c800c400402c03440000411000c0c0c1041d05041da105501038000da111000107a04142002c0e003814010000520318100c0b0004041c0b801e031052022650740804660b0350b41d80c4011520a0b100c00010341241401000b0003103200107103070001c2c068841c11501c291101c85504228a0307110807075005000c440c16a001c14107100d15550086194021070b0011101d15041600d0030000c200500075607032100292101c000004010085030b0f000141c820041350000f080307070300c0c1603204010090521902c0d403030042c0020044000554420740081000c2400351000803580c03401c01d41507080700c42c0c003c00480421f0304840520000b0100680300f42b504020303050005c06c00e40c06610f041303584964810884034070400c1d0049002d40c0c50060107610710b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 362599928 1250 362598678 362598683
    0xd030c03181508090f01020723010b031f0c0305010b0712051c0608010b060906030411062b050c041d0912040b071a160305040f080d060f050d0803070c0f 67
    0x20900e100e90080c0a840f0880680c0c281966002d111050240c3c00414030a5030209604100c0c180440750042594074015803201e0700c0d000307440d5281c0d460b125554604000800001d41540c0ea14440c0380c2c0314140b80ba00b15901c610041d810141458010000c10b00404140c0c4c210740d4000c400d000740c040f4102c0c07060f03c02c0e01c40c4101120400241080302c91340380c80070354044002c0b10400002030066400c074008020440c40750038400741e4403040034000315003c511b002c0c00f41c2444800151100e07290190b01c1c15240070710410000c94a07800d18031a9400c0955990601915400c00600142181032904000e20002c3c803492441c45d49c0c0d1030464180001308c51103003c00050804041c40c240e1540d407107848130403a0748917a0000400b0b0301c3c42c07942ea0720aa49840351020040b481740541241b103004107520f1200840140401130300980310142e1490150300030408030001407500142000c0f002481031310305203070074111610079800944910300020a1402188900341101d60042e014a01714414405500d07000b8100c0031041d101 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 362601178 1250 362599928 362599949
    0x7090c0203090909060f0112060b0a03060b031506061c09020a030302011506020303070f0c06150b0d0c03050903090d0f050708030a0809010213060509060706050c180d030c0318 77
    0x641042540110040c09020b405030b422061a541c0d19410301d45d621016504074014203803810040000201880481c0d8400c1d20411000c43e6403900c142c00100f1154840e0015240e999030341c003207000c20b1b180400440320f010040b2600d101c041d01d0402d0024245005000080d40807045508117005aa20070b544141400d81e8006c08402c1c41a07260300380240242112003906400440f070650203d0102e000005030707803051a640d41d5003c4d12041d1450b04403054400d2000c1102d50944800d00c940480c0c220038042c0c1c014004007540b003a00c030240559104140c810280c800030034186880c060010752100401161a4000103807948072182c1381074908201d101c10750103c0641a402414004601e6560200040603514100d6a42d40441c3e16103a90071800c038806d14041e015030400000c02000341c940104050001d0460050106050508945941054810446035001114400070340c0070601941506e100e404120251a408003007085940c0c0985045485603003d011310008503044000d500c4001c0c028000341a8203443e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 362602428 1250 362601178 362601191
    0x90a0e030403120e03061303030f020904180b071b0602030702190303020403050c060a120e0c040c020a0507060c080a230c0610060815060f0405030f060a0609020405060a030c020709 79
    0x40c007040300d00f83c9100031000210041c80060342c0d40f80005009000311451010703490a40f88a58082e4018403c86105003819502440948002c3d501c502c1001e80c540c1c03942280040c0046685048600801c1c02001142400b21801c601c005c070f00c5a900c0e8400c41c4560260340160b50741c42c3d2f12426441c203e0307404c0804281084031082e5404140c2d254015100322807241c4120791300442c5010810900740507181d030101c0010480c2040c06550300b100c5d00825409006070b0151504142c2d1240454141c07000d520070013003d41e005520350030030060100013090041c40c05203400205415a070391000c45038801c22201008000200300e00b4071420f190640002405d400c880e41305940d078184080701d26101c400c11500210070500c05900007034594050b040f09881480109201c00d200e203520001c200e030b1034208108925924400303000204140d00e08000c10780b00b850740e950082469280440e61b80c02540c0164000c0d41d007450041c40100620307103a4030240da1554142d400c01180c0c03040712140c201e2130070019a2120440d20700300300 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 362603678 1250 362602428 362602433
    0x1060302210727180203060901090b090307050c0105030411060301170d110d030e0f070806010821040303050913140601171e100801020c0601090b011805090a0e030403 73
    0x1401c0c900840d0103825944800d0f92406030030800d20540741c03034118086003070030000651107480c2c0c09003450400000a000c42c407401500032030701d004811038241200e40e42d900c4110041c000054121a40282101d004501c0c0c0a110754405403100c0c1101c0091341403001c080040343c01c01c0b001c3d403070b80340300b203000581065182d60751802c80800840716517000144038001c0c00320700030180b40320f140d05090410840c4010b104405c0503a07411402003510b007035140001d0103200d41e4013413070100501402000f080a00010f0610b541000340980c200041c84151500e218400d54085100b07001c0c0c1c01c180c41c220398040c2002c5480741240c501081b0340c200680140b40c1c480b8a4403011380340da840701d6a2141c0c060035003a610b0f207120800b40e841c031041407841550788021310b0020107003407242c00084c5040c0a9004265100100c0340c659904455800d903003007400b2200d10751300000014494000c1a2150740d0b645002480e165101c05080c11010300344011600469020f91700840001e41120026001180c610b00207100300d0f5542d44e601e0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 362604928 1250 362603678 362603719
    0xb030a0b09010506120f090c0904061401060c0b16210507090f080c061b061005030d05043c080318030606060a0503071808150901110f070501060302 65
    0x1620181e1003465060000f040314204442690000c81400c996501c040c2c440b210301d03c00880004141002d14410312100303040c1a00c0703c0542501482c4240742c045481510101c0160802905802240c10040c101c43d4501c0482c021200d49900080c2d071842030074000551084c1140e081c100217298490340c0400ca192841d11562a5004510484047d6603e224a0f07032602e0008000d40541e00c07a1070605e0b845001000214035150000741f02c1030304440c1c400f04042c4a02d254060518104a607100a007090101e8200b0060505100e14885090a480c0161030301c2e05042035940314000051010b1008a0304070f844449440d040740ea1114840400d14603050007d5403500b807669664010101da00c02c902a5a1804110b03090014040b401504000c106c0303801e0010480e000c9425400040a440410240180f40c41c042100d00025101401c5610042d003c492203519114a42c44000b40c050081a8134050384101410004400e5550000c10541d00a94400140c100a8050605c2d908003035804070072210b194a084829 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 362606178 1250 362604928 362604941
    0x6150e040b070e010806030a030827060106020616050d0e07170c0a080102070c0b03101a030619030b130804030602040e010305070911040b0903031306020f0c0a0b0702040903090b030a 80
    0x2159680c20307880b903000f401100c83d00016901190181d200d5000742d4002070140070016403020540350302c1103800e0390050038404a90b4201e03140c00d100350449070060001590600149a02400c101c54403207a03010300420080c0b4078407a00300d5258141d1b907650b81045a8020170700c080380052501118115a03201c0701007001391503520101d900380c4940c1d035140000070b685106000385d820032500649404142840c1c02d800d14510b42c001001c0301c0c520700035518085004541d03d6060242030810102150700c0c0d26210341030080711203a420a9072000360780c0d0002080040c09007a4a030340d100d080320030070741c0251b0001e141041c1075000303030341000388114004079010900101b82035440e07040324012400c03956926581c8440750111501140140f0803528104030900050304100002c2c001d04201808030382c58001007a5845400600c07540080005030814600c035038444904200404854034201c80c00f10086103041c1e000c1c600c52003038410080c002c80d1100c000d501450b00401c0c4210040507003001e074542da4500b41030f000e00105071 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 362607428 1250 362606178 362606191
    0x1709210c0414010308030c09030319030c031107120e031f090c05060c06060d03110619050c160b040302010e060f10060e030604200406031b0501081306150e040b 70
    0x1d80315410b00c64a4445000314126034001410614586585440c040300d5403090460b035030103100801185050f05502060900404e00541d800110342c1c100c1d0f08000d040d58403200b0748141ea401c043c0801c9010031030300c6001d00f00050380c03030402244072004039000c641019416105c07030205882e0f43d101c030142d060f151341140c00303da4465022000c1c110348640c1009441d0142c0d00034002c0d030350f20840c001007080c04c1c20f644480125020741002c0c0b4050500252251a0070740071140480540d042024203011041a400b03056088204580d40078104907180c502c98080184094020b4010403072100420f0606000f94040c00c407055002050700c91919266412109200301925184c0b001c440000000800b0f5208070154181e2a00050117059542c550742c0b00c0d440d10008143d2035960b04003400c0c4020046903140d124180003144511481d05910b94a14183e20494203150701c80d90500800e0000c121182c00304c0015000a258010700c0022504800c0301904082201c60304003201d0703440c200060005100806103154070420 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 362608678 1250 362607428 362607431
    0x101101110f040e0106080c1206010c0206040902121015080a06120b2d060d0303110d0b01030f3c02310303050301060c141e070801091709210c04 63
    0x5d03070341c0800321050481150b03595035020092205100d182c010320b80b40d68000038149400581381040b50000382099000f58000295103600181c800c07241e20b0124500c0d41e0080e050a41c03c00c009203450b12214401841c0700c1405c080122440001d5807652180c4d00c00380191015203400180c4402e1403501900c074040685000c859000043c0c4124003c12011208065140240b450b19856803140d01c02c3c0629481c04171400c40600d074444002d214030701102c0b0054500303507600d080041410701c8131000150465110716400780c091403e25941d0980c11000f40e09004003a40380652403c002032403c055009514070306004a40e040b400043c00b0f00e01c5441e68070070020150345c0c04048050f00159a50b0240c282d48062000401040d400c0c0010000d050190b0109a00795000c6d08840c55184480000c040c1407585c000c600c0404032101c442c03501128401044100302500346240200074803203058440c0d0201c00c0300c880c404c01c09480c001a00c04407607200c2c003c685c421210000100c00742d99822004032502e43c11480c1117540110b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 362609928 1250 362608678 362608681
    0xd1103071d03030a030207050c0405070201230f06100c140601050a08150f0907080111031617011e080d0c050d0c080706020c12030406240302101101110f040e 69
    0xa0030400204001c140010000c0d40b0b0289080c4c4241d0180d000701c0e2041c1d032540540c0f000310360365840f2800b501d0310402b01d941c000101c64070000c0d01c240e1860515004071b20300190303001c00c2216021000105a4101000310341d01800307000d180c0012100c100c028640108140208085094035200004030a13060324812107403034441076203418107245d903080404442e01c07a081100005c2810245241c20703144d044100c040c01e0314402c0e0340f218071650039125048101f0004050010400030a0045a9182e0060b03841e107241c15002d82d0104051030030aa030041c05501d28880302c0341000c00030800030a1041d40100710034415140c400d4000302d00981841003501d401c1c0d4a40c043c9a501703042051080c15040c00c6960320041d45418959141c591400139001a40500000e1003203c1c6154005404031000e14491071040c04040f035411040155104c40e108521454181040c10714400d000683e150140004c00140070700d00b40c0c41d42c02d4090328241c01b40030001d980003005070b03000604160400d501001001654074510791911705 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 362611178 1250 362609928 362609957
    0x3030f130f0c0f1d0406090c0506070b150301020306030604030f021018030311090d0b060406080a140d09030b0c0a090504020a110105010b03060a120c080d0c03021509060a0e030d110307 81
    0x440300788074904c0b00300ca5100c001500060f016403002801354001d01903402050f407200086603d50f84180000d8a00946010420003440300310500e4004601c000e4000f9401e42c189400880e507070b450003920081c207206d541055819118401c11551407248011041804200da440e01e41112084849905400003420240c0b21180502500704440010202074006004881d054645011300c01c4050700990b4844d440311400610034a041000a14240c01804c000e071807100450410b625250081d200b400c1030004412040011035030080300164000f6400c6410f0303035a20140042100c605900d6002160701030300c0800c0c60318400703034490304034003e2008000003000750340d8070361070507246c180002c0358907540c800803580c0e00b8040010502c0c420906d42e4071503000102d43c0c40e00c0e00b55840c140442a4a40400115200c00060a06504200c0340c625440d510080c0007040c1044184240c56003801001e04141a8550707006c039003100030400885009900c05101001840c00c0404900601d500a480c4c000c00600a810400103 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 362612428 1250 362611178 362611199
    0x40504060b010813030206070f090e040b0106120e071401051908190608030a0e060d060306050a060b03090a0201081008030f0712080108032712010b031002070503030f130f0c0f 77
    0x1d454040d002000c1f15601c61800b00d44241131602500100580d01d040000c85ca01074804140c05a071094240656070741c10244001d0480300c4400d115980700d82071003207202d00d000b004111001611203040041140e48040300c01a5103510880146400034070b0300d5400750808950204092740a0441603c40b007042e100060803150540c1c1240c00341403807a0b04100302a50301d1034090549400100b40c0a01118206000c15161004850b9150f009440c032540b100200301811100b48070b920041c100d1600000c0c1107007006a203c4d903031131031164002070510054502090500c586c4540d58801400c020040f02d5031540030003950b1840c0c1d00311046c1100c00c001c04000d03141d070940c020881c40781a11801741c025801e00192516848105120644413045030780091181d01c0b06845000d00031a400803000c002013800710803601410303d80040780b005803810300d1041c0300c034000050000c0300312504480c014042c83c0700c945074a00d110030320031030000300104203281d20302050741000154042c1d0811558082c00a481040d6501d02c601d6 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 362613678 1250 362612428 362612461
    0x4030201110a0e0f0a0e010b0c1219200f1005101a0a030f0501060c111e0906040605031905060c1c1806110403020f060405032109040504060b0108 64
    0x4002c503000070342031140c6040c00004c0b001541c00060035002003507076803494054864803e80001d04010b0f000618001c2100c0d08100b070485ca00c03070700ba00c070306d19018148001d903444d140da0040080800003505001c0e00104400d0211a0404100200b034596981c01c0a001560b20141185d40207010782c1880006100b803a640c6114800b2101c111010941c00910311a00c4c2d50280d004c40300311001d055403000d0450001c0c015110795406000d00c6d8407003c410701100d040040240d0003a480c52445140700041141c4104456080d2044589042e14100304075168200024003400c1c05421458240c482c0490f01d40740010000318a500c0c139030050b4140d4000e92204060b82c0c075240300c0c05031544c04a298000d519020f1802e158030440340d80f008160340041d00d110aa41d5282622000d01400e07452030030203c1c017401907140810302c2408000044400900d410703e408046603e030103410a20f6900c040511008601669420b800c441641070000d00810480c80c152130414020000980c4640c00500c0b410001103080c0c0780c0003500c5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 362614928 1250 362613678 362613697
    0x3060102070501081e0c2a0c04020a020a0f08071b060203090f03010e12030109060905060d03030c05040915090e0a0507140f0301050915102702040806040b0403020111 73
    0x7081c0c0e8508010054079181006051403091203a46807209280b01905514240526003c011702030792500c0303044034802c121517000204003584819009a20640e04001b44155409400343d80150321140020f1080c0c1c200301a01401412514841c02c0f00010064500000e20000d4812005903104190703080703400008039060b000d22005a0720810079010145411744070320800103c018004038140554540703d606040d044103942e003c4040200041c0614140c034050000580748040041015107482d1001541015404402034281036681c07058200d20707413080c2c0c01c4030003a104460080c00040c032290151108000b130b0b8444c0440c0945040515803100e4808252495103030307000001050083d08100111a00702e008480316503009544881949094a0030701a152041d40c15001038180000320040d2942d26210040c8588012014124141704900d41262040c403a09104000e08500341d030120400d0b00244220340210403e449480c08000410000c001010710581c40b80d40280000d02c52000b07941014020381100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 362616178 1250 362614928 362614933
    0x110313060513061d0c040b06120c040b0307020a03170103030806090709120302030712090501050414220b031515010c0f020406171203100513060305010c0f090b03060102 74
    0x200082146500301a40001000540b0508000c0c0c0e41e032480200c840359032428250640364040000515801d020410205405031020f110f01d0060400140b6a0722421290034107640784003001c40c81141042003510054000b40f82c24030780d00d06180301c000e50f450080c3d4100700e002030403611511007006002040e0a04a030380c1901c6005050715803104005280000500c0041001580280094100184180c0c400801c2c040d4001e10381e220001d00305080050503c041c00780030300c00c8041d410481170740d101c07040b10b040b42d0540044151800c0030b0000200403070002d00f01d046070104440745951000981e54070a8903108000c5045542e000954075401000020481d1700046000c4080103c0109500540394040c0d064030401c0209000405940080c2c2103c1d959042003503080310341816803541c648200040c215507060070b4016421444e04030f8281c1d82075201401081d0090740040c0c2400c103440c0039504081d025542c0100280101440c64100401d04c21100401000060f1800e000240445003401201d004007010fa02 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 362617428 1250 362616178 362616211
    0x260405011b0201020a020613080f1b0d0302011509020a080609010b04061218050312010b16140a020a060e04060b04120b13050a0303020d0b03010e0c1009030c09020a031103 75
    0x2014401c00c80c5518280d066001c2c1400400042e5a9140280080004840c01c41811350400301e900780703048104003240209622000c810300d240060a0070340450444100c582d060f48403941e1070f04901420300700558202e4001c2801c0041411b6103c2d401800c040620b5903120004bc0e030741c0307908004100c0400c2c4140c601b00030007080103100161040c0055209030703040450224010075490083c010300000c16000395856000031a0001311400c22002081c0107003c8952035504001240207103101401c51040700815842d03114010078107e031000e03c0640d40051b0001e0200d2243c598940b07019001101c00b9400300d201c0c501e00000460400a501c0540f01078601184101c0300c07400ca550b4038034100080242c0b011300f400c003070401c0c2e00c4c001034020800810802d10035500580c03207239403541000e400d9a1100221074400d90601c9145014050000b0f4110907451003141d001c8400000b02d041921101241c4d007004d4000c6030003050118019416030000c2c001024a0780e010050780c0c40d4507110340411701054900c800c1c21040004c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 362618678 1250 362617428 362617457
    0x712140a050c161101030e0d0e04020307110f0d0f020d080a05060a03051609050a0b06180111010213080c060f1e0d09061e0b060f0f130326040501 64
    0xd102a5111801a807200d00d0040384004501c40440441401c9400c142c0c0c4d20340c01c1607296414010011040c104000a03d0604442440900001000079440c1c3c061a40400000c4006101d450301280000800742a64034504005150646691119810f00d02044078001040e41c501c1c400a240c0540001a40d0392064a40b50f0825440103014050300d25a032000c04210044040740cad08ac01400d01071051003216111072454a80300d0811346800420700300040d031500802c442240c072441c08035250b0300c14440c40d4801d082080700059070b0015208290720050342c0f0100e4080c2c0c42070503016800c0244c0b948002180c252400206c108211031192290000e56540203100f04c40c8040080d0603021002c81d4000c041c2420810642d1881d0700701c80e4005000c0d118561241d00d1540c1c0c812120340383e82e100c010007000600600c402d15002c00c01c0d9220b00d1702c5c1c3c110314450000f1251402004501500c01000c04080981c11040c1e44c0d081c06c0d8a405800440c0c141d040c0c04242d092170500340c0000c00c0745d01b01e50040e124131b403900340c215 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 362619928 1250 362618678 362618681
    0x509070f0309050a0b0c0c010e0a030504050609041e090209093d090c060e1f0f110307061b0e010c020d0602190206010807170318030717060712140a 65
    0x242c0c0110707142d01ca0707040b13481c0c006801525524421402c200007180c440004109441c2503070b64424030a4000c0c0c01030103001c0d01095108007100c05956055641070b98030448207000c00d0040403c499050070f03080e80c0b0385101040c40859004040594003c5420b045162244004a9296001004081d20010301404143c01042c1c041c03000030381c215000200712171008100300081054030404c02e401c44503032000ea08140095034000c00c407403100b0030090354044c82c0c004c0d2050728800401c1c2100e640f00c05000030900d4140d04070f4070501d8108500752040c010760f61640703030904d082c4010b04994a42c60840d00303c0d405108c030280d40301da190340ad01c0c080143d45da0b091070201a0244000da5565800668049408109841408030044000300040090717600910643d03140007201400c01c1410307007018015048003249584000000819a02881c2501840c0d841c0c1e118008000303442c0c80c00ca60b10212000d00011814442e00d080455a544142c0c219260385110f07200a1303440004442c580c4e14400d90080140f80400c0081c40103 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 362621178 1250 362619928 362619941
    0x30c0136080604050a0614100b0c25032607020103020306150a0c050c03010c0e090c09030d020c0a1401020d0f050c070b04050a08060609040303090219120b010509070f03 74
    0x8050301000c0240e141d18200c0d0404508a0b0242c5040d0700454103101000154416510580c00c0850007401e2400e0aa1405010761943d02c0303070740a24800801c0c1940421020f01241c0304d80b41300080a0114607000400e1001030101c0741c401a09c880f0b82d9a450000140070825401604000508542d46003042076801500207400141400750400c0385004812844100d05d40104222103050701e6540c2c03000f40c40d281c81841d01c0f2240419a01a905203000300301031682001560042010843e10b0742103580c0c8080c0c26044034081c501d54641d040c440d403014011500e40204840c4200b420503a03280c281035407507903d0700071040344d403489050041e80103800e0280e2592080000c400340c0019841c185c0e152060080701940307450781ea500300300303889000090301300181c0ca000c04007000103202e0035014004a242000006c2c81c4048000e0001e42410b032503040880455032134110444a050903914900c038400d444400005c50603481590481d45e40070320600202e25071401d0340c0a14424060390b0f40b0741803100641300049015016 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 362622428 1250 362621178 362621267
    0x9010614010c0b0907030c0305010506090123090402060705010903210b010906081806010b0a02100b090601260c0d0c020c1018030203010501121a01060206010e07020c041109030c01 79
    0x220315006c00000c00c8440300100030350081002040c1c0381010350400c07081c04010390003070a00c1c4042c03903c403010b0581d2001c0030420318601110b00c0d08a40c0d03902e0011a40c0c1e441340304001406946091482c100b0960018a05544080c1c81114508500303101e0429038110f40e0300114441c0450144ca00c10408140701e80d2030607a1050414603030100c105004c4184074504032003a00142c0059034049418800c1540c10850580309a81c001c0051069000700d5010441010000e0041c604120110201510011260060140310052041070208a1420000c400206d40010300e5001004d030070b01d0910040c2500c00a040000c40768010842080401044d1050303920000c410480380704989102000000f40c2c1e42803103114020f280d038841d0380500312100d281007040f4800013120702c0c640d2403801005029850b4001409415078081c0f02c90810b103601d40e460268600084040000e03070107402d00740c0d0410a134041c51b015003401c5009808581070013524100640f10744055008c13091400c01c9004030304403108410011001c1c0c031070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 362623678 1250 362622428 362622433
    0x180f14040b0307170c010c081e070f0336051c02090c181504090b0a0e072705010e04180506070512011403060a0c09150809010614010c0b09 61
    0x900900202e4102080c0b68024601e000a4054900003c2403d0000c0034202d142441c00b0006611141d480785a64041c0d45a6420140d1240d1072444140322a001141d80710b603000740450b419032519286c001c1c0b46045100700340d078201c00c03911002c0c0c03c440b100e011540017024800c0100070260b0304000c18006200f240000703a1844040348111200136031104103140e0f015075103d0510980d0740b201000e500000407080d50000d40501040600b18105d1030368141601c05403000311078040340b0306070b0703400016003503a985411010403444643e003400a2075410400c03400480482801c8038202903076100c00c8590340d180e10303c64540418001c034092130503440c0950060741840566a0034400d6542d041d01c44625015046441c0b0780406e1000a00f16026000140d01d50b0040007010103511982c0e0315000420344815004e0500319207180c44000c03140710140600540e4010f4903060404d10303100803245000414045080e15170012552030180080382c043c2c0c0c4c52513042c0fa000b5060f1a541001c160640e070b43e003480d15000b0712010460 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 362624928 1250 362623678 362623691
    0x3071b030e0402130e01120506010b090d080408100f021603080402060c0616112107330b0406050a03150e1b01020610032301020d020309030307180f1404 67
    0x5a03503038800340c81c0c0e18031003c14007075600b42001c103545c0c045001030700b206880b83c144180c0300000940002d596810754122004264440805d5004280d9400019100500f000d40104e4045460030300024200041c7e54501c034140201c0e005284000c0c00c0303100381030007004440c2080d0310890109018400710303038002c1d00c09010249401303078008107582400c10607038003a01030407a548002040a503100310460824140307070001d44003509040d0b0f04034210526011a2014145003c1044401e202200f810480108a825914200001880c5560840000c0c0c40580c20607245800a03491807810076100301d02c1514805041d2100003802c40d12040031204151101000c4507484005c13040c0110400d100c408020042c00c0c20f9040e28032030200019080441c01003941d00000704144c0c00b00081110015980340170005d1410b0200305c02c982103000e902a1040c05421400140000b041c4080801b002000b14071820060751800c2007445a01040c0c40719600e98071408108541c2d4120034009088060020100761900800003e00d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 362626178 1250 362624928 362624957
    0x70c0206120103030e0901062a0f02033f07020f12010903020c100806010e010f030e0111030a0507110a060c0905090f180f030412030e0a0801021c0203071b03 69
    0x1c240c10440000780c0c03808007500039082003610540505060b04040404141c1d0510000fa01d104030001f1024081400315140140060303410088011500901500c003200d0f0301602165000101100030b101c0074111500003070700600ac0311002c20103e5540b12031103150240c10307001c100d190f00b4480201035200d107888041e1309140380c00f40700b413a01d0309200e40c014044840441e402c10500c54204007825003403007112400c211950382c2c041480c8840b0002402c100380c204000c01400c4004001230311000c0e03420b6103001e1542d080500700001440c42a00003150074071050340c41d1071040714400700e444000081d551068081c44005109600b040c140380c245858200d80e2659100001800b024056442180c01c0c0800380a0214400d01940c543c8000704189000748500b814441d250742e41ca1003584035540e29402d45078900400c02d8416841c0d60318441c0020300040704180c98800c0b02e07000b503000100d1001041000d042e0300320b28070454020703244201410b4440e91b895100281e41d62200100414045040040ca034001410 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 362627428 1250 362626178 362626207
    0xd051c0509180105150313030c14030f0712090608010308071b03140c010e01020c0607060605040c090e07090302060d0c030f021b0c090402150c0309040911031b09070c0206 75
    0x60b80c07070740394082d000782e5450101030282c0341c0f51001c031001c8900800c1080142ea0180c0d03403200280d155241c0f800d500b00307140d0341c1441040b600c591061151140000940c4401c1c0010000c003030f09950740500c02016135546854010b40e01c0c08071a100b00c1e0082044507004001090b01c100c058140c05005507401202c0c194088000e0350090f1482d00300303d50421031401c9034032503035200304104c65020100b030070101e81140d84030002035610031103001c13110b1203810b00040110030440b080c0c000030700074070b005031007441414002a80030f00081038600a942050358a200068940e6110380514000c403500070f0714032450440142000c10140602150704c2081c907456040c0d051305040320b8802130076001d500507411402c00001281050905401c2c0103118481e200f10b809100c056554801da5010750042e1610466840401d01969415800f0f500e07401c5074041c1c9450481c1062000c0c22200c5031048000300c0c1078403070385981e5440c8500e100300040c10314ee801c03040d010000b90f64940540550f45071240020183ea0800400030850407 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 362628678 1250 362627428 362627449
    0x30906051e0a05042c15040e0d0e0123030402101803030905040b091909020a0f0608070915020d03020306010302120a0b0f01020a0f0f020a080d020c0f0d051c0509 71
    0x800030314009000c0004010303890111185c00b00309600e03070042240f164800001c0340ea010f030a201c0f003554a4892060190f65a90103459070010b150144c8174416900d060240ca14000808403070701290042110b442c1da800d200000095410000388890308584450b003d01240849040c41070042c03290f141201d82c0000c0c0c0464400c0011031180c0d9036083d415040c002404180c50700c0260560003100141d00740300100b0001c2110300301d400a04040001c2c81031881c000151390141560040344040070301000403901c507070b02c0b41d032192140c84941c442c529480d5580341d41c1141007070320107120401130300310321100204144030b900259001101458094100038140070352221140050760221480c59031a40c58004e2800c000070541800c0d2002d0000d8440d82506485910203003030303100401091b08800c602c00904640c3d030146400043c04403e41200e20050041c070300695248142100c0320310070712140e1039080051800d40300b05140c0c81d070f0040282c21081c0030000f40004065007099070b201808414001c4140d640c60300c04075107 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 362629928 1250 362628678 362628697
    0x110616171801112d19030c0912050309010c0c0f09021306030b09010905040804170a060b030c03100e010204090e0a0c060e0d0b06040b03010509070e010e04030906051e 73
    0x240700000481445070845205401c01480c050061186414040c03502d800c11420a1420b054440000d0004414000911440b01d180d850310b00d03030f196442c51059060344921004840d0b508c400c400c0300d880c0e000000001e03400900092407940f04004102d043c2d407088614212441c0301704507043c01300d52542d171425003020098200402c40d980c0803c1c00707100d48283d26150720041a40d400d0030018910801c02080028005001e50b401180c0c559011600700301e9840100d0f03000784981804c602910700800c005640b140d451032070903a14030b82040c2c0c08800f24a008948088201c1006004002001c60492018041e0000d0303888129155400c0c031002488003000d0003880610820240174182c01e22007441c0c0440c0e4100c0e960050070070020384c820050b0180c0c0b680002840a9500440341249956480001801804420308515013650906050000c950800070f2640250740800c2d83c100080c0c0e0702d0303420040c0ba1245c116030103800181c40b100708200300c2e4000c60050491000d05817521444084000500c441c1d81d04c0300659 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 362631178 1250 362629928 362629951
    0xd0b031c0210110c0705100c060606050c0f01110d0f09150905060112110d02030a0f0503090f0904020a21060c02210a0206270109060605090711061617 66
    0x9850005640f00303e2060881c140e50840c1000c0c041100c1e03a95031181e0340202d9003c0c00207507602c40005400780c2c6001d881550b0201c0706201d503a44605000b4202d0300001001000b42c0f094612160b8942c0041c020355401805048080d814207603100d0550f0003801c00c61071489511941c9280343c802291450804000d80e601c2d202c004140b0042c4d920301586440300507031003a100490980c00c140c00069140e50340c4920190104c1e0401e9900507517000190400150200080040c00480e01940801c48044003402141000302c51350764555501c2c1003888400741d800ca40c000c1d400140400240550707048500000700540c00d5207045050b80403655103100403201040040b60240e13002150303880e8610300c90340000407400004412141450070400019603101c2c40034150301d1010040e420003103541190705002070003455a000090102d076005040c684000d10060040030b008510b24400520000d02803074500c1c6c1d03209a04030040c01c45964003407640719001c80300c401c07190400c9003805400c00817096800342540210000c854 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 362632428 1250 362631178 362631193
    0x60903030f060915010c170a020a030f0207050d14011d060a270b190c030204050306010e0906220c080115060f050d0b030c03010606080703050f0105060d0b031c02 71
    0x1080d0728503400109200c1c4110381d09820044000c0c400b090b420041042803c240e001881207160910212501c50076011140e040814810074203a40050a40c4410b80a42c07100d041d44001e4050898442405000b415000f001c1700c003a0200042e01e142d4041203140900c800094620101b00221000e060422a00000c40d0320050901030f030807074a849807001c0525444003a0101020500d9014040c1385990b401900c0360740c01d40c00081c4e040c0707901790a459141d24080c02c104010440d464024000b03403c24010b01d07000f40700786000480c0781c040c802004c0740242c414000410303180e6181c1c40d94a110495031042c030130b050051003007400c00141000a0240184ca440c03000800d002c0e10851066131003413030a40c801703000c005618100a0316540c0000890341c410b5212040451403216007404a0703e00151030f01c8050b003544c82c140000500d140d04c04031302405000582d03402c0c04152a0088a521194401e0103103d07402502007212000702082940704500080018013520012440510403803070a41c2c0840051016810144 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 362633678 1250 362632428 362632441
    0x80102031f09290f03030a051315050702060703030f02070602091f27050a0305030c07140f1003090b0c0a1101060e010b1308030c07030c06020105042402070506090303 73
    0x2104000c1c1004440400108519450034042403e007482840504188010b07035007115256080c0c40c1800c801c024013240c2d640c4c00c0c1240000d019620602081c00c1c0b190f0120070100c0c0c4d10300000d40c1d2404680321a62068103045841e003c0292691020b00102c0515039100f000804421940c000313001c107180035040040c1c642d4050000d00c45080c41d941d005844c45108940100c00040e002000401c0c00c4500c0001d00c5134481448a03680c114000315001590b1041c201c440c00020031000200514081c5581015180c1840d699407144650080c0700140035441180032188030900d040030b80c0c1c500d0180c20a07141c0411444850340341d88158110607100b03519800c100003448010150004880020f1001c1c1800801a0a2401c0400c102c4c0a03818020144105030000e0b42181c01403201c4015400780c000750090300e0790b0b801101d044a0762004580300c100c4200c0030b1030f200082c4807070040c46020320854000c4148031401641107110102c520700c107002c64682542c20310001001c11000c000b80c92040001600450fa00e08020 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 362634928 1250 362633678 362633731
    0x9060e01050306210705030a060204090c090f03080a1e0914151206011e170708070e010806120111070b090106050a1226030a050114030309061308010203 67
    0x442a15041c41010020301c07000741c60720100c2c80d4146a681540c3c1c4003840c80f0138440341c18010f0076800b20f541441000c41d29000e02102e07900074412141a02c4040203d08a4488190344010061051042d40046005c1c100702142d0100001c1c41c2d560410f1401c103240b05400c202c50700300041c040400300c00190080c6000c0c0401582c00c0d008890302034084031992007102d4400f10102d031500c200a0070300a81802c110100c0d00b2640140d1a04140001449081c3c200c9401404000c0c0358843d01c2c0105010100504040360030b00b80034800c0b042c02054295600c0181c000c00c040191050795021300801c0e00080310610382c03003100303000b03202c0d240f04030504140702503540159041c000070100c400750940d80e41e03034903040082040743c4e101c0c0c401e1401c641030074001c410641d83c9402d04801b80c084149444048441a580e140b890855003801180300d00c178219420000c50742c950300210392804e40c044071590103a108009503040c0d4a00704000e800604404101c0c031180a4540c07039040d007681c10980d4682014080381c1e5400c04a811315 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 362636178 1250 362634928 362634947
    0xb0603070f080907080c040b0307031a070f0804031b0302150106030c0e060c1525030501150201200c07150e01140306130e0c2206080a12210504030906 66
    0x103030f009201060820b551a6111001d1340783c0140700707540da1090794445803000d000f03075401150131207400d01e0420409056010504012203107a0000350f82c0e00c401e00c1c5010300a089940c0166059070310000c442e0036200e450350814215002c20380c158484d024000c3c40d000141220310340a810301d03590100b24081c100740041c20000310b00c110320303100f560140080e0450300ea00040504500c0d04144881c84541c595545a024620014150b201d081188440940ca51a0990803460480d01310100c03803010b002208504034200c03441d1144200d420302c2c9101c900408088804023800c6450b04000645040303035a030314070650340042110b041c840417590f00c110280d1650380050b09a603243e0310403900c03a45185800c4c4e0000b503242020011202c041d5aa5016502d02c0080c00c12451038442c1c0003030000c3c0c4140c20304030945036021000400194001d41042c00214640b400841d00b042c0042d417103c00f610300d0050384041560700e41d1503809500c0110351807542d890a000e015009180c020b50003611014951130074280014a03440ca07 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 362637428 1250 362636178 362636191
    0x903070605040b0d0216080705010203040b060d0c090c02150a05390d090209090c1f05090f031606181502032a01060303050d201b010b0603070f08 64
    0x400340802c003c04900300044660700c445000005a50700000b8141000009400e48043e00454000c6000c8080100c154002c5004500420b44100b040d03642000f04001000300040080c030300a4800710070001881a03800640210b203107401036581c841154040406240000c81d10001c5a80e00c4005204000c0c0054440d120310700550114034006030004008000c0013200d40caa850810b00c000218070103028030700d81c072603107041394010302c036000c0c1d4209101c0c442d541c0d0461a10039481175940d407206035060740340400c4c00816000300e900c52600b441c100e0000c0101e00c0134040410ba4041c0190a40310392100030402ea002c002e401240c4655022a044003000180c08909800c07000203402c00040281429400006032403602d0107205001143c4000c0e000350454a18030a00c00750340e60342c03d00c4408003c06802c1800352000d4030a840302007024074142510b1020107003030369084407000c1604001140150103205185903140c3e20040010549c2001c10700414240d0344100d81e0361300020000e0005403882648004810342114 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 362638678 1250 362637428 362637437
    0x50a320703111602150403031707020706090e22030203120c041d041a0a020a110102070b07051b0a060506041b0503010b0c0f1617060708010504020711090c09030706 72
    0x140ca90005503002c1c4180105255080605143d080444d90707000300c1501c3c1d091404501d1600c5a549180250665540b441c11003000810398000a179120720024404040315041d9907051003461805a921080c0328004d0b2110400442c901488000765010070550000140710707034001c580e140c6d0012200c0320540409800740506101c2004100406800001c424400000440164006845600d0300c461038100880c400d00c0301e0700c0030170200103030b5100c3ca1f8041c2183c0d5103a030f01d5803a55a44e00c180e050b03080340303d401001065800d007100840c00c03040c41040502912120010410080c02c1000c0d8010315004410344200c030410f41b250100321803801c180c010640350400c07901c80080324808001000e4100d0205000c0c5501090000c100c504032050200140903441e0494400d0b500c1c0d240c1c0321000c000540205000ba00d10101c0c0942500c00520300010300c3c28402c0e01d81d03645880d81a400c0c181040042d5004000a50740c09003851a610340554070304208a004640b07910500b90358080910a15041001551000080c030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 362639928 1250 362638678 362638691
    0x70909090b0705030a090b01140f010c17071403030c0706060504020a022107020913050f1504030c060e0607080f0601090b0d3b070b04060f03050a320703 67
    0x202540070454216580d410580e40b0307641d50420880003019040c00c0500140044000051180348805022000780e60589203282d0600c003a00054807a55028080200250440f1114484a43d150b034080e01441d40300b001c40602030104c0140306031841d00f09443d10170701b1000000c0c0c0002085010b00c142c3c00104020768065041c0340c2c40c1d42000c1d446204032425804040c5d0405106074015040204485d0340f507600600907141820180307400e4031000d00ca82401c071303420301c61034800e454650000034003864050000c80300d0b220140d860340d40c101d5212980075000c4403044e86480400520f100c041c03251920881d2242d070f90042034540a622052416405002981880f00b110b034140414400b1004440c940751102c3d6012a2041c144071500c5441d104102ca2200c130f08514a0b003503640f43c0c060341010341100b80240c003102c00f95030711030652a913140301e188034000c04070700c800a030091104d010741c128562050300000000b9a640348501542d4081e1179002d40e01150b10b01e1010b1001244242101c156080003103071604000c1c4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 362641178 1250 362639928 362639933
    0x2040e030702120f0120091915051206030a0b0403050f0f03070309050705010e06070b09070e0903070c091401060c23032101030f1b18050a0b030f030d1107120807090909 74
    0x100d104200c00180141448c10744526a212981542e8000f4400741d04503040c0d051044100800607000360041c0520016104003080181c500050010f081030342186c0300d5850354131141d030142c42a0b440000100c0f030701e180911441200b07100c100e0240d8411580d41d140800c14010500c3c003207042102c2070304183c0c10700ca40000c00a02030346402c1d096562940c0e1110045145480310b01d051440e00c1c545500901e600c031000010003452440c00700182040500c6045800c0c2c0d07090f00c0b460701e80305580c004094012403620000040004920400c0f421200b18080d00c000006600000c40384c484462144a40700f00a03400041da190781c0b081c0d0080250035100705401243c1842d4119a188868803070344800282c02c2004140c201c040e40b000e00341c5410000c01142801d84142d4041c200828003078601100e060003903a2600b034003a5042c1c2400700e00380c28914406805145004403140301c1000070031400c10180d06607107050298000044001000081461303060701c60f03000c507143c0f900c8010001282600324452075802c0881c8030f0700 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 362642428 1250 362641178 362641241
    0x901050c030a0207050a0203030705011401170c0103090821070f03020f040603020c030c0a061a1c03050a021501030506040b240405071b0b0a0c030e060402040e030702120f01 76
    0x40000002d0303005a5980140c0c101140342400e0040c010394075000010318035082000540c0200d4110310001c0c107040050380d840d0035030440c4101040f1a186540c02018040010358440e074040c0007024402d06100c2c0c24441c4e8900d01b40301d5110808039170703c08507a40c0000e0100041c2c00070340d8400c180d545032400b5403801c801201c05101c207001d0703441548103058011400f0a0005014400d03140c0410440084841062081c20320310050b20140f407601680c5080c0384542020350410040d404090a410320884000840304d5800301c0306d545c8050403010841c040c50003e134140d200d1f407020b00c5000314080c1004010506140c10808247d14019140c5601d00f03540c0c1540c20502456151a28800c200c115000100c2d65545603080da00180884078107005260305401d08410000408010340c010b404400b010007803003a454070240d0407250100e0b08540a5403000c00042c0052138150070007486545180156800d205035039010074180b010001440c14540c00104004041c24000d01c2001600070f1078440401c5241c040301d84469 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 362643678 1250 362642428 362642431
    0x50114180705191805160c021809030f1819080a0611120901020706110f0d1802040513060b0303030105100f020a20010e240a031503030e090901050c03 66
    0x1401141194510300300d2800c00012a0010054041d44c441503c103401c50180051008032984a0042c01d0300f65100341a5101d00c01a034141603024008190304000061980f00960b4001c208821512081040039240d080d118040c24000240c3d01c08541400e815004110043c5405030703000440c4140f8280402c01407600056408030141c2260b40007030080c0020b000110b481c82a03020a490082c1081d06102042c40c0550052032243e000b14410004002c040f10030320094030881c10a01000141802803a401104507130014042003107100c0785081c204403e40c0031505594084400910b000c40c858442010720282c0d00842c2034504044024528541c1000c001a508184000401c410800040c13035100b078490007040314000b2190081e464004035000300c45c44178003204904110310f0014650021082d018100095050080f129042d8011441801c1c40c141000310740104080008054445071a11039414207007002034051802070380c881c0c0640c0071003001d000740f00c01c01804904c4a685000100042d51041c40180c3c2d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 362644928 1250 362643678 362643689
    0xe031204170c070b0c0d0311030613020d060f0509010603020c030a08090109050f01051005010305160f0224242d0a15030501080706050306060304030909090501141807 73
    0x590701d10049880344a1a010b054144007031442220804103076444640003030440400d0100c100d460038031401c138003141a20805506c0c000044001d10102e540e5141094406100100045005090500044652094420590105542c0014039405004905011010318090405070409514081b084100203a403071040400d40010816004041091200290400d035105034000d4116640003003000f440a000f4401130315415807a00f500312000489501038007031188a003400107092542540003038020343e0580d0641d1000c0085018900142c80002100325099035002a610f00e40b00e07a520b4413078200405564082039a401001c0307000203000181d0780b101c0e655268203d0301140e144810041080d0910b00700c00c00c10308594454101c42000c9400e0300016298000d56140303513828452641d8480c403e544500081c09940c0024104000244071030418074001e40c0c010303100340f0304048403503556115201202c101c0c2008850503512036460851990860308c440e60003a035103a030410000e82000000c03550320300561049 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 362646178 1250 362644928 362644943
    0x9090705010509061c0c091401080c0c03040807030c0305060a02030606190909020a03290d030f0504150c0c060503061c060e06100810230603100606120e031204 70
    0x702495101c450941d8240c1c40c2031400c00307024445c0d01d8111070107016403000840000b030402c2000112101407911028400c135041c1c49100d21070300c9103200b5000c1a8400c00140d40b05200c10080054101c4041169000841c0102a8181000e06502e002820540040c0140040b64018004c0c0310742c80e0f449078104e030070348a41d110b408220701861030426030302900c803035100101032031010804643c255003641204400410000c0c0702101424407001088444030194103080d080f0411b0041000041d0042110130a0782581c0e0030464102941c40c0c14001040058034110000034a0442404040050600642000d002c0505089040d40f0300304000c100f8440200c1001e40b03101c50f80021076030900142d50b100000702c04c20340080d5415850300800c400350844071885050611f12501c03818103050b008921030101410a6502d06401a144890620005003c09004c140d8980a54010440404d10504c5000006d00440e05c40360108032120381600c04407041141c0346086a001040f160301c001e0812455180e001e40d200e03a0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 362647428 1250 362646178 362646187
    0x81006091b0f090306020d09150c02060f0411030a060603050f0a0201050901030c090308030f04030906030509060f060102100515150f2b0c0c11010c2111120306030705090907050105 79
    0x3c540c11040c03030340003030000d500c00940641e04555a401c03018080d0302406c0c441074040520a600e03401c440705001d0410050700031501003480d410101c10040c0d000744c00745040e40d24240c42075001900b407200d1004125450ba9680300d041080080511000701100810009000e10705134507000a4024480e6000003410503950300b035a511960300910401d40510b800420464407403900301c0700c41c408542c058400fa00401c24890700025a0761190049500c03a0a1410142c44591120507061413070046c003170701c01c5055015202a41030615650310610740300d800c2001c05070070021100d03c10f002c00c0e0840302809070300c8184200f00841100d003034081204e0b2580d4903200c0c400350103041d066100f0242c40421544140550500c5101c1000651140c0002c41d600c0c000d015031007680750114010746480c1220381008107038180c0702d00b1b50200610928941d0741d000c07006090400109113800003081c01c0000d04081142600d00100502c0a2800d08003c2d41d4043c004c19160040c0a0400072440780d903d000910600e41080ba0014 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 362648678 1250 362647428 362647457
    0x11011e1e02040f0305070806130f0809040c031d0d0c14070b1303050115150f020f070608160206010b030f0c12040308330904080c0601081006091b 64
    0x1055000344503403522045480b140c681c881c1e03040081091105444900c030708180801c1d6054080340d8140140f940003e42034200a02c1e40d20440780d03030403101003500e4940b800d22400c00c158480d4025000d0340c0e83c0c107a6001a6000c83c0706407800d140550740b074460416620551450f5412600040b84a1402e03070856a85581c109800c00101c2c40d05d8001d401548145401041903145180d170349200005807840f4074000d00215103a040580000c18052044c1c5010300b0301900d240f07074540d014121400a5034018815070301100e00341081d01c0d1920441d13903c1180052083c901b0000c0080c0907150b000c0a0301418809012a94500865103045d80030143c070000050001c040811204030701d0360200e40d1f1a50410701040d12618060602501c502e40446030f1000300750b01d8103140e01d04400000000409004c11001c4260121040b0007404101c0c0c00c001c0080751415020051842070450801c416070081c244400240b24461203000c3e400181ca025078040002a820061251000303451200b0155000c402458902184070194 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 362649928 1250 362648678 362648711
    0x10c0c031121070506130c0314010f06080d1103091014070218180a0b15040207020303030109061e0f05010507031707050903010b0d0b0604090212010c03050711011e 72
    0x2d01c50003001503244040741501ca030b503040c0589100b13070141064031495034828140070310348210700394024481080f4000030710014040c030880700104880c60b8000071b031011083c24060304a402c690080d498a60141c6c04540b0721326841103c805072140c0d2400a90704201918000c1100f0202c0e81c00d10200f0304c500300035201c1d04054a1825500c200750000c08444c481045c905107202c6041c010b46e0061107910311a440c0641c007110000d03008401716071040301c0d507031141d0f100402105d6000e02c6036440355100d50204120000343c1e80401c0558081e11401c03c0c0003c6852911040da4520756480c10f0b4805200c490700d0702000000440b0301414101e034000c1c02d0070783d6141c180e4503040701c200c2c400940c01c04100c80302d0024030080c0c170342c0702c005403081d140190001c100c2e10071220200711800845144c01080700211400050321410b00ea089401058805401800b074040317800314181c00e40d1040c00e0000300090b90340081046043d40248100100c0b00110300030000c400f5401700c1c5901e503c0b5110800781c206c50321080900301d4100f00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 362651178 1250 362649928 362649943
    0x51302030c07170301061106041a0a0902130b0f1e0f0f1801060210060f05040f02040e040305030708010b03010e0f07260a060608070804060b0609090c1b010c0c0311 72
    0xb0580494041c40310030f00d0b25569410078002e410014408000710110f05c0700c002030281c0101d07003025103080e00310100c0b00c4800c0400302c000e00400e40c0326114600d41c00140c6600b8038020b100c00c10900041110000300c1c00380001a00c803040550301c600010300c0703104c500407000044499841002d0b9204080b4510800c08208450384c2040d81c1908403c01500045e000c2c1038504150b81a01c525600b0748445070f0410140b103060340c11a0080107051121584208102d03d000da00c20880d16600d44805130405980b00201710091400b11015000b08038000200b044c840d9210303030740c41c1c0034080001a49086504201d0b03c080100d100400441920b41400081881c1c3c901075804404990719003e50102c1c6000c90800b0040c460006542962103e403c20307a000c280c00d0f0080d0700e11489140c05a99459184e51141ca610025007901d02d40c1e00d411000401c0020b119885a08016101d04401c40710300c2c0d42e48482c0204244504511013500c03110383d01d424508100b480d0300404000d170041d01442c0c02082c0d403050410460a0418 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 362652428 1250 362651178 362651183
    0x10509060706020d1a10081308040308031504090f06150807060c02040e010603030807120f021801110a080a141303060b030d0305070c060f020d090c051504051302030c07 74
    0x140464001c040100c1c94000b440790741107100c8180320105011114480702c00c03060001079071010310150601981440b03842c056601044000c0b054019020a44036107146038000c6d0415552500700100300480915148202181880305903000c01920403030340c94a0400210542c4000c00701500c0e02210700918048480d9580035042900940e010159104000b91003800303511000c82c0610f003441c030b61140d90035041c030038403088a81581b1484100e50364003004984400c0d1415a02e50440c5ea1441c44101a64161020300700707681c81100b00c0040106610b0000d4104002100742460341ea00040e42c140015a424050b14685002801c0a505507004000e010125005200000420f0300e9100310001c24000c0c030390080700d103002003601034074052803401208074242d4070100c1c1d83c0004204416410800071b0300541c4614809a665035006081c03240c1441201c0035590308000a40b400d0000074414041ca203000c06c2c0141030840003084440c505443c1c0008140280010f11440f0441980030000400b1801c40c00200c1c0d01856 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 362653678 1250 362652428 362652439
    0x3020a210204061407020d06091514040c0816050f0a120f03030e120307140403051c02122a0a080a080f070311070f02030c0a0f0e0601050720010509 65
    0x562040000942180c800c2c040026a13107030003004804075401c1100e0081d50043c180e00c0c031206940c2c6601003e8600c940c021070b013034940d002d1400050082840b4405803810062104640c0d030416040a100b01d041a4009000d1900090060010520940c40c1001120016602085030b00c4e07550300010203411241c2e00030043e40b42c80c01c0b042420449030040b0f850001744261410030002c1b24510340d0303541d20810300d590204001c20800c04070b030100f80a850a501040c0700a001d503460a40c59598885c24094840384038200b600d10410001c9600c0d405002d0130b0848041d001c0c005040140004c650480180c184102413504d80b131212070103080a0090084401c0c1c00c4c1c108421540d03481c454a002401408101d8460000200080c04600064400d00564686440c0c0c0e604284c2800d005403102060310015100c100e90510030070120341c80984640007400001c100465811a00b1403134071580301e846840c01401d0504024041145000080302c2050101142c0300e01801480e40e0030503c0c006848a100700c090440d03024 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 362654928 1250 362653678 362653727
    0xe190b0f03070b03010504060b0901171017010b040516020a141005071e090b03040803060f03010e0318090907121401051008012f0a0c0611041a04030804030303020a 72
    0x15a600046041b210305403820800d25a07901d90426290003800315660015441d10540401140340242042c3c10809540249046507620944851404100c250000c026515204901203500d028442d040d8012841503424848142e5108020b40703840c0903000041c25440042c0141150b0032081100743d280c00c401c04e40030441c904221801400c840682d02c06c031070255141c0103a01a82d203205000000848406001e41c900315195075490010304e800003084540c01c420700b607405050a0303409004a408820010014503602e40d52240405492510340e11018080c10048003800703454400010a03034122a00c0010401080b0710516000803d0300c141e28000c0d10315801c00e8248440051100507140c01ca95501d0020042e04a401780100d00c130300c01c03040b40b070b5014000301502050115007036030080c0041c00381490445000b03c070076518002107600c2241720110721074000c5000e01142070000c40c14251001d80f4680300e800c0c10715544d00c3d0320703007841036000040416401003403c1801030700441103001e10843d80cc107078031840d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 362656178 1250 362654928 362654939
    0x306010608090607020a150e0a050d080117010b090403080601021c120c0215010302060c030904060f1e14010e0d020603091506010c0c09020c1f060602070e190b0f0307 73
    0x81d800341c403400d40a000d05804034400e1800044c148021a6104501420b0a021050f000c001403055007e04506030240d4036904c0006001840581003001d42626448410350500c4000410710400d81c140c3c02c0660316182490116548001c0c0d0181d000f43e06140000160341c2c0d550040341003a50f039104900c0c02d0b21100e00d0b50002c154000d0310400070641a40410000000c2144003203a40e01c102c000881c4a80300f4640052000d403c0240085c818001c4004c100c0c2d20301440302e0040340440d07805034040c2030f4030305e1403100c1030204441020310100c4042c0140305010400f410529020740c158000350000b0b040c00080301c5d02040d2a00d075628204000c41e0000d02890b200d2620300701054841c60380c580d041d0700030055000000d1041d0f000e20f500700000741d0000709950302581031124540c000e60024921020500c68400319402486a00101c1c070051103446a022854070302d007240280c600019030300b00020a9414000300280c03450039a800e08035503245c0c0d683c08140c245000010600055007204e0f0706401d40200c07800800ca = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 362657428 1250 362656178 362656187
    0x14060918070e190501050d02010e03031309060305011b020d0e0d060e0c0301050106032309120301080706080105040501060c0b060409021009052b0b150303040306050a0f0b060d0e01020903060106 85
    0x800c0316240c940001d030880043c02c0c0b800702c3c0c07800d014280c2d07c13090808903040903520079401c410740d03c41e01904076403400c54025400c00c1c02c2d400c02e921200c05c503070b10b500c010f008001c002c1c05000300144045112404e1188405c00281d20380d031504428500f0400300844602c9180d88113085c24404a4100c2410841d03a0312107044c258588a5090045002c0d600f004000a01540b00b4400c500c00d0100740c3c8000384417440c0004200b1903850001c0c141008e58803034500d21801c1d0070180f4000718000c03c5144000c20450346001c0f0060300c1c1480590019202d41c0c50324004100c580d400c201004070b0140d20410300741c0e540c0c1e10100090020803032010083d4100c4c0c0d0352400703000c00a4000811a085d10720449558016104d130750303040c2c0c210800c0c0124016184111074405000100911040d07900030f5220380b2008030300c24078200800d1554025a0042e21626100d0040c048480818070540c00c904060070030070b0001040141c04589644078480d07200b89107a940760800711111000703506407548010020305442403035958500092 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 362658678 1250 362657428 362657431
    0xc18060118090c08240604090906020c0610050901060908030d09060905070303030510080309030d2607050a030c0203310308030a02070212030307080a0c0e0603040c0e0a14060918070e 80
    0x1440581200d5516910064041c02c00d0705c645d030010420792601c1d04100c2c41c103002e8070820074100c0b00b03290207001125101a0a1110b60301c90405519458881480c01080100304a010ba01810511030044020302c64844084100c61540440540201d1510440c1c03a004d0010142000b001d005030041c6403020042580c150410341c060003c2911135048a901c0310f10032a10f030b120350038109505a121880440c0c1d20750040d80c02800304007601e40d1001001202e03601001d00c040044134a1000518002224407403030750188110b1111a0350b40c030043d4104052a00d400e0a1240c10780e805c400c0a000002806000800d081484400765074000c05440d140d00300752480c900a074000300002c9110303024420402140b0711000013901d10402041e5100310440c2c0302ca1044100070001c00042008004200340c6c00c0e03050b600e44030021405584281030500b54185446041022a6000b41041b4143c6052403401407594201407007850300030320100c0c2ca210840c2c50740daa01480161021008a14502900c44005410141005203d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 362659928 1250 362658678 362658691
    0x504090515010905040b0d260417070611150c0d06030602070209011e0b03060d02060c0a0302010b0a290c010903050c06070509060706050604090b01090b030c18060118090c08 76
    0x3c2c00559110740c01c0006882012099941100030086840c010800c89030f0f542e08200d0007030004200d02c1c0309001e0910704607401a0001c8220075144e00303900504100c00c10114004000c10300e00a096601040074032603d030030851414480c14003c60000c03c003008000012245d0169481c1c0e0704201c40c40d501d29058010350030400c001e0b41703d0310f1140000038801181003a400c0100d031917188a08049401e0492688407600b01030081c40c0c00107548000b0034016294900141000c05525006020301c9100f0b1800a095920003260315000e641b2140b0104001c01c40400180704000b81e0320842203490706180c1c0380c40d0143c01803a940702500d42c245a0318809040d003020051002004420a071a802e07941c40009035060f2040f00b04641d0015810015500494540e40c4030340d803c80302c02080440c004015803541d408001003078110804030380c0c1e6541941014601000862012141503610400500c440740c441044090010081414800445010440c0400300b4520001500782c0001c104240540042c0050030840111881d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 362661178 1250 362659928 362659937
    0x90609040207050f070807061107060f14071e0212010902090a02070f080a1701080106050a03150b0d080d180b0601030507050d0207031d0103143705060103180506011203050409051501 80
    0x41c42c9c030104082542c200b524030544808054860214044408901441032450404028804a0009401d1008020075102d416601c1c0b80100d141740100003042c817200c2141141a072412919900507110540380fa40e00986c2c400005807510720900704040b407813092800080031500700142c4024120307040444590395403031f510b11075447c60b070b21511402c1c00c8940c603012305503100150b0101080003506045207841c045070940c001040c219000c2d0045a050300c0c3c00c10342100c1c250404105005464a944180d036440407040c4400d09005416071602d10045e440906510304040d00c2d040012007403801001100c0d0501c048000855072602c0c0c03814001d00190f55140c01542607403100890140300d40c802d00503000f003100342240c02c00c81a1101607a0160320709450b983c0c102600c2001c00001c03503000c0d0600b0022400f441854000c00d03e464031034001001c49000d40007440c2012141d521650210b13000160702410b56001c0340512400c5250747c20162251300840e844125000e09080400200e40d016240641c41c10070203888 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 362662428 1250 362661178 362661197
    0x3050603150f041b0e04060507030204121406070e010c0807030509100e10050405090a0b03070b30040b0c07060f0204090b0901080d1b020a050301050108031b03090609040207050f07080706 82
    0x10704d50a10500c1054003001c01100402e010a40540c041138010300b142c10014a080e91f60089a240750942410a41c0c62200b00a0b544031480401d11074264480643c0c6490540110b00c000003034100082c1c08030203401c4001c0402c041041500035012980c0c03602c2d00034003080f20131f800101c005050103c0480c0d140d00810918040c07101c1d440c0101d0645066480091085c001c503550768003440d00900c80701c1000b40d0b2500c5024400950360032508000c0001c1e070302a40c4864090207156101c3c4040180304860000c404000408201c00320311401032454104104110b000c4e034601c22810400003803c0081500d1003400d10019000a00c03c2d417941c05411401400e0b940700e000342c0c1c0d0b00c0394090b4648151680760300c04900319441005182d84c11403111184c552004050712012a101c401103400c41c0c500741c12050b401d07440024820300e266242d13440100000000d078000e5203444840700129a950041082c0703540075030380102c4d0f294108141400750a0090700c0b10745c102c030f204039a20300c1510742d0344983d4820320000c01c28061 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 362663678 1250 362662428 362662463
    0x203160e1905040f0b07090509071d091608100b1603030e061005270c0a09081c080c0c0a03031a03070807060f2604030e010314060103050603150f04 65
    0x30b5948a140c11040f4800034050b151585082050014407000c01c10850010100d00d641d02e02180a019900540e03921001203c4002c80b180c1480d0041c2c40180325841c0b0200b0030100c6106484000081d0391a450710034000e8594104111005020750800d04080401081900c0280038101d0200f100e07501130b540070321030b54810001894079200e05840c0140e108969460034011810401c014103409014103620304080d07038243c2d170760801c00c120507100b0a600882c00900990b04136484803200707000d0502c5501900e00402c0300c8086410b41020400701e00280159600060102c07081d50065501400c0325106071100301d8003071b103001401071110034a03002c943e16100026007014100058084140c403000b900030030345642010701c143d0308950781c1d0b2022800c10500b410002070040d031a8003070210310300d00030380f4220f41e40c10586030207004012030882c240c2c109440e02d0130808140b03412540c0503410000a003000030340da48610000c2410180714000c0807120040300800d10583d200c08a040520035401062802c40c080103e2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 362664928 1250 362663678 362663681
    0xa110604110a2312030403050f0d020c0a0b0d0f1d070e150334060207030b010e090c091b0c030301090605030a0b0a05060301022703010606080603030a0c0203160e19 72
    0x50b4503054030301189001015420100d4804c1100b04100c000c41e81042d60726610300f883d000982192449a41241c09130f0f0501c0398041058116004040f219442d0365400c01c00809514010594000030700c61f01d682c18900da68010352300201c00740703400c050184c2d80c001c021000c4650b04d05c2e0902c0341402c1001c8480020300350300c10078140072001e551b008014107281014004c22040e41000e4083c040900310507000240045141d505440c001804140c0181401070310714148503030000700c140d1152401e2038030941000301d81c00c404200c13170082020454482c462a101d12961007806110303040e05040300d0400150981d0006800009541280e8060740d0034054291500e050644130034407602c0c0200011505070200d01c1203801d64205541c444405800141007a08850502042c510983c40440c04034121940d40d10203410280580e20150400e81030500007410301401081e5030703205014010b004c102242404408642c0c1c20300c20090079029010010b4801a254041c2a407200001d03540d5000c4c611280b84210741d5445d09 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 362666178 1250 362664928 362664959
    0x60603010c09170705180106020d031104030b090a060c05041e08030a1d0301050a02071101030e070501180314010b030d08060102030301141c060510090b090109020a110604110a 77
    0x15503142020a0f01c0c1c03c2e007445501c1620181d003a2103001d0207001180d5600d075160003402080c42851500003a5141c084040e0800d204100703400b040500301002d800003000c0c4542201c0403aa807014800c4082d81e2449829801c001541000503e401d00780080301001c150311501400c03d580700d4100000c1c02856110b5180303000c2d4410f00c074800c019007042c041d240d0054010b0421924200c004a110b01044016000107421214101c031054602c40d404101e44041c03015090f801c109100003800e00308811101c03a603c55640f40400d04c074017810800181448061464101c502c0c0008581c0090028444800e886100b0b0181646800b02c5009100d11241180d007244100407044c017580040e0044c41c6941d08090071250f0784d07104814116001034032011a014500c00038850303400000d024484c0081d26050040c1502e541c0f518542c00415024200b45040c080c2c0d43e9039454880c111520b0390f00044e6a401c81e4841940c01881d0b52000a260703010b40b504110a2100180d008150f8410481c2c0c004031190b114900120741c80b00c1e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 362667428 1250 362666178 362666201
    0x15150c07050616030e03031b0714040203100b0a030e01050f090c0d11010c06060b030a051b0a14072303040f09050112030c06060b070c0302040b09040b1f120b0906060301 74
    0x443c8600c440120340182c4569604903c040c0c00d0b649001e05903850820091141c940ea8206035000c1002001841c02c9d40c4c1107201408021202035142d420840111211b115040c040c0c80c005882c00280c0e100b40328000d900ca0501d00840000030300c410314240c16170580404045038200950701800f41d8000062915022a80030300368480440070140602d00011120f4140344242200d640d59608030200c0d045141c440910310070b26040341e010400389030030509154201d107081036081604105107e1006101d4100b10341d00304c03010014142c1070b100d01c2981042100360700180c411501c144100b41e1b151002100200003030040d21a8264100546070346c645090003185d03402d100f4007134404440c4200c100042d11404611040740c0c01294046204c81d00c1c2c801c6c040f404e0b4000602140c0114852108004508160003000501e1204841d07148440c03401d034940103a0340c0c200038501c89449101061940d1001908403030030b0301800790055610b49103500d520b403080380f1310030654004c80d00d8072480001443c075241c1400b800036440c5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 362668678 1250 362667428 362667457
    0xd020f03010b151905030c071b031401020903010c0e033708070311030301141003060305070801150803030c04120c08100c0806030d05090d150203090123011a0315150c070506 76
    0x2a0703803151540c65001d0303c18000001d4509200202140034404c0cbc2000110b2858001030380c0da69030204060842e400c601b001e00910904c000091000e076000704800d41810440418110000c42031740d260581001100e005001c6510074140000078070081401801e002d40c825103071643d5161000c485196a4042440b503001c0c1103000fa210100c8508160107181d41e44d01741400c2c0854155160381e1040c4c20404c41c1e800204403699a4402442c8a0101c0c000020003805201c2c0a9461414020302444507880341340510340c10b01e0f20701a0000c042081601b0303054010300d0441c068a500c0c0c804105080080d1800184140000721558082801480c010030360048a08103030300c400345841d050700284902481440f81c02d0f110007a62200101544c80240000c40c4500c04101c000561418a800210303030707038000245c116000c0e0b01003200501070010829034070a084a040801d50382c81e5503614070400d4041101d5030303a1580110100c004100005002d00151186000399000c0d141000c0d160030610242e40030325a0408880c6 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 362669928 1250 362668678 362668687
    0x3070b060102070e090709091b0e06211908040f08070302040b060a020d1b061d06010618030213021624090206120402030c1210050f04020d020f03010b151905030c 71
    0xe08443d80115040c500c10790000227030b00240d0312107500c0c0c00080e600408402600508000140c541042c421220400c0808000c100316100300e41a81e075015200084100d40b0115a444002d00c5900d00c180c50050441c014500c04003615032608540f1481c640c031080b40038a050025000311440c0c04015030b804c1e00c11a40c004c01c2280c502d80000c079000c100303103603c1c6100d40d01e01e298508003188041c01440107030005501ea80da07614038a005007600d07112050b80401c0030000f1080c20030f542481e08a02c244102da4044a00911031640740c10750000034400c82e02d80c204880c0c0c0307060a04080080048241c7e00840700c0e00e00703ca041016204030350090300c01c0040d0084d0700a008005001c0c030720860701c2d441600301d0300150032102d8103080d0303a01090040c541070400d84002da00844002076404424000c403944250651106011030500c3e6010401c4075001e11030080c0310741504850110305850940c0701c521f560340010480000b1030405014080c195020500041c0c90291407002e10005d00c5c0144100c03070041030001202481d1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 362671178 1250 362669928 362669939
    0xb01080606040b090d0305130807080d0807090303110319020c040e12040306020d090204050f0a06090b0a0312020114011409090714151903020306040b090105130e03040803070b060102070e0907 84
    0x20f1410f4100d0901400740400c828042c0f00360410406082740800610300b40b41000c1352146030600c1c412030ae8081004100030007501503071240503074044a5040c10481800420842c04a045000350071800e5010052031243d80015a80042d6441c400340d0155020008030380b580540b2070f214040e020003100c100d40c08020800009031168010440070403076260000d5103805649c00182550800d0b2200c10b02c5004600030f111110496204001c0103044450040080e01c0d01c0d0000300c0c04581082c031024001103074009611164038000e4202c1c645000510540c4115581c641450040503025a00c00f14083d600c1c104c0007600c20100050341a050311841c190504440c420001000007141140341210200c00c002d1100458844000746c0c141d0031001182c402503104d140200600080b603000d048043e100b03410030801002903072502d4210202040a595004c103104440e51401884d51066521000c07591000040110503c0307400742c0101e000e00c500340c1c01d580c44c06070b950301031160350103080d941407000c1c2d0480302e006c000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 362672428 1250 362671178 362671189
    0x1b120507050307121407021509030309060408030403031d102d1503051603021206040f11043315050a0c0c0b1308100e1b061c0b01080606040b09 63
    0x2e14850031380810181184000c20404403000da51348005039025814406104c1580340b0340c5613000d41d070040118151314001c100d465a808000d8005171081900001050500d4800e8001c8a814910294200e00601c0700c0e020640c0d41d00c000101c0704105500c0d017401030911480c0c3c540c00c00c1c00700440701200100c1c2040716800c04001d0000c403401440040c45010000b0000790140304100c2e41e0f501510116003007a241d80140302c0d08140d00916158190007105c2000000fa410081212215401601d40c401c480c60340d402117401001440400101148005140f6894526040c002142d00c10054007504102d59a1200c580d140024010b00c070001c14400e110040302148901580303c44c0901860508034400d5854001c1c1e0ba00c0e40c041650070380c0180c041c42003031161500c1004000741000400e075041007580b201c04800d94036280c0340c120080d00c1d208016107145403136441c00c05481d801205c11100042c5150408060401080343d80f078600d0102d85500c000409918040d416201100c0c041c044035480c24580c28100007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 362673678 1250 362672428 362672447
    0x20405061014092d1516060b13061205190201050a11010b0a09021e091318050d052d070b07120f151a0702090c0d1b120507050307 57
    0x54004800c030030003000f0464010300f40e1038181113148100e9403040000382844408140300d1000d80c0c0e5144108080500720080f0444001c0080c0c00082c00070f0b030b85001500158242641d84802040c035820984003007005003004144c1c5500c0ba1080080390b000007288203803807840c0745140c840640414420b00c80c90f0340c6140114100114000324000000d030303135114880001c20400090300140d5403141d0200c2d85001001e0700e80481e140c518400000c60b03042c090280000b8010400100c2400d00741070b222300d080a004c13007602d040c041c0061b0b0b0100c240d5465442c0048014440c1c0c0191498200366011404100c1803d18000210b00c01321603000f07a103e14100281d00d80c00441d40300075042c14200034842e107200d410810184580241c3c140d0300c0300c0c042515403811ba09184648185e410220322283c0301c2184040645060003242e000643c107507602c141c242c0e80c00107a01d501c2d0044001724840541000000b6160089049088034048041e44902014030241e00086049031801c8a150b40410420004241e0302801003400e071 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 362674928 1250 362673678 362673697
    0xf0611010e15041208011412070513021e09100305041b06020f010f020313020904020102030d1b030e0d020c010e030708030414010f1112250b04020405061014 69
    0x400c01c0c49140355100d1925410305031121800d41c88605010402101c1c1c4500f200000d403d1400d1103080d41030400e81c081e42c140d01817030b07584240c3e95104941d0407010b0502c0905d00610f0010f01204c0c000080c6600000a58444444002d040240c0f80714401100146400d6401c1c4e690098080d414115036511b055009000160041d288020385d1030303081ca100c0f1401403408001d4031041d400f50a60081c10b180d220700f56003040700511021801842001464038020461007050781e01100c28688a031190300041c0d00754820040052081d90800b400701d10f0068056000f4042c2079266a410400e101c120a6101d45036031031400301400503082482c1c1d60708030b0f44c498000740c1400b080003010384004542c2c915807946598019400030022034071074220314159680100b40760020389a1804c12521803c0910245516105240c261010922000c520590340f8180b00003000c0b024030780007440c919005000c1c102151600412142280b02c1e0b81000700064181c01e00001c1c00c0034500c0b180d02c2c0c0c080f04594518104060350001ea402 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 362676178 1250 362674928 362674931
    0x3010603021602031f0606020f120a0e0303030a0e0c0409030813022706042003010e0903040b0403030c060c030e0a150f06031a06030703120c020a03020301330f061101 73
    0x182025903000d002194a0961750343c005403d80d1071080c651402c0e01e030140c1c0900c082d13400000e10041d0441001c1245a10f080c0e6003000c0c165266503050307040d1400070b07003002d015801d0300c000310030130240d0809540306100c0c120b2483c3c00c4a9078188040300b000306803070030303240300038002105480815035200340003141900342480200124071005902d008408140041c51503090000307852414000d850a02d8451320108c4600200b03403032008010b402942220344410f10409820224150004800d841d0600546024107001541e1660f02c540e03d060040c004011a0402d0360303100d1415075030510070750207481081440e8808501402d6078244544078070842c00d4115402080450700c0d500c103192241c065100c3c5002442c0305070610402103074201c20703001c3c4101c8001c00450003588a00800e10100d254400010312201031854801d480081074030120b0b400140d190b100035010b60800d2094001c12096035000b00c103c038041d0182e902062400103005072001d04030712403180007280d604810300c011341c400d02d04080104801c0d0300 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 362677428 1250 362676178 362676217
    0xc02010f140315040f05040206031303140403060f05091f02130306060305010e1005040317090309042901020a020603060405130f2f36010801060311060408030301060302 74
    0x4404440d40c011105030f20011190140452607103850301c9889004070030440b04019601d860360210322a4800901010b0b41500724498100415208a0b84041080d20041c0120f48130340d41e034070700a0301401c040c030703420000c20f4100000140c11031030004c3c01c2d4034039840400e508d46050041c100400c1c000d50184000100c180800000403011400354000d2800940c4030700d0001440c401481c800506241c000d071019aa44c1c0d050506000100303074042041d80604981141020303090300c8403541e140c90351191904640d0001d0800e030310a807105503605480700d0500343d20302d100c80b054688400126111041408001d50044080c40410300c1414a070f03000540c480041018605035144c40d0326034004004100030226054501158690318400c98181342104010348031070441201c919000c000703680c080d407448440c010340c44050001c4031484081078004200714000c0712450302039616002c0850291a03140030550b03003401c0c84502c510041c01c01d10222000c4440d070030702650440e420208100c000e50b20990f1845611b100b080c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 362678678 1250 362677428 362677457
    0x6020d0e0303090703060c0c030e040c1b0b0105030d1112091507050102090a0e0f0703090602091018050909031b0a020901120311030c030a0e130501081614010c02010f 73
    0x440c0030703d5002c002051310a1552030600152000c072000e4804005d01c42c0200e00c00681c100700000d0251104950202c0d07040d00b040000c4680c1145803c0c2d00002641001e000f40c240241d4800881c1603c5051382510302c1c0c0b4034503880546084026203c100b089500902e10100c0040d5680003900101200a01c00d10650380c0d00540380300c5903000310006035516540015140c200346007414004005003080d14030920149408890160300800c0108001c05068550708203c08024290b41280e5220800a00d5004450303c0c00030020003284070745080b4218184807110102d500c1c9450503803c3d110312200360045291007103800d0320f00481c962850144860348a603c3c0e001005a81e40103929001c1c003c501c51b01c00ba1030036079003030050501d40602d00d83d20b510341041000584001000c002c035958a40c072403d1031040c0e41d201001007048044c041d220b880b4079501e010000f155000e808140c480070040d8594062004c0e5440382043c00781200d0342c6003402e0204100d64003050055016074841c2078031017421308000b8400d50859 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 362679928 1250 362678678 362678683
    0x20402070606050a0605041404090312020a0309020406080d090902031312020c060304060b1c02010e0f0105090406060801170607170a0f05010b0408161d060d08040308190305070c06020d0e 82
    0x5d40041002c1000450107000039120b032078a00e1118a000c403420f00606003240c0f0050042540c5104c030059203500014003507d80c1e4000c3e0400f81e0015809001040740503554420700da110110150003c0009181c1e44000800030701300c1c0290703400b42d0040c402c01903010003583e441e007143c80142c001e00340542c02180c0003400942c1d5040c0c007540c07003180110f00201d5140b69510800501c03c0b6030550404d00800b40d41d5035200982d03444000390100480c00d944480c2900c80da0340040eaa40c2c040d100c0d029500034140311000c100e969101944604807480c00304205d032140041442c182c5c0722071080700c028000036140f8194811f4025000b05a40c1c0000b01307c003000842c01814038103d001e4480c2604a040042d00005080100102c100400c0d054640c07103005000845080080110510b8840c0050198180007440442d041380d13114411107041035408403202c0ea4441da2890000303110b4100100c0c080d86444910503203a43c550203070003800d101d0703006036072101904480d594410f8001c0d0401444210740d00d5440c201c9505200c000c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 362681178 1250 362679928 362679949
    0x9080d0c092c160917030d060311090609011d0711010e0d120c02120c0708060103050a170301152a0b06100e0a170a121706030708030702040207060605 66
    0x2011520204241c07000c8080036100340241c1400010030004072001035880d03021108000f51002240c0115844c440c030003285c1d00d036000c3d09401301c0f211850610008100a110210720074240e03400d03141310310181e0760f072010050354210034411603490801079920f180300b030301880300910380c801c14600340400040900744009003110240070b085540c2d03900c902c550441e0720742c10540c0c10540d075000c036601340100400070f0030094a0382d402e40c084050555021444806503f000d00904015020b0f502c110b503101c0d81d403030400070741d0b40f80d0485094a0310040c400500d114102214203c4c0d05917040c10b14843c0c041e1164003c1203900d01e080441d00900d08404000e003e6000c541001d01c0c850141c0500e00790042400c1402c1000345e10341c04016a6014020422045006902d54850a10031145004111083c440e010b02041e810000d41c0b200c0180441c8000440c01c2c11142c000c0c0301d050310002c4115442d102aa2040b041c9552203d280c0921940741d03106101610061400d50000d04696118000101c0d120f9519000300d002d4001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 362682428 1250 362681178 362681219
    0x10c150221070909020a050d0e0c060a081902070b01260d090314030909040305160512040801150803042d030f03110a0c03290109020c1009080d0c09 65
    0x940d9014041d845601c42c050f20050503109400b1803400407a640d0140481c071070f80c0d182064080e240c58001c5061101031101180803240a0b224a40d9828038000041c880030301113840c156100c6068000b00c0c0d40300e5052090741d0321194012170070b00e207990900c000390180e000d840700c080040c0c802441490f101c0c10380034400704080419903190003003581d0942c40c180400b462151303100c0c00103600600c001d8296030f540135080750700a034050500e6035903041080402010326140302c002411903c50083e54640e0700015034010800c91301864000c00004a120b40139040d403410b81d10401c83c240d40b0900085c00780880c070041090300d010f002070b1101200e8004e1a03103602041700940c0250f0f41d948200040005140d000312402c82445071070360152044e01c4003550f5140314481e0902015020b4002c0d0054402143c011081d41681c1550040c405207580d81d4502080d0040c3d80290310001c0c06001d10101c1025025250140095103644010b0040c106000098164001e10200c020402080200c100004150031805181044c201 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 362683678 1250 362682428 362682487
    0x90602120708030a02070c0b03101e06050a11010c0806180403021b010207090e0c28030b04020d050a0b072703081305060d05060a050907051210151d040506010c1502 72
    0x92b1101e8840d4a20945a0002c0107460034902c80020b4140c60802000a551080c10704c1e07a181c01d24074004454050f070004116009618060790800c107146c01200c890301c0356000303d803040381c5115103c03051101c0721030507500240564804201b52074041203483d0301304014001071040f1000103603500f11200550320f0384ea034508400d400030040811b80d4141200c002c0310902d81103071000d44240c4c4c004035014040302030b40b00c040d144a0400011604540d540d1119070b80c0c0369041400c8074070703500e81403c20039201c2200356a0030000c200c404c04e040da1034400c050404a034001d03d0041510390700c0d2940e19041016130046042660160381400041103580d03c1030040c118181080d440040c082c5401c3d4244000e001d41504181d110b00050f500b000b408a5221040358406030120320410b41c0c98035031040740c120b0040d0a80084124034142c0c031240c400d0b030b54082c500501d2070154108d01c7c40711144090520084580646003580025502103015022510041c101059041c83ea0310061405480c40c0e095850300c00e52811040092 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 362684928 1250 362683678 362683681
    0x315120109030e090a0903050a030c03140c0c16080a0f020409060e100e0a0816060b041a091f030206030403110601030c051314150402040b03090d090602120708030a02070c0b03 77
    0x134102aa81c140e44203030079990420000d84252000f074024000d4049841c1055254501c07203d6007882504449091040888203580034181041402c0341608841c140203002d00c0b604480d2408080980c1d10501119054400f80c10b00d40741c15109e0000800c4c200d0701c2030740c000351250b0400d80011200c0c4150040881844094541d6400025084040d80d000085030080e641c800e0b1a0500410110411a92403070000c50141032041740502e40000501031440e82c2d9076010b464041c0d104154400140d6124010b40308803040f43c01d076650300e00413030b00440b0f02061100307501d1b410318014401400c00d00001c64110303010313060400c019840c8640192501800f40c104a81d0400e024404010070b040a4550f001d90602000017072194204501100803a403a00420018070b44005902254254131554100c802910b12082ca00b0355900d41502e0503aa2803400f004d01c000000c00c0108000307080c44c07001c40e101d43c200141945462900f106d039103d40449030000781149a20550820030400015000b5070712400601000d9000c940303d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 362686178 1250 362684928 362684957
    0xe03160618060f120f050c0405040b0a0b0706150806160908031c0f140411030c060c03091905100c05010614031009031b1401060504090503031512010903 67
    0x40c0e000004414035500c2203240140290b5030042154501c0414528044001101102d501c0014021640112030320700d1601e814002c0809540000b0800d42c0e07000e4030148900d0090409100f1043d039148921784888106100e1100000c03a80d80148490100408010511949071407815051502c255900071984804a25141c80584c014141e14004c02d00c00c4c0103542040b80b19401100b10301c1110402010142c0c1c1c401450f0b0028080d50301066150310384940041162401d45841c1c6009580d010340319200380b00d00540e0303841c0c0d032421b04119000101050051810f01c03400109004c00c404100d20703505240d1000304004112741e102c4c0070340c0402d00302995940b209825201e007019401c413030164000038032916a608141d6081d40700040c2d00c030214801810001541403482c02c003101d184800b6921880807060040110017804204504c070303905038940d0002080702694880c200801c551009400030855001400003480c071040320303814490080c0380541401c00c1a44040086403c4031011a4101e02080240210460 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 362687428 1250 362686178 362686187
    0x31c02070b0a020403051902010e12030c011508150705070b0402040b0904050a120914222a05040e180c040c0201020a02060f0705040308031f030f20060405040c0e031606 74
    0xb01f0030b44880d0a421001480c0c0000341130040b1054501e0050309020000c00800324200208e801b910640d100030801ca403200c4030f03203140c40384051041c00050710540ea24490703600f0902041a0040c40c003070b25954904100c507a900c0029800090090b0707071066960658803104d460b50360407036200e244640054401000b031407600e485c44c92080c08114040150300c0c0743c10b03c00d203611848030140882c01110b102d0015440329101e40b1803c4041080760a4260401c0499403284505070b081e9010500c032040b1502034080400c404447c180164401c8514800c28500030450342038a40407008622440d01c41617170700c000541c40100d000d4400c006003200050f0b50004490500c04d40c14040180c0150a011160b1041d062400c0c004000e4021408045e08050001000c2810520b8408604034207220840007100c415540c2d007440b107540b010400c800e6420928960130b04445000c444d00c030001c1424010041c07410281408144070040c008800f440b070901c00c56007498215a5410415005c2400c1441c84103440039040401c01031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 362688678 1250 362687428 362687443
    0x31b070b13140c09010513020d0c0917010515010c051009031806020a0b070f1e170906060d0b060a0b120709060c030807031505270601090305031c02070b0a02040305 72
    0xca0300003c4144003580e441990060450300c0c1104c00109082180a50307100030b104100c40705401c0d600c2d005c8414401508460000100c80c008a151140f602001c100142603030703402c032041d600b0b105064201400f60740c00703803058840c2a0700a80451300484034810b104811600e8400040c1c3c0403910f1040000d8040791458400d01c060001031020344a8401e084d81ca80188910192028040c0404904580c280a210301440764650296010040d565848803401501d156802c0ad0002014150380c2d0010300c0d02d030f400040e485d02074607001e030000340700d158180c852044150300580b20b140d2105000c0e00c0045c3e64401e40018085034500d4840e00410703820f0184000d0300c20015a40b04e0b1080c0310341e07050607030f01003500310030351603400320940c10041922900c04540c48014803068010a5001c0445654088061030b03a0b4030b06c1c205005d00d000540500e4842d2070040d41d40c02010302c0010003035481085254202c2040c1000d00c40d6004c3d00c010f000d070030701c0308640d100e03000300380b04546000105a0110381042404030421940703 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 362689928 1250 362688678 362688713
    0x5071a090717060f040f020d0f052a0d05030c030403060f050105040c0c1203140903130819034a0429010e040f09020306010f0b031b070b13 61
    0x40500710b201102c841d2201c1006040e00e5850709080005403e212070782c4224400c00798010b2116003080d04900d090f4541418046040d91207210300840d0320750421382001c010000d460207a40c04da031450a03550801c400101e020740f0889050005000b030031440c420130005000a076108140108030050071003502c5084600582c0b10174412420a01d60216003a04038500d07803e55500040030a80ca0301141070250302404107900440c0803d101c0d82c0030010300041c0800034100721424228a01252517840d81c0d0f0507a103006d0145400402d105942d0702c4400207000c1c11400690006650509259a0404540300c0105606035007112031084c4401107040c104500c4880c0c0c0e6807080c0101c42c10060b42c952110005600311040607201e610484007005500340303a024460902000000410501069601c20003a6024000a01049019100f50000490708162060090040d55034000315a4115502c0d0020307000741d81c5103022014803052003000200041070301c0306222031180d80d4034150010900c0072464505900542d06a56 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 362691178 1250 362689928 362689949
    0xc1205132607080f040e0106050c0615011e03090f030305160f0504050409051f1509020705150705120f0f070302070b01150e030a120e0108040f1205071a0907 69
    0x1884007202500c0e06541c1a10f4000a1054880b03001c80280501481039810800c4220083c400008030b00e076100b070040c43c04400b600d05440310fa88071064030444080c002c03a2810b010905002c80001e0141a80001c0307a840e1096183c04076039128261a4180306d5a006481940001c0d260810402c041e03104920060a2101c03603e41880030410800004115000da0302a6501c0f9076180d2440d03c01f0300900304140d01221518103c0314910100c1c030403681c03000745a075aa0801005c1e40b2454009500680d6200381c5481c2c6402801501c09e0800d01d0410501054008004209010742801480381c454542e403040e902c5402c0040c5140200d00302043c1601046d4401000c0748205801040030f03600040d0400d003142e04483d281c44032039406505980060b0360344078492150680501c00c0b030703a0100601140e180442c403c160183c07617a8042442d0b00c1d004480b624412980a001c10310402c2c02003000030754140c1c100140385520304e061410410203548070407030309140000f1001c0b50200002801004c40c0b00340400e20090008810 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 362692428 1250 362691178 362691233
    0xc0306010510021c030b03160603060b070305090904170a05040e250807050f0a03020d05062409040f020304030c140120070807050a0807060e01021c0c120513 69
    0x5000f5503540b444c2520b42c2e0b040c19210007440c02c00e4040d0b040341c0741d003010082c03d0b030728a020071440407001010310b03201c1d00340040e08090f00010408403040403156481c3e0103589840c0b601607400e052101b040300190046544e2041100404028100c0780086c0c0300700b00e01c6541d5260784505d40406d88800e03c4d009400d80541035180340116040f400d402035000d225000c1404c00308040d66480344d09481030300440a821b5050000010110a00c0c0e85c10740c000c00d010560260100007540383c1c401400303804c0214600c01d501c111070342d50f001c606400c99003001d040d01d182e00400c0801e00412041000050703030000d407000c1340410600244001000560807008440c040319034002c115250441c0381901c1202c170012401c4845c003034009520824031010130101e80d4a16080801c580c10003400d4640041c50754050041950203e00d889144860080b0600842d100000b41600d131440b0240c14100e1240101030b40d80d40c690611112010407a2450041c0c003c0c0c502ca03600c1c8903180ca03a61000d5040400c06904c882301f044003c54a25034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 362693678 1250 362692428 362692459
    0x60c1104061205010501050a0e16030b060a03020a021203060f01210212040201030c030e0c0409021503041a10050604141908010e0d0504030c0e04170d0b100206040c0302011206090e0c03060105 84
    0x49c9996400455403503004140d000c1400181e004109008080303400007000124141056096002842c0003840756003114040201c0302030b450040c3c0026210141e0000400940c0c1d4010740c800c4140d0600c034940d41380840c0c6000846044841281d000c1147c0ca00b1790b100d0740003004151760b050b22598480040500f4140300350500c8210080d200d180e40010107100799a6814044250b4a400d50300300d042d2001c000c0c02c0396490405003091941c3d11440707641100d01c1d080d030a00040b89140d80c58404811140064182402c0505050030f0b11172603181e40f2251130304075038082801d80410480410ba0001001503400015800074001e4856090184038815401030000811003000040c184905c403070b04450314284082c0580c1c986182400c1e4072030100003400101840420240d0812507942d00c181031506007210082100c05c6c15035000d98413a0000c5074054036a0314502003c00155004203100d2100b220880b10009103141c0f0391021504548094500c2d4020340c0c808402880a07003000c000490141400311b8840c2e044d00c1200 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 362694928 1250 362693678 362693699
    0x40302190f0c1e0e10180902040b0312070605061c060f051e010509070c050303040b09070e0c030a0b01120e150c040f12060609050403180603060609060c1104061205010501050a 77
    0x1384038995100030544000303102e4800b03c008100c05040102c0707502c000041c0e41c040c82c1c03014040c2c6039002d0b4032440c6000d20051030747c680025002612502c1001c90341c1400030548400d001007000429064004891006601d07031322224008042d01c00c0c0c42801d0020300c2d2940c9a130301c003003140c0d001040034170b03001c000b0581c2e0451444c400700d036203044803012030702e44415544030700080300c2480071000d0040480c440070080c0405c2206044100d8031601d401011500015501d0044142003170f820780d002e150603502000401c10815043d0091540c030300303040c1410442c48044909010031240764201900b0160407072002145003042c611603960704042000710460816040508400b01d4440c94411140344044101c009800c20042d9003064004011005c1c0422491a09040140c03400185d001c0000509240300c03804a4002d00a1090304160707020b541c1c0e041126802c10000b9108011560f01c00e54140104160b5108542c3d114050791002e001500700d609042101c0345030882c00e43d0010703003060344101d103040c3d018060400352 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 362696178 1250 362694928 362694989
    0x3061306050a020f031e090c090106030c0e0901270b03060f040f0209010906030303050723070303060f080a140309012109020901030b1f030c0b03040302190f0c 70
    0x4000000d035502d4000d1102d0080c421400790310b6107488040200070814099903000e1461003030810b40d0300525921074200607200d0038880c5040e40c0c44505140103000c0c65100e40c1c444158611039091844400c28a8030014820a809030700c10030710103101925800806070010046444050713108824032550000c400001c0d10303408004c054134641d1482e01c0c002014850380c444c3d12042c5a4000d8800042035131142c650001404450100390003083c01e000104265a200b001c0701202c2c0e0400025013602c1c0c803201c0304803e441d44e11200041d02015150b45003c1110394460810000170803610f80101180c209038a80030302640300340041030003280c01c04d20402c20166000040d80b0055424212500100e101980410005180094020350490390480000c170410104155580c00740d00a00b0740d0460801e00700441c03142a82d55400300510001c07064a0402030382c0005800f450704648a8019291148402c2103100240000800c1c141da190465020315000d0080c0503445202905003412001105501c2503040c51000c3c05 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 362697428 1250 362696178 362696183
    0x50c0a021506030604110d0c150314132003070806010501020d050c03092704030e15040b07021203042102090a050c0313020f041d1b090703050a09081215030613 70
    0x560840303403050340e42d035000b00347d134444d50000300156183c1e2100c81900c5080c1340e41c00f061006c24074000480c2d580d609014a103501c0b416034007140350f9980540399640d00d01c010446039804505a00e2100341307502660103106090203042103400a000962510000a28000e00b01d0720140c1809420010740c0030707040c408003c840e0112020394070703c030052070b01d68034540d6550b90003150010381d000008207000070158480140034060038111071018480088900d611100e100b680f150b0310b072140d01004454018248070004044080000084da420300d50303605000180116002ca045000d40a40044441181b034000501a040308009404020074584480c1e8a102480094281121804140c04c10011580c80245141203801c2c080d10a0000c01000035070410395000a0045040c2401800c1180010521034203c2000d0341000400f50400c03602c5800046e4004c03e1b000d0032011407292510300341c0c4041100440208035184107010040c125282c82940c403109401c1c1c8078031192207500300a0901034051074041d890314000344c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 362698678 1250 362697428 362697443
    0x612010603180f050606091f0519030c0f0602060c0703080105060d09080406030f0b100f1206080d050901020f0703020303040603020c1e0c130501060813020f0301050c0a021506030604 80
    0x707000b400c403014071403005800501c86000c100510040101c00715103540038100035a2000c080c1e440310500050400402c15882d0600d9100110400c018580503403914500203280904103010360321394845140c08007880d001500b140c3d4401000300700c010303410042d4036480121802c1c1700c0d04103c00c50780d00038110300062140354812100807a02400345400f42d802540d9160b44110010741d00d81e034030365016000d080e11503d85000f00e407030401480c200d8204079150b05845400c50741e466040c0500da42041d01c10800c40b000251915030707a0b04000c034401d2410070640201668589803213440703400d040002841c059040942d030119402240007000140c50000c1900e0036160380341005a19264a110710038a044280401070800b60403000c03449454000214440e042140181e03a002c10101c202c80580bc00d0319020b12680c00080c500200081c003c0c0100000c604406100800040c03080002000190948070300b0355290050743c81c0029030111441d010400000114420340c04545286003580c0003d450f110000c001501c41b0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 362699928 1250 362698678 362698691
    0x103050606040e0319090f17030a18030f0606030212010e0a0308060402071b0f0e07050403031b05030a030501050f010906270503060a060305150103120c0203010b060c100b0612010603 80
    0x580c081c0f054403030304060b01c42400c2e00548082e00c006e280340795030701c105041220b4403040403800c0200c0c905074041c5800b00400551900c0e0341ca040c112084000b81d800e900c1100304415010001660000110000301c1c050540840c3d0030341075004014100b003180b03c1c00e000581c03601061a04810b40032a00c0d8014a405003440300079503450038045800b900c1201030051a07040d51410361403100e44072812400580303080d0400800c10070b0710785801f811040d034151404400b090080c0810070000e4490312002c0c80100e801c103003d4401c100c4650350b861540d0880801b90001c2911140184454248900070700020402443e110b252a8a07040c80034100b000c0f00300d10f07500c00c8141b0001c041801c1d0b4455045000070100070b8101c0720341e8980f6a81c1000100034a000449181c000c0740c00318110100f076044003505994100242040c0f884400c001a1440507440c0b000303e17015501c4405034010346c0d50710806002c0601080780a4a00608500f04140c111803c09003502c0c407409042c00b0f16446080780900c128192401810000340c0e0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 362701178 1250 362699928 362699951
    0xc0507110f01050c0f03030a0c09232b0312050c041404020f0c06090705010207050a0b1c020307050406020606031b1c020d08070209060904150c03020f1201080d08010305060604 77
    0x4600c24580111001d1103210b1615410805c004015446103000c0481000f018440310380448003101d6034461762106e00e455030040710f420f10000800c490003407401490031402c2070380c80c039400c0041c4c4c0e40c03014110950508861b80b1414103030407410200007070302c81a504100e6413801c0c1c641003006000310b01a6a5040407012800301036070b25568100c402c1c0004028880c1e4469905403401381c3e0fa00011100c055050160711800100341d40005118015584002c02d90002039043c1510443c1036084901000032003100c444044825210610045004010aa070740d265240e00b02a4064600600a010036000e80d00c6196480c840390f00c4000907110b03070030089401002c021189161800f1070343c484007002e94001d4825000a007009804401010201d1081e83d8214060341c902080000c425001c0743e0152115200301010082210154010b031780550042c10014141f80440d000b10007370381c0100c440d4038080f42010005201407001000303410500f1116190031110303076040d46d03100e640340e820181c0054040c40d106d504c004d18 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 362702428 1250 362701178 362701187
    0x61b12050c0313080604031403070c060c020316050d02121207051605010513060f020c0a08130e01030c0602060c0705030f0a1407050105040b0601110304050f060705030a0509040c0507110f01 83
    0x3280a0290602801c45031135041c030350303240c01c4152422008240300c000e40d1100e4006840980307100300d903c0c3c1c403280101d8000e07845a201a00c40902e1800460004101440911700300400e003600c101d000700024446448007070800307450080501000b10700f69409101041c0b0b0103035583c044581c006000e181458850300b2140e82c4030680c68501030001d02c80d509010410505524810754034030064003030031050008078061280c1078100d12a080031250983c001c0c0c02050086100140204800090411050a456665400c0301c110200a0308200c0c0d034001c0301e0740c00700901c81d410801c41c1d80010610721302514111650341c0b410b681e403146940d0010b40314004144a03003103500441501e0f251480040b0b200e40d4400462400c035008200c00c8400700d4130190043e000c01c2140d4841e045074100e460f401c200071442c181c20001080504103075001640d6005001b00214030000d00c0510145c0048030703003520342036180c006240c208000c0d1008a8011740c20008203100502c00314600b0900900043c034203907110740703030000c0c00c0c00101c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 362703678 1250 362702428 362702437
    0x306051f020115090f0606050a0804021509130510080c060d150b04031a0705091804050c120d030e030307050d0e0a020a121a100527040b01061b12050c03 67
    0x9440c9100400300049100c0c032a0170241400074490020401642c4620b401c0d14140144119100003c000c000003d006050119840c402d00404c924554100389001c8000b802601990304600c070607a46800c1070001c41c007056070181c2e0241c10007101906100007900c010803924000c1904240041c8c0c1c0300c000c0072540c0c0c1c11001085010b4a01d0044042d529500c0e81031154001a202c155814a44d0070480040c01042c070410946050300e05c02841380c003da44d01c0020860400710042e00603105806100040d404035902c403049100c3d02c02c000c0300900004074030f01201904903101002a04820742082042000303642c1d202040700e490056034a80002c0300d055a414240c03a003000a400250040403540011900e00c00c9245400310480c4260905022088a54486594050252104203145080c02001e000c50716152191002004260381480103003003c00906c41000c10f403d48041d959503855000600c83c81758059074400240f4505210309000d005282d40700780ba4040c070740300356904200c80403d0000b444a0706004a4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 362704928 1250 362703678 362703701
    0x12200a0e03150f0f160f0905060d06080601141804050a02030f0f0c1207150c060204030c1a0a0e0103050c131403190f02010c02060d05091506010306051f0201 69
    0x840c0340c0d00046142c04151802940c5140d10f5940300b0f0300084091803802c0401e07200300750300d07903400c02e2510107440181c900c20941c84000c0309010101d0380c04241ca0301c440c000380c914460000804101140b030100c0a03801e045047e0040440d032a1440c1244071a6182c24170a00c03003000201d038100541c2d90b41d0382800303410448129002507260180715818403100e440004e13216095280801690391210780d400030440ca410b2142032009154000d40c00030003c0d0341c001c0701c2d00070301291030741005820490b0a644c1c541c1280c2c0580c004440320948824144020240408180c040b070111404040c5400d00114000e8645c1180d40b0b4072070b040640360303000500c03510002c07030985140301c094043c481003e9403600031207203890b0b68660340d16000380b080d014842c0e11216004440400f0540086405120840c0b0790011178101d88264810380e00f08204024910040d012441101d208000c130602404000c1c01c1000f20040d00000500300a04040c01c06030705000d0b660f5900c020800854080800317190860034200141c1c090941c40c00d80 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 362706178 1250 362704928 362704933
    0x40e0304081902040605120d2703080f13171605010834020304080c060a0503040809010e130504030201050c03060604050915040c020f06011d01170f0f0d12200a0e03 72
    0xb85c00c03c80c00010501d80c08c1d400c13511070440ba44000c0590000110f5035941c2251240c50034a001c201054820380100068800c0c0355040e4a06410110003594414641d0701100c801e02035080d0300b40c80800c0501a0441440811503000c0d080c0f480c01c40001e0410078060044a500c01110a07150342c4d00c524050403c1d420402d900050b000c10030303e02c4010351682c0185c0701d410141e0080c0f54085500f840c0490032102d510b40c003070300e900d400c40d01c2e26114a0165008803068a041c0040f0142c03020007541c0b004004116503403e9000071846140500d0024252007001d08910101c13402802401502d5581c8001c0d28146c070f109480380301e007981e1288a02d070840c281c03000c1000d4105240900180c00340382c2c0450301040c1501c80c00f08541c1c80c0d03661002404804100c29400540b15100302c1c0051120001d40c45075400d0385030100e0111138a4008250206062840030300c2c041000b50300c2608124009a04160054100340001320200000c0075020780300340003c03018600304140340000041c0303e47c415020b070201b080340c8003000e400c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 362707428 1250 362706178 362706199
    0x306080709020904110405031f0e0313090c11071703040b07060c0f0507020603060103050402030f0601090b01261303140a0c060b0d03020c120f030f030105040e0304081902040605 78
    0x8040c002948011a0a0b000c0c07030400200402d01c3c407905c0201c07400c0340c030003a001388403a0301c0c0c50400c0b04600001103143c2074850384613035048280d082c0c05c0001d80381601c950700422070214a400411411079070b05d1001c00c81880200c01200c00d2035000400c0a10446500c010504428841a0402c900b50b1003a07801c080900800800d4402c1402125807100310f44401d83d40360400d908402c568140ca141c05000c01c0294420800c1000070b2407548a5008503810500c0a0304480350346403288132083c24031009802106000303595190b130480940c0e1008104c41210140400041d00c2c0f4111742400b071f100140145025486400f40a80e042058800c0b41390420000c1d03182c1d8100e0703e030051820000d10311412028152625424040031340170f00d2411038107498a00d64076400400c004040103041c403508144020562603503004205198004030000d200510140311841d14850382c0758105002c00003140d48044000e003280e4802d000a00c25054002036001d41d501c0211603604000300b0038400a00503219030707000542c10070000072 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 362708678 1250 362707428 362707439
    0x705210a091a10030f0c08060a0b030c0f030307110111030a0305060405010609080606010f022d0d090b03280c0c021f0e04020c03161a07080f1603060807 67
    0x5000881c42441034070031520302c91030304444800c40c9038282c03440d0880b400c044004000141d01c0341c5c41c10920364402c048041c036141c0c0d651022030a2047c210b58000105445041c009002d00e001e00403004160012112002c5100300c08000ca0fa40b40903240c07005100251422000010761b000d0341d901e210b05010304040342d07502c0c440384c02d004000c0c0c2400e40c2c003075004906203800440c10034040c0c200311040c0c800480003481250f98070001101c888900200d09010f6000d02d01e110403215001c0c060300003003e007030045608400e001180c201031801540e003108408114005100b400100050421290442801200390300d00e03075503070f01d010305c1948a030071410502e1612300550148415000051107208900849071109140d80d1548a041500210342d030400009600b8944041c45103802c1d4050321440341c802044a040023007c8698400d488411003040c0c82e19008082c03181d02458403a15281e501c02d203e490204240d04004500020010002d0040c52851030502040941c00340710303500449c02403071300710108e0f0080c80d82e81 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 362709928 1250 362708678 362708681
    0xa212006040303120f112b0e0d08060306040f2306040c05120d080a020a03110705060f180a030e12011401060f211104030f0b0a05011d0705210a 63
    0x59940c440c0140c10030b0303080005c081c5c03544182294541403d91080c80c01c0c0240c6da450480c0100401d21070040700c240c16540e52903030240e01c50701a440010030b004120106008401a0103a0b50040503140f081c0d204004100000b032529626400031a0305c020500600b40601c030203c403440400c6449040a40701e480c0401041c84500150b48007201e0b000d9404990a403440c001d01c54030307445002c007110081480e69010900301c507a0b50f4010486407800b8900007550b000e02d4071091006601c50031003910f2550041041c00414a1203180260300414214503038040e141e00c1c0e50009403030328400c0d14083c00380080740c44900580c1e200c0420b9450701c5075003400200200702d10002c41c003600780c000b070180c40001900d50b15100a41c9001c0d031059034480300c1c00da16510440143d0400200a420329403403548040805100c000001484507a04000040c861202e13030f41c0904d04541010304441c4140d028040b4060004283c1e0640c0000055641d001302403840d00e56900c910b0f02044542c1580310100118801c440d0200300116011603 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 362711178 1250 362709928 362709947
    0x12030403051902150c0a03080712060b04063f020d0f05010305070605040f120309030b0712050c04051804031803030512010602160918120e0a212006040303 68
    0x304c07404140301690501d508050b0040c00300029195000900712004240124003640e48015246080860400001803101c1540c5566000081c06100484d0078400a44c001400d004524880c113400c1440001c41a00e8940bc007004801d8841100350340c1220b082c5a0748560100d41c0d020f0403038102448a0300340c80500f0b00007014240b1055407103009521001ca642445007040b2030455210000e6628080e00b0304607001031400c5410012014050300ca07a0000c0007500c1c404509200b041141c45200d4022030a40c3c409080da40001c05c0d640303481404000611007581c400044100207010f031307455000c0035038036072406488001c0a200050081d01c95503d0010030503510400500e041d4092200b0010941d0341d07900140d81e1040390464151980e41d04050130b01100b460340d4840b840d011070f402070920784411203403150601c000d05041c01a0004035031015800c030908000328000003c003400e0490b4241c200c400045914601c00c2c00d0300007440490f00500041082c0c0c0d040c01c800d03603a030701d00401c0959a00d949141c0036111254 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 362712428 1250 362711178 362711183
    0x30204020327010c020705040e16270b0a180902090c040315020301031a0c040b121f0e130f0602040b0304120f080609190504111302090a05120304030519 67
    0x440d406002d02d500018001c1010f600b48640003000402d04190402c4080c141420b001152441441150140305880c3c001300700003400e00706035001129503504004c0c128400803104c44144541029040318080c1c44100c21001211241c11004d01c40e0021201c90340c01401440001039444801c901c1403007107a1041303000034401c5911640e22001300c034031241010020782c0403d07c405001600503803002009500c0c0e020600da4444416011b180c0340a8036598400b105800810095110480b0902081400305499403501e185003c6004040c8995187c01038070904400024424100d822800601108201900a0080d20154071080a41d00c4a40b02c001101007a04110740a507006002056080001070007415003000720480b0303542c0e54000c2d50310716003813010050014003030b4252550650f15805001480d88100c0340200e10540001003000020420098072884000400c40c1c210301c104041c480075512800090111001520b1400c080030000c68141d041d4019584003510302c2c041c030b02062506030414000c4000e241d2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 362713678 1250 362712428 362712481
    0x60503010f0e060a020901110706091703131e080304080a0204050f011401080601110f160b12150a031502070c060512070c05070503100203090c0d0f060e01060302040203 74
    0x3080d00001c0300c00d03501c2e1200d141c2c100350007490100f01c2d40340440c0c0080c00340b6181810a02006a101c030b01152504000d540407070300203014550140810042e144c0b00b526540030500085041c0012100003030140c2c00c2e103108040c140041c40c0302164a0000e000c1c9003600800c0150140ca4a0300c3e80c80411688a21001d0000c030b110703e14010006d807000c1001d888150581c0c1500d0256001c070341949006441810780940841d0604c8a000740e42d030b480a10410030044690110f202a0044d00c2c40d001c05148000065004408541d80504c080307009642503039140395010074200d910002c1c81003260b0100d156040c00d5080038285406500c8054880d042c0ca070002d080323503841042020b0366141e9403e02111140118003441006180503004508640d00c2a40b898425900440980300800e54480000c3c0c6400e03032803e04807070161340100c10401c14180600c0b030403d034000107950740d10580c601036580d40d110720344040d4000c01055440c83d58010800d0250b203c440a15406001199281400c9817902c901c141080d03108400c40 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 362714928 1250 362713678 362713691
    0x1d100608070f030507060804030903080307020a1709100818031201060e01050f040302060715290d020303030402120309030a2018060f0d02041821050d050c0c1006050301 74
    0x400050040b04994004000e0407019060590444440d94054810740800c100101d0100c0464142e00045010343c100c2e0300105030180007860454414001d804130045d80150503c0080c1054642044100d00b0800d5072070001c00c0d698601c0354003212194514051465844007003100641c60602401c0c903070688071151034412501c0d17484801140d80784285040800310300320600003000113040000103005120300c144840043e60280405080807a684c160b2102042c3d0825a0101580e0744441e41440c0c2c2e440d1b00355124002106030350040390f80c0e884041c10003401141142c8200002000c28400e0751080000201501c0848051342448000448140d882c2c1642d0113160090b540340b482c0080f02200e52186402c0c00c2469680e8110402042001c9030b011240c10040412010f40103942c0d6100d0311041070309640c07041200c9a55401c21007004030014046004114050040210083c0c01006030b0b40d030207440c801301045599880d8a981c0340c0d401030043d1031105200d00c000c000070345c40c0701c0d400050030780e030040d0000c0140 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 362716178 1250 362714928 362714939
    0x1050f0a020304081b0a120315050d02090103021c12081e07020a080a141309050c0c0a0b0406180614070c0c03110a0b18031902090a1d10060807 63
    0x724030058070000c1140800704031141c12005650300402c014011441038680403040345d25019651000c12880f030001960750032000c00c0720701b01144500d028120030750300801e0342074443d404a84c00c20010b0101a200d801c4144000d8a0300c01c456000c01d5825a010301e0461200c0150000600050350036180d03259000041d042a1003109070721031141e0321030070a0354010302004940b40c6400000c0da100c0600c0e00f00700520314034044159010f40340184007212208100d0214180303032418000c2202d20203042d591181078200180c0004410020f00840901d4100d83c602445450314500440140090f148903200345240e10600c8041c04140d5014110b5005000b0b5014855502c0440844242c520070304010140c0e418a041400841c0031f013056054003101c05015241504d0312041003c03e81d4101022803c448201c400041085090510045010a1880c0381c610003507403041d80016458034009000441050351402d01c2441c4161004041c140101c0c0807094440380240c481c0c00002510745030107001101d11405100080 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 362717428 1250 362716178 362716181
    0x18020c0d05091509010c0b0601031d0a02030714060a0503060604120807060606090518090309150a0215150d061113050108090a0b010614040506160203010c090f090c020a050f01050f0a 80
    0x44d6903050351360820062299403001045c0002821483c10507541d00c0ca07028098200503860203007900301c5e80c0240700d064240c3c81014540072883e04002c1d0f4a6011140318080d94a5120640742c0c441498240142ca0b039440c100032941500484d03100040818a07a4000b00610016400501446014400c1400255281c20007500c200c02d161103240c1c0c100c400798050125110144000c1500040f10b441980d151074000d400203000301c6103031107010080348400902c0341d0007103070100300701e03040e021013605800c2051800011900c1a0341d00c00d4051350040b45102c00101c2002a05c1d0710405803010030b50350107a2a0301d406c00040080704a98045d05021820b031002040c43c040000400d0b41c02ca592000302d8045580c00c002040b190b81d80a101c125500442c1403001042550304c800c007030014500b030f0203480d00f50344845004050a540405281c0002d000380e80b981448036035014000c3d20305850245501048010444504901e0304040050140c824001c0072101c5190700d1303041d004203004044000c01c0c119203449400070b140 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 362718678 1250 362717428 362717437
    0x807020f03010b030606040c030e0615101106010b0a03022218020304080d0905071701020a08070f140c0c150c070806070f080411041a0405091618020c0d050915 70
    0x11307416032104000588629180d04181c20401c40c0340b402003590540000503d1034910240e4030b1402d02c101541c07230b814080c1000800500404100d10305212040b600b02170303543d211801030080105010001820191450194040703070703904400b4001c205c031600340120030b8442400c07250045004180124005080c0c002d99402642c0c020390700007000b1443d15a40006082c003e102c0120110f58a005042e00060001c14200c0d034a03038011800030004d0703034a5140c44801050540010202c7c0244841904400511a4071100800ca21101013226030b0355034005c1090729103000c0c01c04c5c11075a030000e641011010385440410203080c54416500490305010788a4840303646071041216001c00040358141c10381c81441c4205510394205c0e0040c40312004020750741e0b012500b581c0441d01610640b40d41e03020042d0762401c140c07180075441015040a000711003844400e8402d00c554034441d034124a001c01d5401c0c0d940b001c4035070449410a005030212007207503e64040180030b541002101c14414a88854164400d90100d800c45 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 362719928 1250 362718678 362718701
    0x804020102330402030a12020312220611090406180e01020703140901031107050f150603070b0c070b2d12040f050a02091e09070609062601030807020f0301 68
    0x51201c054504921003000c0302c0104180d0380342c414072480e900407030b4440c42e040410752503590140d07171750b800103806451500740094001407007200f42b550301010308501c2c4000c40300101e52041d80800c1d00c4440004800c1d5030b002d203081c000e40c01460401300107120310300d00503940c881d14003005043c400d00d95034503580342c201e01600d400980400c10700c070b59010303070350304058020124040141400102000801c440c0201034010781401c4825911003402c0b0382850604100d00c00b003c54202e00d884440c1c0c40c1220200740c0300c02c81445014084400416951001c3c501442a00080c01d9421701140d16454007526600c10501d80620881e40604507007148070b0581c807803204998080211148001407501c0d0f99070b030501400304c404c40950f6540201b44400e80140d85a5644e14002ca08000441d030003001070307648480500c07038098101900d80c1d108038010400c4641160b00326040b40c0700350412078110181c89104054072400800e440386052000d9001008001030000a80b1800340281d65403446103030043c0516089510810302d5 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 362721178 1250 362719928 362719993
    0x3100e03030606070602070f0c090b04110a05070c18092f120c0a14010f0302030621100203010312110c03060f060112060902120f1b0f190804020102 65
    0x80d95500f495002015400d01c00d030801858941240c55000d03103204200e50031120f03c0c004100c1041200000d005d4080b442008071402c01140454517200b410138420030759082d00303200c408a074003014402d61150080081520340c20303541403941c40c0c4181d100200b04000f8111003074100100c2c1440903035211404001e000155400c603a103a00d5000c2e04200c1c00e00301d031200385a968401c10104041c10385410924078001c144032006203150417081000541440c44000d5603d04040c410b1042048640e940801c5440c4002046440c1d107160150881c0c180c10011744440c20040d0701e000000000800100350020003560b20503070b40b03000c0104c2581c0c06041c2c0703d0104288032549680300e0030105524060400d80d691304894141450078440403142030171400e4481d5544016040e903400f081e41d10091440122050303201c607041c0d04035842c91030026181c0e10310100301d80c4500c05080e00414000d81401c240c0c1c0460b540c0c0c0700d07041800c402451152500801c0050100e8003207005004107100320502c04110801c11003103030500c100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 362722428 1250 362721178 362721181
    0x1110140406120f020c0a020913030503010510110a12090501050418050a1808181203071106160f0c05030319030e010f050c0a031109010e010c020a1502070503100e0303 73
    0xc941551803680b00140080e5542d1801c00401000e1000300017641d0308201901041b0514010010307000801080803000f5104195080c1c00a5404401c5034155882140c400c000140050b4049402e0b8444040360b0f04280724094000c030070f000700050480c4c4c03040481e50703030480490744070300c01110203000d54841c84000340c0c440c010b110301c44034558100a91100c46000000b030040000481d01c0f0115406440c240e0354100001030203404685031300031103c40003900392151703400e03c200110342030341d284202c0001401400b18620510ba4540d2001e0407180c0d95403031480e84034107100f01428203801c1e02011107002c4521400d03842c0009034509020040e28905001d814100018424062094002e030080b81c1e00b6420030755031b80401c0c058500640c444d80d401401020f5000e0349403023406401404032051100701c6840802c1c180540132080ea8020025502d6002c00c1c60a008088158808188500f25035081f20740e4403109118000741e0150700140600c1255000c604a9916481c4c884a60003101c0890a90701501e410400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 362723678 1250 362722428 362722439
    0x409180308150103090c0b0a0e040501030804030f05070f0902090306091c030b180a14090a05030706020d090507080124051c141002041d090a020f0a0504020711101404 73
    0x440c10b61462010b05020820501036035445a070800d95411800c01180045107000945500c0b418800d1109000d580800c981c0d411601c032080140550310009000880249082d01042000c0c40080001c081c010850f1020300e44502ca040040c3d001281a140a40700d13440002e50380c4180000c0e6100d41c4000000d004040c00c40c4c80004801414284480030340240400b45003a50b40040d0b40e40300e81c4104140000012002d0f0082c0d000004d03220003402c0c1000950014040c0004100088102d4400c55805980189d41c1d180c92100600a003420410281040c001c44200149004040d04010003040680d0000b408662215260125191040c0a41c540250540c064804d2508901d404400307583d00501d410a061092520010300d070201070031881c2c82280d00072070100044080c1200703151000e8200c201c0c0c082a4500340c400d45a80c2e101888019100700c401000b010000e40700d46004001a10014100b5542e40c5054186214104040d5506d140070f1070848070400d00300c0b441341c4418010b03030400c50406441c080c43c10 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 362724928 1250 362723678 362723701
    0xc12010e0604021c0f0b0904150f0e0f0a030905060c0618030702060307020d080711030d0f020f070f1103030307050f0d1503030c05070b0301050f060f1207050409180308 74
    0x41586412540c01c204843c181013030115109801d914132000071403001c6400781a14251030082001a004412003018003000a24012807045c1000548400040a0b840840e2440241130141c103000490b001d41d100b01d250822010035070160b048e0198603052900355540c014009244110344a90b4070642005010800c40716190075034040c004044021070303080c00c42076000a03010794001d440c44000350380403401e01c65281d904065090780c0f11000341859175005a03510000380c1c0b00c0c89010901d90034a662540c0e580c4914580358151480300034110450350f2144400c0c944034101c4181a00305440422101001541d07500d00041140c2c4200a01e03990700c0e0030809096a054515003003681440c00700350b12114184000e4600042e55002180640d885c58000c08050900c24204541c54014040a010400042c00140c50744d000e1203840d00801e4610399503034403504511341640e00400101c408942448014001e02d1a4090090015902d01b02400c100100306c2a00540340c24019100c0200481c1c2c0c12000100c070301071013 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 362726178 1250 362724928 362724931
    0xe0303040b0903160e0106021b0d0b090a0c060f03060906060c170f030708041a0106020c10021615020f060f2403060103061b02010501030503090402072d0b0c12010e 72
    0xd000c80f8004c3c9070419486107034407400d8014000320a54080100302c407a41c100417650301050700003040805016443d010030350f00f0a106002030842850107011800d403002c20840604011380041c54003080e01d468140041c05643c203d802d100c002820802d000c03641d4442032080d101119644c0e00d41100c2000e061b65001941140200d12402c0014240500f80a07281c449008603c100c009648030122460a440d00050340c602ca003151120380740749040180403d980002d1700e010f41850440300b031010b00c15052400c0780303000c14480c041003206440020004054410f0010480241d940790290f03030b90f2995040c140783d5076090448141d038106d4021008a25446415010341543d000d01d8100c000302038031312401080c9841c03000e07402110a2590365043e01c5550100d0710055200c2c0d021840240869403442e242c29a82e40501912980304550024090713040100d418000314502c0303002c80d48400001802e00c00d109654986101c251001e000c600d00050840008004540c290301c0801c4501c0280e03404c040110b04030010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 362727428 1250 362726178 362726197
    0x11103091e1212011d040c03110d14060601020d050705031204030507020405090d08060307050d08160c080304051f080403030b010306081b0a0515070303020705070f0b190e0303040b 79
    0x11800b1200c01441028000c04030300104000d0042c80c2e5240c00700c80c0204204501422648444180c14000044c00c40c43e030b4641143d401c40452008041d03403000007114038001000c010301d80c095041201c02140710104846104540980907140340d600e15034404d8940e0310410320000d260340c10070402070302c0d20440c11398056040790203850120706282d007950100d0111401543c1ca4038183d400403101100699008090039030021080e0050281e2900c0c04c000b0521a4030b01450041141001083c00300c10040080ca82d2044a9003042c11641408c0e5500c01154603544180034050003040120031400710500c6401d280c00c144101076071080074a640d1034400310024002c842410381015194500061451020040700114026810f00c10402007404010009402c040b42e03c19402006210703003800c8040d480d0030942c0c0a15030507080c003694036042482c056040503a56040101c0810580302d020450960040280c0808008a0f03c900303500644018152090500084c1c5543d266000f0402031001c0811a006400b4904 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 362728678 1250 362727428 362727433
    0xb06100e0a090c0917060f07090b0418111611030102090f100215010620070e0408030405010b030a0b06010305130b1614180102150402150708190809011103091e 70
    0x40d01e030406100701740b00304045a0000d600950610039000411402507802110318207000da581ea10305000b52007240184d200b01c2c4000612045903022460058025140310725880c0c1c901c5580d0140b85205910304181800c1c10344e0400b202030000519424144200c1e030200800816041030080008200154502d02110340c0e0114081d64114a07103501a1381c000e42e018080c0c0791944040c1c3c10301c41e221085107000315903601c0c2140d80a0030381009003800189803aa00981c105005541c3e0f41e07130b035080040c0034082a803401e81d0148654084070050001c105142c5000305000da03801d10a5450303150382c01c3e88801076000058031410320340c4046656440300c0b00c00801d6402a03400d141c40c42d80d4440b2042c160743d8020b140b40e60840b000a8980e0b40c0d2640e41400003102040348240c05c8541801d1a402242040c07428904100b044000000e07144203001940d0141d03001c44541d041800740b103120354035000701002419030320224507600780701c100d002c4d40c201e02050740d114001c0107006180c041c0450580040b0001c08110404550 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 362729928 1250 362728678 362728697
    0x6030603020f09041103100515091006030b030307150b1302070c060e0418050604020301050903030c0d09030905030303070309120507150f060807030c0e0c0a0f0e0109050d0b06100e0a090c 82
    0x351800e109a418540c4201800662480c2070b521041270441000c80c00c520174101d0400b00003070320522103044030686003d40340001d002c1d103072000480d185104034180034007098044004164541000d401c4103120b0fa00a440d03110b928815203681d2000ea00548070004c02c040c010032000e01c9000d2007513214107500c902c001d01c040340481406400302c10046581a0503900f0b50000000c00c01982400d011f92a00301200340b008500c0d6140c55a080305250007010401c00201e909d900040092521803401c203006420000c06613603403400c0c07165020b0010310320720100325440449038480f5280c1a000704140c440068001d22448401c100091800d0024403480d20540c111030fa0b0f400b00811200d400f0401d4001139482001d416003214208089580d05040003400210310300c004018201200d54050103000702d6102504058014800440050314000c0d665000b2a0304291107001d0f04050000142040380249400e941903034001c1c48a050489140300500d001e00e4121514010410400c00c0301e41c40000761801c189441c3c40c2e072 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 362731178 1250 362729928 362729963
    0x30c0507200d0302070306050f0105030607050717040e0703060509060a051c052d1b060304031709150f070503010b13030f0b01080105090c1513081606020706030603020f0904 76
    0xb800740790425401030b400380a050040020300c1c412a40c1200c40b00c034019a482d85400d000950707030030f402841c032410070001290600802051041d040304032000100502d482e1601d1710260901b101f0b040f14503a00090030000300058506092400c0d5000c0c06024100200d05800c0005101c2d0440f581c0ba0780d44101818003440c2e00120703205104c0b83c04080c4c0e00740107508120200c8110761192030305c072900703901d081c6d000384200201540032407040d01d4036024155003c940303030703900c2d41000d99081c83c2c60720713440044259100c04c22041c050003152410388107001401d215002e855201c11606e84220072580710001c510100018464461030b01c01278203d400080d0801e020654503603807802d40311440754004840c907805010051051000a00031507500c000e17600c00929a00144500150030b4402c01c008400c0c0c5c007500000c3c0d254036a030040c1c070040050b0803004202e4002c0c507a110700048044205104800c010300909074041003062003800b940c01180d40080c0f600c580d804200d410482900390260048071081100000c5008 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 362732428 1250 362731178 362731189
    0x1302060f031317030c03060f030c0411031e0609010504200d0209090903090d14120301171c0c060b0a030b090c01020705010201090b16090e04060b0a06030c050720 71
    0x41068051840030206a15140420b43c2002c0c807048801a601c0078010000038145e20001e0300e6020030100c0e41460a0072000000c60b04142510a00c2c6800078104401803192040302002540a500c10200241c11302091070805080e081c000c0e00c0440c0d000510000403c00381c9020307001400c903600780d000c03001c0000f20f1211400300c0c1a03000c0801800c0721500414800b000b40b50072900c5581c070070364420286240101100c0040d917003c10314080103148410783c000e03a20007950100140062044c11000180e9296100d4200d9030440b650100380158038801c4040401d11860b03075000c0030034000c1e43c43c0c0b9501600c072110f035502c502400e1400ca0003034018003504800000b04001501c1e00d4016142840644518501540020704000d0290402415603040001182c00038010301481548000c2c1c052640c99200402c22045643c00e01c280e000074030102d000c00907c414000e440d8490078004a0480d030008245950b035405a00351000b81030703540e001c1103091142e040450400132500c3c40d000b81e40002900700e413010000150 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 362733678 1250 362732428 362732431
    0xa021f050c06101e05030307140f01020f071509050706031109042f0a210f020c030c0615060d05070903060c0203071b05061e07061b12060602061302060f03 68
    0x550b0010f460104035020f902c0c54024400c8882c9a001000c4904080c0825a80c2c8100000100005058800040e2110b401d04c0115a07501004009540c1c1c0c0b2041c0400d100340d80c10030030080e80c0c07101c415800e2000145061181d450041e600c4006010030703c4c5018070542c002c00d20629a00c801c05400c001d00c0e0380541d1144100d0304916582000025070302c040070903041d00010588210081d110080100d0306916411254400c1c48501c0041403420482080180f04040c1120300e0b5000515030011804003450540070001e0621000e480040711320744e5a95000c883c0944909000c2c40b44c11080402c2030502c014001d80083c0d40c4400c550800240040d569501c7d0800c890040a6003001078001103860001c0002440d4080d2550700c40c186030400d558104000070b80701d4421520564041003c0b1540c241d5a500c1480690761400d411000800000f40618400c500d0518034039841400610302039155203842c0d075903100301e0742603c03107c1e07000307081c1541c600f1051040c9101c064020b07a485030040c800706000c0c00d1060000d6 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 362734928 1250 362733678 362733691
    0x80d06050301060b03091c0e060702010522080f03040e0711010e0f06011e0f05090403200d09050103090b160504030f080c010c0207080606150909040309030b090a021f050c06 76
    0x4e41d504d10307040001c5401e102d4600c40503c4131182e1000b03400d83c05507020940109840080b42c2c3c166079100340388010383e0180312b00240c0302e405842d1003414600c0400200740c144121403a8a06842104142d850b8140c0c49214502859101716491030200310018801c02c0500491560280000756280d2051a00c910380340d104060703200c02d64050b00c0140540c840020f03d00742840c01180c0f074414464108007060354410001d00805024030440c0d0300040a06101e601030350a00b0100064203503074000d200544a4980070a1b0103114045082d8500000e40c40d4807038420018007070b800031a02d0000d62224004030301d08131004540b00e01080001d00021012920352144c80207402d2007201104c0c0c2e1303109a101d01c41d00b07450322a5954000d6402c0407400300108207010600c540d011004a85040c281e8a45406d5440140a075080641c0c007c0d285070208001c15400420780401d0380e01444203402c1c0740d960b000c40281d80c1c400c1d181c1c000350401c00c15034462880044c000b0101200c107800b800e0560905580381b41c3c0c1031a200044170203 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 362736178 1250 362734928 362734949
    0x31018020d090b070905010f0806060d1514012a0f0201091a031005090408120703021b010b1503010f0506090f2d0406060504150e220e0a02030a080d0605030106 70
    0x1e1041e80c85d000809400100400e00308440c444d11b0011010b0001c0c41c00a01881c00b820001941550f182c1d00340c0d01c401c07614811070b51038681941d11900307012071300d8000b40f0000f40816550245c00407414030001c801203041c907000440341c040d040390b41c2d11884080c8001c1d01c03ca052240301e0324085640c40080d00c0400b0924080c00c060b540302d20f84011744080180c10f560006001d90840c500b400040340ca590704032182144074603400d01c1a602c80c82ca04400a108101d090f00070706040c1c0c0b4103203036100010b4100d160607501c06c03100440e500c603460101c0741d81c81c4030a21500c040050b0600c801c01580c2030070406441030394401420f04502c0c0c44110003042c3d00006007054901c00d9001201400f000036104005110440c2c01610304111031f608226000d4150b220702c0c095001030007807500482c0e01140c0704039101084140060700c00d4401092030482c1c000d40d03808103062079200c0e40c1030141130400410009003105025800a0091650b101191180503581e406410030801440d00c4840210303940c1c409010340c4000340f84200701c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 362737428 1250 362736178 362736181
    0x260a020d0f021801180e16080a1517030405090a05060306070f02100b120a06050a0c0507120e0a030f030503060f0d0f110406090509010c0311031018020d090b 69
    0x201002210100d29442034070038418081c3c10f80d076004016004080320000e00f0315178100300080d859800c0c0141998803010464500c0b03400c10107028580c41c0620950756142d02c41c2c00041c0c980c2414102a549420302032040116803c000704404151035a105102c5114001a01c3c0b5054075800800c032070410071102413240d50744034820b11003a400c0030414a6445003c0349028032080d10f00700380082d240c4070000258400251558000d024903074460301c0000c0d0030111502210300300540c5183c00700281404481d21071000b80741c01d07507064005011f282141c81c081d41c05211103880c045c0c00002035070050081d07402d460b0480d4107440b004c8001562000100780507070003929401d03103c0c0352040c00c104203075000d2060b090144510035040800076040000c2e0200c1e00d039006810100c95000400454024071440c0c0c0074107101d038188014054400010b5101e07501c501515a030910070f48041c0131345420320740f005880c906202c5845032400c01940468004941d0a5000c002000d4035118040c0c902c2c400350b84103500241c0700600d0890 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 362738678 1250 362737428 362737447
    0xe071401020c060a050f0a031b0c0203060601050412060518030a050705190203060402040b030f0a1a0f01060909020708090a15350408090307030f1a0115260a02 70
    0x840c42c2411000c0b2003051030a010302d100200140160403099541207404509504400d02a800c4015a428820b1592803802c01d50003004001000c0d06030140c4c0240940300100300254414400c803000c0d2212410001000301c0c807a40c0e5500107110090002c0000881e05c82045000001407000340102150b560b14a9180c03051405c0c0307141000c0b00302d0505004e80100c441039800603200850a01e5100343c0444000a5440004002c2424400700700d0013810035025400b03403a4100300580c40d80c07c02c890102d112078411603171303080d400c030409400a00400011401e48242040844019002007646a01c141381843c20302100c040071a506848039049014083c458040c08581142c1c02009845448180c1c1c4080c400b408100000c44104000c1c0810082c04840320400039041c40a000112a1001c40280403180401d60b83d04010b04074040b4021f0880b84c00c0c4c034411000580c1880012020305035000030b01000c019101c581e905035030302d4800441d8180025001c16581409160386000c00d403182500400140e0b403544c140703 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 362739928 1250 362738678 362738683
    0xc030506070e03010204300227060f0102030316140f0418060e0627102607051210050f06040b01050c0303060420030a0c0f110607120e07140102 63
    0x44a0a4001d1388140702c01c02c4070004141c44d00c034165103402a11f41c401180d0740603410a0043c0814003030341021100c0c2021340001c0300018805125123040200400540301c003000c004600385080713030040c01a030090011594400da40ca40603010104142003010000d415001e84040c250000004905030190224040020307103031290414540ca0109141084010308050107807501c0c460140c02c0501480a04c103400c1d03124039a642d0020b203001310a46a850843c6000c80c40d078408440c884c0545102c041594070720305850f118041e410600c00d14820054050b040c100414007101c80e0485070a20200c0c0b05000a90b42c1001491003260300919124015501900d400307400d110954614410072410480304000c200d0350a9004000d507a00700c0d4080310003282c0c00700305c0d0200e84405041c00300340c465000800001e01c005942141e0010044280c00d0301c8444d0701da1040c0905586221102c0b0306049150045c50008011501c1510070b90a840d40102c2d00190015006020b0340c64214150000d080c100314985074800c4a42c0c04 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 362741178 1250 362739928 362739947
    0x616062c06040303051b0c0307020307050114030121060e0610080d050f030601020102070b0901020414040603080d0b030f12091f0f0c02040915020702090c030702190c030c03050607 79
    0x80680411600140d219555558400900250403d65205c0108007503a803110031100c2010711740034200c1d880d000d250000303989903400420304034440e01ca00d07013002825502503c0c6240b00442c0c1403030a103086a107400c03114620701e001d400001202d48090400070000500c50302c15107104070503080c001c00c21890101081242588141c11031062948580d40c4860015400811a1842c103c940c1d00e4030340325181c020050340a8010341c18001c00c000c0698040100e080d005601400c2290615110541d00031030380824801292028000134002e04410000d110740f0f42c4041e0005041900003070304586244800a041600b8544030031300940104800143c0c1c46081d19000300000c444801081a24084503107010300904482a040c461034103125180f1348070004c1d981e4507440b960718142c00100b281c032880b6551090314000c2d4040c140491107045c0c0c2c2008100b44c046c0303250540e44550803d4000b08011140030781c010f94003a80703003401200c000754181f001200190004109400551188000b400c0a0500d00c4c0f000c0c0101c400c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 362742428 1250 362741178 362741231
    0xa021f080c0f0706230f070801060512130c09020d0b0405060f010c02010809030c0d09081b150f1b06240f06070503090a0b04151d040209061606 63
    0x105000422296481200f00e4169079031014000560b441ea205203c1e0080b0fa180d02a650140d5098080000c84d2012042c0c6501c00d02a940d40e80c1880d81e01e4a03000ea406003d60071b0130b180151030307107030001d0840e082c1c2e0300410820354020b00c200d04509030385508800a80c0d00900c0c060280c681c4030b20800665007841d02440f0f4001e402201c10004104044000902d60f844513171002e4108108080421002841401151807204c0c8447c15a105020282c0028200b02e0091050b140710b0310941000258bc141014074075480c2001c024610014902d01c084180d141c1d800c54001d5000c00700d01080700c0c040d5856521441c0a0449005000c0c10303103841d0080c018030030081400001200003c0c824031900040c0d6031801007005004007180d400f52180220308100d4510700844203280e402071800c24021032100403080140040740c0118980b038101c0714a4000c03c64030140c01c2c0101c00d140743c08651342e1403110314080e0081c100502e00540407506010640030142241011407400752442aa540e150b10200d13144140c80b01584034 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 362743678 1250 362742428 362742451
    0x20a140f0c09190207020d1209060e0301090525090e0c0f0901081c052104060507020318040b030f071206060b030103030c06091e0309080705190605030601020a021f08 73
    0x10700341c0c10f0a11007101920702064020740c00180c150071995907070528000740350800c3c860034960584c844007401c0080240039210108607140c0d84819507103030501603660a99407040181c010407510440c4240c43c50391042840504403110030300480c2c00700e101c1c401e4000201c400001028003460002c2070110030100c804046000d1041100140b0000074002815000300000c415440c0100b1110740c02120341d4003415102c80e054179200743c00f01c0c0866000c40d400034041c070302800d410001510340f0442686e40e4400c90020000744000041c0040385880c080d842401c1c1d1303480c0501514200c111407501181400c1c1e0340d4001480c43d1081c0300d4043c0600460744920405041041d0398140345504649002c2c0c04405840c0c0000d03c52600d0749074280c00c005c40006002c4010b0a8412380303004100141c075018081540341d005004261040d00400540c92038001e002e62841254890364141071804c0c400100c40c1075100400340ca05511600000c0001604d0340c80150385c020603040300070b0152100e0100000c1c805e20018000000300e4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 362744928 1250 362743678 362743681
    0x106030b0c03060a0906060507020405070201150b07060f0e0318190905090f07060507030e100c0b0912031005040b010305010b0306100306080303040b06090906040f080307020a140f0c09 81
    0x9481810303035079009075581c488503480c0e9440100040c08020309800c10211075042c4500051215000030181ca2001d100312014041e941d0740020407401c9411030b4180d01821400c0b40300810040e075052004102e1036000d0000031410710072207403400c0251500710b09503141980c000101204101d40c80e03200d03010402e40c1100c00f891078004049030031110788064003560070310f5035480001ca070705054204440141000c03110190344081d42d0399400949150000001500464840c03551000e41d460401201a20403070b00d40c452006d41001d5407108510803034001e1a5816620034288455541e00104001e5481a41b404d0b80340b8444030704240501c0156052469000e0605040000501c49000c1d40700540754041c200b91080040e00c1441d850480c041c0200d40c0c0700004c0c5010020500003072010802403d03200e11401d03598100c4580b40c8600c5660780b20340885006d009024500c4c418000190814000c640000d064412560b40d030701e441c1c48260381c2ca0a4000342c40c9140d4810381c641030500c0400d0144428503001201c4030300c4c45 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 362746178 1250 362744928 362744933
    0x21e0303040818011e03021b07150e03071d061201151a040302090f060a15020a12140c0105240102070308090402120117010f0902061e04090908120603010603 69
    0x20b502a4060090b2007032800c450302c0710583d110f19841203902450325806402c0b607020300c401078000d40c0078559071907045028900034003461030000380407821141c54450414a4034120b40703048402e62040d140e65545030240d800002001d0200180c200e047c080d500164441c541045800c104090900d0030341001c49034100b5101c8495034108160440c00c940340080c80c402d07a038104030ba17580035a03c56174000a500000c5101400007084241c50040d200b0f15040d03030024141381e1505503402445680c1c02c1c07400d0041c0d2010300b03d040001c010110a00903c55181005070034034840c0d481c8007055400441d20100390f40e540d401002503200021318400c004402c080c4500014006000c0000c0d2980b03018003000e000ca81000403481d00380d80700c1e54120b8108400e24002c01d003495031142d103210104503503820505925030034011202810f540c54400d0100b803907801403610f49030401e0356040c10500c507680e000b05a00c40b901400009003162003801801201481a104c1d130343e03940c2d491b000c42c40e10803d02818180c002d07807400c2c409100 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 362747428 1250 362746178 362746193
    0xd0308061c0b180f0106080a0c0e040203070902160609050f1b100804050c0306040c080105010509070816030e0610030614070c0818060f0a0e01030516120f0507021e030304 75
    0xb00080e4081a05100c02a0403518610384064090300d4102c4c1c4d072a244001481e084041400030401c0d10130445400d681c0c0c0d9814038290140d0f0140c2d4065032541150303004100500b0076500505007108030015401098070541c40b160200d4112034410380701ca41282507807424194003404841140e45d1a0b8004020303000d80000450b1095070701c104c04e1000d114895011400b4071a0405c040303a00707154014121100d518041c036158075004c3d2240700d0002d141d8200800803a044c03411010603482003100b0b90740c200e07045d41c9540140f15003180d18208503050540d40d05030100c1104050020034860800f49903440d001da0700e54075181c000c4805400a215440103c2428842603c0d8006010780030983c10018682d2108200c0151842074140110456800740c400a280005481401e0203007120050b99250014170f22203c00064040d1041202c010440307203040344200102034020b0700d41c0c07038400c0910a0000b0312050942011800c540b000e1700c424016903c10707040c09140720700c04010300200102080c095401c42c2010340d01d190 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 362748678 1250 362747428 362747431
    0x140108060a1a0a02010207060c0f02070f151b02130b120a08162102100522022421010501170a0515060310051e030c0d0309050d0308061c0b 61
    0x145030b000610155a20b10035019100c135036400c003008001d000c0070741c80003a0410240b01820700160040e8100041c5449009804600b00c178041c420001407410201030480c0c0c0300040c3d10410301e100e22030300c3c04800980c40e951070b1000521006a8001203140c010f00800a4000795a940c01449501060441d8001740d400c109480504800b03400341d80a6190900d0301c4030b140c41e440d4082044c41c0d680303585000e690940c0000c0080c0441188202080f09032100c54021500b00c401c03a8951114440e031800f40c0340107082c0410301c400103030342d00c407543c83d103c1c40006004103265116103e00441c1c2d8500146058100002c1070340c260040c402400c00d01004601c1044001152130001c048941f006d035240000340710b1101c4002d104100300b80041080340d03289002066000b00e50920702505003e00c18510309032041001804042603000c3c4000d0050140d00301810800c52a6007440804804202c0207080c00945502e928010f40c18880c8203403502103d5107410b000b40018550b841c0c0c89806c00600e103141d41004507400e03a0945 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 362749928 1250 362748678 362748719
    0xc04020c07031b120f060605010305010b0304032a080714062811030901050403080f10140409060204030807200a14031e0c03190308062206140108060a 66
    0x5a403181d40c1c00f024155900c00e00102054140c07202c200b20f1041ca08020b81031181000300841a10f810044041741c40c03d005088602d081040440c021902551850106084040052018204002c1c2580c4607413400316040b5103480020500300b080019076094044025200d40c01008189803501c4040d1814080c90500070720110102000800ca0300d02e40c200d003070b002422110391540c03424070b084003900074582110282d00052580020440710040115a98058840b0000d5094410f0501041400c01c1e20b41c90300f03c0c1d84c06950340c050100040d0503400940021809a00d440380c481d0b1311400c000f69008980c81079410901d1780f0400c2c1880325516001e841058408001624403c0884000468a0000100045105901d1440e1080c511450000c0d03111007010081d41512200340d421000142c0003562510010f0128201000040d01400c3c0f0002004000400d480b80c160352350746010746031040340c90a0704044840f03841d800b200c5031256044800c0c9e1350002c0c001c0e039056001e82e00c0c01d000e1200c5007030f000390340 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 362751178 1250 362749928 362749943
    0x100909110903120f1603170711031c15090c020d020703030c060f090f0605101d0f040c0914060406060e0d060507030212090c120d020703110103060306020a030501080c04020c0703 78
    0x8600300a484c51040c1c50f2030100c1c000d420443c200d09403c018122a031012611034280c0e550314001641584508800312100c40d10038002e40c02c2000ea859011500c0f61514801030742d10340e5803615000380700310a03d001c0005207800c030300000d004100000e00074104248481c100041d940184003c2000a610a81150103a500540c0002d085000e410b40c40d0042c0034602c2019180c69180c0014000b031003455408107000710b042c0b40c6a011101d98035180c090b0342690b64901d0000d21003040780002c3d50581c800303010300c1d84184210941712840d910342c00c88c1401c84040048041840200d40d041140d507080a04ca08406881c06003030050001020350002000354800c624001c050f0350300e0740040b030301d0b550198042e1401100441c001d00441d151210850b5920b07840425224403407401240340c241d60f10701c08a900801c010541d400380011a04644410140c180c110310414105a0b40e4000040842c10030710150940c8030b41c40e5004507007135141c010003600c3c054032008042d12807441040380410380c610003d00038044a074805003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 362752428 1250 362751178 362751187
    0x10303050318060a0b010207051c02100e12030a1803210923090a0506090a1e020c1f0e0c01140d0203010e010e090a030801120507030210090911090312 66
    0x35916400da00d5490b282e81035100e0b03482400042c07903081d040191281c00c00e0b402c8400295030f41040240303256000000f18102c00c03401030031001504080041540701c04960800d0707a44400c100020817000ca0510803030782c0440c1c002068611000390711000035200030f1030340e0074600072190458031401c040b45e028a019400c10741d80c0300d410108950007010703000c008028203410801181441c0031500c000191240e80c0d144910040b00014000c01c0c6180300340d9000e4240500006282e0740c0708410540200111103480d504030b800851b01031000000350009045621040d009040702c0200040c840d060400f10040c4010031600740080207440d0140084d00200f026024a4800081c2040140d1000c07180b040e4030250b0750042c000000440e48600c0110180c3c12510b2940d203601c00c80d03940d1000c42e61510b05084006001944a000410010a5008440f08804e01440655080a0b0380c4d90024203a03500c001401400729030a49410000036540d841556031281c10f01009615209035000081e859030b1516403035908113580444d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 362753678 1250 362752428 362752441
    0x30c0712050901080c071113090302060903180114040b0721020a02091609080604030302090a140303030403030506040209091503010e0f07050904080705010f021801230306150f120f0f0103030503 85
    0x11590a03840082c8c226a104c1045115010142100c04030550251054601041c503074140001213403101d03401c1041c070229500040c0011681c809050425541c03c450501000ca002c404007401000018402c0f45009402c0700c00c40301c4c04590b0380c0300c0d40c2e1400640d04030b40d040c0c001580b54045c003241d00101c3c7e801d0041c188000d40c00d0130b0302d200ba00b5800102d001e02c904002c220406826500820168008540d010b40142c1d8138a101202d5a50703a82410b40c05820078404200068080e4101c0380e0025001031025007049a113030049403009108545020410f180000070500504081c42042d141da046240909140c11500704103170342d920b12a101381405071901000103828441003d0070307210b01d50350002c02031002d403400c840e50001a4020015410801c1c44c50349a900856004803915240309a9444254007428214480140250002481340d40c01c5406020056400405d0340006c007550307200300402030384982220700311449107480140744c0041c003104841840b030511003550003141181d506107040c80c2d890741c0f500e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 362754928 1250 362753678 362753693
    0x61508190c03061e24270305010e100f02160b150d050f0c090118050a021312060b0301020903061f030f21091802070206070206030c0712050901080c07 66
    0x84c0e220135503018410601013200c00d01e00c6100701c00c903100001880c040382808038403603500600450303030003011543c02c900d500500010000115070444038011514015940c0380c68090950301c3c004a0000142c10032030325810602c4030740c841c040139400b0f001400c40c2030030855650941005510b5001800034195000000c0c9000820003c01e07106c0d05005c0c140300c6040c601480c006988203400703a0742c41840c1c05518603021090030656030850481e40700000c4080e4a406800c440c000509020b000807415070b800308540c02d000c42000c10103800514285e005100e41c00b01904004040752041c3c4100c0b40300ba40100110440b6607000108950000003491902004204844216251190720350004058041004500040c0120301005144803012800c1c030008903035000b0300071078800c8001d00911801c60803801417001c0c145240d80c042c1c90000d10103410645840d019400040c0c0c5500202d402d41c2100b000000c040f820010b46840c000414400d6080050030082c0c140000780903001c0080209032041d1000c6880300a100e41c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 362756178 1250 362754928 362754941
    0xe01020c012106080d110309010f0c0f05030c03041e03020f2e0503060f0a152f0c030f06100506030c090901090b04201b160603061508190c03 62
    0x1080c0081007055550580c00e511624500d05d03190214110883d9a07800c1c50001c4100c3c0d201c200e0595418003132035003900701910b80b100404130a0303c001b003104c4080c000151301080104854180d990082d03441d5458012032002e4002c00c0051068142c185c000c0400041e00d5807540e2481c900c00889103082601c086541a0103666070a910141013010b40d401c540040e031750080019406028240d544013528401c2c90300341301e02d070195031080c1c00066075070245202c1198801c101c0f07001a001542c103402c5003c0c3c84a000701c0070014403911290350a4000c034601d6161841d08003e41085001d10f14041c2525181481a07505131002c144a00c90042500000181d051003d040c122030070f2100c0249088400c1d40c4031200d1000030111071100b1030040741b9100302000c8008101210070300102c0b1029499160041c002c0c11052a224104812811403055100d200080302d0356080701b1015165691340052a075282021360341c2d006d1800360400e018000c0080500ca0861400d10750101300030080000410900ca40360000c030000e000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 362757428 1250 362756178 362756237
    0xf0b030c091c08030411011d21150702070e070801140a03050a061e1103061009080d020c010f03050c0d0b06040803040e25200109080304210e01020c01 66
    0x1501c1030103070b040051040144d40120300450a41480103444e00c01950340481800c2e1150641c174520710010007600e044008000c0080324407208420a07050056120700d0005824a180031521298042040285d410801c140c02005004a89042030030990f0002c0d20080060003640d1060300840c00000180c0c844000c0c000003503501c1400c49a64280e1810900018585041407414a0706210600c01c0e4910603802010101c2040255241c038503202c400030820342440c48005101408054600014605000d1020002c103450310b80140540304940b500040200d034100c1e100c070090614200030304c41d18000e81000d031003d1110a013000110340c012500020402d01455001071035500c00080c000c41c165880200050040b100c004140121202c011035a002404200000c04001411071004c0f0144507031254103052040360320741c000101a04141c07104107455004031420340ea04074241110344004112016405240059450700b42442040c500c0006d455503a0448020304019114541c0c4d185100d040100101140 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 362758678 1250 362757428 362757469
    0x10c11030327010f020c03100f180f0501150f030b04020a0f0609091406031f0f09210201060e0621011802100801030201080a0c0e0d0b0a060f0b030c09 66
    0xa108000d0700092641030b90128000b42c01c001c02040c0444c0002044003407100001c1c0a00301e0602c00c600108010409401d0300880c076500c41800000c0a6030500c0c0501076070707004204034505114942440ca0a443d00084014206440e0140400141000007244404e0b66403000b00b5954580b01c500000e0415105500f06581004802200182040d00840424222840d4000178014000c4509103000d920b035084840315010380190b491900c0303a00d6220000e20041d144844001002c1c5010303850031044600d40202201d100100010320900c180ad031142c4034181409510080c003403141801543c1e4490200036101900511801007241694540740c0c08170ba140c40b080c80001c02500e182000301c400200016401603004441c4d8040c54034510f403145200034162070301a10307180e01949941c2c507648014005404a4404c2207950701c13030701005588ac51804007580740110400401410301c02d084c90111090345d4803020351015580410407002c0005419240d0125079a0f11460700c51007505c01041701041000b0100c400c18 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 362759928 1250 362758678 362758717
    0x1009050408070c14010212070804050d0201020f0f010504020a050f0d140c1c0c150504060c03030b10030608011d0a06022107230f0904090c0f12050d020c010c110303 72
    0x56000c1d103074801340320f2090b42200d507902481102c0e100c00d0300c1501805000028104424003071400c01c540080f8482c0e04c188112460f00f58851402401c2581075802c2542c0c594445060000350300c5c0015000000c3c0600711910103043c0910000165580c03041040201004a6000c2402419001380b206910b40500034003100071244202840d6070903c1202d5204680642401c400802c0c561802c4000c4411003100d9241c4906d4981400700507940b280042d9021010162148940a125204c0d00c0b0140d05002ca5900c02003900c0d4100410a0300791450543d114040a805120381c1104140000f40c1d02d850f281c10a2006980305082030040300b0310b000a100206031100044140410a07034003100200c4150074088150740e801f64805041c0a0030311a00d284030310240000e010100e00d603d400d074880754034648034114400840b591244142c01000d50f034cd0200c420321401504041c144041130214424003c61803002d00302d0000f031301d0001f91210350514070141211280a641c0030883c1c40400440f29248016410f407800b4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 362761178 1250 362759928 362759939
    0x9030509060403080d051003020d080309120c100605040c0207050d060b18100801091127090a0c0801140f0a1413110a0510030b0301150603090c0e1009050408070c 71
    0x742c0d002e04a008005e501d0000000d50611074a02c0f81d0007641d07402040441401402e40f0380c00740d140c00142c00340c65a80540451140440c3c4250020070090305c101c805410000015407800301101c005900450281d41820305441120b03502082810030f0700c1c0c0860b03070041c000d001c60800100070300000d0500c6d508854800c104a10991103013019505c50324140c1004090b681d100e0420500360703244a40000d1006000f102402083d00c0c0a022102c800b4040982c0ba142e10f04000c1e140028080f01038074500031319086500c00c02c05000203905250040c0205500901c00d69030b5200f840440148003d10781e0652403611030205030011295049003501c41c070799640030038045c20315100e0510b402038981c0c1c04651641c580014071310306042c03408440049070300c018805171032908400780030360240611201c00c544c15580c5203501e201100b443c0d1211000340c030f20b42d500020507181c00d2030115400c020380d070084c1c03520b40040b00c200100d6052603c0c4100507030344103000100381503c49180c400a0f0780100328008200400c0c420000c0345 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 362762428 1250 362761178 362761193
    0xf022e0c18090e0307020108060103091709030d02160302060c0703080d050105042322080706060609060921020d0231021201051509060d020301080d11030a0309030509060403 76
    0x40105044003000c030304641d20580a0101c4022060b40070f010340003446135201660203420407660120042c14003249901c1256500c2c0d03040c0e02d00d1408200c60391404610a021810104948082c14488ac0000c02c0ca05c0b81202e11840c103c0951f00c0b0084c81044005080360140d0307004d000980007076074003a800c80d4444549000072005030400f4003840b800b0360f00d400c1c2680f01241c070291110b1400e40108000c82216200c0c06030b420100602140d01913000d170841d204040001d03209400400c0784034011080003c070a801c01100a0141405238000c8040004851061140002c0702c1307961001e040c80081042c04601017440400e641d2060182c000c4e5100c82c0c401500d40903a5034800c0c1c00780c0d450003600007440b0325032030440341f0304203d010b01112400c42c85484401803001d824075070315800d4101c0380c0d11415403d001d440c9001030074591061510003d540e07000307c010818010f0030010254050b0160400c0002403482e01806552806031026039010541c80d07500600c207041c000e100f180c120000c06002660340b1074990603c42c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 362763678 1250 362762428 362762447
    0x6150a030b07020c03011803080601080603010209150306030c030f07270c021b030d1d0409050a150b0f09040605061504090e07050a03080301030b0726070f0f022e0c 72
    0x2170103542003242d0f9007000f04410004041883e410340390345090361540ea0044601ca0002043c85070107650820140103150384911450f40d070801120590b82d603e142035018141040d08042c080d038025840103c2030120428080b847c0e405680e214031003598504203000410f0030000300340001044c00340c03404c1142a0700d035601180106115120300d00e00c91205e9840d9007410340d5250360581c4040000c649841c550f1200341e1a003c6a41d6500303000300003046100f59500d50364240300c0700c5182150940511040c840c401210303401580c103101c00441c0c213050b00150340004036600c0c00f00100000c0207140c1c0d030800200907554100c0d10b03000107115101200c0e16982c944039510002c1c030310004030b00c03050311980c100040d407440c00c2d401d000b0950354002c00113803e41c1d19503030f01c071050712070007505803c148411011503450a040030201110404048145400c50381003415000d0810134911040318100315403407120005198000915801c90160000d0031050354900b4000b0308840400c41c050340b58514140516200056030218604 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 362764928 1250 362763678 362763703
    0x8031504140405160501020c060a030902031b0a14060304030e041d0106181104050d0c1a0703090509040b04031b0203060a0c09051e1e1f02100e06150a030b0702 70
    0x40350244c91070944415816107034800c550050340003010700041800c040b400303008501102e00740860a0781407a400079003005400b041d03e1030490400d00c101c0f05946065464200200010741d4031404a0991101017902440010005014001d40d00460461501c40e5400003d020b56500d90300c5403480b21092a0720702908042c814040000300c0303d014501c441c4014410b00704961551012603290625240500c417219910341000c4d2102c1c1c0c10742e100042d090400301110b01c05518043d20f842d54170041c03403601410004142e08418080d003c030b1001c100002d20003802c40b50f0400c3d01400c0600d100160a003a00b50080d1801000071340601a8005100c01c0c0c0c1c00b07d400c0981020000e0b141c500c8a90389400038008044081066600442d050306080d28103030600c1c051801540b85020304101c0c20341c1e0a00d0104142c1e0078012980d141c0350304841c00720840e80b98107001200c000c070391030702c1b0a00041070f0707401c6125a01c040282440c5204101c2001ca00d03550f80e16602c0040065074005850f40c0b007072a000d10069254800720740d50 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 362766178 1250 362764928 362764933
    0x210050a05180d051b0f0a120b0a0b0d060b0a061b0212010f1a030f1507050f0d06120614010b0405041a0901061806020d0503070e0a05091317031308031504140405 71
    0x100603030380c60860f1f05103082c0d03545400e00e90b01c20300e442d84418110790030140c14043c80340c0e80c824840b549506d9001c81d4a1346940644004a80b44000a050000003510f960121040020b01001c014070075540328203106101d41c0458085001031050070b26a030060503060100c40200e441c1c09500f2100e00400351a8140140b0100c007514000700701303801107e454002c000d1013140314983d80d9002074081d5010f0703000b41c40101030112420303060801c503035010000c81d5019081800c040c00d4034001402044800d00901d50303138141030449a80385514000c02d07a4410300490080901c2079860382100310b41040001c0780f05100000041c00e070141540c3d00c07500500f4002e41c4050b1a181c0300708036000030607494000124a00c0000329650783c1851603580d00300072500c010441410a07802110f81c000000c03030f91b8800300d001e40a042c0240f18031985205924040700a16408400c00000a005104200c2d8031071500d0115180c1c150468205913482d075915400380d401c0002518907550051811160f040c406d0b40c0c1d503140c141310740d205804 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 362767428 1250 362766178 362766199
    0x501060506121603180614070c020a05060c100603111c03090312020c151b0f0c040b1201020708030429060118090f090210050a05180d051b 61
    0x188207561080302c9881c2603035104400458903940305001c81d620f0144003450b00044081e03114600c4016a030032410290381003621855240125004400d900d6041803c2c1d00700394003009200c2e8007095a90031240b0070103110303071001308140c500240c040c0603030759038201d02d5001003000c99100e29000404043c2000418012040781102c00030380842d000160004a800d034481e840075034699681c00004052160010302140280c85041d40d19850700308480c0c40d20102040c3d016200e02d0b400d20122040d81000c0e55488641d403050724001c006990100b8161800c0d08260750100d1035403890808282c1620500150003069840083c0f0703803040c08080345c0079600403031190407100e03074604400c0d101078040c642c07980341c000c2d5070070180700031803070542c0146241d260b401d00c040f0002d00c5166844104100f101c00c10001359072090f4071507100004624141d0321018030030001d401d0150070405165002001c601031081010301806a10032008690750f00c0c0c030008444503a00c10700701c6040245403415100b40701426540d10740120b081a0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 362768678 1250 362767428 362767439
    0x1101050a091a04030e040203060a09020a0306060f2318030a0c050f010804110127080615010c0c090e1204081e03090f041a120f161a070501060e0a09050106 68
    0x2c452a001e80e8055480d04000719003242004002d40c400742021340d0200342c5600000b2118000d00180071185030310f4500003411442c100c40035010030120f0340d28408021010104c80350b440d10b2445006422808248400d4842284140302c200103550104110b0f4141305544185003044203d04000c1c09a03401034030200d100c04400340055801440c2a40d00411098415420b0440307540306100d408551004c0514241c40c3c240e646100325070050740c0d13030032224903500302504010705a4138041c080c42004e4001e2901d012002c1040c0c95100c40e0306018004d441c16903481d0607184000d40420420024520702010825640c1e5030745a002c107942c0e03c4008d201035883d10707054401c070300c100d80701000382c0c1e1602802070b03d00b0a211403041b0803c4020540c00000c0003480300d06207025010390302c40c05410031040d00180d0090a0f4100305050705031070103641c6068240d1516014400b40301c9402d500c0d40d00e0340c244000c1c450703a40c0c032808649030550161403030b0f40001c43c05200c1c000c100403901500b50080100c160095000300130094681c4d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 362769784 1106 362768678 362768723
    0x70c0b13061505040b03030307090e0411040f06050301050a061520010203090619180b131202030904060f051e1306140405070c0c05101101050a09 64
    0x149014081401c1070b119583c1441012030040d410351030700103c001c0103112b8900503201200c1d11080070904000440d6040198518010400d102c0b00c000c12075a40014840351007007d2107903091202181c04200503108282c2a174004c600c4400c0d04200400741503690050750b05000d9017020340140c000001030310a10145005002000c0602802e0414100c0001d00300600041a140e140c904411840000701813003050122a134023030f002035102e40d02c20610108105005502402102001040c0100c01d0340c04002069110403c0720b0821a60382c5502c8803015800e83e5014007900701c1c0c00107050081042c0324a24904100d0030081c44290f0440e8241c410302c0a803041e550008044441c2079030507206502d00f60044a910103864038000d800c00c5003a40762489a0b0000340b0409001e0703107108000440c83c51003440040080e0488000038401070500d0001c60005003d44501681c012a0700003042800c1c00d00d8 = true := by decide +kernel

theorem cover : BRFrame.Cov 362589928 362769784 := by
  have h0 := BRFrame.cov_init 362589928
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362589928 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 362589928 ≤ n) (h2 : n < 362769784) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
