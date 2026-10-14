-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0165
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:13:07.207014+00:00
-- url     : https://prove2.me/submissions/1ae74bd3-9409-4d03-8d3b-5e428d0e188e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 29496408 ≤ n < 29676264 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 29497658 1250 29496408 29496421
    0xf1309030801051503060906030f0a050705040c030519150306020703030b040c1e0c140307031d04020f040b07050c0a0b0d05010e09030403021021060608070c02030601050f010c0507030605 82
    0x907284141d01182c424551003046060040040043d241c00c140140c401360429281e520009040051141081030144030790800b80080c004001081400c480b003d44081104400110045064810132900c40e240f03c00595440c010300245540800400b202c95480340e10f0041d1030f41d8400007a0791000700107400090b121030071201c89240c82e20a03171094400c0383c00c009031030408a610012803c034100c400e82c001e00541c0c02070682840b5010201240c005059800d40303a40d100c0f03d14024080407500c61030520410800e0581a080741068401c40e0340e107010743e440072400c05140c007091251a5010140c2111280550000321402d510741d4410340d0081d01e080c2a4041d2100c0a4000b41012610164054030708903000340284002640044101c8082d01d40560f070085159601034001c1c2c3c3e15509141118103400581240d8402d040300c9139000a00f0350301c41c4d644040031a201c200d82240d1400c0700c440c1c041d504d50404001008107180c1030311003034107060043c1000030540c400d580f02c1f582005940c0e401540e8081c3c8a01c04c0140 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 29498908 1250 29497658 29497667
    0x305040e07110d0804150906180303021b01060b07020904060b09010305010f0c030203011404110f030403030c1e02072304140928080304030c050105090c10110c040b0f130903 76
    0x910b03040c81c03400c00000c5c6440d45031140044040035030140c1c0340780d4036150a011b001e42900070320303040341d0715141c0d01d025030000e481e00600941c0001d00c0040f607000710f04d020051150041c01a0360455040442050038521107800304100808045e0048480959070700240301c4685a04c04100d000710b0156000013080f0411115641c1510080d46002c001c0510420041c4100080c4001d802d03000c00d006d89001030b174411000303010303007992143c0784403030980030004400c000415615410002200c44a951b614040642d54840a044002c1e640521005604008414004004190018007a42c07006240c6010312440c1c0002290490303d000d000390300603a601e80100440d0709000c10401400c0401260101c0c40c8014028000c0a01c0b40c050070028401480040400c060600c80c071080070410350884000c01c600d050a40c200c540e03992104508600072814a881400c207103000700204140c3d680e80102600501c0b82c01c9003008001d044642c840307075004008207240c480076240c00c5011620000000c0002030700302e540f41800780 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 29500158 1250 29498908 29498923
    0x41101080c0d0527070503060a0f091a150f0603060d020a120605040b060303030c040909051501090b0f010203090303180d0b0c0d1109010c031b0503030709031407051c0305040e0711 79
    0x4d5550340a44020043d684000545070360240c141e01000800301580d06848001e840140d0002e40003000070b101001c00e034038a2001c503174011700c015106020340020007000e01c00285800c1c0c900c20351010b01440054101e003004503001c00c14510041043c1d0304135460742d002e035285024440050b1401541d4004003c10804e40309012500301d0f808500960031407030403c540c1d203110703c198002c1841103a00d41410104004040011440441c544045804550303103845c01e14004103500e4410324801c0112a406445c0f650000c402c41d003420002030051403410421040840307420381c150445682201c0e4502c407480c0411003181c020b81c010900d0080e9030ba034036090103034202e040d03500f400707149401c00c081081f040034940c0c1c200400c92401c640c10304111081c42070031010003002c096185000b03090740c000001040384046d4810b0608058034030400c04028203281010b580d42c0d450206003d8a45c0105190500004402000c501000c103a1322a1800c1880c00da02c0b042200364249054403800086660181c000c0c000200902540 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 29501408 1250 29500158 29500231
    0x603010b06091009050a09021804090209010909030507020301090c05090c0c0706030b01020309030d02010c0924200f0a020907050a0906080a020403020a0e010303090e041101080c0d05 80
    0x34000e0000e024006000c622508540b144100980c61494400500644035400140402050b1107903003a950549100a58031078100003943c80050040c0c481985080e00c90441c40d03d4000c1c2004956a007800d040c1402000b940d007040c1c0074000103020b1540117a4003401003d0368039105101036091140750502740a03124202070050041c516050000740c0140800007640c03422580c180c600814074001240040c0d007584030b15a030b000d40501403080d142400e241c054000800440c2155608a100341d6917500c0020304e0070412428440540d070100d280481307a40300328002ca1a1040030b00c0103400d0561000000e41c940203170342ca002291030700040100d4096151015400c0d60100030380c01c240c0e14100d10440c0091448080f805141c041c000502d01240b440603899050307402565020340030700c0f0040e4480c1038060b60711001344802c8000a26102021400045900030b0500560b130000890905030516401501e00d110010712a41d46100b081c44003c0210342c00f4090781e330283d0b84611300c0102c0c1c40742503d00f04081504c011080e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 29502658 1250 29501408 29501411
    0xc050a0503060c031306090f03180906060509040e0c091e0f040803070f0e06040810180807080901030b06030f06040e160b07050a140d090e0705030403030b040906061409060301 77
    0x7080400c90b5001c0071a03034032007811741c08400c2106152400800924024501901c140d50301e106960805402041c00d603460492801c5842c20243d50b0404001652014081c1d1307030011780f06000d00381c2107080c26000340310030080c40004d65048142e500c1c042000c200080711185004000001644036402140509079001a00e5010360006481c1944520003144000b42040080100b2500c0801e841803090040c10900e0400a04840d51140e0320780349190f49010304400c103001e00c0e2800c4104c40d01000c040040140a60784410903c1c20041300d5180c8140c1500310100f0381c0e060507110b4411500c84c0d81d940000754429400c3e030042090707905180c018032007100c400c2c55990311a94400c20010041c24815000c84085800c0c07904603c0c1d40750820724005003440882d00d001854070140b074460b221550300c003040d0f0420b25191943c0d0a90460768030a2100c03101c100a54210300454002c102040100c0c0c42500041491003014002044c1410540e032908100c40c06644182c1d21490b070844c0a0b000c91a0113801290071480c00c400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 29503908 1250 29502658 29502661
    0xc0309150504030209041a09010204060e090f0c1602040f1a09040b061c02040c0f1707051b1e0102031503060103021503041a090307020a090c140901120501030c050a050306 75
    0xc064080d20540c0800f0303101700c00c610009000c10032000600e4400070b2515102c41458100007100a010350060302904000c10040c04610b140e80c140741d0001840342c40d8180700300c90b140d101d4410010352980985500e0030240d1b402c460050150726503000e10740d031014071540c00040d12607591210990a400c00c440b405c2c45210480705002c0491207180311990008021240036041d89241101c000c0650700106c8002c1d009410986040d0880c1d41010843c80032550b00e0f2206446604031072004240e00d04102c1c0d6050115005100d0012920384190403212111100d5084030f13034403900400034030780c103500020701c0e0401e45e90008100202881490428001c50b0001e400800e000d5041d5800180180e19058600741602c20110025061060741d10305030419040205505409080c440d0810740c83c0e81c0020300507801400c00040002d0040004d104400043c9407176510b80300038507100c585450083d030040181c00e040000007802256480a584145402184a0004540c1591a00d018017507201041da120f5071180d08540b0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 29505158 1250 29503908 29503949
    0x30106030c05180411120a020306040b010206070c0f020f030f0601090e0a031b08040e07050414011d01080709080313080f010b010504140402040b180102010501141003020f04050409030c0309 83
    0x11040e400f00c0c10115400300e044050b0440307040d001d0245e00c0d45251140e8501d014821070101d580c0c000c0d03005040a4034281304c20814600103a0383c070b0318142c844c240090300c03030004034020511200400000520041801c00c0003201d20000030300c0c05001918a0a5507000200100f1144805101326840c0e42c44840c007911107203250743c03006002101e845000711000001007061004100f080c10844000d404500d414203010304210700c004129800502403001d04d11111141c0205640c01104074070858000480c10100c48a02c48004450981c4003409034014008050341c0401c0c00c00c1c090000c0e00181e03040003d0b82ea001071800ea4901d2800745070701c000c0c2d40240d240004007440350742d21000300d40540e1074180c00200503402810200c2c0081c80703036510a80900c840880d40710000d600d0150010106d050076402400355076207407070188900d4290300325659030082407000c4d609400783c003d0b0003401e4140025100242020b0380d52012405803091007004030000b50411a9030300030560429501c0b000340000c089039041c0516103c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 29506408 1250 29505158 29505187
    0x316030e04270816140706020607090b031303020a02040203090a0b0c0703020303130f0804060302090112060b0301060c0f02030d0e28030f150606050d0e01200c07030c030503030106030c05 82
    0x400940380602c00681c6804802d208900284c42d25441028420304a40304072905c0d403a0300a6018603001805460003040b103652050304071200391031151101915603110611002a00d540c440d00c124107502650740988050b968600c007440c4a001d4040140004007806c0c1f41c64036810200070003000d044c5105002ca000032035400070640e81c0c4019041820200364185041003c03015a69520041c900134000402042c0f10340e064002d00303260303c001c0e20b40e1903801050002400c141c80f1300b4041c107840a9020700041228a100340c0706100d0150241c200d03400402400d80200707051800c11081c3c0d44c0421800c45005032981000070421800c103600000d0390f00c2e0341a4942d61034256540724840609040140700c040e0302449149203a499854a071480200300c09555043d0180c03060f000500301c1e0681e1803801e144c80391081010702841c0c600d090161903d05260480c50758000103030700503000310718140c8620080400044d003200d1f5918003850142000356141d40c540720700207087c1c071000704074042048000e0045200c00d9008 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 29507658 1250 29506408 29506481
    0x90e221412070f0b0c0403051209100c02030d030b04020f121f06021504031e0306080708030f0702120703080f07020a1208030a0c0513061d0301050f0f090316030e04 72
    0x1113940d4400e15180c5880300006401a40c0001d4107502440d10b9006044819800038605000b00313440c1e41026150711032090f10202d0040001035056000000300d4849148690b1103d0020399004200500307204000700714400c0394021490301c0c5400c0c80304a0a1180303001114000c082419083d05843c2841402d1050003074581e2841200e00c400014004003107810540035840c1d00721046007940b291410342c8122030000300a80380030710400960340110000070869120110845803030072561890340e45072950741c0d0700340990800a031302c441c201c50155a1000c40015105802850307040480c07600242c41c2e4840b80104a9849000da2090480c03d403010340c0e44000420b40700c1500d6110800810008000c0101442070340c19104051442110190707038070021a1003a08151054186190001d000800403144800d05080703801c1662006402c0480c20001030115801c0524168401030403002c0d03034140590020142907550010108401059034484500c40c50b05080c824034640d00203005425904552a000081e925a0b0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 29508908 1250 29507658 29507663
    0x1031203090510020c0a030e04061a1305040204030803040303060902030609010902070f060510171b150d050f010302100306031709040e0f030c060702030901090e221412070f 76
    0x32103100a409122040c00300000d14040c0400c15542c80861003595521003030046c0b02140031400840c40c03001141031a104040540e50301503038003c00c2950b03506100f0340a0f0400004500703500020200401c4036103c50002d07100543c0300d901580c1e00e070305140c035002d420748459421142d1198418010440c02c3d0b81e80d850800e0440c0d9500d40e00596900040c01d201901c208150405040941440140985401801d00301c6084903c3c20f4040522004c080703c8440e03e64100981c00d07224901c005e403902c8403616200381400c403c458441d040d2860a040c10b070521040e0386c03048580b058000e18843c010815410280c0172b0398078042c09032070100705460560342e80071140f0300c200726440d803180004100d204c030702d0b1520b80c404140f0302300d01404c4522010180008070740c0c80d40141804416400b41c100403445081c000410b50340c0600c07058403071042040c00d20440601420b001004d903030080104070100d01c00f0704601900005058005e040300210104883d02d800c2c03034103010322101424174800304600c0d07002c207000540700801c21343e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 29510158 1250 29508908 29508911
    0x30d180302130f0c0807030c170402010503090709050a02040f090b030a0809040b030a0b060a060f0c020603041a100e010f0e01030b18030a050306090708040317060a08010213030c0b0301031203 84
    0x40e00070700031802072003c0030028500c1840d000075900c005070009042440b510b000c0d41c0600c207081000c64100c0300c00f110810340390b0152404c900480c00540c044c030091a4480e602404490006d40c0d141c040000b6200240e030391489083d8001010b1103440d40001c03004025124803a014011800720a005c29660443c1c01c40c041d02000011038211001d9903541c002d00d81d4801e0080480c0c03500348190600d01c6a0107829180d69104008080001905e540201c0e0b0403044a14141c803600550440c903000d12005600081046901c5000034001400c0c003c10340b2800b5004040074005c0380c01581c20903011250101040e0454802920049c0f0100940100c6403d140e042da40d02c51070f0744009485400d11030000051a0074403948900020524000c032551050186118003002c4944400325190b01e0000d0b98070000a68010b000100007450144050b402280c0260304154003410060b01540d0310120301c0d089030041c020316121840010707020000c0c8660b44d100d85014181c10101c00b49903501d1980d030001d803441c2403000d030011f25 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 29511408 1250 29510158 29510179
    0x905060a0813060b0607051f09080a08040816030503041406060303070201030f0b03030a05030f01050901031101030b031509071404020a050a080c040b1b01050f090c011d0d03030b030d180302 83
    0x42500590b10300b038000381400c0e864041507d4003a8865802c140c0304010501c0c201e06202c0e1000c2e5a0041181454100d81058a0001e20100484104c000140196100e040c100243c01203100c0d0942d640a10700d020b55101c030746904291514984083c0000034030442640818280032045e40d01001303c4502650909000682d00d401c00c01d52006000c0c1220410303818000860110a03103500000114031402c564849048960f0303c400c03c0204041c820700014000480180410b6a554000c0d03004e1080950300900300c460007450645070400a9400726404032440d040034108018548034501c088200e95030460307041d4201024464007c120703000380d6190400f04044280803913008040b071000c4401401003249400d56621400600c02170b05031180507440d80940c038040008400c48412101d00f40201041005001e00110308001120240200e401030003680960700301c0d130042c565500d910920210300c207841c00b0a4540700d2108050030040b201d9064010b00244a07096008001d29914480540754110f4044c60320 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 29512658 1250 29511408 29511413
    0x601050f0a090c200604080d02070807051b030d0e030a0308040305040b0309010b010801080102130b090102030d0e01050406140c22050409030804110103020705060402120f03040f05010905060a0813 86
    0x4110140d01002200b8603098511a1659004054131150340f0f09008543c81910207040c95592454101c8024001c214180714100c80c0e14081d8008241e03281c05510030500b030400d1a10b44504202d112218500300310242107484040d0f00f801e2100b42c40301d0f40241090800c0f545d00101080c1c07142c50010340181000100c000240c2094021000c3d10050b0142e001080d4413490513141d410300034007012001502060341c520000880301014000c550b1660301340d000d03c6410600c3c0084610580d000140002e041d0b0005118007903a801d00c40c45000c0b00b220b8203400100d864205030901004a410001c4405100210344081103003c0021200302c8a503000040d0059814040c02120654044891342000380d001d8140f0b03054009042d8403c2200f805075000310300305100c09510308010340032407140c0c00004146400c40d500080251038010120090000564180c2d031050300e03144a06d034110f9015400c0309862500401080c80256070005112002d0503060b20840e203010411000980250130040181d4040c1202c54030b001d08 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 29513908 1250 29512658 29512669
    0x4080a020a0b010b09030115051e24041e031208070c0c0e0717010501091205070b0408150721180203030d0f0e030a09031e05070303030b0909070303020601050f 70
    0x190881c00b5101035503101d0134a001e0540c803180f6413502c17a60034808504a5603850082900803030b000145801c000821039a41025141e92107207141768481007a0405003840c0c07101da81c0d0580c3c0720342070790f1105655a00b07000f030740c1202428005021142c003010910600c0000c0c41c40c10044d41454050409100c10b170b9032150101c4603c0d82000b00104240603a002c002040084482000c0c0511495114040d000e0043c540c6131241c1942440b44d28000b8441ca10100a404900c503641c0310101d0003070040e00e2083e904c0b841d0305900d039405503019040d264402d100c406085449d000e58907410a80914054400c0c01f140c6004065031500d10101c45680344c0d43d2890710b00a501001d1080c405990f010703090b2502c5604607864a00101442000410018184455405500c86c0801150911491504c41110b00c3d41162141c800f41c46540c101d03c40152851850b00010031400c1040500551196401040d20031001d01030080d140c501400404080d440104203200194001c10098151003003605d16090003081200000c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 29515158 1250 29513908 29513923
    0x30105060c0f070311040c031103010902070501020c0601061e020111031803070f03030606030c0206090a1410090f060b06070c05090714040305011a0a0b030f0411060d14090a0b04080a02 81
    0x14030b5481400000020010724503100c542c0c0442c2100d04205a00c10010280d041d520b04040d480714200040005200603c2240d0240c00d00600030781c00141020800e4294a1420034203800001c0814030001d4078044080c4003511001d000c841d54070003404411511804048940000f42000407803008655000ba440e41d81002521a105d405c800018540c4140d4100130b00202440e00030500060f0034440c1003030b512b5000140d130310700910301c600041480301c2e0f0a4448248403103020b1030015241c0543c02164801d03120502a80f00e006006940181e1107010b545001000c4501c0b08032594014201403020350300ac11020000c6208403402a20150352a0750303514001ca40b210b0f0300c5080c0c4500e8800204001c4180a01584003480040301140040e021b640e590080020a032010b00c42d04401031410400140080403e40d0090303041440b83d41c900c1081124680003c205400403e0807000c01e681d9640d511034618250081241c00c0325405002e0401500f15480341c14258000600240c60020000341d1220054030812007170 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 29516408 1250 29515158 29515183
    0x302010509120109030c050706020c0102060408030403030b0d0b16030c021c031d030c1203040b0412050403020d110109050111030904110706020c0f1606090e09010f0e03040f0801020708030105060c 86
    0x20804113006107000f4041e040401d400744c40c280702d84080803030b4084c00011040350089051f0001c044590301c9585007407003540001d00c120200750311000700c11200d07107a5a14407425184642c09402484c0f8026000400340c4000480d03101c1014145011502403035000308994079a5812801031640e200058a0260050084031042d91007054100042c101034203000f101800700700c3e1a00c000e0f600b04020308160f8a4050200f5100546035446250220780080c20100300d48030b0301c03003a1307003052030405036240c001482c034a14900c015101589030340402c0025680c840664009402c0c2420080c2800c50070114913a920b01450300e03024007031940c560780d144044021809544566510200565503280071894540d216980500c24444130b11400d42c08c1c0380a030178942445000d8541c10b548031106545040301030782c002240a0a02036180d540c0b42c0c1e50000b842142e0140c611841e00c2d03c4001d641d82c910380040782e82c00305550b510084072644188611030001c0e211004690440c3c0d022526030791036062072a505400c11040c450300 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 29517658 1250 29516408 29516411
    0xb0301050c0d0c090b0a0207050a0b030c0306060304031205070f02010c09260102090402180a06110c0609010318030306050a08060f010603020f19020c04180201080601050a02010b030f0c0406061803020105091201 92
    0x201d1b84c042e54002264016588281c6080c04400da654070305002034041a100192900340c207000252140c140400a035034414000e1401e4600144c008004000f10390003039136810009501002d05e28220b980902031001048124a081410070f440c0003200b5080c003004803007681c100096003007600c10190094060340c54100d0028421541d9034400da108903400e00e09074a001c2d000d81266000000d0007030244030305c4881600c55802410005142c5000c10070315910800c1e859062565600582080340b0b210041d030300004d4400e8034005000382c203050401002003299407060a00703500a400b00850700807240c00050459205040c00b41e10f889050448002c540a07200d0000c03034184a0f60420903a00e6400990f800c452041a00c0c104503525050403206440f00045201901107100480400c8965100382c0080182c0e5282d4400000c0304012030300040d00b0a10481c16086142d417140c1e05e111a03519040c07040c1001020b003400c0520421804481031012066070344006414032601054404440c2c07a0002000e2000352003500 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 29518908 1250 29517658 29517667
    0x906060108100e0a05040b060904080f0d0621050c03010213120302070302030604060f0501062619060e250c080f040f0602060907080d09050402030402030307060903050d0b0301050c0d0c090b 83
    0x1320402044120340030369803130450202064940c10a000000d010350340090160f0300d02181da00303402049502058644286690300d80c400540c4a0b541c84154207426114000403800b944141005854000e0300070845203e40d00c100015400c01c040760442000722041842941000c0c1502c0c20203a00305045070380069098081d08042000b003062582c029048100b02e003c00700116621241c5c2129407250388151802000e81c00b00d03030440801034440000e036000000c100480c10500c40b4003e00b00c192a134030340c042d0886c403841f80144613041481000e030809508140d00c40c02d0b680d2852410081c1480410b907000303051054001384c2005003005c5e283c1180e020b03003940303503401001c203984040c004c1d51200708880c0307800d60340998000072640a0700407407d0090621f5540d1002040360510302000000d5001820499041c4001c2091400207040341c01076080c3d583c040e80300c964030b900d40108203c05860002d040d840c4640d160508021b0351000290644405c070011100004030000705a50a9409005940000310501c50224 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 29520158 1250 29518908 29518921
    0x80f06010603050912030c09040b040c020d02060604050402060f0f2811010e060106050f0c1606110712030804030c0219051306050f0d030504031205030417030906060108100e 76
    0x504a81203464540d410002540c4402c44030b510f48418108000f403003e070420110b0b03000f08152014008d070820007040020341141c031500142c1101c2c04426070303001607003040ea500441240c0502441e50b2004d01a541400390740b60a0b03002810070302c6040b00224031041c010a0321107820307084000359012003140c00c04060000c6201c4200860701002a54201c0c0002c1ca03140900100308c1040c004c1c00858107507640100301e164200f103000d03584c0e608078000092100e4030910200f8108001000614800742d0001c0d4840011800d00c0340040c81b949000c2c040b1107132035010070f004000d00c3c0c600d00e18600b50a50103290001c034945452034121000003504d80080d500c0800c400f40c60070311040303009200c1c0c11601c00712000c06480b05500050415103000b8814954801426802490380d030601065903181076100f491308a02c0e15850340d94642c4109990749c0c6000024401100300020052010407403150303003964901e0681145070842e5045d03034411000340064100040c0030b003c145181c030075642c014090413825843d12007030307e08036 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 29521408 1250 29520158 29520163
    0x40f0b01120c090c170606130e0108070b130302010c02010e040903030608010b1002060f0c1308010e01060512060402040e0f12030f06090403020d030c1701030521130311030304080f 79
    0xa20080e00c440160000c0040c1150f10b9108400781c2c90020b8a482040340002418200040700041c0000c2d00480108003503e030529561103220040c100400c160007035541407400c9280347c14129008400c041004004100c200418501c14604490742442c1c91140d029032440100c56240c4603002e80c43e04103003030080078001c054240d0002000d4818540c001c21a80710034404000f00c05440290200140c0c00900104800b20542988654000e00031444a407500c250050b40346c42c01300c5550b12030820390755900d6810210721020f003c0c6400820742200e0045241804030360041d00d500d00030f04007e100b1030b9510140c021488041c0502c2603a0400601902c40560f401400d40840c0c1c3e01c2110f41c1e201c1d041c2032500241c0c0900d40070807a82d0203036416034020b10f0010750a040c26401082200c103554240403e40400c0380c0c2c0b0043e2101c00602a5120b54040c05001040c1d001c100d144002000c11401d40610070b1141400d008402d13079040c0201c07504401d0388501c80ca40c50010906510503500725070030314001c1840328102d62500 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 29522658 1250 29521408 29521439
    0x70203030a1119020a06050a0515010c0f0503070b0103050d050403170306010c0209150112050709030308070905030d0f080f0c18010c0203060a0219110a03050901030e0f010e190218040f0b01 83
    0x800081c407407984e4200008d001c50b40101c4c0d2403554035147ca0540e6507154441d1000468840c480c0410314001030329522003902e90342041c18100e404030f070f4120043c801c103e824000000e84c0074aa040481c01c1504540e29000e07804d80c07000784403020b0701000c00005c8250b0300c54242c201c0916005402e0104074204180031a1001c1b900804250220300f5441d0800f0351401e0611405110300b800c2e64811a0f031070309658040707503003d401601c804100030a451020030705036400d20a40740c08840b540c50381e01c0180030740907014001840041130001001c90700d0081108114500045030b0a151980405c44032910b494001a64440f10440001e5058414482008004c02e01d81e4020412510f40d0030b0058000e002c4003a0480d18000c2d1010425540d8010004010000340114007030850404141804202401521021454108021901d0803030740c0d110400c1c0166814188402648141a24000c2c654450700c1c0d0045010b0314010341800c400c2c41120310000d001e026480c00c17a00c0d00198880f4109002d540c0d2142d400052032039 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 29523908 1250 29522658 29522663
    0x303020c0705061204060c050712020304050111030a090b090301150b0c120406090e04060e030c0606010e040902011e020c03030c0c040c05030f060f13020c0102071109070203030a1119020a 82
    0x1070180041218039042c1d060781c1c444655015458030641d81da5a480002e4080d551504061000c1448038000041000d00c4480c1c502100d82d00854950b894070000420454901d54900e42581040040310300c920b502180d0b0209403648001c0183e40d9104500200b40103000086d901c0780740c1c4039980740201d1b00c403a5201c0141030041440c1c1c11103084c888840c40c214811703c914481c41010540c40c43c030401002800c0400c0a45c4603004a900040818481d1195415076119681d104e503160068404c021296030841c88000101c01c064800f00003204040d400a0095068080001d0701c90b05000d0008440c68420000c083c1c546102809480c1c40311811408540e55000040e95244a10b00303010b0310111640c802c100341c0c1c1c840d404001c0610803903110441481075030440085080d8002d03808808081e020481d9000420103884010001655840d581c1000105c40c8502d11200d8858180c000034402d00326400020750360001205140003c0048101c1204402c0340301d40303c15565903203007289091002c10340100e4240c1500c0d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 29525158 1250 29523908 29523913
    0x90301020c01051806071d0112020304030309020111060c12060a0504060609060306081903033303051506010507032601030f03030e0705010906030e01060e010902070c090908030a0b030a0605040303020c 88
    0x10013550782c64451204903403140c0050240c4031004000e0101e06010301180106050040b1015540b05140c01603a008035415004280c82d40807903021542e01610130440c1c80322400150055080c000d2a05e01d0174404e8030080d410103116000030134441c4d41c56030000001008010810081c4950b42c43c406440700e030b82480740da400b180c60000b0018030f1003c04101a54010107901c2c0020b030048071654103500600000125020400e00114002800410584002c010b10b80140f00194a189503180551401d0000d0350405206019002402100c0e41c025098a50701940760802b95a14410b1241c1a01e0841c54038000702d0300c44501c80000070074404070094110045009503000d100c030444070b0a00719030b40c0040d84152800030702e812904005851099020200549c10140081869a9940e01144400d4400c0e0003603c40380c0c0d80001d00c0d000300103440000b0740007403da520007407010520b0754652a080e404020012403200b5200d8540c0c01c49580c060050500e5190311050400c00c608203410010020341040321040d1851 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 29526408 1250 29525158 29525191
    0x3031d07030212030310060f030e0601081c0504050901030f080f030a090c0e1003060c02030d0504060b04060602070608040605060a053a05060c0d020c0d0e0102070902040503100b06090301020c0105 86
    0x1041c01301c12240700d019400043e1100b81d1030607404480100584a030700c07041603621181c0f41d240c50710502c2058000c1180500801010902d40c02004009900036000c200703101c1c2c10070003005252620050181100e802102c503005030300f641d003040c4c021441400343c3c00e134180d880041048052841503004100322030141006061207620740c4a0075070103980540b0400740000c90002d0410024001d600300100a00882c41582c0c202a1000ca030b000641d082910100c0c0c8081d01c92480180b40d05051040038018405403000b0303c0102d14158002d4140300000d480070f0031198035100040e00c15281d40d0100130040c9800b0700505840c21a650411007240030b40001030004c15000c09854002082503500f2010494000000d0201a221702a0f550110b600543c101d00080e40c080c8041c071189102480564225501500c03050020003003000024103010558000c00c4019105100c1400f1603200000c0d50b01c00781c8040003001441140b00c80016070300d40200803821340d2540c00003810222040c410341080d4000c1c5030041440707801 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 29527658 1250 29526408 29526439
    0x10f0e0405060a1a03071205060c09060304030f020102120406050f0c0306010f0c05011517070b0301140f0103091b050f03060915040c03021005030105010807020703050c060703031d070302 82
    0x11001035602812070740c4010040707005602030764800001340700c0f54100c400131105940042800c1c00c000c0e40c0594908803522030b0610500006200c02d81e17006c13000240342c5242c0107186001032171600010b071000e0100402c0100e0560200c1c000d50440c1d030203a9010803054041e00d410b04d0030310042d081c1100c02d490080e01000100b01d01090311015203000ba00161941d6510b105454021134403040680802c0d1502e40d00c0388000d0000c41c080b00d142c500a0414400440c03520300e00158034a00e4a0619070251401d0b450410040180d009000c0c00c0110007a0106c90b21000c16a091004030080c00300e10401810a802e000304039000b01d01001c081c2c1045400507142da5500d204040b003054ac490604645801e40c54003e0034000300c1e003100b2041c0c0d05a11621820160f10b419803aa00804e4021720590004000302e40000014440c640e00401c03140e40c01301b8248000e0040904503582e1984440140f51040d0040c1404074881c010503009801041064041200ca103656905441c02d9960b07460252000744c1c080c4090103000b040 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 29528908 1250 29527658 29527679
    0xb030d090503030d1a0d08070201080916060c05010e0f010209030114040c141c050d080c190302030709091104060305100308090603060609090a051501020a03120507020a0b0708010f 79
    0x2150710007009542004010100f135800ba1201c440e420b1120b0201886210341c1e03540b144042c12050740260903143c0c0b641507900c005050b459003e04050560303848160030041f03c2c40415117820580d5228070782101900c88a03c1d000b40075114045c660a2540500346445400c10710550140c049100105d00a102c4101c18040380481b0480135030340600907902c010402d0011640d42c3d007400d034282d40301900381d81d07001410424813003001703074911002c484540000031004da02580c403000c86c1d0341000400b00150f00c0c10203025454000e2000c107803500310034550003000083ca2540608685c0300201080d03c002d0001118150720401181d0180c0250800f00f4070f41070100d00001c10414a540136640e001c8205864100d40c90208091900024032081d400381b001c014024413a100d0a04c4035000301d101900104135401d000c9007a0700380d070300112003140c1194050a40503022950004030754618000800740003620780c4641c0422418800d0b0040042d10200c20041400040c5038404038581c12200c402520700040c5448990240 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 29530158 1250 29528908 29528927
    0x604061a03060c090a050d08030114090f0604090c080304060507050d08060d030e0409060207060903080c0903150603030706050403120f0c12020d09020a0f090e1513060204180b030d 79
    0x6400d98001800103c0d00d010050050581340c60042241d500190b1b104000b804007862090200c62488000c070042018035500181d810340e40e4005c503010503081c9415001c10350309160050100b845151191200001d100c411000702000d0500030701640e665075150000030300b8070ba2140c3d004a40f54031071112034441251185089901411009100d13203811581030324207d0300600c0350701030298410b9540c40c3d6580000c506200078600c403846940b010410f1651801c000d031030f0003c01017011101e40b40400c54441e80341e801060b414420a00404260400d46406000c00d00e1400350b4400141194682030500c0281034010b004500319180c1c085048c4551804c2d541c1c880107841d185040e51012802e01c001d040040d0441d50060140c0e9030a0000001300f00149400254841ca425805a01d03454220324052003019014012a0740781c0c0c1c045001091442d90340d100d00104c1010041200d03541c800440182801c100030390301164000d00650302c05002d039040c00b0455034014140d583d0000c1c800e1141c1d00100045c0341c01000c00b00d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 29531408 1250 29530158 29530211
    0x11190203030a080a0e0105040309051e06030a020a090815040506101a0904091208010519050f060703140301030605250206150103060302030a080714030c030406050a050c0105040302060406 82
    0x15810100e50341d1007a20403e0000d800030503129110354403803003015000d2080c01d108a0182d5100303041185031009111138030a4002c0607001752110000c1c00030203500c1e0002165003003148070300300507a180c41c4543c0864a2080c02c0d04104440d000d0240e080c020018001c1156010380d01031401e0f41c0041d1500d040e032160140851103042d20800c140300c5120350307035050140a0140c411016102092046080e600d40e500d1041e03012140011032103410040c00030b420b042c0390858854551400710060f9070304140018880400c51014507100d8000010507504241c891005a09004030200c4031a0303c9507101d02d001c1002c3c0008a030140d60801503000007103108984c800c01c1d4500405150081e05003519290308101c0400c3c2d44609031818161543c2000005880030401141400e0003410210b4440b9403a01e000e040411000135110202da10901c0324019207a000300850b421070700742d800c240b03586a014400c29110340c02a10001882175180004010901d90023042c03041c4140e1107400100804501c094000440f241c0c00c0c2d40c0e2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 29532658 1250 29531408 29531413
    0x210f0609050721030e0a050603040b0f06060c0705040908040e0108060402151603140c0304140301050109020a09091a04060801020a080a1503030c0f0605010605180f06181f11190203 79
    0x1907102080c017030510a10a10b10180800c161a42c94401040d2990b10656044840300e10480c100021241c0d0700165940003035007100d00a1600d800494165136400d59800741c184900d640f20059410450b00100312030062480e003140400660b0f541c00c841e61502c8003124260f004044580007e0441c42c2401d0407618007001d019071140210b480354800700e03008900345004012145007080b14001d896007c1000c2d0009002030625800300030b005038285070944030182d0010f18400c1c01480a1618a074100300c401041e240740b90310000d00f8008038000c8181581100c480c07650054031702a0042410b91040d001401c032a000ea0716503207003a84a000307081c022907400784803564643e40b8400c0240002489680041e03500c6025140d031040500a0740ca070303501220402c0e40b0107030124130001042e001e68541d00b56000d00b030403401c075041d00c118010440130400c940300382c184000308071150406040640e0f84406803500f0511001c1c4c5001e1202031078907401360140c50805424042d5114003840e41171000034152440c5040c0350301801 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 29533908 1250 29532658 29532719
    0x3030406080f041401240503070e070809010908070609110f10050a0c05030301080706080705071a04080c0a030201050106090504090f02060310091a040c0503070207210f06090507 78
    0x9504014601038400c4400d12a690b00d1305000361002d00803041010501500042c43c003a0755143c3c1e81d00626154400750107908580401c104826075605549e5100c2d540e8180701d0400c0c4d039031a5045004142e03418004154a0000c07811400303100c180d502c00d888991081d0030550000c40e03118100709a41c201c03420f00c6035214200b20301681100d07101d98080d01c0000c0d164289901c0c940003c0d6038050960700300f600b0041a0f41c0c0200820080c0f10760001c603a581054960030054a004100e45945003003200c864103511803205200049010403180c0c0044510040c400820745810031810700d8024041e200a00c9440c000074100000170515240900ca4000782c00ea020352550742201803a4244840c0d900b0040131030100c1c49070b1003000601c280b03150050112000000304040c20346900d00c01040120f50400c6000710801c80203000700080540c0000b102c1c000d031544140d10385187d80030f00c018140e1030b515820740208071517078199040c800c0021030341103c2d252030710500c02c0d41e035134030f440d00d85001e080030380d03080d00c82c5205c400c442 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 29535158 1250 29533908 29533921
    0x902030c041814010e210901030c270501091401080a110405060309070503060a02040621061502101b020706080a09060207030206040b0603070501020705091f0f06020c0303040608 78
    0x2d012004504410741a181490040e848120f0304032420380c410103c90351141d6030314651110902100341442d03c013150350a1004424190f00c40c25003c0d40c0c0380681459a10600103607450300903a070300c4085c1030552000440070000000d9020304a40c2d180315a502250b00702401152410503101d01d8084000b0695543d071566451503030400260016041101c0711050070040802d40c1e40303640d0015440350035150020070020b490300c4103041c58060700811404150384144001d0012a82c0038940004003000b900c551801e00390280083e800805c8954400707850704650000000c0c1c420b8011800d0102c5c0d4224179402c0000c1c82d5103403c5c510030201d842e01d1810040e0440c000a22125000315a0940c01c50010200003074602036503960701c012a40500310640260b84418104070811036154095980100b083c0c000d0400107140000103503582080b40100340c0318050142c005082d100352000300c41e02c403c212000c071104050b55000c1300309034590940205401070145a514040b00c2c140002150100d51082d82c806440d43d0b07074823 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 29536408 1250 29535158 29535161
    0x60203100302030a05060106020601091803050c1002130503060a0903021e100c030b09280c05090a03030c0510020f0703110a1203021804111801180e01090506040902030c04 75
    0x4003410300d1402031000100260b00c0030800d14040742c0c8100014940c950400c5006032811030142d110308411400d055450010036604522041c0855241c104151034540c0c40410310b0074244105007001001d480400c0602c600c0024141c69030403164190280e038950703252010450148e0340c0501d0054056400210950381c04948014000042c40c0d01c0d80542c1d10a81d9030a5101050f507640e5484840025103880c0c0010040c6000101142c00400601550b000301898441080300c81240d081000308040d0758011440e005030243c021150000c400501d84594a5100d180140c0a14000002070301c89228404000c1c0312004a44200ca442420f80d500b041e0034001c940d581100d2003118072900c0310080c01759400c4c90740001d1440f840c08c60100c0c4162000340c2c81d281403606800603009001c020034403035800d00740d46d2048480e40d88100c0b015032952920b9082d50154190058906094008280c0d40601028000080101028012505a4854807418059606c4000800c0203480c48a1306c06076040c1c000b041448410704c5d0a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 29537658 1250 29536408 29536411
    0x90813300201120c02010b0406060302131802070602031003030e0604030f020913151d0703020901120501090209010e0406060501030605031c110a08040302030106050405010e0a09020f0d0305120106050c0307060203 93
    0x5140120503c5030108104056a481c03460120160707450300700d404070f030f031400303004200c00790484e450110309100181e105144050854031485110302c1c503540401d02d800045804076905aa0051010342d40c1e41801c1890800c021400e11080e80000ca1034040e0164610b4600c044908507500f01d00c0282141e5416001c02c800c441c0d028282030500e01840c099280042c140e00c0c101c0304a4a2000c40005105011401c1c1e56446443c544800c0510342280c401480140c2d140c507409410340e0000282e0039080c2089240c26401842d00d028040d600c2840c0f8400007078148007a40f890b512851082c42c09002403a95000190242c90090041a40c941c1102d4400c0109150404240c81c5004c130500e0322400041c903160b01103003030900d41c200542c0c4450700003a040c802c0d81030034026100240000d44d420030075503150800c440c000c00d00190683c034605840341004800e5588442120807205401001401989010703c1d002d48075070700c030700c80d4120008241310001401e036003c0e106031204003c1d4980918940b0171166600c0c0001e610 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 29538908 1250 29537658 29537663
    0xc0706030c170702010515090106051605070302040203010b0d060803070f0209060a09180506160906050c010902040606030902090609040206191e17090601060e01050a0c020409081330 80
    0xc10400d4402000400240364041c2810344c0000600707082001c0440da0741e822818020380100c0c804001084540e81c030408031031104c44604031440004600d890185e05060560344040e5000b40040004a02040c10000501c00310b5481c41080101940d680d6407113481e40940c400c040c1c00300314203510010141c10001c03543c0b03601c4000100b0301c60049440717131110001c840c10a0104001401510741200400000f000300d5234020501012860403d086040018501c001a00490b401c110000c10041008a42500325802c07543e40180240030301c0e80c407664020000d091520040e80700b155001c020445038140008650b01554018003583d01d03007680001015040aa00d9412000f0800b00b107818511103460b400110b46042c0c115500c4240640c41c0320484800e046002e00600100d810044c010000280c0100d50020800c0080c02c4c180e4607100d500b07505441d00300460002030340090400d0100003c2109400040644031030308081b0300030441d220b00604510102c14242d00c00140b80752003080d1080320007503840680e01071 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 29540158 1250 29538908 29538917
    0x3010603110702030a12030b030c100509030319020a020a05040c0c030311070206030408070506010602070617040809040f06050907020a0c1205010b10020a03030b090408070311010b0319020301050601050c0706030c 93
    0xb00d940800c0c5809083c81081c3d443d12400079034600b10950502464100c00000ca000340140c145600002c2c0c4000420311041d014800002001805900d0610640300d4500003e10741c00d580f00c0340b0000203500d50241100c02c0340f2445180d0001b180a281c03520803e800042c155554003101f0740c0b5541c055004045103681b5040d01c3d8002d03c084401070390740600451095100b480c010b600c540461411a1803c0810303084401550410403040c8034280e4030201307170f404000b440e42d08041c00f611203080c40840c0744070f010206904103081c0b000401150449800800480700c00703072403c00c465503407002e040f078907100c548000501e403070301c0c40508000c0c034169107540400c0c00e4041c00001a081c1c180500003484103058082402c056000004000c1c02d068051043d1000f50302c7c2507804001754601550750000301c3c81003074801401c1c0543e0400c120b016034003d5209890540010b01119908660004800401d00b84d0f01030883c802d60805e0001075035948240d094503041c0c003204004001c00380c02d00d00c0a034080c105150040d030800 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 29541408 1250 29540158 29540167
    0x50106180b1207020f0a1a01050d0512130302120d09060201020307021f06051918090305030a0c02120301080a060e01020a0e0d151401060806040b06032409040503031603060b0301060311 81
    0xd200a0246030101ba21039042550349041d1801c1c2030450600581c0050301c0340c5d1b440c81006011500108034034000c8904c0320084c50f0380d10411050410401c02c1c42d04080d404c0f01c90583c041124160004178441485501d891300d1070111f940e040201c2c241d03c011181400140c110f4a0200e03120002c10240082d50700c80c090300800c00326103400101e06245144e54a03032080d210741c10400c0141d001710300703420302202c99858003c1c4100151a01c0103090b52102508000716546d030307134182d8034109100740101d03040c036101280c80d0b41d03582d6075030704010790f480c11000030a482d0340d40f811070001c0c000d031014401c840d5010542e442d0041d50f4078003102040390f140401d0205594100461800d0248406a4424005c40104c0d0454801055040c901c00510140c0024030403801a468600707642c00c245d617071205581e0b2043d052540744e0320404050540da9a0004045003494004d08020244402c1110110255205864400f540b4174002c4212400706c0685075148280340000a0802c0140a114402e800490002480300b500d00c1c5031 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 29542658 1250 29541408 29541433
    0x11a0f1207150203031b0a050405010c02060705062706040f06110d05100303080601020d081504110705330a02030c19080912040b0d2304030201050106180b120702 71
    0x1481c03842c002410040c0c00000400071a4072001d002441d645448003411424448889000341040c4070340e0186d07a040c040c00388a03e4046558580443da2029441000e4a00a051940844808040b500103c54a10010b07510716800b2140010f240c034032a07600078001c400d20b40282d40740c1e40c005200f1011480801c00080111115200e46402164028078000510001d444c0c82c50400502e582c07405000c581c115005404040144ca43c040080c940001c100a6680048105000000c00070885560045c90074400402e94400340f05c0040f0f1003582150755210700304210000401c4440d401845074291140390642d410110b4203c440c00d50145611070072090560307244c11849150082c0c001c0c10103a0107000208403600b00401c24105101f4000303c2c44c0e41d0b26010741808c0c1001180040c13401101080d4101c5581c0744844184c203440b6548004403803001c0503441019090508009000e868240510f4020490310303081c102e44c04082c408010102c1d403600081c51b0610308104c0c41601c035502c024140c1c07400c42c03190501000d038 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 29543908 1250 29542658 29542679
    0x9050a0621051204050d1103011503060e0d0504180207020f09090d0f050906090d0503070b160e030303070c030f021609060807080a0c1814010e09011a0f1207 69
    0x4601a0085a07080a840703149040c41c40c10010342e03500301d9050010700c400c01c21a1244c8005040c803590200000c0030a101c0c071400306c1d0042c0010302004440800358600002404030540c020900c2c0342e010030540b05503007021001901e45114a01c51039100c03500348084103100220710360141072101d20040080403d800000d0000e000401c0c01c0d11141459000720305c4040304c0a400515046004180c0d0a0490900131f00030002901c0f8040c00c00f05c94064040b00c3d04a50410005200b120407142d4402c2080b040c03401d010707030340d40900060115007034080344050314800180d14000013138900c103031020b98400c141c0030f100d55000ca8419264141e01d6055205402003003110f4030311103405001600740389000080c190b141119091a0070304681c0b285050b90000780a45002c07a8031085c400b01038642c1b103090203a06020b06545070000302011200c42048012000c004180343e032081a0b040e01a10842e00248000c01545c650780380d00f455503503101030344941c814600a50f6401c0c00c40c4074000d01030540e016a050607907607501c2d859 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 29545158 1250 29543908 29543939
    0x4020708030901140105010906050706060506210f04020603010909020607020d03080a11040308040b28020d0f08060d060b010302070206040311100c110f06071b0e0a0e030409050a06 79
    0xd48000010040049600007442801026002c59029810035490200003801d12041d40c00f810f020030400007451810b1181c3e0380c0001c0b0003070401614190761a078103400d0100d460211202c204840f8401203012600f03400345620454040da400500c1103256903e0f00d91403000500c01c00300c040782c012005012150240c0d8424042c11901d80c026161640145050350071407080300c2c05c80c450300170350060901051020603900000d46081e0390350014815a182810701c440d07010120303040101ca445401020040044c0c0e64082082220100c441d159240358030100042901d0044040390540c0c1c0040b40044990302261007600285480007040c14018030700b591907008140154020b400aa13030842010108400c18200490320700741c1d000032032400307480145080c2d50f524100130b04540001e10483d000880e0b0131603583c03840d0482301d103903034441502d417104540b8281041c580c840501c0784011200400d0005144103000d800360b12007408a440243d440c060802c0640b40041402401303010419585000210b038200e41d802030302 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 29546408 1250 29545158 29545163
    0xd0305010306060801020403030e0f0a030c0f0305060601050705030901080705090d051c0507030206011208090a0603150807050f2112040e070f0c0b0a0e061005030c120304050607060b040207 83
    0x45820340c194201081651070703070303800041143e10422040012030780c025900501004100c84038081c130310b0310400003010389069401c09042d5944143c0c0028200100060a40c112442202a40e07072541d541d000554440c0184600941607400c100b2210510b0344c82500c085138030076a1401d10078103001d00320f40450140350b480102200d0503400120000204a200304c03603041c0140103450603500d4204a568020345070312061080503562441c0d000c04e502041241d500781c1d190110017925203082e065440000030003074802100c01c4520015102004074800a0100305502503410203405440c01c1040213040c80a404143d6030b41c009900b512407070108100400f44500000c00030108955038440382007c00304820900098929010710080c0ea51460520741c100c3d00d000807054110002007050380d80c5421000c09458a08070404250099104000c4524252000759050b1941502100e0340d043c01074090203201605e042d5442143d90041c0010002890210006d08545200d0f64020544005501c0410180d0300400000c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 29547658 1250 29546408 29546411
    0x1a041d010203010602010905070f0501050403020904050102070b0c120609040c1404020706060609030b010603020909070804050a02130606020c04050c1603021005070503010905060906010f0503070315120605070f1b060e0d03 97
    0x7c4001d0080411200b0064044003d414590f070b850240040c00711300c0b07140b000901401d4440009018880d080d4142d07204190022500700c81484c1501078501ca681c400d46601b00d0040345040441da1505250941500c5240d1006407125904e00709801c0e40303454010714180a500036001c00c05403001a4160040400030442c903107800340910b046240c50080c0c0c8805030003800401d44140150390302130355040d08030340c3c0201300d07402c1c03c0360a13454074241031303081c20400d6201941042d152460810030030181c0d8401d2089500e103a003501c0d00d06542c00102301c00d488041d9900c00865034280300c600311103520b00c000003a0a0344a80119544c002c7c610780c0380c0054510840d5000b0114002100402c40e80302703d4022640d110b18210382c68465403a00b84000703020511041400030401c01c01200003140340d40254009800180340d18081e2011540c5d9070304480c900180100f08840b483d08007404211414040c1e203032030030991215183c0303100045503052450032984004c0e8050b1a1140c494110150303800092003c4050352056503030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 29548908 1250 29547658 29547671
    0xa090206210f0c0d0c0c06090b06030f0a020303220e01030302010b09010603020a0206040b0c13260a0c1a1201080609070602071409040812010b070b0a1a041d01020301060201 76
    0x300c84414004050010080c014410402041941012998401e083d058005000d0018610407100c40fa10100000e1030307d803800115205100994441c10b00c40d180840482c0d90200883c1d00880d110180313048001d4150b070040c0240001e060b0001c500f4818003a40e0100180084d5894541030307901c910a07401980580d5581e0ba5580c80d41c00d0000c00b0501422050400354904080c40c48000e42d01c3d031009201030310b000c0b440303c00305200f80e1001c403c88a6031050740780903030b5500d900c4040c5180e69107880460014441d0f80280360065415000c00c1c00100350f6000340f980c0003150305c0c04080090181c46070380e4005011707104004e68102c0d50901d0131002c4c043c185510091800d841c015000501d800c0c200d0b04010b0039540500e20403c40030704032102900034074400b40c1e400d4045444928000c0460301407100f50000301c800d59800031400e40110307005403802c1030250900505644404e40000102c0342c3c0000c906814640005d0b82c0c500c0360516070003640c401c5805221214034001600640d608903002a04034200507511103a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 29550158 1250 29548908 29548957
    0x20041d0c01020703020a0b030a111321021c030c02060a080613050903040b07021305090a17070f030c05150106090504060605040821040308120f070c02030a0602030a090206 75
    0x91056003140a00061040d42c0c01c3da0002289001d003072142001c076006c0040004c140001070780040b04805405031826880b1000010454109541800392000c1022060540c0c40128403800a80c1e90b0b80740c02414a282e030f18680080c0900418018009805001d44031a820005840b04001424001115030f07c0404a04182c01001080032801180007251030408080c01410720b40070046070212060f84445c6d40d1b40d03107058404a44040a11140d00c04454640700070042c0e1408041940940e25111301342502030140d80500e1810a0700410801514890740c0100983c004307802070500d0301c0e4444c010303800c5510f00f050103084181442801d0300074400240208104000d58142400b03000094210f6003011030806007420b08913560b88910b8140d01101d051017022003c000c40c03001c0d040314042c5400081042d61100d0301d0024004005003070342c80c1000010388070002844103100f6580004119402406005034203150748690000e500080d151112540c1d49140e00c40042e6540002001d200100c03210b10760802c00c160 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 29551408 1250 29550158 29550163
    0x30301150e0a170a0201090501050316030b03160801050109060605040e010302010309030c2102010b03071208090109030b09010e0d0912060921020105040b060907020d260a02090f040c050720041d 85
    0x240e008d68140b040a0042c450070030070200480100d40a0b5180010b0340265880c0020320744800341c40c0c6c0401010340c0c950003141c80c10064000318140c90080400f03000180c5d03a07031f808440ca48154410003003211881030042c40198441c0d0001141b10740a132a003030362295280d455400b420000c0d403c0c07501c100100b0f4141741240540a004a5007540c1c412405460460b00d0107480c44181c3e2041a40200301c400c001400d281d09078000d1081c5006181c00800101151800b111003500a2034903010f20401445200b500600451103150b120054131003c03d044142d40445550b01000740c10800c01c1115503464005a000e18041c0704110301003803151b0f5600101c0c4500b858200039103141d9014000b203004002c07940810220036000203000702013980c4c600d840801c0d94042c1140c05a8000300780b0850502d071641600b0310584001e280c002e0145224100c0e07034950814400400c200480e2a500302d2500032400034130400c00402d448a0b0816004031820241005100104c40013a045a07407083c44241214100001d102005404 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 29552658 1250 29551408 29551427
    0x80c0a0209010f080c0103021b190506010909120e04060504020d020d050a060b030f0703060302271806060d0c080a0f050f0303010b0904020705010914031b030301150e0a170a0201 78
    0x30381c1c00320100c501388504191107900a41925050540000d854000704840c000c210400401c900b0985200304040c40c0c55909501c0310810594640c401c40f400421f194102e485a0840c243c0c0c0507010f0010019880002d50300d29104100b403940c003d41d10304000925407140d0000344042186c085d801640d44802c000302000b2654080d0880804602d86002805003e0103081203d0304070490b1130410701566141c82088000d4201a00020740108402c0c5441880000301d86c024044805103002c908546e0740d42c00410307040b0b00e045441e8001940e001501181190601d03108020000c4d01034040d4405c2c2c1c98031050251314200d600442101c01c10740c1400100300f800814404410541b1902c00554a15490209001d01d18050040002c1c0f0880d4005130000821034250b00800c41254032030340c0b06440d01c06078016143c880e041072042c6181440201d00d01001d409010003124183c4465040b044030713568070500c044940d605806c4c00c01e40c00c05940d00000c620400502110340708805901d0013415441544d10004110055 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 29553908 1250 29552658 29552669
    0x3070f0c06031d030409050c0408010f0b1809070323030f0304021c03050304060510080a1101020105060d031205040302190501060503190f060f020f0703090e01060e01020a08030c07080c0a020901 85
    0x36003c0d014a101d84012080ba000c5400c00000800d0503213503c00340c0320350b0b4407481d4050f2940b90300c2c007001089040102d0b001400380d070208070f5a4020b044001e9103074280100d400c4907543c502e80c100400610006019052001c0d0b1564030b0400341014072999002e40c0d140da40403800f003451001c00841007000b103103400358248000c208004c5e40c0c2083c841701550041c1160002502c0204100e48480000d0380880317040810340001e020b5481260361402c9a030030800000703415140c8090055090a0003d8100d05001c3c480e4002c265159031401c201d403030315000c4003004010260048045018800c2c812754134a201c0c03001c1c240c40d28001c400004a19141a0400d850140328010008035000d82145000201c1c1c65600348580c07040c0c1084001c181003502d036501100a120b6074428030440c100126460041c9a030020340301094414040c8101201c0c3d8132614150381a101e03600850740141d110540300300000e031201002d990006d8510490f90f0400c0c050b5034803c41c05404c0a480c88030707141d000701c07240ca043d840d02e00b008900502 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 29555158 1250 29553908 29553941
    0x120c06051207030f02070c0902030a14010503070302130e060108030a020d030b0906040c0201060b0a110f030403050c0d0f0803010303050d050a05060112020f1303050109021810050f0303070f0c0603 86
    0x10000c0701c00400100e0014424800d042c1e990643c07000c0c140c2680c040b5016164014015210580c6404030507000303400650b41c03192401e1403c4080c90a00481c11840c9040c0d8100400a1910f680ba56080244184000440c60040c50300d803e00c0701c4072603204110f000e01908141700555241c1110a000919102c00c17490b10301c082504000c842422500c0c0c4200700d43e0040f1f019078001c14400341040d01a4090702450b80841e1141030001810428140c1c8160240f101020007010746688240340103117242e0740d0081d800064210b400110b50360000d85044074a4401941c42896025074610064507a03030810f4100360304c2580499000140c8241e200101c0c403915074030829226040000e8202000001d094461008100300065070002e210b0610104000076100000f5018000c81f030f5854030b81c039189010b4003192104901076862a1500340348100d200310010302c0785180d22610501c041c079103c104404102c001c0c2c0810340500003000284080382c0d020030b000040f00d0061f0600881c2500c0c0000040840381041102c48005 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 29556408 1250 29555158 29555167
    0x20715020a0905102c01090807050906061309020d020904050112170c030c0105010b0c0d17040f11040c020a11030304050a0e0c0f0a090303020106120809090705090406120c0605 77
    0xa42e0042c1a040035180c003a0380540400c0c0907604181c0b840846286164148038103280c0001072034807050751403400c061080e42c03899242e60f40c2d00406071303588145004141e440100d40002404500341030b07028066540c494460303507111030741e14810b01d42203903c0541203500054000544404034280790150500502c0c03006248804620251180c01701e01880ca0902c0c03a0070703c1c0000e200990404100199001c1c840d04000810103941d6a54905590764002c49414032140648805d41800600a48080310344c00d81143c07002c846580d480c0d030b0b008480001140c0c1114420301800f80122203844500c2081c04000454006194070200380c1814140c0030740c00c8540e14440d500411091000b80c4400c201d060844407a6003402c41e107a2103684021020b4010580360b00c48c4200045806486039501014140c1100d0103074008100c15a203d54040b50207500c000000350540c0010091002c00e1b08000340c3e0580d10610a14003141040c0803040002e0540b0510341c40120646500d03c035080074401d40b204428001c201c1410f095103032 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 29557658 1250 29556408 29556427
    0x80408060a110a050a03050603070504110d061403030406050c0115030305032401141b1501060e0303030106090b0903010605130b030601080a030f1b0c060302031906030818040f0501060302071502 85
    0x139125440300c0c482055121404a44071391020403620010f00340c01002808140c0d080b01c1c2c030400d95005820f692800764100079000860b04565201d8113403c1801030301941c6040e06281e01542d07140d121401543d40c941d038503101d50f03100040700440140036601c240c2d2060f580c0d0030840704200c914044102d41c0c0d80800401450700c8826a000104402e020000169107070f02c1d24545010003c41ca01c0c4101c06211a005017130403400598080101e01d410380c0e903552600c8509400314401d05a680c002400f90f0303808961421814040303c2440d034098030745010002d00102e2265150800f05080024080c0d101c802e168440424404c98030b000c1c04014003501d249001070016884548000780000d5410b0711a0341402000d00190f5000d041c201d625042039070700310b1b000c0c84216654500040080d8000c071030009100051441c40c42111006000c2d190441e900050740c10304054407804222285101c280030f560b07100b80c0c0c41520010203009806001c0c000d00190305d00585035009420281908000c451036050701c00e204022005a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 29558908 1250 29557658 29557667
    0x4050f040e0c011b0b0c0a0210050f0604020d020d092003061b0c0a120504031703060d0b070309051f1404150b010507080c1b010215010b16080408060a110a 68
    0x20345004d1a043d031507110003110b80f8086884045000e000b107000302e4200b00580200600500c8040041ea08a0350000c2500714450104e640641d850502c0d4103800020540505d0a0f4001d01301400005200502c1c162181e420074040344d4146400701c4109100c204000d06501c4014a0304401c0328050f4090055890010107500800794060001c0306203000c00b00c1e4241146000f0000c900490740d06c03481d560f402e011041c201800c1c541147c8030072642c1e45201c038218203240c02c116050328007805001d00705100302c215542c1c902d021244003e001400301030340d4003000c2c008540304203c841d00001044c0241c8045c11004080b0005403203028043c0c1c0034403000782041c000010030080c10700c800014a8a000912466618012103041c03050605c0a020718030082081004ca00022031200e00c40d524058407048580c01c5d00b801642c4400071400e40c00790102d40040100010138401006000d03464401c094900340d040655100f03071864000740c00011540c0e006108220300c139072092194080f4800801041410032280c55001070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 29560158 1250 29558908 29558923
    0xc09030a021212310b0901030b01021903050c07050a0f09020f091315050103050c0a0309050309030303010308040e011e290301060c020405060d020a03120c0b0a0204050f040e 76
    0x1d00800d1a0300c02e00401c0c81c02405005500140c41103416611180f004410500d001e01e03c014000c0d45019243d140b6002007081200320440ea038181845007000600c000540040c500c0002d802d05502881c0000d4280a22191404003140d2080d00d070b45803101e0241c3d18491034200c06800c8907010b4080300c44140b20554442c0401d1040703c16009000d6918010b5a642440c94021b8404690b0080d5201d00c41e00c8800d02140c20a00e82c400c000c010a205590755500118291441039070841800e030b00800488200307034801e0300950070b210f006504580c9031840000c04246158000d910603500d01002241c1408840e030891880ba0040c1071030141c0b00b0060702484000e0329546802d00ca1607040c400640c0414881d40082101c425080d40c281900c00d4403036a503403402904180740315104900c180e03c1c000c0040d1692904044c8a500a5000380c40d01d03450a086640c1c070551f1403080d903002c4c01841321060718400020309038072043e07205604c070450140c0c48a260000788a203c0c0d006048152041d828214042c61000b0001001c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 29561408 1250 29560158 29560163
    0xa050705030c031e070e010305090a02090610020718060e010803132310120b180408030601050d0204151b151505040906050411030a0809040504080d0504030c020301050c09030a 77
    0x142d50741d460389510059840b4401c3d9111306101c0f450003c1007800c41c1c00c490004140c0e1820388090103180c0d91800402e4498400c040b00a40c040c103010007007034080c144040080a031041d1341c011a40c800391680c011040c1071075058440000c10b5101c903020f106180041d030703126005001410017181403903540301c07100d00d06408038000c081075944e040100c54225540d800750380a51190152600d9041c218001008140c00b400c580a800400d00708503001640d410060202e101c0c03100d1080b140c0813107842c0c65840d40010751007e40b0840c10400c05200181d41d1409030b2006100802075003c4d40c111840f40558042e203c130241917403541c0b42e950b2022008d004140204140a018081c80310002809540078100300754803084c5800403030b049403034204030f0700410281350311181c003c50141680d2580482d03440c1c03c1558642108000614000303007440200c545082c16000940c000303101c0c400c240e0078004148454022a1070842d41a800112000381c81e0707065050070710409820000200400b490148008042545c480d92003500 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 29562658 1250 29561408 29561431
    0x30d0203070b06010314070908010c020703081c020405090903090f010305090a2a08010b040b04020403050703062c030d0e030a09060e03010204090e0304080705040209090402120a0b0a0906050a05070503 88
    0xe5000da200c0d5000c07002d0040e41c6c005403086401c1014000b41440349a00487d440740d0310700011000a0f0f400011801e0460794059101440c0c40c85048003e1030700240c40112035001c640034000410b1680d681c0244511500510001b036803142c40f800100b1081d1a054000c0f60305241c42d1509028030848042201200e198100a0400c03022082100c080043c030700044030342101c40f05009012649441c10b40000034028ac04403000c1c81031004d9101008220b00c202d00c001001544045420000542c241e000040d01c45410005c12417003460f4440e108920030012003102600d5080000c0c4010801030f80d218801c550074044004504100d01d104001d401180c15000b00d4091168005000070a982e0940445000c0e1144800911030a051a4191a6070780c0050081c0300841c01800e002050324145482a901302c51b80084c42c0011940f61a02400089074009083d50980d0041c0d10a100129804002c9036000300d60750540001c6216042c10401c007280c60240100c1c015506000602039440d92000c01d0784e801092a985 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 29563908 1250 29562658 29562661
    0x70521180f0301050a091b0e071206050d03050c240105040e0a0804030c08060a090804050d0201030912050322020f0105130e01060909050117071e0e0a050411030d0203070b 75
    0x210581e526460440d415801c060402134004940e030040c400703403441394000c050300c50045d00240e28894a580561010352000500258565104d4001032007002c0701d034000052403a840d4408a07440e131000c403030305a0101784000303030a92000d4400c2100d50001c1280501482113460701c9031000c14181410f00c51903214039240d206106590f10f0511071960034503070015116669550b42d02c2c103081a050203109201c40382c000e400c00251886038500690040e1031f404070f4400d10301800c243c00c00c502c3c591010f034140e0400d82e0310b10003400018801c0800c04d00c10099610341c0750b00d916100321281010409818254020101410031000507140c1400d101e13103071030090030712a480300703003103845a0307a2800f29501040d5001c244400000d584d5800500400690b0304211081c05035a1f22031104109000e0351405c00c0b00d26900c00903042082003d02e194000c0180c0604000c000226038803e145a0727203440554110861565034810b01c420480061103035403164400b5409404040c1100101944900031260040e018115500 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 29565158 1250 29563908 29563957
    0x210f15120c040204030606090b121504080c160503010506150304060504020f130c031a0f1306090c090f0806070215041b0603020d0f150504090503041208070521 70
    0x7001240c84060011900c1c4c5940b414110054141d074410700400340d00d800c940300740c54180302c5083c10300c00745004000c0914a0704441c03e203c01000080c420349060009000c0e081d0401c000b480b40c0d516a84a5071000f0390b580b810700080500316000074080501c50780d22982480309400c41e0800f602d9205811220004207079507280042074910320080e0400703621030344c04c1d08a8036100c2d80c550320043c80b5000ca581c0401003100304541c14038002c0c44490071654815168110712400b403610801c07000d0b02614032400490a0744c1d60b41040804e1324405000007000c40c107550414000d42034480601d1700203184401c024800c0e03040a800203501d0782850b181c1e8036000c02c1040c0018007070203004080c4185040c3c1210845100d2952a40000c00940125540e5a540fa003088103540308800c40d801803044001542081d0007030a031414040200130290b500d01241ea6010500000171201802c90704052503034010141d107582c40409207002030a041c400140c040348620000d010881e00d0110b00203503000503500b03500c81800c809111 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 29566408 1250 29565158 29565163
    0x702072105120c06010b0f12070c050616020c0406030c05010f0201061505030106030e062e1d01050a061403060d02030124180203010311010305060a030503210f1512 72
    0x400141003440707840c02542c04203140d940284410226842034803084e07602c84d0f45034202ca20540c1039840041c101070100d164440ea4240b4030b00d8000c6070a040c54420002150b5a0358200703042242e102c00f1003443c01840610300d41e010711204c03102c60b2044a041000c5411961095136042032800f40c181040401a4a510807500075032091000c1c108011601d4900341d13403c3e40040855100340180c00000b410800c045c1802600014081e0180410364036a10034001007889113100080c0208a001780600070354070008906c910b0000c0d64044241c181075030f441704c1d8103000501070302c004035030b00040801031014220290342c2000e0b801d50390000c1c400c44480c113807003801d4000030380500301103d070310315101d40d40f2005003001c8200030140bc02100c170003a50115110303181e038007900100c3c0005d200c0940903010044482800f0b41c4264440b640c0044014084c032640c80d107980340c00c4e180d0741001d0781c0103090080c29010004521400d25006900c0f940010307000e04076203040410b5260380702c0400c60751400382030003130b1045c441d540b000e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 29567658 1250 29566408 29566469
    0x2010b0402090a060e0114120106110109030c030522030f030215040c0612110a09060f020304030221070806010305060402010e1203090d080c0d02070306050a060605030c0a0c0f080903010e0303070207 87
    0xf044140c236154210f612400c02e1204080c41114003003510060281002441806110358254050b112020030900b5900d040e60154098500e444406e0444000041c40b42980010f00c0007840c0109409489607005240291402140c02801c19441e2075030002c000010b80c0c0441108140c5456292081d901f41440c041000540fa83c00f0401c101004003080c00804954408580c408071000d6556080c0228580101a6124442c5010107900003500510a05180c00e003c0d80310010311403c04119980030340e4030000c860514030f0a80007103c240c0c2045003444150340c1d103e0003400001d1400c6940c10314034600002216070344e02c640015180682c030f0050f0400140076120003590b00340c4524100355034110a8582000352505018002262910f26080105a00b4041c91141000751a815180e00d451502c801d41e030180c00d0381105034a04104103907c0da02c01d00284420f40e940f134401d4402d6071026203d000d10010107013500c0148919514580c01402006801a800036060f0202c41041c80d000c40d0416a40b50290020000d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 29568908 1250 29567658 29567687
    0x20301091208040c0b0310060804020303120403170105042702031e070f090212010302060f070203070b030402040e0d050d09060e060f0f0106050406140307030906090b060102010b0402090a060e01 85
    0x106005a050720300d400c41c80941c450f91040000500c01515a8a440e101d030109a074201803002e1025801d00c0418014614160802e000408072420205d12101030781201e0001c4a04800091702c0450140c100a140700b41180940011503050251401c2207500700400031504a02140300d00d020140c0805540b414402c08030307492840c0002001c03c502c01000103548006c60711890032060740e8004001004011031094644824002286168a9103181c08004c1141c02226141013000b000f0402440149d07000c00603074005003a03405403661130380f030240100021540f00001403100c503004003142e007682c07650201c11105040e03d451030020308407415041110040c440342500055900c034150500c010103110030141880741c81c00240040071680c8903130084420b4020b510524020810b10b001c9202c041c400e00d00034552080081c40d0009030000107803960000d8031b0b5500c8081d66000c0030407042c46020b5a0a02611000c40820307a002e500c0c0030303510300115034400e4492041008000c0c1c02d04000859a22901380f00d0041c1c038 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 29570158 1250 29568908 29568923
    0x20907030f0c0906021005010e010506090118090504030306080c0306191103010b0304051e070b030a0e0a030909110f09060901020114040503040e010e010501021e01110a03020d0c05040e070c02030109 87
    0x140c2041c042c140f228180909030140c49001c1403101d8440060065906888044038008600c1e480e00c428400d00360072000708ca50500900510f6214840340a800c0b09008009070034000c80d2074100713814083c044514a41101480381c0000407000e048e9200017542d5a0444e9040b00700034000010314200b600144042c03403001c9414100000001800301405002e5801903004078150348108251100000f0b00c00b0000754811125005100d00f001442c144e00d000e19441140300c480824180d030201807581c10300006000860104441c14014008881c0d58070400b88001c00e001c24a6180110311854100c440c09042d954901c640c200140c2201141d100f904111307000c800400820f40f1a080916066071690024001d81424101450000407100d0000c500e8a04a820680103084c46000700056074404a0741030181125035074a80d11f014081c0d150400c02040105401d030b400580b00d444000304107003559035030200681004000d01003030000d01142c1c0f10395030700900c039801e0280c075045262001c0313805001d40b41000362805 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 29571408 1250 29570158 29570171
    0x903030206180f01150302040b030d0c06110706090b04030801060206102303062d06180a0605060301060306060216062a06021801020606031203150109031502130b0a0507020907030f 79
    0x4002404c00c4061b2403007203506021411055040c955540300c2003181000142107001d1103404225903502c803039440584420300c10f2030206907840d003505a8008000031140f60010781e082100b407540c4401420f0250540d40301034901410000060f010755101402003041c014462812141072424814401c0d80750320020381502c04503d00f9a2905282c40741c121425401d40c1d0800395203d00301480346a43c00d00c0340d0001043c440306c80d0000c069100306680c00501e0014110303512035010440e640da0f400a14001c003002e54003c500306007440ca0003801c140320744c1c600340355a40103c04144070458121030045200690981880c07850049100001c441c851500710240c8007520015417070140440e50740d502d5040c00400e8080b500207490306014950b0303d440130301c84500b641c901400441c11080980d4030a04180405240107038490345c680e2100d03c0d24000004881881c25800100501c212440d86510001003581781011410030035030b400090725912a610000340714440c10000608214080e502628604503101400c0049 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 29572658 1250 29571408 29571431
    0x1080711030403231203010605031305030c0f0105070f0e0a0303051c020a03060905091f020a09030506090705120a08030f1305250b0403020a140301020f27010903030206180f01 77
    0x7010b850503a158640204608000320f45c0740a4110b9048403455a1030034074550b40d486400c450081e1005088807207010411081f05002c60420084440c106901c0000a00b8201104003a03e018160102c207018040490070101d003a42c0e031034060400300c0750982056903079080388403051202811b10900090900d80701050b49a00c095155200005880108400304200c2e00d4448440303960f0540c1c0d9440801541034000080c150f45041c0d00504500e51841c2410a0100c2e10b913680c65061140844000006901c1450204282c0c0382200842800954842c045c1491600c2070b16502101e100041030003401d07801d5440894003002148610390803031038100701544c2002c0e22008001503080710100803040c900000d104003094600208044404480d4010704502c000d503c1d205061081c0d03100b05e000d4962656003404080101e0070020010400c00e10321180540c19503917080c20020b00070403081600340c100080c5070b5050000070340010f4000d8200c080010103030b14054038460818900b116130000582c9075401d020f0b40542 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 29573908 1250 29572658 29572703
    0x80c060c040305070f150f0207090f0e010c08070c12170c0307090501030204050a052206030f03030c020c13051305030c150a020a0c02091012080a031a01080711030403 73
    0x1541d1040f8242e50100383d039a28010300850305070081e0f4016000400f608140c42d40514980880201340d0700603034210b150780d21144000c480e80242e843c9800364840000541582080c4280141121103081202c22404d0880e0010582c10507060300410820522103010b11450180159400f0075103042810007071480c0c0104419110b4200380ca0350400b05100150208042d0f00a0090b18203a45002e8030604c0d01e5850142040114101500d0f80400d00424007660b0000507140c0c014032010358001c0a04400d8500c5a00e0000d003151203a01000302150032800c0c0e031703044607540d0768135a990b404128100459661108803088019030b981600060461000243c855a10003000c6101450000c0e001600050740d61089241010792080140d0f0200240320070401c44010f290041c2e4154000b0303e050f96540340c03251500310400b41c0d102c0e01c3d44140d03000180440c102c1030321640740c010000400a003100c0032075100e10080010380000009801801480500551186001010410798004540080c0e082d80303044082202c1a1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 29575158 1250 29573908 29573917
    0x109030507110a0303020c040c03020c030c0705011209020f040c020f010e010608010c0c1203181506090b04021204020f0607020d0b0103050613050d0e06041206050106080901060609050607080c060c 86
    0x1220b0146000701c2c080c00d403030400b00000403070b90150060302400340904100802170070128085012300d03600348840303141d030038080014101e50400b01c0014102c484c00c00c0005480c03000010b5202c1310f1701e4144000000103885071004840c0b0094140c4002c242c20390481000c0c2e0611110101c0d081c015031a0042000080c5d10540000040303500060080100d0b804841c030459100032003000141c8078800c480741c1806154072a5100002c502d80a10885002109654681010f50026040d120740281c884c0c1003401403101e41e114100e00b20030101d40c00c51400e800e142c130101ca07401d0000c0000c1c0c400c4043c00744400ca0b5880d440102c611403a402812540000f00b00e250038951107100b80001d0341c980c400e00000030303601070508044a25058002d4001d000007404000c9c2101c460380740c0754400d50815003c2c40b0000d21960030152801c8240d10444012503598100280100900c0307004007161016030403c801000201d4010301c8a509954003620100c0da2003480c2d084c6101c09200d5013000c510b40d80f00b0002000303040d046840142 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 29576408 1250 29575158 29575163
    0x606030209090f0604150902180907090504030c0201030506220e0f0c130b0a090e10050a020a05070b0408040b04030f05100c09050909010f060b070201020705060412030c050f0109030507 81
    0x30603a0780390112210f98501105900b00c0355035020001042c04643c06105101d0074407482e00002c10003008650200300b0b107030340a81c04040529035510a20469107014044080075002c1004104500d151a40307004201d46d0030010060305066a032004501780340c42d80701c00f46200b901c03100604c40ca061740303201880d4000e019103100c0018a002e0000750303242a4030049020810a80d0082c6031030f12403d42c10f80320740300608041c00900e07231020400c000040c49803002c2c000c10060400304000b5003402c201031a030001c02d0782c0f0000e1100c2500b82c030400c50010700e00c0c1c0200903518903e8000e00900803d42e220f180c124528802c580181106540220300001046810406110043e03c200c00b84c42240c0140d00900059511591480000c500148402c1c40142014210b0980c0a0241800400c5c102d6807800c4c000100d881d07542024103804000101e0f10103550701008000003c0c2420303070b40315103850310307040c1400100030100d0304c0102008961903030f1100744542005801461f5030308000030450b183d16460054060351106204 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 29577658 1250 29576408 29576419
    0x705071103150c0a020a021c020301051305100213030503310509040b060118230108040507090b0105040905010902030103060e0a02090a0213120c0501020601080303070210020f0c01020706060302 85
    0x540e5110304012840c40b442c07031201c208402c1240c5401100c0300d00b64000c3e5a401c021403041d280c203c40566940035a080c1c025050300c8000c14081603500603d42518802810401407070941150320002503000188001c02101c18400140ca4a1885c0c501c09806129540080c10754800801d107009440b0007203403529055403206000e25801e52001c034501d10b00100754030950703a011401070005004101c2c0780c2c0c41301d0b0740180c05260080040d048142d48900c10f1210360840d501e000b039031800d0480c3c0140741c0c203061130242c20242804075181c642a40c640d5a1030b409400b4856071542c4030444214503900950541d0301600603004140169a103602c0e40c0c2c0001d4100b48401e070380b83c9003841c60381c1866410104210242a8010340052000d582d200503000c040e500802a03000b40844020300010107041104101c44058400e4910492003407030720000a00d03040044e0080c407440e82042046c000e4032500060b4481c50503699110260700c803245c40840b03000c940149046d003e03155000041d00010449503038029400c0c0d91003201c9 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 29578908 1250 29577658 29577683
    0x1090b1906030507141306020705030a150b010203070b0108030306011211192604050609010204081b0a0e0a05180c0303040302010302030604060f0e04060b030a0b010302040f0e0105070507 82
    0x20000840480c0014804a100c03508003805028840c0d009194019020b0910410440b040150900c10f6030003000e2885440080c18014014540d05102486c01068200e0040c44066240d8171480c65050945070f440c103c0aa0380c03081c000259000303000b6192000d070450401c20040d0380d41c406c00c60321b0b9401218030600044008503010001c0c2d20750311a1290018050140e1814400312300428000200c8900e26102070020362190b0340650360424202e0340400b00c0d2110f1961050400d460114944000a802c0e50f01c540d0062206010340c05001030205400603410741002ca546d0b25400102d1049480c6070030000c0c50040032000c0146240c0c00342c00c882d0141405c01c071420395115102e504240c0764240d20325442d41c940c1040000704050740c881d1b00a036801100080c000101e45a944180b110140910381c00103000604520400003400007900c0340181c0400140e014204986c45640d41c0300340100d050000070310956440c40318074455062035001c6106154040000c1110b0b08203a2000b0304540c108140c1141e0b10303a400b0b031 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 29580158 1250 29578908 29578931
    0x305010509030a031407051801030f020f0a0905060408031903020d050a0504110405010308160204020d1401050910080703021e03010e030405040e0f030307111203041109010815060603100e010e0109 86
    0x189581c4109015655903041603c1d5000400d500248d241031181050744401030100401c103144010100c03203140c1140c1c03903500c1007003040241030400c00f588410b100e0340741030004028020000c800c498402818400c8031010000e00c0200340c0003405541d811403011480e1104029041803541d010a024070700903142c54180c4481041004144d17030090000601040003800024590000c400060900c0c51005002600b0001c550107404200c4203403542c0b40c144030011000410841c2081c0341c0352600482110030000d0035030b0404246965a510600c4000d002d402c040c0304048400c00300c100c4442c15120002d00921a00e144040b84d00c3d525081030141b5031003a0b160800d1005d005600140c00a0032082c1c0d40d000c0d608542e1400026502c04080b130f50b60003001d020b0001894040103200b07008510492242002142101402c0705108840030160040d00c450351240744151180280401001d41c0080c003110328590700e694009000900114690045414541110003c40c9541c6141805816903904103820400d141010 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 29581408 1250 29580158 29580191
    0x501020a0e1002070e101707051c0f0206090112020a030b040b0d030206010b07020d051c140304020102031b100c0201020d240909030315140a08030a05041e0305010509030a03 76
    0x107030642e0140e4060b16040006a55802c41c0e00d5008820103189600c0320750351020000408220342026050380c010030020700c40e5241ca81c0420880429039a1641030745846542d0b900080d4074901c001a00c01c000110302d810140e03201c0d0b20040d1044060030425920388903800c1340a00a010007a034120701c61410a10320500b10b0a00507030301490740d6096801072030f00b82d181007a1421907030300034801a600101280e00e1200422010480d1910128441100f641e501010359401408000100e240305000b540c100180405031380c0c000b06071665444c3c000054030718281c04440251034041c0a2000325070036820300c5440e034160394065020b88245000c02e10203007d452410400428210b064140300130710007038450003d0107884190740c01282e42c544a410002000c02d160014821865890b13885901d40c1d1480c14109010382c1405003811009104a034000e50402c15095401380190103140100485c0d0251001c00e60071425241c031800e001560098002c1089080c001c4107141c480d80f10649890219003000c0d003000c42603104 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 29582658 1250 29581408 29581429
    0x402130905100608161211040f03030f020102070c060e010905100c0209090a020a0e07020f01140a0e01060b16060605060d050405061003050a0f140f0304060f02010b101107120501020a0e 81
    0x55426002d00700e010a141951b101300800290155150703540500c007159503101000300040d014010501d41034901d1483c004004c0013400300450110390041c03003a440080d80c0e54150100703886141c208001034444c804012220751260ba40141c1e844400c03a1103040c50640c0010781e1340c0456009803003d0b02030307560b00e841595441c014400300075000040c81e40c082000004030307101990060010310540c1c0c50340221103121429540009281381c003080380c0c0814080074495078410542078001842c000d0044a01e0154410000c2c011803c4603080304604912160800059920400180400070041612000701c02c0000e8002d10044078111200d10582e00420484503138001c0301e04c226503101c8000e0080324401d6986036000059240304807840c0e007904040d148020402e100d0790a2001340c02c00151344617850000010040e00d080c004940035a45802d49001107900c03403240720740441085040c0488100d0f100d0b140b040c60072400e03030b001c0d01821800301600c00c10400306400811240a41707590320314040400c403003081200d458 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 29583908 1250 29582658 29582671
    0x1060e0a030507060311070f0302060708070201090b0f07050d0e030306120f071e0312030c0306050f03060a0e0c030d0c02090114060706110903100906050c0f07110402130905100608 79
    0x100e404104013040c82034026188a04200b00103509000c11541c6683c8410701c03561003240503800c10000c2201d00c5512109255010640740300a01c01450305458040e0400030180c00480c16542d400c00145046d0f018030102c070400c0142000030482c13a005000416125081951140e215501d118a40f810010000940450050f20a4041c3c43d02a18085107802034400e001c0000501e80e9501f0b60010200d001000450100002a100803d1004030300c140102200c0240d04024400c03080754036031000302d0b200094001e034015509440090700c0012859000d2808242c2500036a1521854900d925095441200286514404c0d41d42e0031140e600c03a1103248d02011070104990f0000c1e0280303d0407010910310340080310011400c04a40b481c011001011a060001c1d405000401a40701c0c00711a00b002910710946a0200450581d1410300c810b200651081e4130903e000a02520b5500c1c52425440d59664103c46048061100c034229442d503466812000d00012242c51030320b08030410000404501613411a8401c10707 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 29585158 1250 29583908 29583913
    0x803040915090c02010510090606020d03020f070f03090e0703050c0f07020a0905100e0c03090c01050c010b0d03030e0f0c060901050a0c061a030601093809010b0301060e0a0305 77
    0x2414140e10a005141a504880341e0500e10803000441c080540b0443d070880c507060b03001140701c2c681700302003843e03000240d0300490140c0c0c2740203000c104a0743d0214001ca4030781e8881c07030090781da070810f100c120f003440c013400307602405044c2d0881030807040540001c039100c21201001e120010a6540302c1e070035000c0314003c4407295410340c0100700b650b00c0c05403c0001042050701c010401c001541e10341e082c5a0032100100c4d1104400035111000744032000038650010b50101e00040280c1c0345280c5061841d8481406da100141030140200740352038009070a410800071044003a1840034040c9684c18002d0107420851010000360207a19000030220b80045030416030f41d003015046601e01058040110b440354099031102d0104a03d640390003000a42034010120204c110403c42c040c4480c3d400101800d054060384409280b502e080304804016059002019070380509075070385500360f04144114009854502e001c0c0d0b0b40590504004101c0c200e4210155041c0e4081e0707034940d0104c0c0150800d0000c01c0c2c074140000307801c59 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 29586408 1250 29585158 29585167
    0x5010803041e0f0b030a090b0a060f0503120d110403081606180201020a0b090309030303010f14010507030905100e0607050a050106081912030b060c06040203060705120601112404020310060803 84
    0x1c0c03a007400550700440c4082000a242501d030302c0340304608c9000d80301c904107503840301010080c07842401c0450010300411006016001d030405058041e40c07280c0b4042c01041c5807151000c500070811001030310000d541060500e03035100b01c40546962a0a03640e0b030100c42d514980440348849100500054060690680090014081580325545459030007400d8000c01e10081211000c0d58505002941c000c0400e40360410500d81031008079074004061001d2030f0304100f01882240082607001603c04202e503401d4440c0119101e400c1000c072141c400d19996a03420440c00500d12040103400201200e8441c0100001c01c28952140c04981e00d51449605030340f030004022118101141030148018461000d0307040014041161002060664214090b50103641e0000401c100075800e040c0f00311071388a540c40ca0903614010b0503100025005002404041c1001030110318810240c1081000040d0595528942049480d000c10100d000503002c4034100d00a0055511690099001e40101015914008040c42c04c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 29587658 1250 29586408 29586419
    0x11090105120a0f0e030702030d020c062508030c0d0c030501180e010905060906100e13080a17090102040603061d040b070203120705031807031e02010302070605010803041e0f 76
    0x144402601c040c0c0c040340d4448000018058511801e0244e051810107151110707000d004050802c600c03c944a803d641040c18444210b903111022107003e0054840d000d40002509442403840317080001008003003070000000c0c48006024100030b0a0b44010380c0d04140a820380c01134040303065542c01e10800c00160141c90346401c9030394043c0c100300920091000001a0500a501c406151003070945940d00660071200501a01d00e601d90a01030192000c0b00c0c6046c0d003810804a0061103000c07041d0082c00040c00451410a003c0c411582082280b542c038001c2c610900303100f5540341c000c0d40030b0300c1800046440c06d1400182c1038403121040c1000103800420700103c1da101c0e2164110828000e0860045000030090741881240d912031060040038550390303980d1039150150840b884144078240c004129031000030104001800c5504004070002e59140c0d9104d41d000503c01600a80600340d80207024508110011a00c210004080e004591111101540c0300220542a42075901c20780111042010f046105002 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 29588908 1250 29587658 29587687
    0x10603030e011b0210031b030b010203120405160602010204060315030804140604081002040311010806090411011202120615040f03080901050c0f0706080a020c0c1309020a030b0a11090105 82
    0x703645820740c1c040000b08181e84d0010b007501003001c00c1e060109030b4401001408801124031b409008905007020442d02c2521000030355a40600f610080100e20314034009402c01809002c1c900120300c05040078500b86445070800380c040c0d04240a1003000915207150340002565101d80d20046a80000189180a080c09460011402c0b151805500007008000024815408119404c9911042207006848174110314000103100b02d02c0c8401410491044180225980c07140c580c04c1c1c00c07e0f0b1013040001f03411101f10040c0c80e10280010030170343c600d1010039403400e629000c01140344100011121502c0140d8140e1125695002d540030310f61400300059801d00c0080c007050001d0962075030504250f4102088821030600d80b00c000c1d03800541c01d070480c9a041002607000b080075900030040200c10750801d14070600c0380c0c5d81c0d1102e58041610a41c00301e4043c1c803d031541e0703500036000c0d0b60b0050102103400d2f446e400c1030a05c0c080299030101d696403406541c5448141160300b42c500142050b5103c916140340e1082d03061 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 29590158 1250 29588908 29588927
    0x315180809030a020613030b070905063901050406110a02030f0c0307020a030f0501060501020309100309110303030f0106080112031b1a010807140609090f070908010204061d0102010603030e01 84
    0x6805106a003c40c00c0580d640402400c0c55040000c510f1803041e09600d030480000340c01030003038000d000702c1c81d0041c0417990359030702684e54a140007450301c038000100d01c4c1c86920b4141c095054047e07401142c500c0c0110002e044d04441d204502070101400b040e04d004c0100300f41c1748140348031103006820503c610710800001c0d2004007040f040d40c004032418120b080c0c0000c0c40c004130039030049440103802001542004170a011b250003d1000b40003a50901c01c5150104003070b02c80c18804882095955500c5e80100160222420310700c1c800542200d480e0302d000004c1c4a0f0252007801000301244003140002071401003000c2089000d40e065441c581c2403094404001c00000c890030003110044814102e2400c03403d189003007a0b0080170300e04024540a45002c071a03182d006401d50301b45000312010809502280c90301c518054001450400b07aa42c41d070f4400e1011039a07515150000300d2507500010b00014a00d51241100380c00c40d00f05400f18803500d905000590072243c0522005000c44c49454403000c2c3d541c000c0d41e051 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 29591408 1250 29590158 29590177
    0xf0503031c060503030301060512070306050f131e09030912080d0c0e1005031f03020d02120f0709051006030507080604020a0306030204020c010203010603050f04030c0b06042403151808 81
    0x454103c0d1582c002a00319042600001c1c00550007140d40b1641003500c5a1664000f44c00b41802c211481c28480031800703001203000d61038001c3d01d03401d843c3c02c1ca103281da81c80f01130340340c0300070b00c41100c0358484000840140c107200e40c003580000d908000100c0d10540b14140403031455880451070389000c009500400107426130302c5200d820310070b50086d040f94940301d48504480d4071388199a29541d82c03401e42d80100c054502d00303450f01c00b80ca661080c1840183c40b2a032060417865011103921280c9005030780a81c0c0f900520710030401c00360240d5200010160740b00d0b00040c0c09800101281c12002c1d03100c0c0c600701e0803034108451704c100003600e290100360903040a40c02815034049516003c2200703070320394001c5402c1e030348240030001c000da40c0003004001c903561500ca096001011001e0884040c2003607140109111002d820141003a0f8605010520301d941e25400036100c0c0311604140d60480e19905a084485035042c40113403104403588508200c505107901c548520414a184e890710703a0f841a45030710300c00d600905000c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 29592658 1250 29591408 29591411
    0x60109030f03020604170c0712050304050a03050c0906060306030c090c0d1d0f01090203030a0305072a050c011806080903040906080a15020f03040204051b040801020901090f0503031c 80
    0x80301248220508000341da001e40c0043c0042d04082c6840484515091109005410706201507491890040741503002c49880c28002005006541003890a522030b44d4401c59204030301900c00030402c40003150747e041d196011200480c041d616003060080303910003101ca103a0325810001800c4c009152607030348a03820000710081c0354140182100410300b25180034010050403d544040140700540404c10141c05003110070090214941c3e6078040f80e900e0003644d416800345610340b800100560710603254400c42e50300d140e45080c0555100203ca400c89150349809036540d0007984804c0c02254000d48030f8900c98460103200560303c80c540a0708450030b110207401f009060104003c000f6200d4039501441c0c019000752030240a03c1c108525001c500760301581d07243e1100e00d00520668440300d404106507a406601581c1c04905561500700c8011404201710703107054414000301b008105500d055010b4000c64200781c80340650541c581e410742030b0700d01c0c583c440d0a606500070002d01da01035111404078500030030310540 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 29593908 1250 29592658 29592677
    0x402011209030c120203040e0603070305030a0f0309050316021e03070603090f0807050f060f040302060c160c0b130b0408031b0f0d0e0406060e030a0201030b011205010306050105090912030f0601 85
    0x11480300701c01025684e41d0041c0d01c0407905110700c41300c81040340d802c090708800074090103156a07295500ca010700d4000303905100322070400d404814080e420882c00103030b100080d2565042d201c0c1004010308062182039010740340880256212850301a040f0b0034480c1d00500829400d0b00d4104100c0c05014661000c840508100721024006030840b005003007510310070409462818141404a0310b008801065101890740e80300511010a40200c0c030650007080c41502242d6030100e01030b0840100340003420051440d030864034000381c1d18154801500301d9000c1c01074a201801e9540c624030246003e03d01480780d140d0410044005c02c10b2000c42507079071046410003a11100a05d070b60015050114007000c460104121b003006410740d141910855014241c54102041078411060100340d4441032810028141561a00090090f078001d000e00c1226401d6882c0602440da1a03140c00b10242100b071003503c2c0600760320404110705910108450740900703072007d946400d65850200328580c40720007902c000c0c103020f030840 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 29595158 1250 29593908 29593913
    0x40f0b090c060c15070507030e0118050603040302010506040b0109030515070e060c0604020112090302060609100b0412021005030c070305030c0f0301030b1e060102030406030e03040f0f080f03030402011209030c 92
    0x14058900c0391030f8070000c0c188140500b0300c40001d4020013000ca004202080150000080e00b103140c03400016001c0c6807425001f02e182c0e0b006200c5d80659007000b42d00510100400c0201581500b102c3c3c0302c2c8e00141c030b051240c60016001503800032024040203106d9001010300402102800140300c1e4084070510b041a59a2410750208056030b000e007a4107546500040100825540c000d8116884103503c194104103007070054900a495a80191001c0d2191801c41c02107003074605400380c6140900369403444217a46640e5074503488103821180400328050004199860b104c0c40c000c00c00d403407042d090304140c03e15106907558200c9440c1d01c010103040d0030391000d0004030044103109000e140a144524410196800e001c80d00d00c0e502d5400034049640d1006440c1080b00300d903804415070b0304641060401150420070040042c0c2540916001683c444c03114030400100700e14280481e90031625484180c842d04c03008181200d4503813004035000b90108010403070090503045c550b07100d003801c1da0103071610151142517603 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 29596408 1250 29595158 29595169
    0x6010c0825050a03021b0907030209120708150109060609210501060f0e240f0402070209040f03090603020906041401020a05010f0605100c020f0d02120d02030d0c030203040f0b090c 79
    0xc1d40240c1d029400351003500100b6804100000004005d100d610f508445084000342d484400141044d080640200e070303050f0a900d51003d908030f9020a142906c280607100c0543c25a00c007a002c0403808051044400013500312500d00c581000e58450340e1740c0b030b00d0701400c0c00b24004103038510840125043c00c1d407030801408114288101030180000c0e19a10380c1e01e0b407400c0e903083d000180242240c1a1044400f801c0d03c020301d03000124012084003644d1008200d111100090001c0c0118100a90000036800400007000307403903410000346601c2600c665803040d88a1074110124080c12010303581190042005011000700751503004a4258148101c540c07c1000303544d003600b0340c7c011000c00c840a513144c070014045807801a4440140c01c41c1464000d842c0c1d030903a00002c41c40b40503035040601982c0e290000b94250b46a290005020300d01e40c50850340100d2250b84003e5882d809248045100e42c50700b965101c902e8428021203000710342140c00c0315080d08803516085c600e428041c042d1903180c800c908110740c403611070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 29597658 1250 29596408 29596477
    0x102030705030a0605100c021003140405010203040201020105070903050a0308040c0b0a020a02010e040e1002090d2004060e2802040906060302090a08010c0507080c071701020c010b0906010c08 84
    0x41e641c1c90303241d0a02c0021401600d60540115100d001e001900792102580711048800f90354049030521406440148260002e10848038a03400b003085503000c010070b11205400440c01240300b80e0081000b0b90b2003007012140d030303107444c04003e1254021001000110340b02d210710342e0f00f1a0040d51440e99a42da01e00ca03000c500e078400c90b191409600080003420941d13030041d10548044d80c0c20345052017a40c00115620392500d0007000c003001120303400f16100c0040c1d221803144407242944400d400c0c079614400ca0394116242d0728442c501e481142060404100c01c3c0004150034000c0054440c0c105005110498200020306500310102d11303650300f8080020700a03142e00462000b011075840040c2d59046540c1481840c040e070750060042030b81080e552030754107a804001c0314055a00b01401c140c079050800146400c051413940308540101480e614414440c906600070040141144000c004a014a9040c04880c5104032100b038081100d50f085040800c0308034004118000060f02c0f101d040c048491091a0030602 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 29598908 1250 29597658 29597671
    0x2210303190212010e06190b0a050304150509060a1a0108040308061801060509010305010f060c02060a0504080307080903010b010e0f040c02070b030103050d08090615060f090a0806070e090405030403140a05010203 93
    0x502c0b02c01c0c4400360500340301c03810500e594090b0700d902203408d00710442c50710300c82d81ca006010000e0010029042c0b05220500c0804820000700c28092428902403440d902d0105035802034440b4a013190303481c00c00f000413000d88503c4074180c4403013003a07035201c0d00d05031000751004100d203800c000e103400f404400f03020b40a4580e0207415161a0a5100d454150006049850580004a0310602418180001c54003c80500840c680c103c03030303041da40c41d0754004c00c84045c0166402114140300114080b420840c1c84030140841c00401c0d0000c11100c0c0100d80119601016040c0464120000403010041c60400e0703084001e00420600480318603d13610303003250141d60b100760701c2550300e904100c0b081109164410b07145601f226100d4020422414041c55040f210b444400519100707410020b6000055071341d21050741c0040d00001e24420105d81d071050101d4031400204c44c181c0c00a03403028494035071403514541c0140200d030030000030744c202411035441001658030b0383c07900400da02c280d100c41d2000a209000841c4101d5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 29600158 1250 29598908 29598929
    0x80f01020c1b060d110a020d0504120f030c0503040e06011d0a21021201020a0206090a0c05040c12050403170a02040e0105120111180a14090f060103020d0204030606030221030319021201 81
    0xc00c0071002424096070460315000c022741044108115103030100a101c00a400005590100145c0c4c40c09072209000ca4000074070602001c42d00045c03a1184e0300d03825218201c281c0b105802c1c80d880180c210302101c00c01c120325a000b0001c3d4414807040b83c0082a010441040e0000c40012858540000302040310003801c00388160340009099120341c0c1c0c1486501c1c0c1010740b94000b044c2c4010a030342c506111321524081c0e61f00403a82c8400b0b000310188285d0000701200d5101404000c24141400c00410609100320200c5080282c1c401144d064180f074800ca400b2107007560503400759030f42040304001c5e61030030446ca00d00702903403075800c0c500d1261105001440d501c603554466110340c100c83c6082c07025800d09648620b4500344034075074040d0162144200c09911101500c1c3c2c00003c3d965520040c2c0003801201c52009003940f000c5808410010254032100640e0f0088542a404202500300c00d0341101d105002c0c01d9058105102064180034900101e0318010350500c005418000354441c81812440300342d00070030025 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 29601408 1250 29600158 29600167
    0x40b040e0a1e03020a030c0c03170a02010e0601060c02041a220b0303031311030708030a1706030303100608040c0e0a05010513050411150405030a0b01080f01020c1b060d11 75
    0x600c2d075164050b1002e0350103903100c04540700d0300c1c040c1d180d40082c0b20142c2030299030740d222020060b6900401019580c000303040480400c20601e4101c640c0c1000250501541c0f0307040500912100018070340e4103c039001d59610008080990a00000c0d00c44c2d100c980c600c40340904c4030503509589554130012510000050300001035900e14103041a260002c030312078000e4204000b40210f00241180240d822604040144502c9550310003003844c20f140c5503c03020750381c04013003030103444a0341c49840c10000400d00780444800791580005c0507244d20080c2e56101d400c01401c8000c22215005070302c01d0354043d0040e400012250751b16910140b589904441040030ba81c0d4810042c8040d19246050304004000305104011600e4940d8803016951400c82d4005c1c442c000e00c40e42048039004200c219400703454045c050760003c1e4100e207800e0b181c203c03080c0510513840c026081482825101407003070700c9d0281032140c02001e092184030007601c682d920302d841c00e80e00400100b0080759518081c2c024071041c045000c0086599 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 29602658 1250 29601408 29601413
    0x90306060b1c0b01020c0103051e010e060a0911030708040512071a07023c010207060504020f03060405120a03020c01140403030b010e0603160519020a0213020307020d0c02040b040e0a 80
    0x2e26080e2008540074500d8081203000c60307640010949600007085c02d0000f1b0a4803401003100c60143c100201415030407070390703001191044120490350b0003000203035440c03500a9102d003c01416950b21015807c10f0f11000d0001a256034496030038203030414001c20580791403801c0d040008655a001c098283d80700d01d1184c0e10752480d0610060600c0c0e1000952015280410807600c0800203000c1e540031244824859680c00f040c0c88000c20b83d4058071030b062000840d610080b80c42c0845c040c1c48100c5c1d05920032009130005103c18113000c036810744120b034004007030208810604071040d01e80e04440300260801d90309000382200b10b4001d216160499100180c503410311318280ca401002e4580310311040e4100120001c1d0742c0001d886007029a030b0003a000c141119410b1400c000112158051101a0035200c0404034960096640105e018480107009485141202644851030808ea101c155207103070041e400203042203000c9209010507800e00b44014400700b10201000001419120201d00d8842d003038001c2c1e00300004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 29603908 1250 29602658 29602687
    0x90d0b011a040b0d0906060906030b040501060605090108040609050c09010603090506100f0b0c010209150d0e010911010c050f0145171e0301090c09080c01050a090306060b 75
    0x308459500c03800b440d140c2407440200441c00390744032400307480c1e440700d000800b08112900204082c24845800f005038554030304114542d1141541d0a80d10f9518007a030108549218070200c6102a106849042103500c580d503814006100305e1200303541c140281d103041c1280340c1d610b29040e0700074105a500800e2400c042d04042c1c0c184003028021070010010030030100807130040381c0c03110004c56108105070f80d1500846441c403406445040d0401c0e0b4402c010300c0c207200d40d21804c4030151911541860082040011212501c0c1c00c8270503102014000038200c0038142500d40c130420035203418502c41d42c1651030041d800c034400c50940e003006458040c6d03242c4100428508a5044103404174030001e0601780c808140494112600110b0030280141801e011540c00c00080516917044501d200250b0740d041c1001c0781c0c100100e80c0290401c2c0140d009890800800007040e520075440f034000d480420b805000311299990040d2040c3d440f40070007409100700d1200001c0410382500c203400040600c283c2c1c03036079107044c541400c08 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 29605158 1250 29603908 29603939
    0x30c09040e010e1002070302030c0f0d1409130902040e10021b0705100e0a080d050a0e0402071104020a030b06070f05150f0a02070606032405130f020d0206090d0b01 72
    0x11902da240844190b08200c2c0090b41c040080905807006079121040d0804a08603c2001e4000200c4d01c18580c020714018400204d9840d4230515581d0326140c51030340405c0780c80301c2c0b061100e01644000c134a02111075214055118020552000b8000101c050100e2120303420190002144580d00c1c4d4040307121000c54941c040450011507040c0c000c0c25a0380d08050005010003d5100700c1400c00c500010148240e49607d01050f01426001c8121203010100313805c0103010f9031010031480c000504080030622203040034000d4900036944040c1c900350b5050464140700003500001011420103031282e2a4a1182d00c45c2402401d15501034505446210500e051442c504a1100001d51540420714200b1610710054081c082c2c00caa1b0002c00035a4074201803d050000e04110f41014010760100c0c14030705c031322a01c3e48035000c410100f241014051039a4110b00e284600038856805440714540100150051a10300c0301a0904c3d84014081c42c103002900020505403000c0780000c0350b04458002c0103201080a0242a1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 29606408 1250 29605158 29605181
    0x50609031e03090f0601030b01080d0306062c0a080601150503090601090902011e02010f06080304080a030503060d08070311010b04050106140304020a08030a03020406090909020105040501050d020d02030c0904 91
    0xc615040000c001c0c1003040707426807199020030740c1c048040380c81120144030144000801c003048034000d50b12030800a0303403004280305441d103d224032041d02400f18001d00a92088954903200c45c0c40c050401c95429070000714401945aa5000e440641c4a1942c0c035216480701a1040c40b0083c0f0083d0b05001105c10341207954240307142404001e200300304c4041c60008483e41940e03000c80011a0960f800c4c0f0050342c588400c44600401d4140c3c050100900590550140e440040c4917030040c0f001d6603541e00030684038451400341d10b5041e00800800d40100b400b420065801900142292900554907141c0b100682c000960407000240a0042080941024000c0e600b00710011202004154504000540b150400c402d098006400200000d41556981501d0100411051040d80d9030307102c40440c000c0080d4058020807022540d50600810f6a0341c451084407015a4180c446514050500c001074ac1d240d0050704810001c5a000c000d0744c0d00200300ea0028500070044080420340744c40c051001c00c0140c45914422 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 29607658 1250 29606408 29606413
    0x1050405040c031403040b070305091011100b03160305010608060709080606012706020c0a0e010e060405040c080d0c020f061317072c1b07060f0207020418050609 71
    0x40c0408520782442c4001201c1c2d010104249100300640b07024214050340d80f10300784070351002ca140e50500d5005001003141803011262420304280b50a01030300c409680a003848282c3d80400701c104550103050707026541c22400102101c0085041d00c4000c00c445446070000c172a1079450f02c40030040581d04001c11030300503089042c040c02c03490412001a65404d801480541007001000100803020744090303014104e001c4020b03800c2090f544502c0081c0d6903000b182c0246024000c1c0e102c0010701010145d1529050b00c04840c0810200d44840041001815014200703642c0d00000c1c0a0004049004010f01e1000042503101c064040d0111300400200709101a505070041c00704003d44211103000406110130b0b980c0103041f900c84842c0c0000c6c1103190542030f8019141614000e0514401001144503080610391501c80340b114540c1e4084012407e031042039060000c0c441c061000780c00040003504041c400c01031a110040c1041000e400003800c0d1900c9180040c84040e243c121041071110510200340c3c0044040f00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 29608908 1250 29607658 29607661
    0x403080a030605092e0e0f040b0901020a02032d070c0e0a060b030403030f02041a120a02090a12210806040f02030c0d090f0b01150206011d070c1407060f0801050405 72
    0x400304024403104c40c41104074505d286985000380c4803200c42024004064446100b860100e5440750b44090584003542c00034507030000913413041014001c580d00106554081c6040504109000c0d07007800954108400e1440894401001d02d80c248000d0807580c1d000c0c402c0122140d2030b10402894808002e0801410141000028451072002104036034106506140006820303034200307100f000a010b40c1c0c20000a10849403c2000000100701c098209102ca0241407590364030ba5020000480c41081c0f5107580020840208002602c855450380040340d000e1129030b000d8000412806c064000c1c615550700c0032030300305000c0c001c1d40d0500c0d00c0f4107c81006c960500714618200009402c02c1405500204400b080c0c035680301100300400d100801d100103600600c1c6002c1543c43e000308405c010580c4018a005103d50400080c0c60313418840d400007414040091404c4540394110110781c009403040d000d4808242590043c1d60305281044104002e110590701d41e85030291812006114103c181c0c0178901c110f007441c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 29610158 1250 29608908 29608921
    0x60303040339030c0b0306030a0c0f03050115030b04170d050f01080607080c0d020a020a0204020d02030613060b030c0a0c02090403120606080903091207090501060c020a150e1011030403080a03060509 87
    0x5100c01074640c0c07407031503d441f80c7e5034200082c5030805009000340004080c140000c2c041c01200110401c2d24828030091000b00342410104a900308244405844e051000c400b150105592100448000d080701d15510310745a10380c0d00784401e960040d525000d00c58011401080046800d100315070700120180f074030740c009081c40b025214082c0980f00c07400c411260f0000340e02c01c130b9a000b0040e89042542c041c100f5512006604070f2000213400c00c44243e405410740068402d04800540710341c400351100000c055045032645890444260843c41240e400d00008606400140c1c0d60072886a201e14425035958502d0070756803481400750361155000e1001c2c804880240a1404030100581d070340500c054500000d051402440c0a150855aa004800c0e80f45400c001066541d40200100003190094601c5c0002c2561501c5151a100b28103000e100000d0b41d0307000c266070030310304204175011601c0503140419000f141081e1070b50459119074011901114005240c0d03403c0c5816000d40030050004503890022854540d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 29611408 1250 29610158 29610173
    0x90a0317130b060d020d14060705120a0515090a1b02030403023607020601030c0e0f04060f02090604140301060e010e0c03040303062102030c0306071706030304033903 73
    0x200c030000d00d1419880001003440d01c900f01d0741c0d4440c5400a11b5084204030760300380240361094059400180340214000103101e94014411038030080c100510090040e0742c2e0100c0200140300190a06014180858180d40d01d40d0b2194240c1c0d025800b09280001c2400211024048518190043d0802c0d0b400c24030003040076a0340c080b200024140781104810640c0c102402c000042015005519070f1a501c580601c071140782d0004440d41620310499a00c10b40e00d450b41e1450071118002c403040c0c00030350b41000005000525980240304c41d600000303405030078602d4010005071301d41c0094103d15601000150000c04a190034090b9400520002841c0c03295135051900716601424018200d440e040c4000010a04041c400da02000051405076101c07000e031011b0810343c0c03003441c0030440140c1c030038861080ca0610ba4900800d40310b0240440341c9440c900300740440c05a01c0040801011160306000070301000001c00c00405801000c01d0702e40c1900d0762802c00300c0c084800c0c1100c030304c1c0d50b506140707229440900004000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 29612658 1250 29611408 29611441
    0x80a0b0d061a0405010806010f0906030b070f09080105130c140d02100e150a08070207080705010f09030204060f08070f0b0306010305090c030f060a06050306100501030207020a0e090a0317 82
    0x40034000c074070110b01a0216440300601e1009942151404c0000919000e01140c0319041e103401d003000304102981c030200318095445500010b07140d07039000c1c80810726003405011342e8044910340e0300f84166a0380d13440802d50b0864a04556000b54003103502c046070100f0500789602e902034a4140003202c80c83c0488408101540c00d4194000d0068003001c2804140c1e901940c200e01000340014240c050815241c1102c00031030700507541200c00700d1180313404243d0b05800400d1104c10355200704001d00281d4030300001142e0030207551840c2024484105004809a01d0782e00030800589041c040c0100b540340b0f03003124140380954a9014110640b1044c03c20320201c3c0701d00c400c40350004000d00e008216078032a503419a08065248141c1503140c4100f0507045264440072466601c204190b000400c0901e5540c0c0526841d200c040341d4088005c1c00e500c1040c000c66001e1707800352000c1800a000640011388036101544507140550362102141c0c003140c2c00600f0964440054020311f0700480000c0100c0c1400d01014440307400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 29613908 1250 29612658 29612663
    0x30c030b031209010309150504080d05060303070b070e0415080304080706090b03060405180d110607090803040302131404080403020306060103020708090f01020309130b10080103020a0e1003080406030c080a0b0d 92
    0xb1646d00308014413071035418020400c007031520104442d041515290f14146d0101600203011030030100001c60524001c03055031312540d0405580070050340c070f11108490b00d40c040c1d030f03a2903401659403810b622000001580c09000d04903d00045546a0508030864603002484d4845020010509001c0c80702e04c8201c4c040c1c80e001202540c0200d0142c69821701c80c24624440c1e102d030342c84d81c81b51508070801154410008851641ca107400d0380c14603241c041c421614182c00303005094460384208010001070a1a0042400104201a0000f5040b601c000f035420044d000355025203d5072030100c1c092080d8079041c008d50f900302c0c8090808500d003c00c0c2e9914103101d40102036040e4843d42c101e404054141e402441140c120810040c41c0d0101540310310703030ba130b0000c1100c4008640101009404442e10380d0050340d00905070390f0014400f85d8040d140100701c060071403000b0002425041460300010014081310047c201802141e01d000c11080f00e20003009060200c001d1112071002d007013101e154260b44072208103020064 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 29615158 1250 29613908 29613911
    0x10816090b03010f020a020d03050f1012050109020d030807021002132304020a1205010e070c150b06030a090308060a030c0501050d0b06030f090712020612060d12030c030b0312090103 80
    0x25803a40009006000e44c0400c07000180c00043c1c0107200640c0807070800f0740004151000c000070307103032190008110002101d061103000c145480038848504200000c12180f48071b54004121125643e02194070a005d0080440103d0b542c00706000392980c041c0011403a85900c45811070420049896040078245280b0480810511030b817410344421103a043ca681c45607001a10665942c0040c1e440101a091840c941c8420756150000105039641c5981000b8080c203080c1d5107150414071a0341f0380f0b800c0e000c42840c1075441c05a03180c10243d099160390740618441d01e943da20009100203d42009002c41000600052048010306418400a1066a203100035a0000c1c40c2c0180c50701c0c0031f96801f03801008040022035016801000300140401d24102d183d104003071000681c2e82d419a180102c041c0000d40c0d550003540f0142c00d010b41444078844403191984018000c01007425000c094843c112186d48004030800040e0b1105043c00a0a4160145801c5010300350000c14036412000e44c40826801a1a5141d0405 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 29616408 1250 29615158 29615171
    0x6060108010b0702040f0e1c05090f060f041701090201030609051b03071106010b0705010c0504030b0c070218090c0406050f0604030813030203150405061302100e220e0601081609 78
    0x54640c0c2c2d10040c81107480090401148402903119075940d003910041e04c0e034044100043c41c2080b4410740983e240c0cae40c1e025185031106145d500c1000a180c204d4190032900c0b08041c84009500c400c5562820308051041000054211032800010250340c1c10f0b0b0001c03a602c904140c10300c074a4409012280500c20030782048030707880c1e0301c0c0c00508690300d103403081e500b641034402d520002c0395501e140001070203103500c80c5008001c80c00c145107065446000d02c2c40040c0410040a0001d10040c039179000400700300340300401030800c40b0100920f255450f041620104840d5010341d4075940e10b81064401c42c40070f0302c02201e2400d090400c210004986100702d0000405400000c071f03440e10089402c0c1c0910700170b15402004c0e1000004000c075070500c0764008490a50399485208042248111b08144444510350043e01942406c000b416042da1000b00f0010b00c0358000c10707030600c0030b04d050302168121402c01c14402c8000c241032000d01c0c0900d04c0c1c403106030098102500f1a02d10009814407006200c4100d4440310f1b80428503 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 29617658 1250 29616408 29616413
    0xb030a0903020331090501060909020c0c0409140c06030610030b030106120f03030c090308040302040b01121506020606040b09070f02030f04030b0610030c08130804080f1e06060108010b07 82
    0x1140120101403103040910000075852000001a041d030302c4c1149611800101e41d41c11510b02500c001b0300c52080490340541040c01110303581c0d0010300203010004104c4800500410200f0100d6a2107401510440301e00c82c12401c2c1c100092150790840541103641e2410350501c1d0f800500c001020b00312107800e00d039030b1301030000154800390020001400c959240e911000242d08145000000c1e811048001034030302603a904950f402100601d041ea40c0040c0080d06007411070b401c0c48014944110341c1810701040d0f5019081310b115601038082c0009629088003c45440c0501c0686007000140ca050301c02c40c2440b03031083c0c0c1529400c7d0440c0d448491460300805045121005a0441c41069075000c01e07400c0c001000b00902031402101e0380200c03010340d0101000001040c040b1f04540700f0115003000201540045a9000c01441c0700400d01030103581240e107003582d00c038121440c10380500002141070700402c0a80b10000c620b0741c8d00668089503400a4402d503c2c16600003000a1014041c0d003a442501190b400203 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 29618908 1250 29617658 29617663
    0x618070302060c0a02010f02060f07050304030201150801020405040c03060506030c071e030e01080702030c0d08090c0303040f0305160305030a0302030a1107030207080d02031804020c0f070e010f0b040b030a090302 93
    0x440e0090451595103d18800d82d58076003030b080b00d05034081020648414482c1e031001958a104482034000c207112900c4018046a4603880500240c046648130f214580e0004000390b1014000d000c4080010380d04c41c41d0200f408295800c405420040c10b207052000c0149441c1d25086039405840c4a111a540700e800e0b00e0084100a85041d00c1142035a140d08418201a0000e0a20303210703441c241c88500c1c041e6a203840c202e940307100f003915440303003600800f501001203400740408503085006881914003280d4050042455900a9480741078401c000c0042002846400d001c207043c841d442128600e451811a1030b02030344ca2041c0d00e000400c0603070000003c1c9122406078046540307468503a03000382d80c1d0341c424240290303502e1590140c003610b401004007222500e070002003140e0100144c12460b882c918004003c02009401100350041c0074041c110b10a05010810700244001d8902da0303149080a50410190100301c141541180340c5807003003008184801c1413001b0550350310680541d400f0807070b0901803400700d0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 29620158 1250 29618908 29618923
    0xe0705060a18090501050a0e04020102030a0c060b1203030a0e0a0c0e0703060f0305030304021503061305130501050717010501030c05090f1201060f06030e0c010c02100203071a1501030507020618 85
    0x20103428256008901c03c07081d6000705040b40d0040b05c1c094007481e04c500403000c0d411000e0350000d025909c100b200b220864007442c019401140551000551119206c011034404070142460740d0f165000041041000c1c040c80c0318801e00c100c03202d4002c105840075580d4a03052111103014145000342c03075400141c200d81c031035006840606400b01800d00722980c0ca00e4641c0c1d5942003500e00301d2250805460142000140100741c91150130000d0483c0100741d165904d001c020000030701410801501c40e18400046502402a0743c0607001640d03640900c44034000204a18401c1078101e2410182000700c9503c125500030141c44c81000103c80b5407008100070000914081c1d6040d41c0038040b5400d00e880050354003800d4508074101d0300303140c40a104000f00682100c0d16120003281080c086070b46030b2528070140c10864a212000201401240d1410005445103288030100e503810710070041c1e0340c404015407019201a1059007010a08050050381030aa602030f44542006190300d40700440007010179a40e280c00c21105 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 29621408 1250 29620158 29620187
    0x302120c10050901080a150902070201050408030a080103170307020604171603020705031605030d0c1a01090b010906030e060c0c070f080705091609050105090a0815190e0705060a 78
    0x10401c0361680c100a072054000b0a14140860b0000b0001154031b206800b0b00e42c0a440c02c01103494886090008020003034215840aa042001c1400007003090302081004099115203601c2d002503540c90752501040c0840e04100c540100300043c414003424030307000240150010791289451400c1009003690711294001c0030b0394075580460140c07684040c560049040c0c800c0c0c42d4150103032803080c55050780d020141c501a00c1800c1c0c05602c10385540c28994070803240042141e02ca40c10150b011900e01d42d41d002c19610070b03082118503580d103103600101580c101742120300820890806010b40150307804096140c580040030b43d0802d40e0001003224000c042404680090144030040159080c0c9509600f03070340709018082d5601807203400012860368422441c8581d00c6400d540d07a02e070001820035004480c650441e6840a4102c000b60101082168042c004c54003810700c0f00034000c5280c94440d03240c001e00030081c00f07524401440d106d14807030004008210603060752001c0c1c40c20fa56039111a1011a030504003110302 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 29622658 1250 29621408 29621419
    0x50312030a090f12081009090302030909040807080c010605040b04110306010807090902070501020408010614240f0403030c05060a020c0703030503060604030c060f0e0303130501030b03010b0306070201020d23010302120c 96
    0x642400c5d41000b5881d018810646e5006140f91700c1742c003480119101044040e026074000e00205105280c100a801d03407161291301072506100841d601e2402641041e2680915a51291424021400c151150f03d4180d0402c40742408105a0400510054400908014100000741d80010401809413640000400031110304646d03030a024103145000f0b4105001d241603a5003403000c00180000c4400e1803104450004160407140269210344c030042c0e100521040c54480010700054406683d824007801c0118000d0303d07001c04c1c507411480c0a80c1001801040b1000151051054205143e0005000710680c1c4d4503007012913a0f031f1280c40019505000c0c2d980014003100701d80c80003044895002d4100c10a000c01e64481024641c0d52004041d200e0081091003440c000aa000410080d8403070303001400340800290000545801e06804207092082c1110700c14050b079000030f5a91100c0046204034480d1115000c18070300d944150100850780b0010620010b0704c200507803051005e688400b0f200710b40140c0e43c02840e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 29623908 1250 29622658 29622683
    0x52a0402031003080c0709150803030106110c0a06050a0f140406050702010c0506040f02030706050301030506341805030604020901090519060609061d030a080c030c0a08030f01050312030a090f 84
    0x8199a42146000c2d261847d41440219004109151201002d07a440c0c803014606582c04c040048542080c0401c202c1b040348200c09082c4010303103401001001030242540d9440d230350940c0034005418500d80b406100304001920000c10307550401201510142e849034605103560b8450350004940000d92071502034005e0180b00c050100304a403200c481d0441c1d034420750903208180d070307500f0050340d450000b4071000e0119048140080c0e121500825003213605450000c0c0328000b41901814010000c41d0b40d0384004c0850804000c0060305401d04180c20010001140202040c0c40e0607400b144000c4810700c00d00000d16110030205078410005040d403501380581076420807410f82c3d240300040a00c00c2e58803642c008a85042200002d203041d400e10b2028805001e4014074050b50342d943d40d840503a01100312001c5600007417142d00c0b44c0f61003d20100000d10b0158010075100e0030865001c0c0d1021070b040e032003035203ea031081621110f0014035005483e40301d5010040000c40300c1050900001901c100e86008050103401e80 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 29625158 1250 29623908 29623927
    0x150108090a12180b1b06130f150218031006050a05150c15061009060c0f05030c120304050f060103020d030507020406050a0602030304120315180f020f07052a040203100308 75
    0x8010b040704a01c05c0c00381d00952414210115125030080da4000d40300440346c7c00410200f154040704d0fa254901c00c00201c1002a03800349080100c0c1c00040c0c0070000203d00906546081c0303000c20008800d2001c602c005c004003032a12002804003441c51040501458100c0d80c0640785c0160721055a0f403040303091007910b2245500b003191102010040f40d4082c4201d0082102c80600c2d0301c162600c07415101c9981752011058040d803a0680300728502d11080321184810050303801192001d1040b0200715440188803a10303410309140c21820030790248681c4046500c071600400c05a039444040c080f615801d420302c6666280f0034000701d00604031940044c1d8000103a6000082c5441e4000002e6214a025084850441d14504011400d4600c1d0004800c2204174011050001041500100b40308680e403a0000540e404980351200907a0003d1140000c1813078003103403c0e400d01c5418090200314402002100c61342d801410180f0401060b01c10500740203d5022000400c10403144aa0740302441d0007007002d0380c4404610 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 29626408 1250 29625158 29625179
    0x3250206040e0712060b1812030a03150801020327010b1c0b06030f060a0c020a05060709060801060801080601030f02060909041506060e09040623040308150108090a1218 74
    0x41c2c40c43c1000503c21951200203207042c1c0f14400a607600b4180b860302d4a89507034107110681d00905212a84403041c803041c00390350b020401c01059000843e44010411361018406040b19550382c0d408048140d00400405c59107601e20a0030300c203d4a101850340b100e0740403084945004040c940085900032400715540d04200b228651041c2c070761417044200702c0c0507540352001d00d500c0f8890504139141a610100124001214036000b040302082c9910440705002c041c2d498035845d25505442c1e08001c2600301c0b20030f0102a92100b00c0c1d601401c0d05041582c215403500704580d594071014440940125804510310045503148021030b8050440100200d4807402c140c1030883c19900102080ca41071884c3c00c00000c3c48600031040c0d101c4004005140c46196074694031b406000e4400300d11580c0310086080403845000e002c1030342c0c00707000794026600c094a501d0810304650840603100010f03070500201d8010000c1d2404000784148070305e980400c1031007070031040120030341d008492030320000090401c2c0500401c002108 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 29627658 1250 29626408 29626411
    0x130303030b13090c0311060702041508150405150604022a010f06080a11031204180c2a060204050604120203010605010c0206030f070212030c03100501020606010203250206040e 77
    0x2c554030000c02d41d03005280400c0707810544005103082420764040001c81c0d1525a03820341d242c000350010b03150480c9580014211036044248040101d56014288040d0f0b104000c0d803d43c01c010b1210001329401c09440f0295101d03820011000504041000592962143c2d0140c0742240d942002c041151103140d040303100f82000070345042440b0b43c81c05c3c10100c0a480140a00d808039503010014040e0320710207403182000034894030a190340600c50116101400801080184010150103455018004100924030280c80031820b04a0402c05c44000c40d50a94075215131000d10022449a9101003003442e14005000c1c0c050741d4040e03a0f00840200d400204407181031500090309108600170041261604015a022461050043d40250043c00018542c03244034590719080b90702c0b80100c640382c43c040401c0c43d01540c0304031440095104084144036040d4001300c201c1e00030304000d0019244a152510001356a03020b4080401006c0d00c07d80c075401580d507046050b540d0b502d50041c003503d5540f51510080c08a5150 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 29628908 1250 29627658 29627681
    0x40311030c01031b080c0906071b0b030601080c160204180b010b122806030602070210080c0d020703090305060702010e0609010902010c0f231c031a120313030303 71
    0x351084065035610a02c10300a8901240100d04061003100f51304807800344d8000c00000050404000c055200d41d44c240103841034030b21500440d600c0076486078144411011b15440b246950b41c05000380445e030703070300690000d9100888034130302a21583c45a01c40d0100f100d9110000c2d400900d8101c6294200d02445d0007081014001d10a0a40310391ba2901021418402c0448044403604024089a440600521070700707140d03290729041c04054619a81d440003200c8055101f25449035000403ca0110704120506005c0700303006080c59422490a00c0c0d030300c0d00c42d03c15601000182640043c280c81051b000c1d01d505401303190031004031800c52a103240f01070f0007024826040852481594001001c020050240c809029410303541c001c0c5208155456103801c032084582258902078200f0801c0700510440310302e2001005c1900200005165200681c1ca0408613400d03000c201424283c2d0241c01c001d1588060607240015980601c0140b05180600d0441c050090080c5040038140400020b25500d80c1040c4c0210b039 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 29630158 1250 29628908 29628913
    0x30b10051b0a0f020603070504030506010806160512070e0a030602030109020c0c100905010c06020903010c02010f0c02071a03040c08060405030901080f07080703050c0f1c05010512060406020a0c0804031103 90
    0x70501412265104002c0e01d00414400c500d8481000508020b0042c54001d041c0d407d010381001d840356a21410801d0980000000e60700807010000500124200011540900e041052404030f24113003140c1c4485c00100701c50b051140d5105c0c00d0300d061f280c0203000f2005580102d021512961907103c4171001e540401aa21614030420188004500c0c1203560102400203603183d10120a1a103401528000c044100503901c4560a004003034041e02d0070300954805107501c0c4d0000500416510008045a900007044c07801c41d070200106110030a1084180301e010007000c80000d0b00c941d11481c0092102c00107070082071b102c1c0201c038103020800c0b00000141c592603000f601d49551681d54042c03140c25020007110a0000180220082140d1034025400b10740c200031080b003120f1820003030b251314076425800003800300b603050a0b8001810820300b00d44103550240004444e0000c0e0406031070041b40d078508000c1c101501c66940000c0c400342185c082c0600c0c0441c150f01424254556940c2d003090000c61401d05a602d0090 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 29631408 1250 29630158 29630197
    0x6120b0a05040c030209190503030a030509031e090307080708100b19030f0b060915100201060305060115081305030a05031e0a0903030f090819090b04090615140a0c03030b1005 77
    0x1c40407c00800e80720082d0045040950480084028250103020f40a86000400440421304110701041d80080303100d170f1034207944250039018507151219542c400c42e01a002600144070071440861810303500214800003003007000241340081c4000015141903032018641d42c000000308040a00300310340d0540200c86041141c0d442009121112104656400e82c03c0c4a0041981c0c403440c2240c0701c604441c600c1e10000800507141e0340e620b031400c0420b81243c404c0c14503c9000c3c0d1380e11544006d039a46d1001000620602010056035103a50700d0040c585044103010f0003000064400e42840e0346510308407100080f60382c1d1030501d4161100103010803102540064103000300383e0800c9015006410351a03901260151421007040050084008040c691408115006c040040e0350030700b0902400180110840014549103415640c20224000344021001d015900b40a0a0740c50190b200f6541c3d456040d05100321790040c0340c07030102d0042500c1c1c0d06850380010b030b4029041142d64401c02030300d801b6145120f5035180 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 29632658 1250 29631408 29631439
    0x305061003090f0f11040f02030a06090b060405060c0f070b09010305090a0b0a0f0902030105090114010807030b0f13080705060f060402041a070302030c070e040308060a06120b0a05040c030209 84
    0xd5400b40c4402034603100554110000143c02260480c1030107006402400c420101d00d0001400d4845d095400c000280c0c021092040c00d051600ca0300c4000c000c02c1030304110301148074005c105540101e10802c0d10513140840c0c00300c00030f0414808903072a030b50842d060b00c252a45941280b04283c000340d592500007440c082c0001c820050010380000400c0d000a40a030f01da40d074004180340a00000002142c109480b02c201ca001a102402042d003c3e880c1e000000c90481850042800e0946c416030010600394026481003000c10f012881094101c51001030741c40c1180d4400a481901800501c0000c041c240e000804e0024080301292542c01030707407000c0074041c80381ca4410820059005600070b140c2d80c1010340b034440c10641000c00041c002c492203801902d08040802d0010f508100e0f0702c0e03200345044c941c0e5200300010180e0184860398001012105080c0090030705000809804580315016071007640c0d001900611784c5c880b41500001d000081c42805000003c000c014003075008116454040c05015110100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 29633908 1250 29632658 29632661
    0x715030f0c08060d0c05060a0908010b0306010b0703030c02070b0f0d0b090606090f130e0304032a03121e02100b040b0f0d0807020a15020c102f0601060305061003 71
    0x4903a00c030760391051003940b80c21040107641900c03160211a000c21038007000846460300e00c09807540c0d01007600c071142e1061428805030300b541c2d0343c1111580300e5000341e001032184c45a130710240d80f100c5801d880c0003d0b55100e98041a03140604a41081105c014049210000501610000e080880444070203100417800c1600744214130109888041e0b012000303012044c068141850401c241250082c4415030780310101e8000402c98000c0301150041c0d402c005814001d05c1400102030002042d141d040c4086101e02d41300c1c40d142c0031024000240805d660440c1d00e0b040c10f20400c03000386400f0302242244900065824060b41d5000c00181d4900c809080200010f80d0340741500c102c40400d1170180c00c40101c81500c10170844146000c203000c03640b2a4007880b84102589461000760701509000c1e5081e80036500c0004007910344450341403020310a5441d115818502903103c14204501d0350318807401000c1c014030402514402d041081c44130703d18850794000003116035140d001540a4881030f81c0e0089c01a45c1c41d6000c50 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 29635158 1250 29633908 29633921
    0x90f03010506010818160308040509090d0503010510210b0a06020f1506030703050d0801180902030a120c0b0f0714030411090a06051309060b03031806030a02040302030715030f 77
    0x10b02184072540045c2240d02c2c400c5146410031030080076118007014290b08841c0c0b18910340c00c290b43c02d400203d4148244d04224004a821116000040c0a4941c01110040c010304c0140a81c502403000143c0d14101640500407058040e413005800021b103102c40f0407080000c0c07030700c0f0003040d100d400c0102c400980f00380007045107000c0706d4500e0301910280b080c6512480000c3c50103400c0580512071084000f011032820310072260401d559503030312480755141025a9a400c00070320410504240b03840700e88001a80d0005045107200c0d0300241c0728098912441d0b083c0d42d88080c20700c010b0040140c110401ca0009c0710300312a1752050381d40c0e40365441114074115070310fa4280801c880041200134010440c1980d807409031030f582d6002091843c04280139469002003207510918a83c2650300c0e5490310345200400101d4081c3d000c504c10140c000b1810010a40c42e40b80b2031030800a045809400300201059441c41240c044801940d0041c0489411b155a0148051072005288c1e12200017407070240e9401e01002c09000d0700c1e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 29636408 1250 29635158 29635171
    0x5040204080a0f0516030b070215070203120a021c020415020a0c030303090203071802030601031a011b08090306010815060307120210020106150c1403030702030a051b01060b090f030105 81
    0x921001007070390f858601c094015803040d01ca9210308004a018101d50f4075494020b50712030280d1140c0d0741008417010303150400a510203005005140c003000719082c0d00105480719007500f010702030307010b0b1100a4404000d00c5802c0c10f410411500d01210308041600e50024400c464002c0306a01d05d0311541f000c01c98640da11207100a150f802240740801c0407a1294004114143c00142030300ca04a6491040e6500003900312a070074030050f000300c10000c46603054801e482000f4044000b12684000040c0028510070034414245030100180803100d0501c590b02080e500c0c0c0c03000c060210760055864000760b45d03541500e0416505c131007140300001007a5044c04540c0c0401c0341c04405002201000c41d0b800c200200080008180440d0758403000080c1041083c000840e0040860700c80303001e44807250509203200031424122040035030041040c0820f07030b6030000880783d03440310500c2d2841c6c85030440c90814480741410b10a00065608201c0003007003d8142d1002042d03862411114002001e00e08000d241c03c2c0c480c2200c61 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 29637658 1250 29636408 29636413
    0xe06030601140d02040b1303110a08060a271103070611030a08040503070605150f041e0903050c030f12090a05070303030c2a0203070806010b0703030209060c1f060504020408 76
    0x40380032140a0b1010f007140c100d203c0d01c05800e060701d54000c3c3d5200e4004116111003140025020418032011500e081d101c0e01c401e6a80312002030070f1030b00c101e03540c0da000f03403503110501c2c1d076009070313a008822050002c1c1030014510200c12041016090a8200034203084040b0701ca8056101c0000d50207010b004000b4003980900c001e5400c103043d14600352240000204180c81c0c0380000c10982001030050b21600380f190711a00d43c6510321b90154024800e41c1c1040f00703c1c190045180180039001d06035080c07000d0301c1b40c18603540040744248071460700325007030b0252400d8001d0710321001c6040241c03014008068800080d0084031114a96500c003501d5544413001140503000d900011001d101191094000207400034803828000e018000800c080070322070340d282d104540c1824503084c08004510b018880d44006000640040806506010510242e441005001018940d0020341640581c95150640305840c5008040e04e0a02101c00e598000141110202c1e100d1940781100101c3c00303141902c00c1e0303415104035400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 29638908 1250 29637658 29637677
    0xf05011b03080705160b0103060507030209091305070302060309010219030b060901080a060f030507031e0b070e030106090609020304021809070603020c010e0a050d02060a1b051c02040801020a0e06030601 89
    0x3000d98a030b481c0904000100403003085440030000d801400005954030074480c0044030b40c91800c008c400c80d1405440c0c84109070040203400e00310341e40c06222036000000c0c2c5030115100309191500034980f903e035520081d0088404400c10008a8065001e40320342403801c9010383c120840200d040741141c40c1840f40c198040e0050001310f07080d503c0303014242d6100700f04103000a409c607114484960006601e0780104d880f81d100308020b008110440409901d00740f00e400c5220080c20b13450fa60440b030380100418400c20020070a0360013490b66825004400104500001002202e48030182c010107580f0896041e4000d154205884864803e000a1148074510308809410b13694200b01c0102c0c0694403000886200c0d64076508101044031003444170900b51446403008240710707070880d14040e08144004196140e46403403c540c52041c03045501c0940d4089295152059452090740505d140f4544403280c0c18403110301c0802d011a440710151b008280d00f04440e01d44034030401641c01040810710045a00c940040c0d41d212 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 29640158 1250 29638908 29638913
    0xa020901140406030203031602130b03030a0c03030902060d05160c031209050a150213090902180601030f0501030503040503120301210f0519061109010c120323010f05011b 75
    0x102150784800001c1020030215900c0e00001d185822a000c001c8420100001900843c80c20600b6005804a425002d1200030aa140041c4e103a005802c107074018002107801550405210b64020034400c1e42c010445c1d503c403640480d001b001000e084800c0e141204c0d180c448242c009008001600c58590b0641d03440c080382c4994081c401c0a0503180c4402c40b01c41c4a4001c4010000e013403095402e5521400d034200680340c00b071400416410103425070104100c10b191444035000b58a429000c0220a2448482d103c80e5845040040b001082180c810b9140c09142c0703030020007009004002002218012412a46114110342c5100e1180c8000c0c1f01e8210010401000b80c0b5140c2c02d0015114a05400365090910007003042e20317464100048584403241c00c80702d001e000d0b030801c5100d00c9903004182c4110781d41801d02841a002034280c00380d0b40c0001d001d0785144503200d02c10f148250001214000b6040d807048822140a4507880c038481d081c0540700c9070040319000410154829100100000300c0402e82194031511074 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 29641408 1250 29640158 29640179
    0x230901050f010c17030708010f0815060a080607020601060216050913060207140303010602010606210e010204050d11120a0305030403110304090606020d02010b06040b1b030903010e030301060e01020a020901 90
    0x3640014140001040310710040750007101c4e052000703e20200c0403943c034584640f0080100704142c02c042d5104201010500a81000103040383c00011b22480c20500b54440c000010941c1140d83e0006440e8814007081041c41c82d40032070f55074103c2d003898080707440340d9800541a102c41070700d1307000e40ea0300301122000045504c0c110001e11003840e404cc1c02d005280c0602902d403004051400c5400c098550b02c000010064a54240304800040845143c0309071148000211003649103451142114406d8807400c0444c0103034403e504581c000c000c01030481d40203151501d4500d15615420005074840e81d180707810704420820100d9000501517261351041d10b1542c59681c240e41e25000e481c40440d42c0d2106100c080f59002c42807241501610003600105143c4403c0c1400038250358420282e20b0164100b030004000c080c89080641d20010301c03140e03415090300c01c00b200e02851401031541259040d070034959001904400840158103840c803540d99101d400807001c005980e134030100300000b908050540010400348488 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 29642658 1250 29641408 29641429
    0xa030504080903010e250b03150f04060609031109010614070503040905070c060c02070602030d0e01020f0301060804050d0201090201050d02030403020a020a093602060307050403061523090105 84
    0x521201418120410040f81c21110011a14103140e807203141a131406100e0107880f528806a08401c5410300ea0501868150b2804054030b41c80402d0140754074580d04e07946e0b810700710441c203401070001c1100541d00c0c400241016107622040d03a2245040c00305603203c0c1482c4100c02e0580da141d44400b0051000180e030400140d105450654250000b44008204407100f0f0044038010429980d035a03040101c00e040c10401c8a00611116003076505c102c40800401d6004000d0315060082414009400c40c2440741446c0a48900d4040d0581d1340b00000011804507041810640114001e800f140c40c10308400006a080b28124174010f0b021402c144480004001940c0045a10601c2032050346c07034506156022494000880d00158269912003003004040401d0000c1e41504665969082501012140804000d40641000a801030200000040016000c2c804440c02103070300100405c40b8001c0d0450f80c06c012600303405000c27414840210004021151103154030340200d0000d0003008164a000304028501c941c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 29643908 1250 29642658 29642663
    0x2030a03081305060f010303120b030d080a0e06090d03150e0a020f040305030703020105150409020913050705130222060516030e030a15060e07020a03081f03030201020703030b0906060a030504 84
    0x110890782c0da00040342840340d18041c29510080ea002c0703505501d0083c041701c0c40ca003507a85100d8500414034005580c000b4549040402c1e500313001349181c47e00748c0140c0c0a03003100407407200c10b44550401d2061280000644c0038101c0710301d036000c10103d045440702d225040024465003480c0c0f481e84005c030302500c906038020180d0a01c88050b0034540f0f41e40b0703038400342903030000d00303040d00581d54440811900e00c40d41e0308104034940081301c1c100301d40e110982c001503420f4030152010003400b40c190211020048108040000303000e005042000c8540305006841c003070745c0300d0f180702a209290b07040400780212200250009507040b6441d114103008000c402080440c840080943c200050f81001880d55203051101c1c801d484d025038100c10f01d41260a50040664109034484044010030320200b201e000d1f030105540361000c0d41468218065194070036025190212200400409a2007003800810182c05600074080248203032410300401800b20100401120304441c04c07900a1010090301480c1c1e4170951210307a1151 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 29645158 1250 29643908 29643931
    0xe07090315021c050103050d09080105010815060d02031f06060509090109020d110a2003190f0e1504080606030606030d111005090a0317041110050702150301061b02030a0308 76
    0x80a010400f029650281d2080c0c03501e40100c25400082035001c00c0000280000340002e00465140c502000e03035070301640022265170080a004148075548800c00c5020301c5070001c2c00c0340c40304048074403110441c8032081c01c14540945054000280b40b40101d081d6421044028103020b4140c1c40c2c591032a01070340c81031310040c402c40c0d03550310000544841c501c042d00c04072a850707a5a2403600740ba0080303502d14506d10600040150f000f4400d90568602c083c240090540c11490301410780d1000200c0be50b80540c05601c5d031640841501540c80c3c1450380c003400742040b20341540845009072141814541c403580203a60450b01500701d80020301c15170f40240d0f00b900380c8601302030441d4260382d41410040215242510070031959002654210705156101c190350a0100489400c55040d080130b69443d03500c80007002e009409600203d1007170824070b00810a940703060b81c01400880883c940c42d5400c42d200c0e4000d000b4080854682100d54480303490000380300e04c0d60b5038080c7c0181120200740e2002d0368400d100801c504a0f40c0c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 29646408 1250 29645158 29645197
    0x1a031e0604121e020102040501090807030c060509030f010608011506210507110601080f0c09010617040807020d0c0806010b040605040b0309010213030303050411012c031002070c0e0709031502 84
    0xa000526010280040c61341c00180c440d82800e0004010782d88941c801c050503803001e403042c00071848484400d4119805414984d6442c22000c02081c10305280078225001540780c990006200d0b441900a040c0503103120314021032050f211541502c14032410350b5110b003204113500070084500041d40c0032030b82102d9241019205100c1900c2441d143c18002d8004690035000300c1608401030b8400c0144130307900001221005c8403981804001400c50302980a901d400c041060b0118083c001260b00311900650082d14100c0e003c005401c040c84150079502c50005107204100000860355600307030940b0265450359540c03525280c81d04400d440a604050000900c655081110403002c2c2007502184004611a4801154901c0d160038412014022140b2031414410024401c2001485100104225214000e900740030f1800400c04a40351032040000d0300802c9100040c00700a00044141100c03c03215014095411565409405c441070825440f000b069284480e10f0501441c025801030185007220752041d843d070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 29647658 1250 29646408 29646437
    0x190c0f060c060606030c081303120f2f07030809070e01060f0f03020a0507060905010902220b040b01051204080f04030c0603051003051c03020d1a031e060412 69
    0x5141140d21440100300100400300070001203004000050010b81002c02034460075500141003030344001d2850700c081071004184030415001e0b22001d006d080102504214495204480400034503040402c0a0382c081001899541d20070084209014044481541818070405940c142c0d00c040000e060710841e4000c202020414110000c0c4881c0280440d56401800722051600900520b0380c8401f18020180100301001e981c03604101103d00e165840f010000c0e251075642003040c0108030390200254040e10340c0f40d60032004c070f40d910305041001020713000400200789090704120888442584541c0400c0e0f0a000c810a000e00c070302042a84140580201898201e04450b01203543d40203030021248408140000d0210304e40c90301c5002c0d0b0001544490036846411921041d94848601c840010b42c5003225201c0201c0070b219406580e02901e4048082c044140300c07200e0301850f600030203a100d00900c18580c1c4490081940d0340c00945641c07902c4060001c94580d61a0551588100d60f944010b00c80030030040e042c1c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 29648908 1250 29647658 29647679
    0x90303040b07030201050f1614030411030d0f17060a0308090102120703021b0609030a171303060b040b060f030f0c0702060307091a04030809060d110708070b0a090302190c 75
    0x600c540b01340e000150324500070750f04d4002050080c022480c2c4800d00201104856006480035500140c40480d00d601d9503240e02d880080d41c1506201c0c1901401404562004503412001c12045c03918a6283c141ca0103c030500b507056000d0040300d4860340040da13000d042000c44c0e081c6008240402040c8190b84c3d903031804071950313452a440141c045005a01c20003c130140a403203650038a44a000031180c030340ca060f03c00d500007540d4a0a480001d08140b00009809036071194900440d030800c4000c4c60014007865980c14060000e0654808590046080c10008040707403034000b04440408000c9541207045850701c016141072080002c01500304a03004000001c0540d560030040c500c80c164580d6210310060030601c05a10070b01440c030607000d1081c42070000380001107011302991034410003079071140c1c0c9800c004036030700000d007600074048070800400040050030b11510b20014021a07000e807107440c4103034a90000c0801140c03034044000d40182c00010b14a040c00c009424500c1085000e0f4003244000740c1c85015401d03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 29650158 1250 29648908 29648917
    0x21020f04180308010305010516020c040e010e0703030309060e06190b010203040302061903060512100e0c090405030c0d05090d060513060203150102100b010c0b070203040308040f050117010f0b090303040b 89
    0x2c02007407003040100b08100007402500d50003224003850415888058002a648440d40c03070259120350b4503060303648038a4100350b004040c01800380085510b80b0b42e0b641405001000071a40640d526820700200507075864002940b103004a0445801d00b104402c09041d07100145490441181103000400c40040941d035000040c0511032a0000e001604107103481002d002c65803030344c1c0450702994060701045240503021410f803d5644d08444d000c18000c240340340490615a031900c019500102210038081804000405401c05400a0044070710140c14602c003603407180106507103185c1c051b002d0070190000410a40055810018400110756000100d540c3c82090b40c00072500c82e013480600c0d00300410302c1d41c0c0c100070f091581c0c0d10f981e00c100000d01c04040020b15807440c0d4040905000c0d40c1d14081a9081e1003001128002e40d00030010366144d03a12000208440a80c606ca00740c0041e43c03070210720200140e02c60707109040b11840502031501034604411100b8980120509c40d915000c00e10002488650b80002407 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 29651408 1250 29650158 29650163
    0x30105100611070b0405040b03010603080a02010603121b1e0212100b040b0f04272018010905060102070803030108010606080f070c0204020f0918040c21020f0418 71
    0xc8046042034001031502100103221141ca5005202c200403807051602260706030303030090790042031480340b134408603026002a038002088601c1c0019150705c9030f603041d0f10140541e4800c00507c5800d0614401c12206064102c09141d82c15004000d8540001c0c10105070008021480c01000041011500020842049011800302541052114010504040c0702e007503c3c0c1c00044608004204102010400d08880c0a1206020315621140310012095aa005881d150a84400340c11554403601d48200d404c0c498480c05890310312400802c001e5450114120340901051800b501000d0386031a40010103014082c080703505501600310701180300c00043c8000e5000c0c01482340045125480c050000701180401414402d0381c162410900c0170007a40810301d004400e03011540503854101509031a070b41c0d88100b603056a400200309640c08800d034200e5628901c40c600805002078065652003804415001c264034207462102150294401803030071000040103400054000590031601c626002008500751805 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 29652658 1250 29651408 29651431
    0x206040e0901050709141014070b0f060103150b031e10090609090206090f011814030d020307080a0e040b04020703080a1109030a021903061d07080106030201050313050f0d050d050901060b070212010b030105 90
    0x100b08a4810bc0502c294100030b0a20701000440d202d48010060a5002d024504c040e100c00000300380b9070030b100020701c00d80c080100b01070086410640031502d140c803400d1003070301c510505103500000c51005a11681c29442d40142030249002e41450404c01885130141a25052209820700800040f58000301c41c0701804c42c990040e00b081d5045010140b030500c60501001c2154000c10100300010000c5050703948000c018102135098038401d00000c0c01a07e00a40b410360440d00c04610382d000d16902034461806942c050070100070811130b011791301640c0c1c46601803058159120011200050401e842a0074503014a000091255034503540d400c81524000403030f154250103002c20380031000100348980001001404020001d841c650b90020b13245000040c10148000c0e1207000202c280304050000e060908401e8068a91054502002800c25041446401d80c40c628090000d580b0f010148a214250b50041041c03d00384a40d903400c01c900d9136109220804203540b19160441c0c80d0300c00740a40fa00541e0003c11 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 29653908 1250 29652658 29652661
    0xa0c120f030b06030c04030305030a06090f0501060f1706010c06020d0903030b0109090516050a0c05010e07090f11030109050601021c020d0f020313090b0d0206040e0901050709141014070b 82
    0x20000c082d20822403141d481503908200380f1a064030814200ca08507a41400c10340d480c0d6591003035030801800c9513440585820309280c06186010001d5104c1340c180c90003601d58080c8003100080413114110302603072264038400030401048181d07001c2c10454445902c501405444c010b050140c200070b9980040e0100e02203901d540e11384140d983c1108105007d001d441004000c645423080c500010011540604810310500160082d9020304c2000c08145141d00000203011042804117050b581e090184103701d0030078500040c02d48401254054940700c11078003c40a07003564280f6a120000b841e015201d14198410f0b003050742d0409010200410786204150083d000c40c000001c0042c06c0c5d4101000a0700454008100c10030741c039010b020b06038003034606006001400c40c0220010074036410300040040d5004801003000151003441c098442d00c00c1f150080284207070385414409076180d401500070181c10302c028000003036282c18058543d001b002c026182c0a484c0003802070665965038040d041c140c445400140 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 29655158 1250 29653908 29653937
    0x110306070206131101200601050103060906030503070204020d0221010e0c04080613021201020d0207060608060405060a09020303090405040809090601020610030b09010b101d090613020a0c12 83
    0x456a54400098006081d091a10004043c40c0d1040d00a008100c11045800c81065034811509a080f10200c410085c4110f64150803603556203000f441641e0000782040804a0030090038010030046035401401181071000d65401c200103508840c40c02d90704140d0a00c1560700c802200620400c1482c280b150880081d4100281094403135801000494100b40030041006107400c00101c5c0f591000700045042c40c160380390302c0012450300800c01c582d00340c0c0d80045102009110654002c00b0210321409041141ca5511300700c898491301c1c00c0790050503070303009000081c00c8003290303800c42e0703030400c0c40102503e1400b01d082c40054103c1da0140d8050740c09000210304000715040032004950030203400d0008003032500c0c103904420b42c0407070340780001400980c0100110700600402d4221411180c0d00505000d110320040c1700013000c003c003945000381d40e103182c0d0000c10001d06096815600a01001c0c0c055482d2600000d03104005c0d40c0035010740360400402c2014903010800c041a40040150309955481d501c1d401c56 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 29656408 1250 29655158 29655163
    0x302010b040218120f010204060905030c09070203040b07080c06010f1e03020919020405040e0d02060a0e0d050702010c06051504060803040b0d05061206010303030203042a05060c070b071103 83
    0x2080500841c03040000c038650480f01c1541ca00c01c05000c440f911007000c440e07200c4a0030104a00c251089a60000c14089100c036003101c003401c207440041c0d080310703034000310101017004180055840c2c00c00358004100030700c02504000010050070f80100000c501d0007840d0b0889501e8002d090b4842121200d2202090003901d10010780010f5840e0060031071024241544c001548100005d4400c40c0151024030400e20f0546860f01030302e0041200500800403000c203038803102d8980c0002038440340140504000101c182c50b10b0320445100c4c01401e0006c1a9402c003144080e02e041d44040b170b080e410302942241c1c20000968502503a449150318106070b4200d42150750a1006494030364000b038105400c248000c0c004120900d064a60645c151940400c0546500c1c0200390040700c4580a243c6501415001106240e051340045004a1040601d8015a0004003103803d4480d030700d1785400d9241c480850100818501400509469101401900c038180d6071050040704030f41c0088422a000894940090a1031906 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 29657658 1250 29656408 29656421
    0x305070911090f0613091a120303010f05060a03110c01090606060c02090a050615030c090a0f03030e090c0f04080f010b06130b0307020307060504060207050c061e090d080a0903030201 80
    0x7421111400c01c032a24002036035440140c066a4040d00010a4114400c14082c012000400340311404210b600301c40d00a1000009003464454002d104c0409420519800001124100c3d01c0b200501919141010b0400005074004841d803020140c03140440008291301200400081c4000740001540c4502454510144d0b03115500860902c038287c80c580f000b50301c514800c1c542c8142c000000040795038404000410594802d48000f001120210030045a003d114004040055003258103007011540c0e50101c61102e8007038003000b000555803240d5a003003410150001c1d508110500d8140341030036440401002250400d91086a056002c942c030340440c04002c1c80703203d240300410f4640c07629282c0340b40905480640c29204040c04c4010000020322503034400d2083d25281c9600034400e000600b0039041840c041d4000c400260380380d0051011b0302055150144c12102280214003401c201c4020b00030a0719a0741d00724150250300310103002c840a0020b1000001840300c1c01c050348aa00041d0f046007802421a0360303 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 29658908 1250 29657658 29657681
    0x103060b040513060e070c030e1e01050309010b120c0406080105070c02060f09131d010c0206180f15010e0a0e100b030a02090a0f0b030102030609010e061903050709 72
    0x2500109000654403a41240c06403401070798204101d818a0a1200003040540d11608501d4961418464419030281d0024000c60096079440741122181d801c1100016682003a800345555020051096500a1001d55805500c0000008081c400040880e042044150245002d60000305480c0d440c0c0c54180720300801f03040103000820080c94850000782024001c40f002a124880106140c240040c000d0111036507040c000e00446114880d660540d806400000ca620a581c4c80c0a04850900181407103080d032501c3e00303a8001c00305500e0780030070b00048810342c5280c1007943c014603440f80c4040c60704009101441039070b420b0846403580751003854002c0c0b410180560803a2820046080078021001801ca9284500030300009240c0a80100007031802e82c1c0844000e411105030020024040c900390710641e440c40114400307229007203454040500705e02c402c42d441c03a48406e001005000205908103803940c032203c041e00b4002c0c210791700000032141c050141c0c001c64079540282c1d4148060140c03030042060080c1c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 29660158 1250 29658908 29658911
    0xd0201020c06010b0304081306020c04061508010506090a12051513030504050114040801050a09051212011208040308030c0306030d080103020105070b190903030e010b0a030c030605070c060c18050103 87
    0x1203841c81a161290b0040c400c40c0120700d000300200702800201740031030780b80e450018844000c866503050069150111180d4136403290307180500014030040c1e0072001c580b038010103070340714125a8204001c001c0e058000c41c0c07205802c00c2c0f040c600402d4401d0784800982d200781c0904014480900e042c05603044d007000c02025400f044040c80740180c0003030380003c140c80596009085c00020701c3c400000000c2c1c5030107580c0c8842080e600301030502648000590104880724000c070700b52144120b0042e640006032180741c41c0b01c04801c0d01c0500401440001b000d02103489881444034515007641c0ea154004241c01c180c0c0c010009000000c21710840c3d2800b04507091400034641003540c032640c59a000600a4015a44080c2034146e01e0000240040c045030201546004001020058003915080007402000001160001503180245080141c076040314000c048070b6000352206075041c190303901c0030080d100c06440c1d007051041540102c03000034060b00502503034000c5940c586c040c2c030000180c42222420564010760505 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 29661408 1250 29660158 29660167
    0x106080703020a29070303090209041401060605030601050f07020402161415150f03070b0c0318190b0d0902040908070b1e07030b030f0307060204240801061409090108030a020d020102 80
    0x2804d880038076818a260745204580c456100e03080c00d4002d4020442d001f036002c4000820003042281e2603004801840c00d039002044496101c2d0700c240e50610041d84c515001c00d00910286400e4140b04004001c0c01e48041c002508100c00c1c414400b00348605120100c424683c0d1401c0141005004c0142c1c0c650311010044089050400189101c81800342c594042d005a902041e54403407920100721480040c003070780391800c0d5250280482c0903242c0d0414403241d50514988200000070b0300d0242c1041d001800042e503010700700d925080c0c1c80c01c890340c082c44041c00c6a58903001ca000260b907943c0709903135540d4000c3c103020f95254103900d820850b040e4021f000c84943e8540c0005890071200c4034280d181c0c04216424001980705814002a1501c5ca1241c200985e41c440080c0030b4041101c560050001c0b5000302c0004186602d451039003100c5506400b40010009840c0001000554412001100e8407803d5035211803400701c002022601c07041c2c09811030401d0307170700014070120425410030400450500300d1000314200f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 29662658 1250 29661408 29661449
    0x1206040b040611090a06050a03140103020f240408100c08040f080d020903010f02070b0601020d05070602090607120f140702060313020105160302060108070501090305030901030f0e0106080703020a 86
    0x31204003a002501882d60f400d070030000c2400040440350b140e0001003c0a507290760b01c0000402d42d038001c116110000e030400d10000d00d41041c0340c0d02c05050340da00a0041940d10100b4040c840400300061a12017041c1d01c601c0500d0508401c000100094030230540545692142204a0000c0c2c1c0c030050340c1710040218003c100004111aa03007404030a9501018850769002220743c0381c40030f8041c0c096140e91552801c00b000a41e83c4180e0f0003017021610800001d01e00d03550f5075006a0319481960045000f00b8810422000003403403660003800c4481c002441e081c100030958660514101071000e848012480d00050b15245030f800c1111080c1201499809030b00d0190150b02199541c00080c00010a01c1c0c410703824001168000c07802e94805c030060b407c9402c1c0301555400c0080d9240130a110314a2203000e040000301d1103512440c03013030050313a070041e00940c507002040303004400801d0303110408410315540d03070300210081d0380a0040300001c102c804005c0503824298010854083d00e145c3c0112104c40146020504 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 29663908 1250 29662658 29662673
    0x105160804060c02070807141e030312130c06110c061806090a0e04050a0c090c080402010c0c05090a02090a05060901020c31050f070c0c05190b0406030b120604 70
    0x1401580700ba00400c03400c050080c00d0303107452000e40128106d80140400824042007120740d8415600c0b00726600010b98804001c0900b004a44146013505a04108020b04041c0001801c80d42c200501000c0c085801d0040d8a501c0b4500400e0707001880041c214903084c00c0c2d2150108920f00c9000c5041f6800c5c3d1401c10340611f141025413a04210600501001ca01a0156921800300c00010821402e20301388a142915002c0c0d1208003c8504441240780400c0110750b00d40300d4031071518220100d441d0b211403610345400558401e641c000044500107064074000c106a10341404883c00b4804079040075840d0b0701c1c540c04018802140d9048240030f481c0c10b028041090f1782c00100e11041003030540e0200c103540710720b0a003010000c9a11004040491080480c080b0700310050b8025403240400100380c0040742c40d1040304680c800842c0340c0103002c0c2205844c0c18002494900800c40c50780009038074000480e40e0b1064202d100340c0290b404940030964804100c485814601100301c83c01c11160301401c01858907555649 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 29665158 1250 29663908 29663911
    0x30705040c0516030903140303010b0301031403160b07030e0a021f0225030201080105090412030e03091c020a150801090b13090501050103150207020a0e0c19050301060201051608 78
    0x148500e4035000d210718594054421a008000120f03280c008008240c01d010303241e054184030071070315404a04445002d6440100c04d0b64162903030040642d15503440c41d105c8425064001004150070300013040300a81c2440c040420400c054840c0c09500000d02d4940d03006403c49030381c0705580440c0d801c1641280010784d15213041810440019901e421f5102c44810202d14000c49201e10f1110402040800f80315403888444040480b132003642d50342666a00c1c0c0d0280b003441d44080c1d41c001d121b040a807000710038080c0030b500800080c9104400b26810408a035002520210640c50300c640c035103011000c0c0d5001c0d42002e0b0b207844c0c060030100e901403200d80d100d030350000c110410511500014a941d142884500c0d030f906035640044050032075040c04010b50600300503000700703405c1c40200d91114002c4a4440c841c0d280b80203841d160781e002440030094601c0c01021201c2d102000348441c500303000400280415020740e1507841030003410380e501c0a03141c2d8101076020342110005071101840035200030442001552210809 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 29666408 1250 29665158 29665169
    0x7031a0603070c0c170c0d081602010e04090602070212010b0612090c180901050a1b0305040c0305010e03030a0e03160305070614010602030a1808030703110f0307031e09050307 77
    0x81d94a566041d4103d500594440d0000c02a02d08400009810500340d041e090000c0c500000340da200d418002e080011540c06800c008000c4103041c00801c40455149102414890060514115219100002408440e60790004540d074590118801d029814488252005001c0c48002009101ea009000a999004c1c00891890044102000803205c2905000a9115100142c00d44040c03415520303039204940403c982c444515860600080c3c02c010290249403291f0010050028902d001010220301500000b40f09441e140403040c80000000c00912480c000d50509101441e203e041105084c8103403180f05080c2c0c0340d19070081c4030f05606800740c50340f00e11907503925040c4070b9910b02c100e14015001c0d1244000c41d00d115800480000340903600400102035003604d170754900c0401d0001e500e401010300c0304c03030042404a510070705c0500c001038003d00c0d405417200c0700d0004480d041c040508515103194420304c1c045000806040d41520f080808000710507000b10142414890b03d0308020200741c0c2d0704100d1040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 29667658 1250 29666408 29666419
    0x80105090403020703050111030708090703150e03090a0801020a020607050f09131e0b120106030b01090b011e02010b0f090402010804030f090e010803070209010e0c0a0509060d050f0108010507031a 86
    0x714003050f0080100f000110341c030100030b05c04020050309000c4650811034a410100c0c09600010781144408030325a415286c0c45400740c20b4011805000f24002d140800394044544070400c0429103da0350340c00c900000304004000980e43c1e160b00c1030024100b11001d06420180306080c03207109400c6c50f8100680302c2c5001300b42c4100c44080181c640c00c1010b4840d80e10540b003491102c0250441ca0031b00340d00400300000c1c09840110488246540703882c222806480050076140c428801400059041d4201c4280400c0516207600b031070021440306001d5048a13403440025039560021810785090000d0400f050741000c4031605503925054002030b0080d00002c1004041100017402c00c4013450241d00e240c00988150001c3e41c0040da1100240742e6a0b60000300e0a81c070030745a172000001d03105141480e0034425180010014104001801c00f5259908a8582c00c0c2d807054050203804ca01101034810300d4031500900c0070313910381549480c5980c0d085850141c00842090304001a81003803100300003c203c4a681f007582c8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 29668908 1250 29667658 29667661
    0x303040311190314060a050c09130c020c060f04060e04020901080a05042d02041128091508070e011b0206030c040504060e071701050f04020c010b060409090b09070608010509 76
    0x15801c81c000b003140c0004182c65000b10308100b000000145003071043d1441d56041000c0e440340040c000761070107284c1d11580d006a0103000f400846101d40c1100188600c0d0340100c035902d02d075260008450f5009a400c40301040f0000c2400c0058603400081003211001c20b450462800000600007808410300800e140c10443d10f44002c182049000210b40c0e14400350380c00801001c18500102115148901380180d03c12401c01006100e6900f000d4221210030040303c4252180d14075105405218507409504907050000041c0c0c0010902c0042c80d00300c001d0881f0750b4802d0b860b0700c0d00d603c0151482201c01c0405040000d0400c40c8440c031b002c0b480a601e02a0b4040310740d20307104e540b0f040c0240c43e00e2189030000c541150800e040007071b40005d055849401804561520ba428040840000c542e9020900c20341c0d50101c0c40302c600c0c28172030070203500800d0048004070020440000b22401b01d5020f03031240d4001d40c5000c0d0b4a409510a100c15030643c2500070000b035000d0b20202c0d142c0017000300b0324501800313483d101e401e6100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 29670158 1250 29668908 29668939
    0x5030f0f07020a02031e060c030108070302091306090303050402030d020d0207050607061b09170604081b01090209040b07020f07080303071107032a060509010f050d0905150403020106050303040311 86
    0x2840300c0e480d8001c080740c03807290350224041d401a0f804060851b41e0302c0382c4400704d24905402419a03058a4126006100c540d10319004c101d5080009400d0070700e11560b40c1001404601180150142240282c07000320303040c10244185842c128407450100c0454005103030143c04a540424039600f2140c1c03c40b111070b103a10b02400c1c004004c4c1400b000b41868000c4a0501c0800320f500800a10100c40c4487c8650050340161b214050711404102c0c0c004020010400c036402c030203268000d58202c045082c400014a0060b2503010070b5a00806403001d48003059020300300038080360304101103541800c0107405884c44034905102144d59000180021050080c0701d04550b0340e480e000c00c100402141c00001542100d0416414900341101043d4002c40420014030041500c80c09001160214403042c1d440058404c000c800c04c03541c0cad03001851140320741511800c047d00402c00c10054020a0301440820700003906161402070b0844a8560040340241c00034002000468484800400322401c203a17480c01c501031210 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 29671408 1250 29670158 29670163
    0x30e030906030906060109120b0c07060b0301090c05090702010e150601050712080a0b040204030b0a0f180308090c03070302030a030302030703020f04090209010908070b07020607060906090f0605010605030f0f0702 93
    0x840c1041d4200300d0100401914080014802d4021710003a00c0700030351a5141c40320034140c40788000c4041d100131400d1000c40c5c0030300e004400a02c6160702507000054101d1030440040c0c29079261500c1034502d204c000d1400d000c20702e1b00341c00a07a04803029000030085260941802d9843c3d446030105444060160030011719507034018003c4541746644242503103044514004080c114a1055034040303043c0b4030340360020240b820248204c0d0262030b0400100c05143c1e0390503002c80c01600d0402c5200600503142c5441140b00084042c102e01882c0c840d407035101903444c040c60998500007041e504941319900c604c41c00c00160f10040b45a848aa80610300580d40b5601c15009601900c1040722039030b0060710000e00060181066800342494800990b00c48900d9651540303003540e600200c0c0519040350a04002070300042c540342c80184141d42c0700704400b090042990b01c0c0c5900326600e0300d40540300d2240008405003002164454117001d811913003002411410844080c1844103c020410284085c0440c080340c0f005008 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 29672658 1250 29671408 29671417
    0x513030303020d020c06071106010503061015090806150103050903130302060f1303080912010c08010b0d090209130b0708130b04060b0306040c06030605041e020a12110307170402010e01030e03 84
    0x40c038211421400c21f2100144000305e00ca00009290080b400041000e24010a2460003019001d803180c00690070644002a46500b64040754144480c034200010302c008140b2000344200c1d0300852a801810206002405862f0300600d012a01d41007000950120384800d42d4034003d03650103942054807042081c2100c906407003040403042c0e0309940014000308000c1700100508065005641041c446166140c1d09400e032002c1c01c2180c1d0110b190100144500350440c006401e0501202070040342503822a000300301d09000a99055244142c80c13002e01003800b42d41d028050f00410645000c1f52186000d58821201d4001c4d504018000f1603020701240c1403000c542c1016940b004002d00b900c5490400b1300d40082c0080b9584103c80201703080040014013890b080c45000011001a607040c0c035001c00460b500c200035031104a01c0c50038060310b0444510261a1481101603c190b06020300385e49080c0824042c00c0003400e4004442050010020000141d03440680204460b01c282004986201001801030940c001d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 29673908 1250 29672658 29672677
    0x7030f0504120b01140607050604030e01020106090609230c09130920040c0f0c02040507140304030306030204060530030c0f03090a15050f030601090302040204090b09070513030303020d02 82
    0x1042d001d21030600c80c0c01c0003400d0480d19411040c204003068002405064043d00c00080c0c2903800c064000b0380420f01600c20300044d0141440005441501d076078480084900b01c2e000b07802050394403002103002e05112400104021400240100da52410170b413520201c0c402e000880c0e000d03a2100f100c900e01304007141c201d031003402c0c1e12003100149000e00019240001c04c00400e164811402d100da00071815006e01c0750801940c00d242c1d80c50702e65504c1e980a000140c400079140d0343c100480103160128001c844400f0f14003491007075501041b654a5030040109943c001c1d009184903481c40892800c42c000130903054594058100c04400601c0010042242140120b0003003500ea4000c1d002d038445c0c0400040000d144485080b5600100c4c00c0d121205013070100c4c280311b034035800309800300568042d00d5040f0001e140c0c003d20514050030501c0d126408203080c1e0f049607024042054031204d08440502e08031040e0f90788091185010b0341005418030751240341c01c2c258030010741495400a82421440ca11350100d07509001c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 29675158 1250 29673908 29673929
    0x30b09090609031e1e0d060f0f170c040507080a050108010203070c020409050a020a091509090506070c110316031104091e0503040504050903040e0711030406111c0201240b07030f0504 80
    0x1610045040380c2c2d40c032203501b0080b030350300c0c054020a5420421441c0015984190b0318007900790306003a1108000000480031140501c5600f04032500f44e940e9004140c4545020341d80c4440b40c0c20030210782c205030790041c0c00c00d41199006004108440764442081c1003050380440d4041840d5806040460801a403010082e40080c500600842c000d02c443e0065407064104041a00000c0d030789442c402c04550007003100a10030b4000708041000940714031030189038507001c2d0b81407240c18088000040c0c5008180002e00c100714440d81d10800920030008124040b01c8030a0700d0074882840d640e90350840c0c07404070048020b14104a4a81c54042c0310b82081980c000d0b01020f0420001c50521429407039994001e88298240801c00c400050b24051060195840c9542c1b030790021400c040c10600305583c407a4145410440b02d00c41e1015012200544000e111700401031a000000c1c04604411110440310180c04c00c03400340707103800c0410801c108003c01120240c1d601450080c009500c0c1e5242155039100e00d62002484c0d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 29676264 1106 29675158 29675197
    0x6030b01060315090507030c0305070f02060f0a020d0203100f06091a0306010302090306181b18060103060302120c04050121030e040e0a03030b09090609031e 69
    0x802c83c070400000d8a5840d02c072284102c40046402c5070000341c445030400c60868042c0718141e0010a40d1030b10741c41e00d00554502954801c00a4000b10314050742400007801321410f68142c1310040c2c0c001d0800d56036820200140b500040c503600905c0c41e03104004d100012964060b208810407500c880b84410794100007041100c2450704028500303410f250f001c2284811a40d4280010380c4103c0d000c901102c041c08070b00d800d0504e012a080400a0480480c420b05440c1c2d90b00d02c0c080c80c41c045200b000c00c05407542e03081c0c0105c029040381d80c0000d40016400031310070026072020851043d02e103c00d4404010b5130780e071001800c0d00b03a0010b42100c5014070401ca14040800c0c807440c00764440b20310140c0f010903a1440ca041c2185490328174202a00000c2c3d48035404051894500882e94012071680c00400fa6420101a11a102d218440139194503226040031019107450b680259906981e0610741001c40 = true := by decide +kernel

theorem cover : BRFrame.Cov 29496408 29676264 := by
  have h0 := BRFrame.cov_init 29496408
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29496408 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 29496408 ≤ n) (h2 : n < 29676264) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
