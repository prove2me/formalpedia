-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1530
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:25:39.307579+00:00
-- url     : https://prove2.me/submissions/c0aff241-614c-466e-a860-6f0b0299e127

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 275000000 ≤ n < 275179856 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 275001250 1250 275000000 275000051
    0x9080f010c02061308070206030403050a0813080a051c090506180723310f0204120f0309030f0515011202030a02011b02040f090203060f090601030f080c0d020c0103 72
    0xc0c1031240c0e1a00034160320140001e00c01d81d011700d410071624005954a9005600c41e0f4032a48559403198208603000b0300d2000000c01035036480c040d4503c000041040041074841000031481c0241c1d07215900468071491540d4454464103260500307120004100c00400e03402d2250b1000c299446414024030f13a0b0315038a078031700c0c4a10f4a54500d503412181c442c05004a58440c4428060900e48004c801d048240300d00b035040c0c1040c0f45100c1c41802d000e692100f00c501500f000b040d00e1103429814a4245940020fa403155060000c2801a00419420800d40520741d031a00540d00000c6003c2c0c8092141440da498007030020a403c0030b8004400081b40f03042c00c0091000c121a00900100a102c0156006448044802e050102c075800301e0b56441c0010b80d1240103042c201000c20001280c4c404441c81494608400900040c0044404404101c5600000585541140d40101e4075500004407403e01c0000341c452080350304164002c408258828640000d01905c40710001eaa08010180b402c42d0b800301c00740b0b0441007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 275002500 1250 275001250 275001253
    0x801060305010b01091208030a0e060a0b04060b0903190218010b090301050a060b120703150602070f06020a2001030b04020d0903110606062a0106120501200a03092109080f010c02 78
    0x1b100c6011440d0341d0041d560203001d101000821021000032a803801c0c8044401ca0042900e911500c8002d08040c0156401051028600c60400c00d00b0b800198481c5002ca5148170340c40c010b902c0480a6560750007040c1c0581c040c0066000c0036584840c200020359111030b0a860181d0300342004100e05203018811241191203a0b10411f080c08404031080420000142c4114205600d50403807000c04103181d181580202490703002440c44900e00b41c00301c0c15001156000d00c00b50b41150381b04178041040f0032640c0001c000915210441f0001c50360041c1e004000c207214042d0014400324032103250810315404502158044d80350a140504e48401455564100721143c3e40c2008090018016010300d651490804c00007416010094944074800c0c1821a81c00340e0100400034100c2506030706204c4e003880345c02001c01c0c0c241a50501842480000c0e0694880d103000304081513034841c20300b403d000f0b606030b10f07009910201c844001d90540400c4001d00c075484901640c4103a0090341d4104204510503c10080c14403850380 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 275003750 1250 275002500 275002529
    0x20603040822032f030601080f0f07060206190f060e0406050609010303020309010c03270312020705100e0102011d0d030e010207050a020d05150703021215030601090506060c0102040801060305010b0109 88
    0x45215907480740e46016002c00904841312200c1d5800740200741c0a841d00000070f01e8036035000d8040c240380400c8041b80c055250044402031040c80c0d404500360381e1083c8100c0c080e1116215a449940c02040a01d518500d032038904140402e2107400551500c2c0100d006200510903230f1070b0f0608020a81c1001e210084c050781c810481d0329038a500400d00c40358814003a0420160700d129203d9044201080311010b4068119030a0081c4200071160000002c551400d10050071358504210200c0c880c0070700c1180d40d80c00d200500a400d44103a10035000300b1003054039003182e98421611006040c2d03075808100459808241020581c00301e0303e10500c00e170750404c0d030000f00503d0200203d07000c0c00000c5003070200039601d90041035200800c624600800030b020b41030701d0b0340041e0755014041108480982c082c0200500c040d10000100c0399a400040e031b141500d880d804001019240c0400080d01c1e03204040c4050317601d50011400261400307045d444201103d02031301c028410403003070000445800c1464064401c01e551380d07a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 275005000 1250 275003750 275003783
    0x1005010e130612020427060e0c09040f211b110d1211030f0301090c02010603051c0f08042604050a0909020915090a05061c24050106141602060304082203 67
    0x140c11590900120b18151075151040c034006c0780d0702c102d084a08cd116a1850035007074041005e42d41841d11b003401c10800700c0058010550008211441c410401141c4203c5429100c2c18842208142004030200400340101d20f0503d140500c031882e11042c0380000300c0c0140100320f240c0c0901001300d40c0040e4582d0001072a5a080c2460140100100740090046660340c010100000c1d000b0003020480d1a005403076040c4410050034001c180e120515103c43c00c201c208802c3c080050780c9050380840084034022181c04818115103002c0c0540215440250b000b1684840050080440d6015800103070090302c42000d16030b2103c04015000e8006082c0da6005114070b0001010040c2a0307000035004000100744004905a000c8000e900c0380740b1640c256200d041c8400e9004250b032042d8402d0b609100400801d00c5198905080980040076002860f43c03030079000550b90341741d080103c04000350241d008103590b45a041c00e062030081d0b5002490407001a1150380310300302c001400d5101c607904403076001503c1d5001c0e05d00b1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 275006250 1250 275005000 275005013
    0x5090f0d0c0b1b060c0a0c060e0a05030a0f08010506090d0b0c040e040b0114010e060d0b150307020c030f0705090a0207140604060e1002031005010e130612020427 71
    0x440c94291809032061801240b82202c0d500140380e040100c0194212402040a8560620601405292040d2402c1000268080d041a03030340b0400740c0c0055002842c1344c226184e03a41401d00d2144020300034080000d0a0f410b00b5001503c091210300c0310f90380c0c0c0c90640e03203d1060018510400c450160300c41100c0741c1207c001003128200030f5000c0089840d20741025034601446e0266941a9022500052442c0040c4144c84101210640411003440c041c1260b4043c400071078a28032405a132000155100c0c1d0403030344e03252600f0250710602698802903d9503850460402921840319801c8076100b0b000709551688081c00000e451b9007035841c001c15070314032a02c503509090700039800160110349034004d10301e04140c2900c0c24084140700f907004880200b4481c0503000101d080c694041401d000051040c010302009941c500784103c146c03142030134002071680c0c0070300018800507940459814001d00380380c004245404e0340d400c0907a40620917102444007540102914035484249803a000b10352070100c0c2c0b4038010070b05 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 275007500 1250 275006250 275006269
    0x20c0d1212020705010b04111e0901030902031006080706090b0f28090504110c060f070e060412030906080403021f020d020c0a1a01080304060809070504050702150705090f 75
    0x320350408205a48070301c1580c50583e00712450555080e50369601c20390301030410780600b50055130700402040c80d060102c004520082540780d038000d110100441c40e10083d9000b5449100481d40007801c55100416110920340039150b54026070840c1d015855000a10300d010302c04101c01daa0b03100d514503007490b0030303285d0000b000d4000902c40000070444801c1c9044201a0494003811608556140c12a15040c1800d1100391201e0160a0844810401c19100701007004601360350080d400c0d00e031150580d00c1d400e00031141680414400ea0b40030500180008000c0d01d080a800c80880c42500c481d40410f540d00070580c0c07020f804442c040e0250704013502a45c0d003c22541c94220f1100c2c60b40e24010b0508503001580c1d003c80c1c2140c42d00243c9a4814400401070207005041309691016441424070300d0741c10f06038583c0e21382c002ea104020501031154080f40001c0001c1c800040030303040c05881000580fa11060081da2803000d072114841601e4140d002c22416031280301224000000070340b80303820b4045100188601040d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 275008750 1250 275007500 275007533
    0x120c030c0c12031103030c04060c02030a0219080606030a02010504120c180f05010504020a1e0302190302041e081903170c2512140702041b020d020c0d 66
    0x30000c414000100c000461001400150102d40b5500b503031450064a14030f0a520002d44943c0180204001c41411004407401e1301c00c01d103403407410305006101080c5070681c0148000e60040342c50741180045000152803400301c5031480d088490940354407040c107482d0741c0003003400384c00102c4c108070501a10040f4444c06684a10900c0c003402c1007a034650500030340400c0c41841039006a11412442e00150150041c0742c0500801ca070114030342841d200c2c02801c000c01c00b051000b064290000c21050703c50082e030503580340e0804040540307074a52176840b00900a5219008031924180101048260824191041010b90380100700600c016032411034103403040c40104904900b04201c50b22030009084c00c4080c054000c00a01c01c0d0a501da0031415036070b128412103454804200710b4101883d46c081296260000807505060612504105d454440d40941e44150b40c0e01a4001d03061601142801107440440000c507180c0380d00b5034500c912200d804989409068401c0c41d0702070804070406005c545e00d4007070f003080034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 275010000 1250 275008750 275008757
    0x90509070e0d030f110601051e032a0a060302030615092206030b1f2303010c080402010e060a09031112060f0a060f060219080c03040f03020f0607120c03 67
    0x404000004402d21003080c0100e0000b0032512409070060741110191003408031101c0500400e604000c041a4061000000d180000418420b070390299101401902c5062a404103080e1030880070340600c0780f41c20400c1b000705000300b20074003000a8561281c400e6070f000707120040c00700c1013207028030020250b03e80006581580c00080c2d288030644050112200c5008006410404596180781d03041c1b144003000010b1410505555004034100811a002900402e4601541010705e90b030108805000104007074030440d03900f42d1319040c80038049681040c0894407840c400d0360758400120508040c8011409000401c01c0896104001440003442014050300440750140c81d1001c21102e0345030041c43c21400342c4218102c80c01100c107008049542d40030720005051026001c810b585e1401000a6507100d284400c4c070507080e01307901040d0801c42c09004544050440f0800c4a48494a8603000c00203004a440100d100328040500c2401a0a02c0c009070f030740098011142040090fa440001d541e80701c02000f08a080 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 275011250 1250 275010000 275010017
    0x2040204050a0e06090f060109030311070b0c01050a0b060c0a06050a1b081f05150a09090203100501020f0616120609020313060b330409020a050a08010b030709050907 73
    0x1a0b440b90312148009150402442032039081040c1480170900000e810a04030207500b20401c02c840c0d030072a60020032603078075140c80c43c0c403248901c0526040240a8106e005070740c2000450942003101500050700404100204104826034041004601c4c800c1d054805d040d50862a8220041905640141c3c0d00a5141102041d84000c041418107028001400c580119612100f40084184619111002d211690f50360048081c02c1c200020300350100002c000310340c014002a070003583c910854241000b0005e01000350744a00f00481c640d220749205010f40d074010300c20341400d01c00344640011407034040c0ba0070035021800c40203220811114035600d02c80c5200d0b40c540721800041e0b03072409440118420103038603030551800e21543c503000302542c0301400814400c0400307001c0b102c180000c0d001d04a07100e03155151003107185c0301c00000d0080b01e4052039100c0c90ba1544089a8005078903040001003024004c80d51b124026030b82c07039650003c4580001d8402400041e41e0070410701003170801039040c40e04a4001d090100d034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 275012500 1250 275011250 275011259
    0xf01050a09180c090c12050f1504090f03020c01020c03070b0301061419020d030524010302340b010b16080a0c050d1d01020d020c040507211a10050a080402040204 71
    0x50500d401d60244102943d1161540c0f0304560000e500204581286c0703051020f828815101041c5103006440494000c400d814840c03499566648951701140c0d125001000034589030030043d4940c29094210350150180d00c2c6159200d150202d40c040581c0c00030301e42e150071030f400c0603800c4030000035001c2c2e000000030040244101b0552002c0c0810040400d5600401a60508140040c20344d400070b0410742c47c13548000b00380200d041d01c2440cd40c4000c40203180050b00c0322400d0382c3c965000a102051318109107400540607105251200c800308100d40540032841d116660b41d10f01072007034812199540900204501407100244180b4002d00c051030061401c09640304851702d8940c14404820703600d00110707810211205400c8500758810208c1c820900180c0703100308602c1006915600c140030003c1c410f036502d000240c040e81c004d041c00450303c04d450202c1c20112101443c440002e025110780500c0d648500300300c2032410310301100245012202d03a075460307040c179050f04e80c141c406000281c1f089134065024040480c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 275013750 1250 275012500 275012513
    0x312010b040618080a110a17010b09060f10050703021501080d09050303030603030d050604060305030a020d11010b010e04020706060b13051e01301404020102060f01050a0918 76
    0x6010300508410141e940c1e140c035502505003840c0c1c00703c810740440086800c001c030940c081340b43c42c911904001c44500c3e07020601c0028422050f1a0005040349550300d000701c00d642015400301ea00400305a0301c260340c6450700d504204a0f6440d48440c03d03400030303403550202d41c000e2050000d046098130900445020400889916040c41d509030042d440c240d204800c2c4110890b4000907400c018041540a54039508182020a80340d1041c02c400c00c640544a00204940c1d071690b50100004641040540ba100c5450a600030740b100c044141090005483c5620000c0c415811301c101c040b880d0b4161914141e14200c4010303c000380d00b101d001541c000d81c4c1c0300c400044a4521400405031070203005d249441a81c00c150070020543d82034504034400c00b202e0034050115980000c0b811803242c9a02400451140040c640300c004c608001d244200424105900180d49024503003416028034800d0b020f40340c0d6a1f0742c6800385002401e00b44101c1307a00c03030405807080000c1041940006540c0c0c0002c46e0545180f21f040e161503 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 275015000 1250 275013750 275013787
    0x50c0c0901061125140a090213170f03040e07030905010c051314030601052101020a05030a0615270b13030311030a02030702040f09060f060906050303270303 69
    0xc100d581e1000f40c1c00901c144000070b469541c0c0880e2074080b048101c603581c480b81960007150064164200c0ba003106984c0c03105002c004180307510b1305550381c11012200d80030380d0149224620503035401e28001a0b010001007204091307054842e00035420305145c944071021211005c1c0000003070654525141006c03c8082c0a0a032081561b80c46490703a9a0180d00080e40400c031581c0304104030609280c0415065801194140c1110710032211021103204e001503241080c44d0030203082075a58400a08001e960382c004014512034007031160300301703c0385555000a031000094101c01a000892104241c0d100303005800981c46120607242c1600341e07864440201581c4da41c071014030304281d12500c10b010002c26520041c20480041c0a0020b54140fa04800b806036803400f54a900900c6151201c4900c40c0c030b944c90340d100029603604003206100c00d001444210000786118060342a030142009008621400c0003c01c95104e00d0f00400c1504041074240764080c0c0003182051040c1d4140401c000540e2014a004c918 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 275016250 1250 275015000 275015009
    0xc0f11040510050910060e0d0201110f0109030e0603011815080d111612060507050d060b0d140c0702090603190309060813080a050c01110c0a02090f01080a03050c0c0901 74
    0x900102d030406042013046100209000b2007045985014001c007503112403100740500040d640d0348070002e8a840165000e101c541292140d52259400e10082c82c1c8054009010f01da0080e240c103030400c9110b005110485c8000d000349034015003040386010162486600c540f4000d44101c5060208a85a099180c1030004905020002800c3c840380086001c00074080d040d048561008a0642c0c0d03450180c01d548052031041c0d002e00825030780d0b000200d500707004004443d11030003941010070600d911000c40b0380340c030340100d101c22500c94606199110004140c0142c01d00507401c3e0310401e400c00c0c83d0f907405c2200f80c1400401682d094021000d02d001440d0580007160001d5129807200392030207040000c001c102c2d5000400701158503800c00182d002140d486000c0390700518043c030309241e4804404014601610502250301446400021440742100c1d000c00c030f010040340f003100c840c595504c89490702040204207006a50f81600004006400603005500411000d607003c0141d620f11001075002a0441009a01 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 275017500 1250 275016250 275016271
    0x4110703030b03010504030207062d08041217160c1a0f07140304020904050a14100f02090310180f050604030e03011a0f010504030203060a0b09060a03030c0f110405 72
    0x154a010560140641542503800750000c00c024a02a10000e60ba42c215200320303011320140b44000300350100b804c5c21541c5114003240c20410301c400c0d034007001481040c08a50603280b111101081c10360f4a481005164540c42096100f0917a94071340300d040b0310040b00914840340030b00c0103c452400000e604440e02d0f011520079100808510b141c420815021220020000400c000c5640c0440500041010980390000d80543c0e038404103950b00c0c64280e207851921b43d4040c040c4641c40700c40600c1c08034001400401030361a82c2040c00b007203010b0956a030980c0210000242d042c1c003c0da005401c80c015030b42c007141c504503035186090b0703071a42c0e651119052302e15680c100f500d903034100004000525030440d44a511a039415402001207580008520900044040003684580c50654601509070312403429140a541c004080d54a1410003840307442c020420941c943e4020146000010014a0036031542011243c140d21400310f04016541e51442110012900700c0d00212680c3e0500b0b20740c0c9452085910a02c1c5280d07 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 275018750 1250 275017500 275017507
    0x20d050c0a090f290705030c0c03070f0602030f21042f06070b0910020a1715090a050705280e060c100e030c0102071209060203031b03060f0411 63
    0xa200800344900b40d00080d5544540d01d00c10001d100300000d04003c080308940b4000941c0e0044942d80085218040001d4054400416414402e00c2d000c150300248610440468100742d5072035042a0a0204502c56600984c02c00d21031000907103035040040c03990700642d1940c805001c0d05070444208a14050780c007550450000e011a059141011010028146001c103103500340c1c16020700051103500c920307440107000b001200c0128840b1102000041c0b19401c1c0361000390344400b00c940b001002d09064003158034441d14100041281d00314600b040307048819004d07090b07007002ea68880c09100984800307031100041010400000e00301d4241e0081e103030129104d9804c5100d242c803000c0c800800154000d000940b0507a410404900545c0300056000d059403822400402c0c2c00252020301420360090035200300040d40001141802c100f6080404915808030b82c40e01c506154030744500320b0380d034041201c0c0074104c607100040b4200c0c2040ea0901640c0d01a000500102d2480750400102c2d0580b0f04110302508a440c011 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 275020000 1250 275018750 275018767
    0x19050709030c0e0c0d0c030b0a09090215161e0206040e0411030106060f0f260612010207051e030c0a050106090e010b0d020411070f050d120903090315020d050c 70
    0x1680c80050104103d40c61142c01c04003905810ba00c01c81d40d070094540d0766004000c089034001e0308419910a4003d04c041c1407503686803422009024644030407445403280c500c03041d0b1504020000c3d00d03a1001100165000c9a2440c1d03150588a0401c025120303115034800f0a410040e52030b02c00a10140480b021440c95600f094981700e0092001e14041b14480c1e4104101445569401915142080d6591500000a41d00040c2c280c4c0c1500f00c2107008846440002004100d00c514410700380d004180c2500c3c1c28240c40c485c800824201e02030000300810320380080c5012101e200e11100785080e8440a401034030b04e03021303901c85020f10f003101503130044490307944411080058200510030002071018075402441144c0119000503103a80708958000c0c03207035980e04540d481001d10801039400e02075000107960b50804081c1412642e4042400788140091070307507031041ea02c508180c041e5402141d419210a01c2803415503559015440758000c0002e5101c0e4240a07140c2c0b565840e00409014003110340900f48c2d501d502 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 275021250 1250 275020000 275020013
    0xf0c19030f020105040210030c030e03030108070518010f05040b04060503030c060403030c050403150e0c030f0f06070504120204050403140403031d01050406020607081005121005011e0504051905070903 88
    0x50703042030080da490f00041002503110100c104030003c40380d00d800980c219501506500070103841e60023420502c000310000c20401300000380b681c15168219a0224401030307050203030750100720902a400810741e81c0c0ea020852801c0a4110030500e0728018004110a621007001c2071450300581d4000089a22071000d000a2580511070448010580d240503841c01b800e6403a120000d40740780e25840300040d80c0308080e6101000600840d003284100405460340403d00000261ba10b000d885100749041c018140131992050040040390202c809941940503220882e8007000001c01000300242c1c00c2c800000d04a00c10b55080000a0025512070788400001e03e082c11405510144c0400085060003400c00050000680008159601c000146410308095a4082c42074186004582c0010b07004001d0b040d900000c000d011034007541070b101b440010007960380d0390290000c98401464503003201e0b1419101c04d01003414250070031030f4001003440c10010108103a498400440303000302c4e910300020b280b0403030600800c140c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 275022500 1250 275021250 275021267
    0x403030b0a0807060e210d1107141509042d0f05040515090708070603020a02060703060522060b0304060209090703052203170a0c090e1b0f0c1903 64
    0x1607480081c400f09091810191110b001001c100d40309103540358001c1d004200034242030064030714160075500110385501c2e01400190301e44114006a0042800100d800d46070b513000b80149110052000091009030800d411030380c4d01282c059070b04603071203003079402043e80e40c070490003010762500c10075040d041d209403511004c4440c00c2220b500c00c2810031003800040b58000607400014007a8622024080c0c961200003461b10521754801400c601521078001181c80c0c166014280d80c000a400faa00300b60b44018003201110141e000e00c0d68011214000520340ca24944001808480102800282d254440b0503070301807074008039400c07120103800043e03001c0380703040900500350029480c1c202403045051100b4250703c1594480d004141e0703260300c11009010315103d2040c4100c0d090501c1c402c1005410034000c800041d040e0100ba410104000840008140c103401c51894803c4240440700290305017900c0c0811260f81c4001580f000c45401441554035601c81070000c541c40d401c0d8040070b11400006458060084030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 275023750 1250 275022500 275022509
    0x20c1005030609010905060d05060f0103020f0d15020a0320030603070e13020616020612040c23040f02040b0a0f3b031018140c150705070302090403030b0a 68
    0x2060091100c0d075128070f0074060655005400103d46552410003003002000b4030100030b821362160409010180c205808441c2c1601c0c000e50381307a00425011014000c03110860314008288007400d0160081c0038070301e51b0142417400991701e80885c0000810350b8004601c0b410646007070700184000f05003c0d061504200d204004c045464032083c480c60586160010900b40f04c00103030003140c00140028421000d0519080c00d6540100342c1502c40802d0783d0071b588030507405c40e41180e000f04140340104d50703451811a01d8028a001d082031680c01207a103001c0c040900352590340d210000c0d0b004c3c040401c0e1114410060610740e000c5503105200f0004440340208403180c80c0f14000e01540004240303501d45406002c2d0003200c0118100c2c82011341d01c01c0e1021a2620284d61104a0440d240c40040800406c203d44c00c80321103030203030020300c0442c107000c400070341c03210159407006621400b0184502c11a500fa10042c00480f40078000b41c40c03003580c0e0b0b50003240c4404011a001c41c00240d0722501200a803408914000280 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 275025000 1250 275023750 275023757
    0x5060a0e04092405340c05030409090b0f0c19031112010e0f060616030302090d12050717040602060415020705120a020d0311041202030c0303040603140f09060406020703050c0d020c10 80
    0x12150003181040900b115040c8406c114942d0b4001e001e001080048900030404c00004101a0302141000120024199181c0034101074030408100c859007180c0c1902c0602e07246454058024003a1001500100358174001d04490748014008000311070303810440f847c000c1514041d081440d00c3c2104030280f20700d2000700030902c034060174003c0c80103292036020740410321070703050800581d1060b071000010001101200020b000403110301d8a0b0130103c0c0e00070090710465202d1030714000710b260201c2c1c080141c0d0060380280030060b40075400180109400141c0b01d0a125030651005180648a8840508080d541c0203404809040050510740c580d60420203143c142c0d03018501000f00c00d1500044044900c00c610a0801b0110b2105400095590620110300c52000050460303030f4403035592501501030b22900841907180300014001a40141d1a1001c0612130480200078244940d04c90342c0d0f6500075086150250304008081c0442c41d880a010040390400d0036881d0000c01e88061780c4010040e0032090700880384100f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 275026250 1250 275025000 275025061
    0x40903091d041a04170906130315150e2206090302010c0806030a05070603110c0115030209061002070b030c0c0d0206012c060d14060a09060605060a0e04092405 70
    0x1704040c800c04120690030000380c1c9944012000010301d4500039036492551a018a5000204000940802d200b03040b00c807110921605e0f4407000c4004440142e0300ca4240031328040c4000420385850441c039070000a01021003d05920302035155181110489102140980c2d5910440306089400104c502d40c803070700c00c4004281410070369175103944500a0b0b20ae12400d141d21030548504030715141041d201c1d4503021a0003041201200419207103402d031241702c241c0c0149168004a0031a0600d800011003d02c5950001c2c04601c0c64400300300569400101a403650141c05c0c001402000c9050108441b00a104d50080115504140c2c2002101d2105c504201d01e01d01d02c04280841c8184600741e965126030102e07a0866901014240b409a840d22040d1000b00350142e03004001a030340c199408540114090032003005420303110300c00e00500c0d00c5903513101804280300c824041e4180c03415030040b106040c450022400301044103002c8a154664140c03109003616182e0382002031384241c0c5144a02d012406500c0d20700b2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 275027500 1250 275026250 275026253
    0x80d02041d190b06161a011502031204020105040e0a0219020f0c061e0a020a05010e0c0901031410020a050c010e06101701020408161409070509040903091d041a04 71
    0xd1082c0c4010b40780340b81c40b40004400741d40c0700e41c161015882074011494680645142041c8414214034a01c4074001a1400115000244104104040c92640c0056240040e002c4004140f5140244100d040200401000c03d407161032110180c0521188070700943c54850580b0340051400140d01e22108540c8004c903140d0b42c07202d0018205611600030780c0c000d0307540c0300d01d10034210312048240d0154550080c006208418668000f60000805001d07030300030003504845a850541750381c402c04c00a070340010791000600200f05403200c1c2081041c100310840b01880e0740b9040038411b030f0b0030600d201c0000c65004250707411601c03801c1c01441006010080038102a140051421014008601a203015041240d000d501001c1c425411980981490703411a07030ba024004521844d030880c603002d05140c0c001002050301c920306140c2c481500a0034070740c549500300f80514050000034003980105408210b0714000010700101041040d0aa801c2e03984c1c901c401514090402c82c0003000304407031401482d40c00004000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 275028750 1250 275027500 275027521
    0x7060b10030e1c0e1e01090605030417300105010e04060e0711030409050c04030c140904020f03010b09010f091d03070201120603020907020a03080603011e0c050403080d02041d 77
    0x3a003440c0b00f0884420104514104a403802052440c05411202c00700d064101c04030201400c004842099032088902d0b5141d0500b01e50901081e5002001c2401e24650716a480340000050038030180900703c0c000036225100700300f10340e4108203d4054600720115005200319680310904009000c01545c06101c078514180b41c80311916001409071080000a8428440003a8140101e400400113610b090089052820303280702d072030380240310440d1000100300b07000400d65650b000201c50201d000b003818401c1e42e5030b81c0138410b942c0303103c405080d49035581e5103940b8180d0381c645160034060900707601000c0c00e0904201034003086861702070840b0050300300c0c400c07410205000001114401c69085c42c144c250b0100d11b80d58240988826007000b90b0003a020810000050341c00118070948601030780d1640c0305510791405141c200d4812107108101c45603010440082004e164001d048492090318100e450700395642c65820440e040701a405d403c094001608000310b0000c3c43c16585000c4200724007000307501b01038441c81c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 275030000 1250 275028750 275028763
    0x606030a03170c0403050a05010e1b0306072115090e0f0d140403060203280606050406032703021c0810050904060608010c0201140903090306190b0607060b10030e 71
    0x20b010003118400007014442020291801584d01100f1180320000034907059000e04507184082d1024070580c0034920b0000040d4610894080e0050060030a58640000487c0c14000000026500c070043e1445400d132015581f00b086130210203c1352868400e420404500152460902d0032020fa612a8103242210035010030358542c80d5403103080103400300c10040f6490303005020b00d92014000e68804000c002c1c44103620114260f00e400d001260312840d000f01510441101c50f00e001d450005102800203004030b60282c2c0c00001901080b040413004d07098400c0034200e20ba6002a070407070058206404003058805024040428083c0505201075a40303001d6a0000c05d206d5030b4419a4030031552500441c09201c15a031203030f00940280c800270b0240c44030f031140180c007030030b0181614034001d8102800102c504901000b9a400c00c0707801800307412030341c03510307008152101503076213083c15001d175508008202565030b18020043c2c2d5210b100003003054400b00b420003c40618400a06003070608000304901c5203039001c145c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 275031250 1250 275030000 275030027
    0x7030c0b07060f0c09033e06040509070c0201111209061b0109061a010801140120060a1a0609130203070e04053904050f130c110606030a03 61
    0x251120070300c0c00c011026082c10880315040c0d501d001c0003000c049500c582d006064038010300f1a01019045011052078018945000c1020800c20506040888100b400d40c0e0140404c01000b440c14030f600c4e540042d0010400f915881c0104030007174804411541c006600c030224541c102c0240800102c00301800c0014800c0c080c0791803090f5400121f40503d000d800ca000c000000d0020020407180c9038601d0217000401c901c8099084448408146100d01d42c40340c01e909045e50160400e45c048514440019a0743c115104a40741400402041d02d0403030810400c8502c2c0f00d441c1e11900443e41c081d81c0d41607000309580701032005008110400c102401038583c89044c69400d5038030000185d4969520008030b850300003000940d80d02c85c0c02e00e4148080c04101c0039030040d440c0400030003e900b5900700d090215444942505051202e60144804c004a00d0310070410130102101920020303038400c0c1e0250b420120307030501c81040c0c04a98010b143c0580544c00f04030342940081e090700145000040780e100904a0070041e0903 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 275032500 1250 275031250 275031269
    0x10e040f060906020a200d0c02040906020f0309030702040b010f0206130809030a1113050f0a021602060705100b0a0503030403060e030415050a021005240301270507050307030c 77
    0x5880e040101d01e41c002e402054200c1011901c0d4015800001d05000c65010115452607081c1000c01c41818042a11407090400342c071485120031996003800040c241c400401e47d078041e400e000b01c4d104011500000c0d07108504070405142c1d25480c900c1048211192003026a040040d01c5025107a102e40000d90039401c890170303282480610420303260504580c8111040203070075015121590042140b40307a030795909090704a68109231920750b80800c038119242141c07200c41c91f003010f202141c0a5030300b0b50f009041d02005d01c0c00c001e12402e2542c0115440340e02c02c65045a459120328150000000340b03111b52299458212100c03242c641c80c10b0b00190b502d0103a40000f524403655140400450725041045038000d05240700340d1610010000809042500591254805801014009240c506403446120310545a1002c2020403405040200180c0c0303404d0001180c02d90340e201d40d80300d00c00c0e881c1014a032955022014500508a040c9062400d105d085e80c411806548200014030024468005100541d44c0d1080c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 275033750 1250 275032500 275032523
    0x3120c0c03060c0908060a05070c0821010b0d050a0903271a030108071203050f0f0d060803090a08061303081003241d10050a0e0132010e04 61
    0x80408140c255a4070042c03200d881d050022101d0f40e00161000c0454880009135001541d0b84d040c120241c810031180744000422a00c42c10b0000303a4048041c0c00b181803203126201981c102c0039190b100620083c0c0111a60401c081345000680101c0c0c0240c0e640858092424000c111080d030300900316550a54050710f01400e20b0110b0780f11140340c0140300004110400201c4510651b00c0540c800700e610a02403595503004050002c141c0520b05802100c000727505a484c1850000b04c51030484141e04030300011000108100100042c0d10f00754080d040240105001455507000d0581c10080d421400703601141c8140c2100c001c20050b4003c951000e1012901800c0011030303951100c1500c400004590801007101204d800002c40f150344011044095224800b01084001c800101c0780c085c2d040f51041c1d1032000c4e40302100f102c0b800303101d54114540041484030045440e29440c1c40082c20343d029850003000b88511041c1418644152515003400c5920110310f00d0b6042d418100d12441d0150000c1001e4940346004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 275035000 1250 275033750 275033753
    0x4020c0c120a0203100c030b09040c1203030b060a11060106091214121303020f010809030d0b03010b030a030302180603041a06011407210206071704150603082203120c 73
    0x42c041d1a03079070b5a000703040c1c43d09403900d8034000b0b0042c0708001e000c100207403805c03104060f28101641c200c2e014130b4110940e0420940342000c11165010301d041c040f0100754480d49581c0030303074a402c0041c040c9401680c031500d40c00075403a0111071504605a1141d41001b050241c01c002900b440d952040e6010342161815802c0207028100b0386c0ba290414100030700900300018007a00c038040020081c42942e20071602560008903c000448105c0c40c180d9078a80c543e0410400f007290740546502c5104070a10190010840340c8040002034100050328134180c010a400151040240c20070000c100d66241c000c0b2121030960400b5200c41d6840000126007480c0c1207001808507000780c0c00b425443d424100c2001c6500d40e40d124a1610401005d00c1c0480c1c0d40e80c14000c104000388480c0040b586500c5080e5940c0d8156001e0202580d00c001501e020700251008228407450740c2500e0464014140614080c0c12001c2c0d80381d10b95855100c1c0039400c11000040918804004d0002038030140c1d00d020f41801e04e20344944501c019 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 275036250 1250 275035000 275035003
    0x30b010c060216050303180105150f0d0f0507060f0806060a0c08030a15090219020f0327040203010e1006090608131a090607030c03061217040b0d05041104020c0c12 72
    0x86070150017440080108203c00c80c1440f4200b0381d0141c414028015a2030b070f5445031b140c0354070b00f2804c15031110103030386614101d0428412501841c1d01071880d1040090142d11982d00f40907a640001000a640c206400d0150f0780148042e40c01c04401e4400b40d00d810400074000f0703c92200410010120351300003010900f01c0b241508440f000c0d05103001000d0000c1d0392483c00400950019200502c0d0b480413020f84030803d400071440a84d00c3d281c00019620b01140200038060542c500307610a5256200440008407a4840d407000d103018041c2c2c0e195200103400c000790480300d21213499100300c00f000094074044c01200e40c80703108907801c00340000e40104070380c4061074000a01c540082510004084560800c81da014000480324064400ea03202048021443d038411025142540207852884103811021400580c0f040000e001c05c40341d103e00a424181c44284109a40e8440d01c40011540d0f02c0e17500780001d0141e01d81c03810b101d0310000c4604602c2e000d4240f0410342c40f00c0030201140e101348914600c40600620 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 275037500 1250 275036250 275036287
    0xc0910030b041505100609081501030809031920091e070c02040e10110403020d0b0a0b0d060905061e070f110703030c0b090d1407080904050f040210030b010c0602 71
    0x10400300780a11700d000800b442c200d903020f10030071002072a04013000890f00404960a00030003100c41c0b510381a40c1c00e64a079412039611030100c043d0148200c00310710343c0d100b00012200c15154458420101c51842705a80e10b10010781030308115100d03c00c400140010622042103000d0150000644020907583c1c40c83c040c1c848103240c0303901035001824412001c400d000c1c00b01c0c4a48403600d095800300070154240050145034025804002c0d0801201407045010808506150794071810a282c01305410780c1c0c04002c81d6561a44210445042c3d0f1158412020030000340b25036544031800d8402050704803520803001c2e074860ba0280c0306005200c0400010105030f403045000170500207a100894184950b6454000c1c00400030800a07141c000c0074801040b03110401003031442c150f180035034841d515048a0424800c440d4800c040c11544ca540401c6204000d84403802058840d10400b440100c0a20300350042c8040030f2003001c5a04101460b08a804882e82e80200303030000e02c84d400840040c0c55620307550081c03241c1e07035 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 275038750 1250 275037500 275037533
    0x1306051503010b0a0f2102120106050f0702150915070c0617070f0e0411130f0609031506030b01060c03030e0f1b150f13090204031205030402030102090a0b03090c0910030b04 76
    0x2940341040784a5030741d41d600105103444412800c550b441e81d07580c0b42100d60340940c0015580c334000400101c0058604049800444044104868030384010f1600050328108840c800440819011941c00103210082c0200070050500b070500c031003915900741e0342c042c1c0c5c41d1340201068244100304c0000c0580321f119403481410180058020400303010101c040140d070307403c280d80740e078250342c0c1c181400700324006c0301324140d01101d030a03807101c941580c116910340d00000c0203043c412025550340c0c0c00c0000801c800002507070007001540c403020b000c80c0c69400c0080c00e4440d0241d084290f45e00261036014600c0c40004c60000140764007001406d50b2103c40005003248611420b621410500800c06002e98a03504008050b800f080a4800072080e031350310400402c1e801144400303001c1500c800300030211940560021984540300400061405d803040e00025a05d150513008003050b0880481084410b11040294140554080f680758000740341034070490b1045901800000e002c03441d1f19020034100015096080c2d21071 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 275040000 1250 275038750 275038787
    0x103210309061a0a06090302030a17072013021303021e18060a12030806090a11032e03050303130804080f3d0c0207051306051503010b0a0f 61
    0x80750050104121003c1107040684903600348500014500d00880720942180d034080d010f0000c0014076201c0ca41d010100150f036510b042000c0141d500020120503207045c048004944000d010200c0d8801d00010620a0109181441c41007140070400113030000840d044a90440d040f40c424000052440c40c1300007139109460300445c00070000525441c01c40c4042c0d108200994404207065966900301d1540c05070244058040703030804000c0b4405050480106a000585c00c03000301d04080962014101c5a100f140c0705018808038a842000c2050302100c50310b91104074400000d210307404c503100d8948074800a042111284da5030720703400013049440020341c1c004102c100107491466400c01c42aa44421540382100c021407100e03028080b15840f015440e26922031441f603408000d08075410305000401e40304400400f54811060000303901d0381d400500051a226442d00400d00500d86008d11241e8030070058810300c0039070180014030030820148145c0741c121710701d031230b05803001d1210800030b8602d4034560030f508219 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 275041250 1250 275040000 275040011
    0x1e04020d0605030d02060403080a050408090604031a01080d0f05070f0503120f06040c09050607030207090507112419060906030f03081008031b010e06070c1a010321030906 75
    0x16030015900c41c0e0100d400940c280e900764804040c00326103400e000c54008011400d48000314154481552005621a204041395441c1400780f01c0041c1c110707001944200c4e198010b011000800200e403102071801410450000c05003240803d2001c0c10900030be08604041180c042428003d20540b0005001c00580203410382e0395503500d0001020708640700319070f182402540e00c4080b400131305140c03107800303c44112072b5580180b02d400c0504000140d800101c2c1903003148a0300c01d0205048206104071409111907880c2e201000341140a001e06042000c5040b010040c003c4480350340c030001898816601940e0300400120002801d03c41c00000d00d42c5070010318041d8908040401004401d003c079a001500903228000156103d01600c0c5007500b050240940076081032050250b203081d40c000d540040c7d41c102d0300100c3c40950042c0c0062925504451210021744400c892a045c01a0909a01c4400303640b00444002903041da200c0c0f205580b01035155582045c100c0e0151103482e88260300c66881c00d0b82c8160103000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 275042500 1250 275041250 275041267
    0xd02090d0c0518010503030304060b0102100c1e1814130e030306010e0303270102031605031e0c072306120105130903080a05040f08040e150f010c021e0402 68
    0x4006081c0a41405003145590f1040e4940c1c10385034050480304000c00540c0f40d82c3c0e8558406000c1d1040b60006815445680c5650482c1445800340002c15178599480018075800a150300f1b030700c0f890b079045400a20190080800c1080751185900095034042c6101030700021007040803460170707002000750401442c035018114417900740100c02075005050076600c0211500f8181c0404d5202e00c80c440c4004404118014000d04440e18500100901c180500590b03081c8007980d40c0480c01441c8440c02100e00c0d40001591039121013100b4010340460340d02480d035900340312030204a55510006030090740382c040503045501110804101041c9101d00014001e141c46040b45407006201180038007419208500c07600d54a4445c14a601c0703840180b0380c056441954503107481c00d500d401014080c0c002d81c0c1d8840c00d00e13406008550702e840104024140f00111101a10b8800c1d00d000050441c1d16200344903840f0980c01070f40d1680d01c049408a00c6030100c07020101c00d900031031040e2004803036070342c02900a0b001241844 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 275043750 1250 275042500 275042513
    0x100507051905090f1806040b040605040f27030813020607080406110d02010c0f110a020604180c261f06021b0306012115021605010b0109080d03020d02090d 68
    0xb80242082e030707200d4502042ca60410800c204000d100c5e086040e11790340003603068501038100f002d00c40c40251000528580b614003040c2074405501082641c503071210890140c00c801100070310304580c107e40f83e0440001030303030754010f000c0c6802a008681b07a26509107444255590902200c0300c1541c0140b050f0b80c1e60341c3d540e4010b00000d0b00d15102c05c0440c02003185e11044180103000300180c054443d500c55014800d110820354100c18120101c445600c90502890010f0329030f0801440130703040b00c102c81085801162150000c0e2007168492008001c0414844a84d1071000b0b4002c2040105928003040c482e40c5d00074442c1c0c04224440608640c582801600050a94010800400da43d114050601c0e409a054050503a01d000a100b05910200c1d05c2040f07620324501e6120b210030f0207120300c2c0c10019841418000b80c00f070b600020880f080301c100e1312580d50308005007403246400c596001c1c00d0240d0154a400d100c03507100ca40148202041c1034000401c039582072059030481c1c1000e2030041c0040c10b0301d1307010b04055 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 275045000 1250 275043750 275043757
    0x3180a03080117160902070305040b030c071b0f1205010b03120310080601051302090d080a031b0314040227040f050c0303161e020d051006050f03100507051905 70
    0x502903c0070455420411400c041410360721a9460001d00741c0007858240040b0007540000c50a03410820144800305520010030000c6000301050250f4035110700c82070034114403000040d1664185174005460821001c1840038900f000c8849034481c0451a040d6418054094180300e0003296140c0940c2c044d6401020210000c2e600510317400300105c01081c0c070784404660303c040c01c0c01125801948680e81e0440400c254000b001d42d450040d11052540035190307901c2e1400e4108883c0c0d040400d44958008070300e20309a1f46503180040040c07800744000204d41014000c1c6500290010307000e8410030300034060026001071140c1903004403602400ba9854541002e9092071809070781151a8011810349091903d4004207848242c040d0f850040000c1c8550342d0354800d400442c0c180108885c130640307020000b40e41e4455841c0d100301d0080001c1e20040c442c1d05400e83c100c0340d580c2c000702c4c81034a280c0b140d4032035520000345c9422400f440500010301ea13103444a0a03901d034001c89010249500828240145003030303011000c2c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 275046250 1250 275045000 275045009
    0x12030c0501050a180803070c0c08030304110d02012c0604081b01020105040b130c1a07020102010e01061208030402240408010605090106082a13030c0902130b03180a030801 75
    0x200b00c241c6420018000f919082d590074150061200c1c050b1011940d100015078000342281003044003149550340e102c000700c042c0d52000440344c00c04400c100c06e0003091108261451400c035600000e6052503800032700b45442480300c6254032000c0081c00d800ca03107038111840307889450090400341c071680d4591075166150b04002c80703c0c00c2c814020f030245a00d5401400b5442c0265441400c4c061079035141c07000600c0c004210f81041d070700c140d0348610028080e504810403e0920b020400016500c40ca035000190950b130340c2035105046a8500942041b032066107028150307405a2140d40700e941c0351101e000081000c1e080084019014038184e42003c0860304030340040c002c444102d002840466901c2c41003003521700c024442c0c0c201007a841400120318014034510310403c3c0e001c071f1880f070080303c50b001c800c40749c5900890fa5241102d0030050341801400300807117125000780700001003586002030181400d10304400500c03c0e401040c10100110b40740888160125010020440854480054908000b02265001e121b0b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 275047500 1250 275046250 275046253
    0x16030908011103040b0c0d05131407060e0d020103140c0903060a0c020309210703030908011811090603190b0a05060904030e0907050c060103080a0e03150604020a030612030c05 77
    0x100055040041c020120142c0306044801d007566141c2e100c00505030300041060055107010000c111901ca41071290b9801034008504c003091450309860940200d030000d556400859000e0342007001150b0b13000b042586800426203000740103464500c01a80909445080b14680b482e00300c041011b421001c402a10500008408554041e01c0384407115084500c80003d10005030010400a165400c2c1101034107003c8202c504010456002c178041641042501c0e0022000030b041c0000030490881c090003140f800c0920401c0700c00d00840180e07119100e030080c0d49041e41c05414660300160f00d56406002d10741064620481e408442c0005241010440a003190144c02051410b4040780c854103001800611480d89a203998181124040030042c00e048020040000c100e030401001d10348907020702c52a4003d601c5403202c1515500302d11030240540c1c41184c1a64081c0e80f03c0364513100341c3d8014404031500324405030f40050355408841d00440c058040d503006061a20802c0460a0403d9413004007401ca00b40902c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 275048750 1250 275047500 275047517
    0x30a0c020712030906030203060f040504060b0306060a060e0d1a0a09120e0d15020d020c1b03121b01021312020907050c0a201207060809010615030b151603 68
    0x10401200c0c2c00c5511001e00000c0650a0510013280a54011904880c004240342844807070300000800741c0b041283d04550f410344a014014260408000b6503800c003000312181034510b400c0c00781c0103000b6544000420700c11500c988a0b0300038012a07640d00c18a5400e02000c543e068606682c0633009003003004000c03140701010a405031207851007181c800041c0c4000a0449410044589400c1c920b9020407244d244e20f55420481640110007a00c020104c1100500103403400510304030030401c004401002190290b0000c0c400c00d510f48030101c00300c9402c0505508949044880034602c01e00a001e08408004084400540820501c043c010742040451003116129a03030754842034100e6040c00380c1036444115030700150203400005d003050b1102c00c04004214505090b20308800c00640c1d2070700395042c180100e0304802d10038848164400d0b441c50340084c45000070311100345044103045500c801d021003041099610202c503036442d0b07912400341d0307010b0820100c140d40b9441e0070b511494a080e09010220046007080307 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 275050000 1250 275048750 275048759
    0x50f0108100501211103031c060b04050f01050a0212070b18010b060f0c030d050f09071202010503130218180106090b06030c16140a0611130b1608030a0c0207 69
    0x10700482e07040c1c465038210800c9074005840184030181d451081100c5040550282482c030b910204003902907038106080d20040c040d882c00d0134004507043da821140103000204818000394540a6100c2003414003807a02564640450f08101d0514010f49180c17104803400140d0300303040c00b111031845805600710076090000b1001e041020780c00c0720040c8100c6500b01e0011320200d00c101400201621032841c108040e6447d0042400702c4004070b03141101c01845500100d010300070440c904002d01c201602c5881c91490700004035400103802404010910b02c0115080d4200c80c0864031114190941224000180d004500340710112001054428111454540c0391040004d1100c0c114040c0319400c10014041c40d145446041c60012103030700c050b01e404028034803d409000003950100249000110303000180000c01c20388d20b040c000751180940380801c0032406000c6295000c8450192400b03c80c200c41c070460391240c615000503801001c07854007404200010040200300b4a0b16080324224003002e031300307076108a901d8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 275051250 1250 275050000 275050033
    0x906060e010f0c0341130602030a1707050706050403110d090b030109020306030a02030d03051512100903120c090512010203010e0c09030106052d040506060706180501050f0108 77
    0x900e80240014508140300031900515240c5e401c08141d0414070304c41c0c221800ca0b440a040668641c00000d14280001c8140002031800e80e02e02c0a0180362001e5480e250356190f0003482100e40b440d2a18080f0004404198203900070030858003666030011040c890340c9000c1c1005460148880e2020140740079030701040c81c085101d28400c0c81500c46c04001c5900b16401c01b5900c0c402500001d0520390144079040740040580c0d030401c44003041c035116070385c08111483d1131601d041c18640142c5030381d03008040340860301540b41b1000c039080c40004034220300050382c0c080b41d09040b129484960b030003401051500e46000c3c102ca50202c8400c09451007914000d08402c0e800150070308130b1000740300d16941410350b0800b15a012079031600070301c0c103030a0040022030565201c2d000592460f83c41d041e4220002d0542251101100016400f4144250100c608200c50714201004c50740602ca020720003007010387d403440741c42c4001c0425403a4402d40394210008018926040c0300200a1241c00c1c000c41015101c0e405042040d41d41 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 275052500 1250 275051250 275051267
    0x703060f0f0506030d0c110a0803070507060207060f2109020a09020a0e030d0903170d020f091e100f110303090a021504050a05060304051e010614041a06130906060e010f 74
    0x301d5640f40038100c01c42d11403c1003040142403023580078140d08000540400b0810140c0800c40c0140c02030480240f6141000e480d00e4a25031020013400b0030149030800c500d4011002015850b20700180f140303000400c1491400074024a0300080d400b115100000c2000d04407a40034020080c42230300c4111031400e142040543d6810301860b040300091030312100744009040484507a20052140e2591400c1142600d0f21000740d810855201c064414081a0807469140201c1401c18030b032121252080700c2003064021400b1940c007015000705218440312909119407150400500031a014400d40741c40707061068981d5180c0d60038000c10792183d420303507000e1100306003004211021120010404824907242c942840100c0e00000e00c1599980100e41ca03000b01e031f541841c0c2918100242c500000b591904121a0451036505401c1181c0160b1500298031007180306010701c030b40c0c4610201c6819407101e14181c1090001d0080c0e8010f8650f480c03c01c9800a41d564004900002c043d000f40c850211200440b0000c454981 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 275053750 1250 275052500 275052523
    0x1412130f0f031e0510021923030c0403020a03080d150e1302010302090315060a0b130504110702030706180b07051b04020904090b0405061b040b0a020703060f0f050603 73
    0x1c00c509001c000080c6604245040803008010f2602601d00701e4950b07a003000152100250b4140e00043c05403c030100540c020068070209003032101c4111140b54041c1400d045242000804200000104006804400c00e48008540c01003c905480d0313101d20f00550349400034020b942481e07092218401401c0380c0d01c820352055034020000d4140d03541e17404d40216080d20085609905040c3d0030018450591410300c01c400040700004e03407404090070041c2c00d00a9001c00c6a0144180000900c0503068003075400d0215402c0f60411500030071045e217901c51b40c00480c801d20000a52610500d900010760300c1e00600205440350000e00345410b240e5903003011070303c6c510a10a00038919001a420306403c10750343d41c4032a01640001d0401401e01e00c031b800c045000c0b55060705040e80d0950401c010401001010401664019031f00c1c15a8110784240180c8a16940254000c491140c03002003844608030b03108120002c01540c0040003842207000c05c0b504100100300031128800c0a071300f80780c0092082d05000450301d0050b0b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 275055000 1250 275053750 275053769
    0x7061401080a060209010c0f050105090d03020a0203070b04050c0d03111c0504030201030221070504031b0e010b0304290105040c14030703020f0d06080c1003091e1412130f 75
    0x3016903c4500030761090807024107110344070f101c02003c00d19000045070942d00c0741e000001c4600f0001001480c11061100980806004003c1c03068256404402c0d66001c650040c0201010340342d915120f4200340c444418290880c200546d080c1c1450b42c480d050216501013481600d08220030103584140c285038020005d004110100300030030040d4802c0d170003410300f1180c200c8030381b0404207120b514800e900400e60307901d000a64007107024000c0c8490803c0403005142c1c11021150b82d1450f089a0090041c4148514074510b440800010b0911043d1590500040410003448098440c1d0361f01c103a01c18142030160b24011450441070405060081c50000680f400604800341141d492800860103584040c0000c0b14600c0b060207220104141805420040c1174030fa0058254000c050050006500550840400b0181000100c10228080c440c0c2c1c05006418900e281501c407030103081c5000000901c100e00d0b0403602c0345003424001044c3c0c00300549402c0004040c0304c8402175031745a00356000c01060085c071000d03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 275056250 1250 275055000 275055013
    0x4090321021e04210215250302010e0106051f030518030c1c02012315180714041401080c25050618280803070512010b041d0423030706140108 62
    0x118170710311b809000b588807d4005101e10038040c0c42034100f9120071190840140c3e450b0b170121800290203010f0a00034120a541c1b040c3c5a0113210415413240804014500c10725076541c0104141d10f259019031030810000000f12036a41d0001c0d400581d0780c01c00c00c14481009036080b0002c9000d2403060145400d42c1070640c58200713203078808078480311004038040d00702e100464000071070440585a40003280110740100c8580022860451400740c405844103003107001c0d5100410040c0010309020f6a80f03c00f004003860503400c5907860003468107030343c03103207040310f519018019030608804158980d9103012a407051043d140140c45820559074511a01000047c00b80c210d81501d00c2c3d07509a80b0100e946881c90003400101c1040103880302c464991090710700000160000890701110207180121034010900b0b042c007a4a003d141680c0d84040d030306001510b07000c0c18844000b03e8184044102d800b4840c242c00c0606003010011015100d68990201c50704545003820074199100007400b03203032014101c51042000d00003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 275057500 1250 275056250 275056279
    0x80702060f0709080a03031d030c1c1814040c02162d081e0a0b0a020d0b040203010803070618020609060a21020705060604090321021e042102 62
    0xd905401854001000f440e00c0b0009240344c0c00300000b80030b0501076100000c4400c02c1840400e03000440ca100700c012544200303d60403004a00042d200310310000b0314908603545c80301403c100d450041c8003100000040ca04000420b052008202003402c0300e01c2258100031302144044141d13203420190340034400c80040c029040204040030b24000f0f0300c0c00390391290004800c0700c41c002018840c10b80d0f00241d841c3d03845015035590742c00081c1d01c10b540c0602104001c0c0310070000703540c80749407900c0010480415150049074039a0040916080403101e0b44000f070003992a50b07114221269030340c000c0c0009070b4003e800d0050720103400b0984001102c2d6950080c107224503161503441403001039400401070204000c1c4641103070069401c62074040b648240383c00000359942c1001d00f0114640440075040c2d5100d1803418040e000000e4008840c001e604101401040b4038120380d8413008000d00400c0e843c0821405c00e0a1107000e00c410040040090300d01c604008041000d48050f404080f1305549002900103101201c0480c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 275058750 1250 275057500 275057521
    0x806090c0d09050a14060906130b01050f12010c030209011713020105071a0408040f0b0a021b0102030c16150f12180f060e061302012106050604030c051008070206 71
    0x1c01441c040c2044a0315a0740a0f5980843e000e00f1115174070040e08004140084503a00340b00b41c580200808070403540c43e185607190407035524410300c1017521404075449444a5622441e000301c80c1ca40b616002000b058003805806000780d40f02182442c0010040d0350007080420511300100e0054039820f0a01315050040c0d8010766140d40059815280300c0ba40c44511507580428060440c4210b200e5451143c4840c58440f00105079103080d0003031140b410f0240640380605a00040c0d0b40c0c540000c03d000c0c044640311640050b8254404c01da021005401085280c0c14451006481d0700300312a40341c00020326040c8081000c0b101c00304ca9101020014150303000301c81fa41d41c0ca0790024000d482c00040400300310342e0103640d01040c000103504102c4045498034100080c00f0000d10000d41d004200542009400e010350340001c2c06c103104100c1e84005401e072810030012040c2a5030004015007c00b80c0150743d04c64690070001d640312098810f4620a03840061440611449486140e0050069400401e044c0e1100031110 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 275060000 1250 275058750 275058761
    0x50711010507080708120f0103020d020108070306081213050f03070603090809060d05060102010501090509030a050c01060902040303050d0e03070c12060b0310140f100614280806090c0d 81
    0x21410030205000b00c402040407403000300110b40c801d1032000ea681c01d5412403412840f034003c0c55008402404401003003d41c45804e00c800c0000e509103410007403951044000d0380100038641140c040791294003c4040d545203032100800088030000400c410003581d410400500f1042c2540041d010b403c070010821410340a0340040500a2040c04040d0400c41680c0108505811080404a11507108c400380a61941c0a02c601c5001d0004103009002514240f04041d80d01d00c030b0080b0340d000b00207001400c14805c08080d4080b80103030010324815999071b070352420002d010380c1001000e564007501d171849901081c08000221001264403600304e0800f01d141c82105c201e00d040d080b02c2900c1d803030f1301c40240426980d4144444440160080790014812240d00102140f5290003031510380b81196a00c1404401158005900200c0c0c41d5854600b00640300b9508481c02801240303000391807008050750789a041c1203503082d0241e6000940c2c2d1001d2403aa201c0040081d01d01085c4d0b00140c3d0406c040050b80e03480040d40d0000d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 275061250 1250 275060000 275060033
    0x10081002250809041103010918110f040b03010c0206240108060d03110a0b09070801140c07050f06011d070318062003010801020306100519031d030a022503030507 71
    0x1080c01c0043c9034000c01c007030751054480004040400801031081c4001c0e80701d404020040c00030b920281403056a12241c40301c4442e0b0b4000c1c45080d00c05200003050b80c950308007650041001c0c00900c031461091902969650302a01d1801d60344042550703034400030190701340350311400105035255840c1f80ca45001303000010018010950411204103440c000e803c1c81085800042442181828854036090481f2030614910b40c0000000340d040c080500c00b14104080c0f0306800681c8103848a0ba6821580707440703454081c0140e804422801400000550f841030204546481d4107851098452583e17401421400c680c1d601c055401624541e05074800480c000b9844540890f5120420321807094400c0b00c42145070704244d22000c080d82d00001046400d080080c50000c0000030380c10305070b0604103c100c0845a1049180e0a101056a190f000f540841303a8807446159408408007070325611459108000c2d1910290703c1804e0555051501d0080205e54005c00b6104580d0140d941d281415038643e1000c01c40d0070007190 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 275062500 1250 275061250 275061263
    0xf18060807030221061207050915220504020301060e010b0a080709080703230c060301031121010b030705061606051306141006030b060403110310051008100225 70
    0x40da12040e80b11803402084841c0b6030f069810300c2c42e00c0340c10800c4440c00c0c1b00300013015800801c1b041200da01c0b992001d6402120314092101d0000318a008200d030b908125100c8041c44480e502c008000802d07541c4868042c9009034000d114481e02c8550030b0540c03001c01e101d0606140c400b0014845040d101d081100e030414460310b48101c0c0b590b925075a49140a2058000f80c40280e1906000c0b5a20030782c8072030040810917600d0143c40e08014540002d070a80c00140300182403505c00141d007001c50b60701d4100e04802c010050341040400702205c58803a00810984030000d020388100074020846240510039a13500503102d00d503400080005545590140502802d41414050a2101400000c3c0c040c01807011003440242414454540700400d1003c801302684044149450454814030329203c0e071040340d080e40d400c02940740c11580c84402007031600106c800000c10311440c1000f40f20390301c20b901d06500101d550400c201c83c102a00ca0100b803040340b0515101d141205200034050100142040340e8503005c5000b1070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 275063750 1250 275062500 275062507
    0x1303050d0b0901060906030501170303071d1509040f0e190204060302120f37030c0b180706080c04090e0f101d01020702180c2203030f180608070302 65
    0x20200780751580030303002440860110038041c001b440c0d0510855004040500c183c1d40c84045205115031079120183c000410081e41da1541a0004100c08010070703006000351101c101000c0b054581d0659800018043d4451414040c2c10b4064510cd070060762055203550010307005084880300300c0300c000da901c200101c2c0c0142e12000000b0241e61540c14003404a080100501304086022008604000218440081003080f01a203111102e05050b031003000c149000203203032400f28550074155540300e03204030001e1440b405003040040b400c001011240c2c104101404407540662126000c0d120382808841c0d5003101102408100102901030300a410050b00403070030780d40880d00624210b420060003960003c0c803d6201c0005080030340400000d200707142c107501d0085050401c15800200d81c3c3d5482c952101420900001046a20107498201c2d051254855400303000081004401c1d05c40081c40d06c016804580211040000d05001e104e66081724a10642811109030030074030300741c40201c40500100b0800d5070a0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 275065000 1250 275063750 275063771
    0x501381b03030f161701060804030504170f0106060c21030b0d05010c090e450a11010e060a030e0109020d0f0516140d02040e06010b0a03141303050d 65
    0x40c07005500074243c00056120b40d00d40900340240c0c5110b120340e200d00f04142404150000d281035010320341036070424038081c0ca41d07840310306085074503001e1900103541101014415070603d84000032801510102c4900034080306075282c03025034030048160750281c00980f002c00001913110890711008084192400c00264002d410008900d40400d0050f04840680d03507403422428442c1c0200760a00148102068a9428034142c032820b905084d600004640d801d0940d03050b002c1c0b0510072a01d600c0440e00c1c0d100d00441d00c400c1ca010960303035a9000702c0c040e100031502c080d80b010303254842d410315042c10b00050102c92a0110007a02100200b080c0382a24817030b07541c0c5518076401a562000c4010503030b405000154407030001400d105003441c100600c0d450030001582010024128840340c0443c20b45004c540a107907400c01400880c02900102004442038010b04001150350001e40000e05840c08880e941008014850306140d503854005540c46801005400c20303100010703200781e0080035085165040843d05182c0d1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 275066250 1250 275065000 275065003
    0x8031b07091d15060f06070609080a0c060e010506011709120d050105010f082406070204151a0c10050411040e0601170309100f09180501381b 62
    0x3030320804a00a50102200000c0402000304101001d4a601e1080f10f41c28081c000441c02104604070a02500021500800307010f904c2c1c1c0840820381d0426925541c0e502610401803444402040c02c0310300d1494440003c15020052140c0792181806842c1d4440c0f58481c7c14600850080c0144402c00600c00d000c03148202e03000b0310001e8030b80c1100000700460507504140002d0648840c0018040401040004000b031040d2980584210140503076800d00b85000c9071004101c0c50300ca0a44040d40050078610303003000124030f0040181c1224000c0501c0d0964080c1c4404030220740c402c4d00d007818100d512080070802c10b00c040d64081c0d40c00a204000e55003000844601080648041042d00b40b00d681045004200c00c40300241240550340e0054041c604d42510b0000054001c85481e00d58410010094815158a40038140690281402c090501140e000740e440c8440940750900800c00c000001442d01801e0009001003807983d003107803956001c40400da221881d02150008507001c00f00c3d40d02d1903c0c1c400d45480 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 275067500 1250 275066250 275066261
    0xa18200909040c1a0403020103060e060f10050d050906010608090d020601061407050109140d180b0a0c020a0f050102100c080a0908041d100803070b04110d06050106110f010608031b0709 81
    0x1034444c0069104c601e903000140441c1d03c103500c60384600c03a005c010400f143e0364840111043c2641103941c2d21203140f0f171503000c80d0300e0b0040070740300308070540341a040c0200340317000081076030403212560750b03180340e541e0b4007281c00c0c0e203a07070b00b9046890269202070300601c0403a01408030f8402011081d078085080c03010544460382500e034018006c0c1c4015200d25090040ac1c2c0303003031041d02000c0045007054407480e050b031f07510250036160921a1044003c000718806640900c40c6c00f0200700d25030000c1601c0c0c00e0689900d10000750128511501d07016100300614150744105500a0030307031100d42a103071780c04103540707507459440901040d250890344050700b080007140201a20300030303400d80ea040102e00f040e5440c1c80404240c0034280340c1c01c414040d500c10b1222400080740c80400981c072561047d803003140c00d813101d80480c0902550304001426581030400101e07280d50f001a00c07151809a1604031100521a1158503007240c00303e014600a0360810050004104d01c0312a00300c08002d151400c88542070390765000c1c04110750 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 275068750 1250 275067500 275067539
    0x118030516171201050f030c010503060a09061d0a290a05040f06050a0b0705030723010911040506010306061b14030d02040513060b0901080408090a18200909040c 71
    0x1043d40c81c8a901d4480500340540815100780c2d01118041e00043c0e6122406e40302541048070010028042c1d4540c801071200600790042c0034800302d030712280c058000c603404c0d40806211041040008032845c5050242c6d880c4180403081c010f40c000204181c2c00d0020701030804080d04460a01e000040ca91258491200182440040000d5171400c0404002041880c0d601904001ca401d100b00c070003143c2e000c811585840d0780540d903540e956040340c0032003080582c1c0d000e0b608559440c01180c80288184000342180c145402c0303074100030310364075038005404881c2140110300000c4c81c295246801103804080b180b2100e030091003101070841803900310300c0ca59408010782d40700c1039401050400c41c80c285090b00342110324056000340003013820000c10810034042d2566140c100003040d8082001d001c1d4070030803100c01400c01383c113010800344c80d00000d91240e0080035139030381020b10304540b403210680b1414105d607a0101c84c0704803901d45169181000b80c0c0c548068410381d0740e210024000200f03205e8056103d410030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 275070000 1250 275068750 275068793
    0x204021e0405030d020a080d050601180b03070305010b070506010303050a0216090c080c040315020304110d060c08011d1b0c070608040b0f09031e040b120a0e0118030516 74
    0x6070b0401c0149800c00403e00440802d41d40004078010000c0c2c80e250645e086409821800035180c1c0d6940d0048509078100030b0700110030304000a021038500081c4d0002c47c0700d01c0301d03a10705200e070f0b0340d0f1624a030380107228054010f40241c110800600c0040e2040c401803418413420320481c0d80303c0d08000050040c04019602843d406907441c81510f41b000c0d00034154650000715084410306003031542e1103400c280d84a00c000d0b140303182ea000000404020703282c1c8003c000507101800c801001340462030000b0040c600c040c3c240c2d011070142000050017284207208008401c2c0e091100c0b9100313882d10311210f9036884000c2009001d219041c440c40c880c4a0040145c803009140565510704d032808c00781000700c3c409201a108442001d1200708000e0b065400008580f0070720000098070b100d4440c2c84d0f400403014000c940061080040005800507030440c4e00300b001e4051013600e003040014503111041107013210f011442c0301040a030100c900c1d5000ca4082c0010b0107844801c072602810422051b40c400803000340248010891 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 275071250 1250 275070000 275070007
    0x1e120c19080106060f080f1b07080331030302090f030d080411040605010e09070309060f02042c0f100b16050c1219031b0303090302120306060706090204021e 69
    0x11070809014070001040b181c241710f0340704055020010701e1031000400039030086035a4400701c0c10680810303071904602d40c4401c0d038040d11084035242284003a802035540b4180b44944088286410b800c00e1100c0b5a019402c0c00030554011a9650a034040d42183c0449a48049194074043c03161b14140304120441682d40d803448075525041c42c1c0501c400b45d0074000c07140254682002842980d82000e407020070100c2c11030300080c0300e940e00701c400c9001c0c2001400081c5098242110f0b10341c52005500078006030351031900785108180c2d1040090b1462031000c0e600c18140540c074000b1500c402d0180b6900c6812000c003001403210300d0780b550140c800e25841100080d44000d8400084010b00c0740c144400302e40854111400411800205030065441000c0c40303414131654060940c0800300350107403407800000d42412045900c0d0414900f07000c0c1c0240b03600300f016405402152100c10034030070074000f283c0c883c11005041c0d44c14220203407124802000101012070304507508210042c014041c82c0445100c03441810100c0d40d0f0b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 275072500 1250 275071250 275071259
    0x2031b03032b0c020a12090506030103060e010f14070f02010519020f04090603080403061b08040209060d0c0e010e010816030f0f021806040b12060a051b0a080a0b1e120c19 75
    0x106c0c80c40801d001000701842003030000e5591082200c0c1101c1d0440c4002c80c5145084820300e00405540841d0050540340c40f1000c112502c9070f050a40c41490f043d19014031a02c038030070341030f4241d50307044640d4a07030007858030440c024a5000b513026044590300c50b18107504298480840c041101da00c0d4000352540341001c2801c104001260045100780800000200000c00d00184060200c0c480a0802032282080400041c1203880345031185d0007064200780c0074510309aa600584103010000c1c003511016845030400400c1c40c40700003506440384200440310b2044145151595004052020822512859014848400b40e901c4241d00c407800302d807402c4e109180c0d0a0810420045440007004640200890b0718507030100308010401030760110a10101103601d03078943c0c0100b2624562446c01001c0c2140104140d01c48039071281665101d440390b42c00802800844000f00300318140d5602e0802444610f0001c0c10000e41020a01c82030b0060040c401c0b1503400d2060000240c84024a230403004c08030003110300420 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 275073750 1250 275072500 275072513
    0x1203020708100b04180b06010c0201030f0f0e0f061611160b0901030e0c0307050f1c0f0c0503120702061c1a0a21021207080604060902031b03032b0c020a 67
    0x302e90050742c0f017014280e01c00341c0d40d8000017040d005060038113201e8680c0805066901076042400000c01c42d01d01004101c140c5000240108282442080035100c0d01c4003990129a00081c0c0300d001300300c45d080e0302415003d400b404580c0481d49000701311403409000603c4c403079034580e212440050310201c01202d4a85191400040c02c4442c170348170040c1c0c6940502c054a40c552004928038055503401c0d0340c984058614034021507040d80005040b4480e06062030244000e004080034041d0b9601ccc031400705c10340e0680d510410103558410759050a511140200507050042c0b500e4401006e441c401010308400141040caa08000c0781d000c0c43c0190b65800c0340e4140d8005a00c0c00325103102c0a0030882c90200b00c1506041e01310001c113660408002d01503000b00403041c030356400c2000048000c11081049541c82c1c035182c5000b0000e0a000350040f40a44030340c980c40320f4a0000e020841040d810050015410030540910f582441c1180e940180e500e80300c0c07020300107407001607070080662603049500100205c405c0f91902c2c1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 275075000 1250 275073750 275073761
    0x5010e190507050406050d11030423060105030d110a05060108030406171603090305040b0a051b010203060108070f0311070c080d11070501030b0a170f10020c03041203020708100b04 79
    0x1081601d44010040c0ea6908001658255a418640305448600b500403902c014001c85d0002e0f10320b0fa0003c030801c001c00c0501e4207415850500142841c040f03243c124000d50b6620380038098268547c011801c1151580d108101d125004007101d4100c8015141684841c2c2c2481001c1c2c108514a400000e0103101089d0080c11410a00b000b00c5440720203884c0c8a00754442d00c2d11941c45000030142c440c01040c00b41440f650031381c1c1c05404d09404840e500c0c3c282260150041d17007c0d4800100206001c0c6d0040d401d1039040c07007900d10501040e11004403d980c1e218003290101c7c542e134008428595030301200d4014044e100081d1144620a070f000844541c04c240e4140d280034003804c0404108444e00c041800d94900129821040316400c1c02c011454007a5000000ca108040340c002508510301c1c0010940200d01c00200c0100f1191100151805003802100300c43c140d111321100400a503004200400080694550010060b4003074410356008644411030f9a09003101402306658940e11450886220f01c0c3c64170a4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 275076250 1250 275075000 275075041
    0xa0f08071b050d110a110d02040228020d17071101020f0c160806100b03090304210c140d0f0611030c190f0f050903010603021314240d030c050105010e 66
    0x8114050f1a60303500d655220f40c9001c160b000d041c84007d11700854455070187c6a0422a100c1041958210f03032a2001243e050a0020300052041034614040d40f801000c140900010b032500c0081513580321003065968000e002e00c00801594200310146001080d0000307860003090b81c0000c2d00001e6562402e00c007403019a40c0050040b5085401806007070810252110120350301c1c00980740d107903030710780900303600b540075542c00710540305d03030b5101184041b07028500b103000024450301c4140001600d0b4001910004503221285401c081e0843c0360790040745610060080c01482100d0100d01c141e5540c0003410f00741c109982c2d5046d00600480c090311080e8181c0f40d4203031000404c2c90080103c02e68440300910310b500205201c0305211000400d01400d860070340243d8041d607000782145603608804442c42006101c2580002c00000e840f030701042d04101650740c0440b00450019406c840c0b0303984201009090240c82c5070071030a11207503203d200c002039001c0c0a50b80c0241440d0103c4001851300741c00c801420300e0072814 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 275077500 1250 275076250 275076253
    0x6090302040506060909070c050a0209193c060801060303080121020f091f031506080c0f15070b0f04021f0f0e032118060a0f08071b050d11 61
    0x310200c98551b070414607809199490141425603041c03c00303d0400044d0300c0082e4000c00c42d8000c0000c140502c1c6114108901c107098204000042c40020940c120800c61090407104074000c0c035443c5150304041c0c0905036520494001600c9940d80003014219a82031b0300440104d81c44000402581074882441e800d0341c038140f00084094a09940010a91940c2c1080a8800ca607440e0204807010004419020b000c801003001c04211a224203040540c11048485e0b0800241005808126400007040c403c00ca110003410746041c0000703220070043d8001200c0100e070800c9405002c80f0000c2000c2616040c010f40d6071407160f200c141420300501040f035110703009009000003440b000310b10b4161300c0000710540303120b80d15000400a2031140000d040c0102c01c1d400c48001840900c1458880c0307050700c01000c055103492101c80c2c03d1105207040c01564060460100040f0307140380c0b4100c04590158800d1540610b0707925100e4406031183c41004e010f800300401c2030710300d40e00c0700c000c07024079075080400e484401c0781080 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 275078750 1250 275077500 275077507
    0x11d0d050301030302030435011a030718021b03030727050d0213060b0c03030f071407030f03060314030a0f1d040f0b120609070b18010e0d0803010609030204050606 72
    0x407130195991040344145440c903840204c51281e20a040300c0071640d0b400c0001c481552402110741010b020340310042c1003d09080c4005041040e525000400504503065400c05501c41d03a5021210780083d04100a14035080381701d2121041e603048244021481014580c0310f00480a90351481c0e909046181c1100341c1e400c042d00c0324103000c5a40c1d16081c68440e180d0444684801d078034080451406080f032540208008100842c031120b9542001c00903610403010030f180824960340b8001c040b00c07001c022403588840c0d03c904200180c00702c5d11504041c0e10b0b611081c10301080c8139a030380c1c0e110b034400ca41000c1039464681012500d1075450364000342e0790f135512455281c00c0d0758503607400c20103000000030f016401d4402c80d07030350354482c9101e41160800070040310001c0107003090f400b0070034445480ba502103900004038012210081506d481b1803091b191114403540c004507500c9000c400542d501030360207401d50b07032100e4134030504030020380180300850207882c06507108504c0c5c1d40b440c41840250380c00600705034465078050 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 275080000 1250 275078750 275078753
    0x3020f010c03050c04050d0f0507060306090b0a030209060d050a12031b020718023403091203050d11130308180607051c050d060b0316020102090a0501080612011d0d05030103 76
    0x41095409441b0300b1954541100d4030fa150030800c51288040080a40c040d855000036000d0301644040c0480da00310205002011032002000b091003e1800000d60140c07a250201d15a800e0070359840c00b4491044007260650b495640b12915201460644240001e841d18003081041c181c4111a40803407505000400c1900c0c140040381214045034030f4000443d0754003040d401a000700181d0340f000303240c10042aa082021000c00f40051280d9158426004200c51400024142d0210065003081607050b0b41d07041c0c00c00c45d1940018010303096983c981031645005021850f154505408140000c622950203107940b13240c00010740e418802d00002d1203114074028014200800c002103807414109201214421110203038400a0328180241501c0540842c80d094000c208205030320b00450080e61000c8070990210b5a28204078240e00c03c102c552038105041e8601000b10f5405500b10b40d400200046c04101400355100d419400c4030300a03a915060010300d00c100700c11401d014042c4981e03080c0503141107851503045 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 275081250 1250 275080000 275080021
    0x18091b04051312020c04020d090209060114030406020a031b0c0b07140f220f030219140f0f03010905012a08010e15090405030a08060405191a0d03020f010c0305 70
    0xc8040c00785054001d0f48001c4501c2809141c0920000030310440d111020a4510300041060380f808038090303068503010882c2c035030207025894000d00041403014615a210380d00c000180d0040c401e00740605860740a540c5103003140f54000e40800c0e0705640e0ba400180c2c400e082c04070710b0b09000740c00350301030040d5104400d1200036034008440c4294400354229668a560407100c01d41d503c5909032020081200c0c0c0c00104034141441c4802c0100c80c02110702076544510907103481c0d1200181d02c0b583c0d204000120380400749080007200511132890041400c04030140c003202103030030b5412031201100d00ea503580c8242c46021072240200d4a250002120303034005484203e002a14022040c01001b12040c1c00e14001458401c1c0003804a4903190007030b08001040c01c12b40707040e40c0d030b0760090f8a111020888880000d25503082c03d1088521813010ba042c00958080300d410401d0060078011100b0704511001d8011440399210444203010b002d02ca1f500409400c146031404a00b1500400f69010816042005004001d5035 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 275082500 1250 275081250 275081281
    0x120c080907152007030c080d020d02030a05070b0712020c010c170621031303030509030120030a020904020c070308040608251b121d0307030f1118091b0405 68
    0x20342e0240f5010428400c440d149444415400106050410400030544900c0400d249075199400e030211003540741c01410030703a224041c800d0f046000503030901018001c107140b00211600000c4605040f03000940d1203503940182d9000d804442e1842e03440300700c01f5400303540c804c62070700c1d000d222060100c0301410b2550024003090f80402c60380c800208602e09028140c0340a0048500341c0c2c815410b45030304241d5030b142c040d01c141c0000500034400d5203441583c1d4802c480c0051044028410148100c1c0345031342e02c1c04000001e40104500f641c000e582480113580300300c02003126401550092181035129440e250009080b0034004103a1407200c2d0601400b070080003500780781d178071a100d80ba007000c85901740c4074804a1003000c0c1000300039140c00ca510304900b000c20b07002040c01e0500c4a405102d045496280c20a140d0355103214030004007080e844456500105460410129003010000c1c070b201074418901c51070301d001c01000c0d5502e601940050342d48000e600707407032898840002d40c142d40031b1280385040d9000054151 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 275083750 1250 275082500 275082527
    0x1201200705030c19061d07270e030c010b0d1e1109040c0501020d0c11100512041a0a06050607031d030118020907090b0d0c120c08090715 60
    0x55000c10044100714051080c0e035000305962040701c030850100015007000a41c074400c140c500d149000013488412580d184004c407000280b60040c06400d2400c41e100e21120300040100e200300b541c074039050a01d1901402520140e03030640000303589070701c031656006007100c0b146000380344600b2050524200051018176021410b0010b1000310002a006007028854a82140d004503801040e410800c4200000e415141d000da400070303401c175440e0394081c80e42a00c2801040c1009458170320a01103261240c585000a242410b032075142103400c10015107140c843e20942a24112500d20a486030b54140b41410740c2025805940604180a400d18140c040343c424828410050200f0909a0b500c41d5851914200c4100f1608064002c02c6001c0301d1100803058070500711022486a98824041102c0510400461341903d00b1250749900e8800702c00100d80040c080c00c58060140b20044e030800e17003811480e10440c062a00281c54564036403608400460034010340741c0100c1c401303091060300c100040703070311400741269403 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 275085000 1250 275083750 275083811
    0xe07031b080403090518100902090a0e0c0f0c07060f03060608130f050601060e04052a0a030608070909020f040912030225031e020703020f010311090a08010b1201 71
    0x42d20380c0e060072640c2e140e107500030f50340105038405403400b007040d59203140303201e003901c4c000e003015183d215911442644104803c4540c00b0501c04000d00181040038200c6400c85410b107138407490705040c20b070499000e400600124019400c031102c10004c41d504184004e08600c800e10701089010f0a01c1e4000d03080e02c5028101d00036022003c0c0844040202c041c80102a03160003008890f895a50307050000c0c00f08054090160056003001c0c0410b0040d41c0c4180701c3e090075200d081d00011000b40925280c00541c002000d03072010542c6614002821940c103120b40009011202c1004c14511032500600100400400d4070f00d003e5840c01101c1d00204443c85580068507010346009a501c485442d004100401c40201281c04a100402c0b404209500506403420701d0b2508101610b08088103102a078565406120194010703a82192441c00c40d0303c2035002000d0f21980b41c24403402d1002c3c040218204c03040ca500300c81c00680d585c1c4c0062036245003512903000504c10303d03402070180d40902041021a035500e8247e8003e070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 275086250 1250 275085000 275085017
    0x30103080a0c1a0109060e040b010302010e010c0c061d0910140f1302031e09070909030309050d080a0e07050d081803030d2f090d05070f0b040e07031b 66
    0xc10b84180012012207811482d0300700a412412285101e1034000c0c4500007030540380c0480019044a2188400c0c417a0b9082220300074681c1c6103400546603881c090180d94100010400c1ca0400144280c80c5003010701840c2d59540150301c400c0c1002076600d024507a001c2c1c45020340c0810401090a1150414199042185821031009003803011031111115030340980c1d80300019402560004415601561242e60440341809503103e5941c20340ca03100c42c1c10340300c50083e074012400c18049a4065003104034414400c1c600010911015100d86040030b440c1c039402c500145441c81441807031141800f13400564140d41010307214942c60302c0c00082554030748120041054901085c0c80c01a0300d5007880005900c5c1000d01941e540c1d140c1144540001c01d03185410302208402c1c0b006400b0b000b10303048003c00b03c2d0000c52940514104030b036010041002410201252079106071a00400d85260030454140240b65115040c4e403103c0c14490254035400c4000c007410209881e203600c20b0310b090100500340781c01541d00c8c1061404e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 275087500 1250 275086250 275086267
    0x5070503160c030210020a020609011b05120411100314090601080a030c0807240f020403020a031104090c09090506150105040b1308030a0512061008150109030f110a0e0c03010308 78
    0x3450102207161708414804a90a001c0940104d40c00384070f0380c0d0b01d03c0200410401c055241b0700300300d101004440060000d101e00d4001c50980312482d41c105000d2103105507101d13012400a0480c00c1d00008150010361903c0e0701401240ba80b24000e0b07044580c3e00b015000c2507040c0000746545000c03400c8041c041014007010441407290305030803600000d8012020400c0814030145407410a01140c03805c1280901c0d040b11080d41c00443c0c401c3d00d060326070040004200c00d1950f101c0c441d00d1200c840895902c40c0e5a03101301800034000e0140c0b14014801d90101151401d00c40c148241400002802c055203420320b075211540e0340c0e9100c0704940c107a4800310f5007251038107400d10810055902582054600340b10010f03804041c581c00c400a1b0004020f1180c0071a916903400d82403100c0380410441742000700c0c41c0700021840850103501100c100240624184129583e20f8030741001e81d120705007007600d49486490741c43c0c1441c101070800e480034000d00003a034140c2d800c064035014001d01c81444050151980416000c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 275088750 1250 275087500 275087503
    0xf0b04050f22140f010501031211030d05090123060a050d11040905030c06152704061a03031308150c090f01030921080603010606020703020927070303020105070503160c0302 76
    0x4410358801800c4404120541302c8003802400300703000c10340d01c5083c0f112002e2009886a145610364040c418040c508081d90700f203804020300409080390805c1e540740c14800d8112907c1061004500000390728114031400c1210510407a0035940d0046806001070641c0100825039966500308444d400340c3e000034285200c0d08140741107004041100301e69008072418030004040c8442c101c0c0190070103d500c4003080c0141c001c88001420088054280c0d00e10b40b00006020424690040c5203060344800d00ca1052062080040e007103502400c000c0c90010441c22062268050411030076002d0303070900a00042c24240441031440d107000303514489100e01c54008060010380d20a420030161594050070044405080150308142451141490b10010380120300140703851505016520841e4007a8015080d028155005c6c44840c1000805202c1c800003280306440c40803025601d1941c6540305503000e807201606500c1c00a09560001c1d00e030b1001c001c000e000f0710248100343c0508404650f03440c00c260035098542d2400340d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 275090000 1250 275088750 275088773
    0x301140409080a170c0403110d05010f020d0516020a02151303020d080a11010c09030813050d08131a0313050c040e10050c0a020607051305040f0b04050f22 68
    0x1041001d01103078249507113410100035080c0c10360302641008942e560402829481c056848080c0688401c00000071392803c01e00104145240100004101c043d681802c04003079034040e080400d81c040d611020040d101c04207d40c0464103440c584042c18104441e034000071000111070f18440340c240400030b8014000c41c807440f40c2c9001941d0151815004c4841c500707207021542c0200c0012000708024100501c0c49030410302ca00000340782a5150703a80c0443c00c54a403001030760440d100c41a0b00c0c80100e00c0111b402d90700c00020380340c3c0600c039644203070fa0f442c03a1205101d80d4200c00e0380101c2010700151002e400b06914901076a6103c3e10f00e012503c14108181021883c10810303203805034100307140c0030011020701004140c0c1405540014005c1c03049450b4130105407200d21490b0810001030300310710f001c00c040c2d600ca41e005110a0203488098032516440d980000c0440d85501c9074580c000c1d540e042400d00c0b500380b40c058180e00c50030f107800341305192030f0100800e08240d0031300074001820700d1107004c400c041004c6924075 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 275091250 1250 275090000 275090003
    0xf1e03160b01090b031615020a020904110a09020301060c06020a030f1a030c01080906180a0506090a0b0c030405070b031b03010b0301030212120a03180f0606060f0e03030301140409 79
    0x4100c1250542888901d542003070040b03d0120f414940c14154a00b80080d00607104412099038408051804800b07115180280e00d1110460252500c62000340c0d540a080ca40528082d841c0810307440b00308010403100f00c1d51580904c1d0724174018001040202c0e000841018507981020001da42d0b0701c0e2184007140200324008000500510340451220520b4041c80c0071940c11000ba8126a4415490401034400d060304030f40540481d84200c0c001100700304104021410701d0b680e202141c2080c101c81d034425040c07d00450300c1281980c0b24509030300500071040c5020343c000340c17171820040c614200340e1601c0380c070385840380074215a6820010204a4000b4281c1c602c41328240c0e1400da0ba81c681d41c46100c0341c02282d2080c442a841500401c8690502c10390100b400c0c11001001002c49250403203180066024011100e140b41046400300c500780c0c049460341c3c10310302203180700d120001099402c00d00040c0c80f0160200440c020490010b08956030303500c0000490381920414071801c0c1e224115040000e000d020103010 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 275092500 1250 275091250 275091277
    0x6021c052d1e090616021605040e01020405120f0c01030b031e030c0a0606090510050603040b0c0d02030703020a03050c0c0a0602031f03050a0309050103090b15040b0306070f0207080f1e03 82
    0x420202440204244d40103501c0602501032030b401c1280700304c0e03035002e004880c64603540369500d040015103465405000841c44880006d800c05590b2000114400424110080783d13410081c440c4940c00c8061007140d0f4400024241003001510300e002096840484828001c00081c0c00c480038071028500b082a02d201d0b4100508548010342c9030b26010003d8580c40c41220744442c02d0902140210840c007401400b940d5000c0c01041c02c658480d2603031440d0710b0000d0800c03400f01c40200701c020714608203400110300c42d6a00c0c0d00c015aaa8151420082c11100000d2000070491018004040495000b24483c0d114542140000d6200d0311080904a0542940003031344191042c00440041000701c08141000e42500984480d800a030f924001981a900390842c014200f4500b00d000620700040100710201d14900030b400011070090b9000071a292107003d880910100c1c0409c80ca80300030582c1040700b240070b020500060441b2140011003642e0320809d0785003200042c00c400420b20700d044420000e17a80341600c00603 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 275093750 1250 275092500 275092561
    0x105180f2707050a170c06070804030c09021c0903081501091701050106080c0408030712030f2f0906031b0c1b100c020f0103020a0c06021c052d 63
    0x6008980d036000a01c43c2c103004220350300e00098140e04c1071000d0601e8071440d0b0054030550b00c20908100c0d4036400340030201c504000c1407001102040c206a0807030041d110307070000113a03240b1403901c4007654500541e03081151942825100e0002a07448050a504085e10850861915040c480165200341c0e0302d0308010001500701c0702c11180700005400c414100c4a10703071210b0005403286d02e1040c03001d21860083c440c950344108100e100140e84260a103120814620700040c405072086201c0054981e0894155940010018035600340e1034070040782101c03951401c3c1c00a02c4d10700302c640400d07424040200703040a03440200343d4a00c0741c3c5003864211407440c0200d00c1a5860860401a0400e040ba48603e07030714040e4818400419041d401800c4ca2078095800400001030b01c00d404004402950103400390008005842038114001400d60001e00b09102c0c1d0101d50312442c20024403210100c640c02040c5c00b032403807500e54601d8414030854840710f8289501850010542c0d48400c047c1c000350782c80b00704910100c40d949 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 275095000 1250 275093750 275093821
    0xc03051605010515100c05120d060909030201200405130e03120f0916030f11010504050604030c080d0311030a020304020f0d050c010e04020406320c03030f0105180f 72
    0x1440b131141e504040b15001441c040c040c0342150f00307405400e4000c0c041d07800f02402d0302c18044074601414081180d00408114152145002419150260800c60150303455540101c0352107003008110b80b0000c0c016240505003460b080004030464400e01c924030000341e84d000c1c5d440340c0401c1072045881e024203000300440700703041c41d1103c41ca61050440d03001c1264014a0389242d030303400c5003c501d00304880c0c1000c5080d007404160f84032030005140c074102460500108010015981c0c0710318010344002d5004401d000c208071325081c4180d007005c80350036040f800c00d49403161170302402d040001540e4102a01d035500603101e58132840841eaa40112600c0b40d0fa2142003404240201300d0001050b4456100a0ba510740d15020240c0c1400140d000e54040e01c00400d108990303044000c1d01200d80f20b110054044811012100f070909180981d0303012404540240e0800000c200b40038031883c10050060005442001c00e2203114402c01142440240130309070103000c00e00c04903024601d800319640000b4826107002142c0c4a0300c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 275096250 1250 275095000 275095021
    0x20303030705070c0503060f0f0a0605131401080304030309150c0b010b2106031011040b03070305070206070203120403031112010609140a050d0b0606191d040504030c030516050105 79
    0x1960045407032403a048130105440c103000c42c0c1e06000794014000c5155a4607010142c880e100c00003092070410b941e840d00e0018a0f981c800c104001c07014440200010201a9100405104a0141c0003400141d000304000c000280c0d1102c500c0c0c046a03401032500000d9180140200d840351460200581154908030011030550820002000395000384030040490012200740920948001c5030103030340c07581206104449036a429002541d00207003810305c40b854a5141e44500c8541e400c15110000042c1d46e0314100140a40c04201054100d11940025402d04445946401000000400040416881e050706504054507030060b02c102401c1e6400441c0c00c0d41c0c584000420a40141c4500140206242107091450a01d0070405090710006040d4100d170130f0242e05c1d071003a101c0c0058410380d0441000c00503008141078800f8021169070300741d510708244500405446510200804c0c8940c410761030301c030500c1b0000b50000a49c0c0c521650508100f51250400304910240000703010002c1c2c105c1d400d050401c003034140c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 275097500 1250 275096250 275096257
    0x61210020d021b0a0b010b1b030c03120105030f1015052206050423070c0803010303030605030d170609070207082e02040b0d0b0f040c12140c0901120207020303030705 73
    0x900c0001200d507550f2a000e6900c610008010306802000310042c400001c52000034489402c1c1080c80401d100e2402000303501e19801404840c5040d000411074043c41c201082849004000460041ca1801301280c4c0b01e9458510141c141e51007241d9550601048010507100d05008010040003550303100700800c4000a100c500700d00001d541c034500741c00031901d4034003485a0203511208100c81078003001e5820400300503c0000d46003c05011280c030000d000142076500a5018504c00e590114020b403400084c54a804c0e083d81d241c10600c441500e00c100702c103105052070340d40708004482d90511601c90210990070101da5400514070b6001d00341c151031420703051100700c4c13244801c0c4036250000e04040c07524560407070042d0f0082c4034824808008a01c00d42c143c030340000c3c0d19038400030001003640c036480000a0031940342503111404a811104912140702d41ea10800720f41c82e00408a0032054500221700700c1d0180308482d50941400070f4101d4004a942c03050381036440182d8083c0403250381e030400d40704c090030541 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 275098750 1250 275097500 275097517
    0x3a0302010507112a0f0405160206060306040f02010f09170c0a15081311092d010303090b0a03291002070f03060203150d061b08060306061210020d02 65
    0x1c400e140d81c50303110200000c800040d40c0305240d40c01c81c0c01c0d0201c11240442c054a805080d40b041c52a2001501346c0d580d48a03003400356001c0103c0b03100349082c5c100064140301005180e40e1081d00701504100c0803c0d24124002601d60382482e068407400000341094078014829000345140b004072181421402100007611500c031401100c1c1c41c074045985e985048020b00134001c0100004246001040c00c44900b9402007028600c0384000242448586020910301e100454010280d009095101500c680507100c008448551480602c0400d60568170041e1042c40039110361903040c2c0b40020208056442540503584e9001c2900050303030f0f01c41c005c604c4084410208444503100b900c00c1c414000c0402c3c00003c5040440d180c1070707885000c10307255466480007904010300c039101100030b0032020301460740c4100c41d0b0800c0b580b28210004426001180c100b942503050700ca00000e20800406011f001e0381c00140c996032040003103e2040c0c1000c04034065a00344805501440010750000c141d8403070415841d0050446031 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 275100000 1250 275098750 275098757
    0x1c050d090504181a250801060e18060105030702120d06030c0b070c0b070606030602160b1003030516020d0b070c02090c191206050307030c090b010503063a0302010507 73
    0x2e0701481c8440071000210f0034010100c1c0d1044406850780d60701a2690365214080102241c4010740d00042918a9102800fa00740056060001440303040d07000040168440c2040d50980c3c9050070035640000c2c07864010b400c1c039051003000301c00202c103a0b01c2089004082e0000b00c8060b40c5505242140c007025100500041317a00100f28480400d6000c0c2a030151800c09400410000040d0320341712040d201640004000d40b0381940f10308000c03011070450300007843d8815424007074a8401117141060040101c01030240c1d004403041c0e000030000300394410300b41e56610040c08148160342c2d1079480040d40c418104080145554081c4040144090700400c0c4120154002d4409144075510702403d8180d510440b800d05641083c8111060541841400d1080c0406442c80300041d40f0760f02d03070340024501070281c0e004541601d0140d0040c0842074103406074248021003800c1c06802c0d070a140e1300261210011644484007070248000d580420002da06c2090f6100002c0407888015945070f09000780032302300845911020 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 275101250 1250 275100000 275100011
    0xd0b030c1c1109060d060e1002040e0a0b0609010509090a140721050f040b0a0e01020d09052104060c0c0302040f0507020114040c05190b0d0c02060f04030e1c050d090504 74
    0x1a030030103690fa00e110b00d0000700031404201c07599031840001e15145c500d0581c01c1c03090b61340c030b044010281c1c80144050003050182d011181b03030071040714040d01d042c2c81c192030003030f0b206000d4221140d03040020340742132500884404542e42d403807000c61002440c1400c01c501c081c44c000c2c0f05011255400c60204030307060f0400030000f0002882042c03c14181c0b4403d90b005000309415100103008148140c4249401810710071010031031440707204c501401c0e40c0103100c80c0c0c1c1d984c0340d4400d40b94040180030001c03040f0405010b101c840e8a541203010007291402a4460301c401d002c0104160000c014121008001a5600034000c201807050131040200070041113641c0d401541c42c1c5407071000d420984070b0903603204a80c0a050700200c01d040405008583c40c8048100c1c0070303103260140200e9100d0002e005407070740b0a8071600000e48914005030003031402001800701e0100801041c10301001c40d501084194101006440140010012162900500201d40c0000d842030241d040a108081d81c4240036030100c450889d800c3c801c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 275102500 1250 275101250 275101283
    0x606020d080609041101200c10081005041503050303070e011704050d030c1101060b03060102012904020913090c090510060c020d0201030615051e040b0d0b030c1c 71
    0x104a64142c0b01d01c0e6000980c2c030002000254800401c07100082c040c0b40404424000241321014034680c00780306103d07a00301c1d0022999504080f00031801d410038915000349603007090300c41c2080d00c1c1c6080c02020301660f00e541c100070070780440c860346d80015030b489422695207281a200040502e0142c20500d40041c1d5900e01c00c407090303898144214001e40e0000082c1c0199000f03290181c00401005807010b0038002c40d140d04000c500420311900000780400310081e80e40389807210009003101e88a1680000c00c2c09081c0321700c1012404a8140079690400307460060b9120f0106001640180d807480b0a10b407000d0402151004101c881e1003074504481c0014000d20580d01c0d00250380700030003413a0180c000010f502c03446040141c6000d104807100b00c0d006040014840d40c5a03106426400608100c10000c2a40001d50b0712181c84000391909404601c4c01c001d505207800c084d141e4400780300d00b8210300320903520350158640e20ba0303040c02460307210200100503412080704490001010070307100d0004e690410840d06140c2 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 275103750 1250 275102500 275102507
    0x10c0c4419110c040c0e0d0501050a0b030a0b16050d061203023304020a030812100f0b030c071a0a0e0c0301050c040e07090315060e13120302090f10030606020d 70
    0x40740c600d242c102415a1500754810b210007404c0c40c0c040c0ca01041a1241004500c0c2c507280042c2009038007500c00850640340c8203030540e0513074000c240340078025442049202c01080841c0700c0c10390002c000756a60a4400d5040070215144d006e5521011000c0b0b01e0030000240a450300c001d155034a51003a000d407401d0b03401001942c00b00b04603031100c4200b010051920b5080031502d18002c1d80c0e00600c01403582c82c5607502e94640341827a4018034074283ca0135014600b80b15411041003004d00c02004800c881b11012070401c0d0b85405240005008011b050314003140c0d07981003246055030240608101e41d000903e82c6000320b2084060a1142d51000d0039000d2100c080c045030034180102440340b680d403404140740034039018980080000c01844c003c108811154044005000c050b607044003140100d40128109062541942c064040502403850a140c1141c40d80001030540a400810b00180c0c200142c5a42c01c0c10b0200b0f400d1901002c52039408a20040c00d8104141c16a00840a40342e0035801c850740c0040451054 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 275105000 1250 275103750 275103767
    0x10f170321040b0f04050705041d0708012306030a0605060409020d112715010c050a030810050d0f060b030c060c010516050a0e06090414090f010c0c4419 67
    0x11b42190807840041c005030400790003150036070074007001d4984005000c2c1e60701070402c030545c1c1009031241d440b1a43c6980c901504070a034800c1c118a205441000c0c1130020010b651010f404c0741c010079103600c4000185040e501e551041000c42d0b0082c010702e040c0302d01c914000c2c4550113500d086038403d00d40751484514003054008078040801003511110000d490741040010b18160101c2418100012840d000380091014060500300c140701f030316026a03500f0045110035440300d2580003503015090f409106004a012405510f080907000140041c0c60302c00f007004a42040a44800d407500560f0000b0300065454055110710301c2503030906800900c580f00c0c0d61044440e4800c40c040f06000a24004040d10945007050061801e481e00a0000a07445000101e04055580440d03c0032296000b4444c030840c01c040031300400055044a01c2d11200c10324403075a8881d43c0e17181c00d810b0710f41040c4c501404244010301d5988519400ba151800803101180240c41603600d9502840c000c0400d40750086e0715020903401017641 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 275106250 1250 275105000 275105003
    0x20060105030d021b130617030a170610110115060804060605090603060a020c0118030e09060102010203010f0909060b060316021902090114031006080d021203010f170321040b0f04 78
    0x10754150384c900c0e004000c0c2540d4911000c15a103503a611000440034005284a400a050000038580b10328400d0005040c05040c1c1410184840c00e500803c201540d949a500664000070f04010142031888180e5500404840b101c501100e4002200402c4060700420400c0c4944c0c85400d0070301056413a04140725880384181c480d1600755100e480030560609480e00607220036034044c0c00020b00c0c200c0002511071040c0c04100c003900814403940004a40341000c5161345e074095020300003540b441d45407824001c8034484034407540c115a5516415a41007100d035420401c2d0005000f00b1813a00d0381094000a11815420318400015200d5a8020500c04401007030a007120340e00244104070341d038030305049030380d000050b04006035140c0210000007100044501c9100040c3c000c10008200000d41e1090180c64240010804200760a0902c0100440b452010a80c0192405080310825050904407603d14601a41b011f100d04800360000310f03165404680205403180e80102c0e115441d03900c4009404482000c1a1030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 275107500 1250 275106250 275106283
    0xc0a14030d0f021606050307020d0201060602060613090204020d061502060405030a050c0f0d080114090103050d0e1801030b0f0601030218040b0307030203030c1c090b04031220060105030d02 83
    0x11010545400303104207101111982c01a2a01004148002e1310329810fa03401002c00301d140071045c1715400d50304002c025101440c2d0b00080080d0b034245a0040c0d03072a00010301c410b100d601040d0b900c0805040e1508410045076001e03100395101e0b212418484094001e9000741e0000402e54503e100503a480014807600031504640914038210b042c84040ba00c540c000340040d081c0784142030f40e0950020040155002d56955030b40c65845d10b5042c6a44a4460781310600c4081c402c243c040010b00200e0000325180202c1d142c241408218148100c020848040409581e000440c408070000070034044d840400a11407031070583c4265a950f5102c005404a018012200101080524820200d030805500581071160000e0031140c0c0c0542c1c84e40085e1a5500184148460340c20034010b13070380a01c14080070740c2c01008440c02c01c608400d061424a0382d150049110103420810a50310900c0d03a54020030700c1224812240185080044d814886595990340a01ca064000d11409922815980c400700320310704030784214203 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 275108750 1250 275107500 275107513
    0x528030518060d0e01051f0b07050f0607020c010e01091404111621170a0f020f040303052d0d0f0e01020304030c0c05190506030403030603080c0c0a1403 67
    0x4504581940160345180a45000300603100c1071a912800608100030001501180841035000c0003801e4070000340040c21140504c0c12070340300d0b1303952901540301907031042c640164036090503003030091400b15050f402040e40d004440611104540c0400e80c800ea804081e01c455280030180c03001107656005034410101d00e0000322030401c1651400e03402c081356400f20304001c641085001201040d044003640001c0f42c100070000c0c40c03185288084081102100e0f0a820201c0b0209100f805501c20140001c182c03010340780d647c1c80c1040c2d0101362039040d00c2208481d000042d07140c03512480d000d8245d80c000040b220004100d80040c5607010600704000385201c0105c00d1381d41c00c01010720080390180c0346c0314aa1b000804d807115201c003401917003407000d58440c4d400b980c1d942c200303110039080042801c0c115401250042d08074403210340020714448441800c0341e20075110680e5a54031410100c00800068200130554100040ca042d2004400103845a6129045402204880c0e6400c042c08540400070b061760340541001c07 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 275110000 1250 275108750 275108753
    0x11071409060120031305030705041a090718090e010506030106050a180603020603040f0c0801020306031c0203160804170a0213090c080706020102070b09030a17070c06050f040528 78
    0x140c101d14841018144070f61048440d1065041c02d50700104e0000c96540780001d410021440c042288500400040e41e0410a189480d40c43c0f00c0034400e055071003406201d548002c640620b104101c00341158044024040503280c40340130a0000c5d01c83d00c0414403d039030900d0041910f03440d062040740211000108903074000c40c54140202c01c510030030707104650680e594800000158407480000d40c440e80c0300350034035040082d030f030702e44a2480a5141c002c010540c0c414010005c05440c0040c0d4070318419255403100c92542d20668040746144581d110349004100c1b150001d104000041014009031040c41c800c0c00035000d44c09150740d0b41c94501800c081e510102c2c2805000c0f4a004540c800d034155401110304545150715a0100c0c2c0c0b0348503c0f80d00801c0181e5000a0030010300a041c260140c219084101440c60030700030b001c0007862059000c8003a0301c4074001402285a0701e00a60180000a911032001d0017a480c080050003075010040703400b50b0b514001c90214540c0307816140040c01004482c07980c40034080b1a0fa = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 275111250 1250 275110000 275110007
    0x6030b031005090c040f0b01090807030807020f0d0515100506090607230a0b090c04110a1202090301090302071403030703021e03041809060b030303060616021f110714090601 76
    0x83c03da110301d0300a545048503503032101c0c001c03180365000c0140081b41b440d03030200005000600070750140e82c240d0070403041440041c0050040300c0c009a0100d50b18000d441160001a0f0b0048444000030141d12130f41c9041a09000b0107040c0034810803a4269081e056a51403003400018404c2021090384070381c080001d20b00180d6201c440c640c20140082602021440010f082850110712040541d03110359144c0800c00e1821042003030002110050724144000034180c000c621090080407030020a2112000040c1d19403206941540e1800c00014001c0c00b00003410304000c0c2d101d400e5070062200000302449606554100042116101c0380e05034002c0c03080c0b0b07101c0c0030b0071070401c031012080c800e89000c20000001c5180e050518031401e0155400c0004007410640b4010086a1000307071400d00a4109104100d520b9440406540c41c1414550b40400140024800180c04080c451f503600a080151400b4000c110740c000046180e00c120381c0b0071160f4890711600a14090840e02c080307554041502d8002a07404e510 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 275112500 1250 275111250 275111261
    0x230103020711030703031709010204051003020a0201090813030506061c0227150108090a020f0112020904020d0504120201150b0d0e0607020d0f08010e010308030603030f0406021606030b0310 83
    0x1503142c010708029810000c0d040002950050380014004c030207010881294100390b58010305520021803625161201081c03144400c00d00c0401850b90202da007485c014000e41041c070307072540d0080b6002d581d5164030000d0481d501d01404142d4140c07003a04001400c0c2e003400680e101403251100c0075989035a96550030030021802c0504d03018190700c06000704003107403103041c0d418a014121702d044003a00040d00900061088600901c001150703032040d040c2d80056140ca2015182c0a0001c1c6000c141e401c8a1400c240c029100740c040440e0000d100090840b00d00780709134032460103144105901c1c49288400c62080b070030f03030b0240103c40800040548080015070310039402030070030704c103070203000304202e14620001c41c01e11100f00e80b2040035801c04c8140d8455103a0020000e03000b8010740c20003403404d50400150348101081400007c1100c0c1000002c45c0c00750703404109543c0f5004645684580d501c1c2c0765030b0002d4550014031941d0040c0c40c00c4410120700e450003805000c9660101500828800034004c1041c0040c00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 275113750 1250 275112500 275112503
    0x20a020703050d080106140306130b0d15060807050a0e0109021e030703060302011e200102090603070e0f0f1e01090504060e18010c0f05180406090b0405012301030207 73
    0x314081001001410910901052071800c2c1c941c11030a62500c0000b500311207105074180c04101d41042000403565031485118030705c0d1844140024141c2410b004554106480d11018003480c0c420400c50907209400c1e040f6205481651064496843d521170510036142414022031100440e200c0050200c403400f41e0141c031010b4102d1800614180c3c000e8280341d1030358404d9a440000a031102c0003031055581041c00c0504102d0041da010a45c117aa401c8000d02282120320f4041e03a200d90114040c65250094060f582e45041c000d0441d64ac0781440b50014102c45084e900c0c2f540107250400d4400720714900244044955076015225902581c041780110710046007202c10981840100040424252694803500b0003138907505411000301d0a001c400444400881078a88805a06254162030016400300341c210034900c00d8140140c13140300c0d071440c6507192940310f21060b812905e051380c00034120140350002001148103460402030740e41c80b860704400b2a01ca0240c00c503241c42e040c105502007548298000e0031910b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 275115000 1250 275113750 275113753
    0x23030415060b040614040b0d020702090c0a05040302040510030203030415080709060e06030406110a020307110a210602040305030a03020403140d0219050703140a020a232803240603020d0204020a02 86
    0x10380715000c1107d0b90f002552003c0b0115404030341d480440c00d11400850b00b005019022a0800c014100018079521a038000240243e49400210b2840e0100962041c050b607401011b4035112078a8100c02000c2c403c17404141c00000e00c1003400b003800c09001c3c94142007641c10643c1d0f05640c10744a40c00317100c1c1c81d80c00540b040325005d40d00c0381c042c1084d4a01d0000b03803040030000e40c00b56903505000c0c149500f0301401003041d180b044034034032410085c000388580821010000e146442a00d00c402c2d0812074001c3c0219400175250380000030741d141c0c5407a4075a00600549101d0010401c0b200503a91050740e1f2120029100c1015a2080f00c000614a0200080c0ca102c40e2040c0c0450f01d081e42c507075503918454410380b2140b403103d0744600e60700b90440c07a005140130080c105240100e004880500070901b0074060343c1c0781090168510304403c484030b8400072001c003030f00140c00040492460b036925044403c07034580d040102c1014a1340610050042080c01003c0450350002d2019420300715a400300300096000c0c03403400055 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 275116250 1250 275115000 275115007
    0x3021b102d0302090307140f01030522060c17041505090a050307080721020303010b0f040510020c090a0e06060609030a0209010e0402030106211223030415060b040614 73
    0x10303004010003904411601c1d0390096200c80e000c1051501c0c0c0740058100e07a88440d00708841a14940ba040b12288003190300b464003140b16260100d4001c103204000942510241121386401c00380915500800d003841c4c001d541e0b510341c0070000c44144100210030750340109542c98102ca5503000800e0342c3c001640002001e019580c1032440e0360b40361451a0b10080c0201c44000e80401c003882070208090124540401000d4000d0003030420700c50003512480140034211a0500100701d4500704840501654040c180c0070f0f080c01c0741c50060603400b968610b8803041e143d100d00521000a070203010280180c44102480c90010503403074407030008100941e04078900082d018400c0403545805030703651081300750090501c00000320160426005245c00e4038a150800000200f23508244801c806094100080940d006070544061040d441c104540c246c00c0c6143c1c0e207081c070050010601210500800450003207101e03c804600800c0c841c40002e003a21081d200b0782009082c1800200b0440e4080d0030750140020742d03024624138 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 275117500 1250 275116250 275116307
    0x30607032004141306060504060f0e0423180a0201120e030a0503011a0f0406030207060b03010609020909100501080106120b09040c170a021309020303070213050403021b10 75
    0x4590b000340c0d03c19804002c0c0d003800310845083c00842c2c0742d0101c111040510031181407180103040b038071580c8102c10810014000c20610321780b155558040c0503e008005201205445000c0c0340d480100200b01e89120203402c000c50354039140300070340076400d00194001d0012000250010b4590b04c0c80e1041c0412466220395428142d500d0034030043c250882c444d01c2e00c585075410090b46801c1841582c0c60b000300f044040204114429400042d5001c90306140f80c09682c03003030140703000c60103000c010340342d913416600700000070410302d159401510715040150f40c28041c41e40c6441c0c0c40341540b042c61066501081804005101c40f5101d42d008214110b05450089a598192800f01e00c40000840b42642d91000d504800d101002e802c070007035421050454024282c0c2a0741c1d4001416258402001182803039540069504545051040d82d03086d6400908000c0e0306c0c1310104e210750207840d0840d0200c0c010700802c8101440040b000c6109070740b40c0d802812080c0b02d03070000070040d1586140380d41c241c0c040007941d4141c941c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 275118750 1250 275117500 275117561
    0x60e01050c060406091b03080306100e090f01230604031101020a1208012303120c0a0501020d0e1504080304020f0409120c2102030d0513080c030909070c0203060703 72
    0xe002c3c038440da0001400413020305140c43e802c208190440070b103148404040000c5076203401980d402c041e00700d404200c80044e0b047c055036005008000c403900f0540341c00070045e001c084009030310b0488541045241081008804031100030005001e82a8010001e00085c00030031400800650b49403030600442c0c00c500115243d4410b240e407902c0f404000030314003000520460313225041011504000c030103030304000c0080c1d800098503024204040d0507405004503110704850410402001141c0e08240210355448050b1a081d018107526551244d241c4034400d0040d111a502080551040c2e40103550745017551502d6003042056201d041c1c106038080d1302e6032003800115a0104485003040d056855002c0114264905141209901b0340554101c90600503241e854640110495803003030391080001415a50340d00c40f0304000c2541c150702400400020980c24004a000070003010f0f021804c42d01c8003101d0f9960750007261a4069460001c0d0507030400004584a54040d420034014454441740d01d0000b503140f54640ba = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 275120000 1250 275118750 275118763
    0x20d21021612031505010e0d02061905040f211e02091815010f030b0903041a0409050115170403020703021003020403060b0d030c031b15140703090c060e01050c 70
    0x940d000b84001e0a41c0a5640e01449040d480c0f1040c0c8111041040c80c00c07002902d041740f80040c8600a00c0d0340b800c041c04641c0c8407401c03a5810840074110003001c0320402c100524035003150040d620000d2400034049400c031440c103080030904031900100ca40615255441c00d07940d000c200d040781410004200d031b6000594484038075a229048610b5410f4160f240c03186d1440c9451529001a4600310301c200040c000c9d1426103082c482642e40120b514602d036250400110314504c6503502070418400c92003000044440c040d0024002c840404da402e01469032945680c403a4100381c0c9c1c0c00d07174000c03801d42e07154041448420712450364070038002d00540320182e81e2500450348640d0294514800a0782c0003c1c1401040540d102d8480090003c1e544040204207565004d001e0307180569000d003c2c442821040400d1031002001c0300d00030b039403185582c0d0003904c0150612010b032440b101024052030110300012801d40c8a80b180414003900903046414a0303160400985414144c10307545410020301b0401424021f6040005 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 275121250 1250 275120000 275120003
    0x3010303050a081605030a0e150c07150c1d04090b0a0516031109120a050a050706030b040e0d0302090604230102070602060708160e031006080607020d210216 69
    0x1260342d60b105a42e0b00504401e0000c0070303a046680e20081c0703140c40301d60000549901c504821b4001917111241d01801740f1b040d40d290060845c0c09034040c100310710702d40100007422506104907413003800e81000c000c2031400d03a04c503802048001865081c403030080c1f94200302070013441500a8000a00b440c06600d9805032a0710407a964203c0584038000d12595109181891503204018907040005212844001c1640d2042c6e0940d5440340c07909181d80e49004009110340c00c415039000c42122810601490b0164031400705205000c042031400b410181503050901544c252240407a0140030b10768100c030001c2d0000d4008007041c030340084d420311021600718046079902c001d40d00400304905907015070200080ca051141e4120504540182040c4028541c1204615410800c0d101c941900c021a03c01c041310320703820140071140d140c0300d401495000c031001680414191000310040c0c3d201540c94200580c0d03180348010091340042c0c481c0b101c2140402201000c103404058105001d40303004000d580c100280c6208690 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 275122500 1250 275121250 275121257
    0x14120a05010f060507020f3d0221191e0e03010c03020f070602070501090602031501030606020309061b070302041d011404151a04050106030c09080111030c0a0c0803010303 75
    0x1808204800450140201084d20b0064600b00c4207502040d0398841d0b10150b58041c00d1031000449070134036490150b01a4101ea40b440e8080301e108806103841c0c0c240c442c4512001750081921070b010401442c21043c4250161540103464405058901500c0b203581c2e18100c0b003007003255820174001d0340c1c5800100440e0700f00c82e50b601c80c003030101d14101421291a45081d030b00f8544100402c4a4072032030042528101c0d40c0016005840308450f051550151000310360091116100000f000b44a100101e0240d1003038200b82d908015a40d21458240e80e01e2081e800e040340c2c800b609100025011120002c2c09004505110a40340e00581d82d901150607180300e501a1075032140307580c4028400700c2c070911070701001c50400803104605080c6500d618a5031400100d00603651905c640492409401c00c0b036140407810000340c4100415039450340020020050b50030346100081c0c0c059800541c90805001340d07404200e031030900341d1561f25007001c01c01031036100e5102282402910b030010408200240003850086004e070301d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 275123750 1250 275122500 275122511
    0x402030c0a1d09030307020c060d020f30040213150f0806010303082a0a03091505010f09090b010608060a080f03180d050d03020f090d060c02010c0f08060114120a 71
    0x10310b46103060300b0040c0340b40041d500a10070004404d60016034151100070a6801030390f03803410854400060311500d645000911000140c1c41d405841125901907050f01f0400c14124100b00441d005401c0041038902a509c48032107540031201041540c40800741c94211008507049a03511a02d0001418247d400342006070000c0004106050700004005c0d0f00084100c8145e2001e50105071b0984800680703403000d4150355010809140c418003a61100c040c040c0c00451040c1e44109801c44007002d08006d0042d0450440c041100042d244e500e402a50100b907400312461b010390782001e8084404003402400d4590010290314009104001440001c51f1041100040e569941d00554428100541c90781014010301e0703201c40c1040400d501085a0000000602c0c01696403900144200c803240a07503580c55902c400078200d178100300203841d40108803000c0650001c1c00218810b400a031100203401d000c510104403450300244086d8804d41d01c0d80448100314100c5403d100700c0c501b0755010400f0450b84c01c00c40d42d9460 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 275125000 1250 275123750 275123789
    0x121e0603050307050c01020d0f0822150c0309020f09040204180803040c0f0305100b0102010b1203071703010b040905040f080307081e1033180503030f0a080402030c0a 73
    0xa01c5171500d144000e00050214002d1028010010b0890181017020818400080780031050540010f080d00c0c050b0042d612200700305420b20100080c40c3d0402c0c454440d18040704520298000d0180d254995002041745080c2c0c0c80038002e01c5030440004004a0340a070b42c404551200600d0060300040688c01000119100c0c5024905210070040d26001001c5a21212000300000b031030008580c400d54001e44c6c404139085c12a900140c0c050700145000a40c444c14500d11143c10480010250075024020640c0c1007000a400329480e80d24442802031810b800f1040105202c0c0c0b1031079800003038200d40f00d69903094101c00c158840c420759800998448001810400c00d001a0a160b940c1a0b01d10894950b142c8602c1d05140b03551102e02d154511500e5034035041441000c5505134402c80c4502c1c500b4079482c403985a100c40080041c80100702150120780114519004103190400000382c456400341e244145240002421003a00d0501c00144100c0c2e042c03041e01d4003103604d500c42d803507110000e0413076a03488542118003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 275126250 1250 275125000 275125003
    0x3060b091501030b030c06030712060b090a0e09030d0501030b0601020d0807050301170709020a020304080d030b03070b0d0b0a0b0306010f030e061f0b0c060612030901121e060305030705 81
    0x4011034450a40d40040c044000103061003100070440900b00080e40c5401c101c04a401e028420181d50b50100c03000c0104000c0c00c1d041049800740c035401f0b00f02040043d854003504102e6018584d841e42e045189440103100034600c0103585504034003200708803803d0007120040c00060318400d0300102c41c0049800700380001940c04011103510b42d540d505280d0781510380048002d145000500c241400b404545212103c5244284084005001039080c01d41d610000d8150280d501da00c644140f150500c07c450313030710021500c41d2054a00858000340548501e0b440c020071030340180c00624022000d40d0781e03030301c8048180c2d0701c031b80304038000b00303441d41c020360b01c030f1509400141911a40b60340315400e15040c801c9101c0702880200d802ca50040324003604010343d020740d60b00c0d6010762416400518a0000004804e8113516000415a01c1043c00711640c1440304441c0b081141c481c0242107513030b4082030599000408180d0306801c0744100341c501d5144854a06040603d0758107442c502c3d4403d581704d03040010000d080c00710 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 275127500 1250 275126250 275126261
    0xc09060602060f0c09010306030b10050a081207060b01030b040213030201022107120e06040602060402030706110c010e01020c0a060804021305070c060213150f180b0405010c050313030c0306 83
    0x45001504452820400c2030700c0300c0f00c000344140007064000620030790f142e0003648901d01450b002001e0080d186071a0240c5007140205011309031040120712000500000e00055001503014045202402c00311259944000b90404c1d641d2103051640f11125107415844034030160056140c0016450007a80c514000a4140300c00f1180701d5104000c03c0c0210f007201802d04040310b002c1603000e0444236a9100c00c1d0b41c11143c20400c1c3d0803895205400080004049900145c1d02e40658004c40986142543c3c0380d1054980c94400700703120b6010f030000e01c2085003c0d8002c18215202d08010700543e0403220755203000400105654010001082d50b6805000550a0642d018491400c0210b4100b00360b042540015040045c2e40c5801000103800207404010251840036450040c1409250344075080c1c50004040c00118131041c01c100003440703960003044550103000040003180ea0b440c05043c0b900b4248001110140c404450540e81444100110351456003000c843d0802540038050340e21006045291141c02c1d5035 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 275128750 1250 275127500 275127509
    0x30a0203160e03031204080d0905060406110901082410110714060304020603040c030602040e150306161803080a020a032d030b0f09091e070305120703050f03040c0906 73
    0x940001c645810f07880000403144031a913810800311083c2c0d40d0303107002420b0b0321401c11113402c00d03410004040c0401c0000540280500e1040d04148a03200c0340b903c0f446518018810410700282d0024041040b43d0075071140f0b141c40c9248040306890b05007152001c0ba8800d69218100720000c0d0400031803181807034041c403511024000401c0b24080c040e484400103001400301800c0a440f0300d2000000c40c00700100c9010000080d0b40c000c80a649941e60b070b400b00c50b448001205c10300035800c0081344100d00c0e4980810881c0c4141455018030540d00070a050072504000f0014620b50820940071002c0041034a110180070940001d5001740034111280c68020940e60480018038606070001200051b10740d250140586064131524001500f611180001031070100182c0b1415040901c1d001407050451000c0303141d450140c1c2601243d02a43d03245006140da5000074032014085401140c1010312082c0504010184a8041e00c1d055003400e041c3c000381000c942c001e4404035025134180d5810010208680516001071 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 275130000 1250 275128750 275128757
    0x70501050304050d03050903210a05070e0a090f1d011b18140406122a0302010c170c071403150f0a0b011107030c21051c030908030a020316 61
    0x10308050350380316130f00c1d8010b10108050540751030010b480f1410070400e45a0a2800e00c03a15550700320581c24148031950140c5031404410f0400000609140c015030031000d44a00182c82500018545070620004040180080c070400e520750342074490000c0780c040c80144c020384400001459111016801000e94800d070408020700003ca032002004140d5030f5a94001c42d8458440c20094901920008004110680150041761030600e21201840020800031a980418203a0400d080c80308400602c4920000d100085c00140607030210000510304226001c424019000328a08001036034911a081202c2900100d10540900d805801e5a1808020880448004104a500300d050078410306001c140b00030002d00015446004003410f0f80d00c01d41c80161180c11100a403690030352685400301203030080344a042e184040d81c48100c0319070fa400c2c118240007180d00500900f03009400c8200d2540c2d1400708800a020705503542c0011010641280c000d6100b01c02007500140e50745007030205607080ca280410000c080 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 275131250 1250 275130000 275130007
    0x10504020612090a02060a030209010f0201060b07110406030804081c0e0d021207080613031e09031401061d090105180613110607050705011e0804022101091407050105 73
    0x150719084112a06090002c0c0c20380c88580e243d8a40925059400400130342000300060b0111405a26501401c88400c0903a03034200545202d000407400d80c1e04601a450030100300b0080178000500b100c0395014600005040412002d50304e840d40340c00c0e5002036100000d290490034982e15a403080e0300c488529801c060070b0081901090501003654404240d000a0084a10b10040300e01c4441c100a4500241042c0040310144e1608104c03581e44007040040882c04200d100c895688110342e03030b0324108141c800c1c42d5203a82c1010300e142c88201460b1641c014003031080d507840101052200c90040028a200040c1040008605040c0b40d030900315600141070590f000c241c040380036050a0049200e50b00901d0865080103088001e040c86400041030008669200c200040e49500b04500800c0b403108694098035030b000c3c0804100c00009100d210100502c00140ad050005401860500c0c2e00c0e80d0b00c016081c410b0a40c4400c40612135086621144040d117803a141840350000380c00b01040090080c01c030030b2038541e05 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 275132500 1250 275131250 275131253
    0x60a02040b03180138011d0f0d0605090a030e030d143f010b03090607201603110a05150d0908041203030f09050a02040b060f0c030d050702010504 64
    0x542d00015203110900a08070201e076941e42d400b50404000c40d0160071031400d2071034440002d000c900c1e40640309061200c0c000030007034000d9805542c0b85001904020031002d00d40107840d081007042c1c00c1202620350302240f40c14155010901e40d2040da4410404000248420321460401501407100ca4001c54400d9212054030354015501500c1012501c000b214801d403a8910f040340f0000c46020080c00500d040d01c0c03141c4104415452407051401744200e85045042c0d66200c41da1298148070886020940e58054804540a10312401c0051510f070070041c6c1a4204a0145a03114184200c2140031580c0c8103520b1018000d0109142d1107400380c070720480d40142c000d403030107002c41e5001c02440701400d10f0301d102150300d005030180d81d003020690035840340c8444c0d941d40e110015041d0b03c0042c1d02d81600005d1a18075465105038840c440c90032900c0d0810010510240941d0030000901708000c140340d04010117020060075481004050318a5041d04005035441c4c981c42e800000803204000c010804580c1000207010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 275133750 1250 275132500 275132519
    0x120a060506070b04020f040f020d140f01030b04020d150203060111010618090f0f0302030c0c040b01140a110f01020703020c0405060d020d03030e0d03020904180503180301060801020f0c060a0204 85
    0x10b910301d0388451001c0d0030703584500020b2416181c080e44242c01034200b802d680300e500c099500030002c0480f0254104558a2101c3c03416028090444090000840e04001400030444200b00e040d0301900c0101500094045952025040c00c5209500741000e030700441417010640c1c218a1101003005140003c0081c50318091203120820b00e00813803040525510981041032120050f26495019080303181c07106c05554078a80250b4a41c440c0500e20024000e4100202040c50980100030380010141e54490480141c0c1c02c4605540d840b0121900c184400140d000034510383c203000444403114190f00040c1c40310210304000c0c1c00d2a500e4007980303120f0b070b181104104950f55041c5000032501d80694640000e0000c1d0301c1c058005124113010b2101510601044000301c95041d0002c01c0e4610003a6400c0c81600040320301100f070b013406030300000d203241c209201d001c400308040c00342c0f02c0c0754181c02030010408a980e018001e0072a071210310020750507031000800d0a00030030100104c0390403d455105c2189003034035010003070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 275135000 1250 275133750 275133757
    0x102060c1b010e01090506060a08010912030e0c040e07061206080706110321011d131b05090a06090605031c051c0e0a0309050d0f0f140d05120a060506 66
    0xe40240c80081e50009184400d5001d40d000d841c0e6a0001c0000c03440030b081596507000102e98641c03042c410000041a041c1043c041c0b1005264400d40300c15454481c81810707401761031807526040c60b41c0304280303010302d0a580d98003a4015058601002d440c8007030900c2030003082040300d1882c0c02c03840c9040040405c0709001c0050685e0480340586401003915216244e80d5040d440f4204840601d8502c1c1143c400c0c41400641600e412560b00380c2c401c41d51001500c180f100c5080d8105c0381035010030a07800d40c070350102d03204031941d15441494240080c00107454000160030298260b99101801c0e83c0c480b418002440d46201c3c020140004800a20440d40d0200c1c4018040034030507440d80422502207005110074036804d000c58100050302e50306022a002c050b410390350311144c421303041d400201d2030301d0000f5881c10f001c02c0c0c00d040d0641240c005103280c9425107401c1c240949154049860f044c202c1d0002e0b000c0c6905106814005401d030341d4050b5a5120803400e8084604051701c4001030340c2c83c0c00020002513488a044 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 275136250 1250 275135000 275135017
    0x30f0703173c0408030705071703011814060d060623040c02011401090903050f0c0d03140c040e130203060702060708010602070e070f0c05030f070b0f090d0c05030d1401140102060c 79
    0xe1355981e070300c04400b11520b000d02c0c10006c15100c1c0d004031114145003070201540c140e40c503000015510101951020b800d5403a0000c143d0305000010300800c020f4241400d0115026004500100c1c51b25a1249601010314805018010009510441c0a070a03c0c050040b02d444a280307100038881015049940a60840184030700300c9044d0782c40d10b00701c003010b0244040e5110003010301c6195071a6044044a1601c8845510480d40041d2401403000e0a405000456038082e055240c481401c007400d0041010709500040c0072220003c210445104c01070740c00301709480c8141c0496014007981c0c00c0c0340318098002c1c1c01c10380001703095421000f8288400003124800742da0110321850080d0b0700496104060b01e2260304810301074000d002c006030801c03090018a00400c0728510610b50a4496510044540c00004040d14800c400381c1181c1041513030148109007000445010344180e078900343e0901c407480d0455070032030641d0403150003641c01080f8815020401c0c030000170342030000d802546040024103810744210103d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 275137500 1250 275136250 275136263
    0x80f0a0f051302090a0c050d0e21091207060c02010f17180d020a0c03030302030415061d090a02010f111002040b030108160305030f0703173c04 63
    0x20921111a041000280500502084030b800d00c042d296603042c0c20110b05070302800c1070201042103000a0321507a0102c0703034181d540034144050142d0b800c005d8a44007400300384074031840d588840b071502d04521000d20340d03540c1c00c3c0c11541c0f804114140030394002c2036242c002c442c2d040b01c00b003040031941001c0c803d00c009509180219450300180000e407400b07000d007901c07141d10994080030400a8200c00b038503040800030040480e904085d130031100700c0c0d44020b104030080402e1480502000000d00070b40181d81c21030b11401e541364030300d821458880f0841d4560360140d003410100150211211714001030b002d4108900e0809030042040d503070006000c0380b9000c214403041043c4001d210700807503818040c648008054044c15990f0b250b8902510060f03400c280922082401003254028081d07c0c5401187d08030b9902901a504040c5190300e092510b0700709900c107030180080c13088003803203035190708010500c00c5040072080300c00e5210001c0d005032102d124001100380460180c0303081c8400c2d0310400038250b103d0361104 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 275138750 1250 275137500 275137531
    0x601060e01051b0f100513020609090c0c0d0309031b0809190803070503130b03010602060412090b0a0c0501060b18150c0102070b0f06030a0c150e19140a050108 70
    0x405a43c2c0c50321a044900c4424042d9030340b210b0301c0d000d012903041080400c0c9201849642c81b0031030503c152040001000b90320034400c2041300103500703000c207459501040e030707032a81070030125400c0100341802000400140000c1d40c0c0c00c0318204164115501580e103112009070f07900340200e255504155849504c0046102e0740c0c6101071000c21022454084002e045d06c001925102d802e940340155803500300c3d501e0810001642440400d6010610068a0480b80d140c0c1c010609616540c0715010322075030720203e050801c080c0b1a000704910305128010003413140240d851062028a40c1810b90031a83c03d5001a0340e045010041d019a400010b0004090914200c03800700450b80c550101880b24030421012400f194008035594040c0041010510701c580344162500407207989500402d600d99080f648001c1008112040a01040180002100b5003403140e00301005122903400c000b0351a5080c1e0922060300c2001e00d042444203000003540d0862001e000c4c0c0703690030101c2c180800606054801400007180c0e00540 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 275140000 1250 275138750 275138767
    0xe01060833040303020d09080406031413021008090a0b0c120f0c1b0a150c080a05190b0f030f0d030b031c051c020705070312080f1501090305100b040e0601060e0105 72
    0x1f40e011503d03441d449007540e80d846690742d1029010381943e040c01c0c1018a00710000425141b011130642607100d43c000c0c205462a036058200ba11040c0010305104040e1003100303020303800501d22502c01e074001c4441107000c80d02c9240c0500d414801900088c2000320395070f07101040c450790400c0c80041d580d07210540b20b1540060b40021041c20f1800c4003144001d00100040314948a02c0c541a6002c0340a06281d6a242041544c0380d500324070640c0c40c107a640441c0c0c1941400080030515280c2d200ca8035545000741030108008131540041d2a022500044a840e600031000302249030350144a42e41ca042010380180440403da0456207510601c603440100501000080d01800281c0f00006a43e4946400d8021501da81c21800d1103680c958103404116500248401039160344d60141603124800c07050002c0803c01d43d43c5210882c05c804a5003410641032209030304c1d0201c0056410303c0000444400741c0f20000c0c1040c505001c21060314910011001260000c200610495610000d04041c10b0740a003072035039454000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 275141250 1250 275140000 275140027
    0xf050105030a050a1202150c04081603150c1106070e0f100801031106040302031e011413113d05070503030a02031012030e0f06090a0e0603010e0106083304030302 71
    0xc48481d420311b207c8203040103c03000344007005d001650042c008407500e05440e08841d200c00c0c0114000506410354945101d49c1820f155000132244081c20700d450301c5408540c0540c03524180b82074035010003080120035002080c0c1440c10101046a508880d480601d030017402c0050440c950600029219084902c0d5852460300e80b281140c0007150301070101c800d0504070240d00306442c1000301c0f06110550130040c509081000009845005d2090140c1500721040241d498040000300ca00002d50030101c1c0181100e00031405d540300f004803c040a280c0480c40145483c0e844a0000107465179061110500c120800700d400001500c0d448500c000005a4a4440d00381819200070b1035805441c0140b008150703c1c0c10150711202d05481c11205072070321483d05001030700b004214002c0b010b40540021304c20008012140c000300c3d41903005800038000003078040b1140c02c06c50a5688640016041d07034800c13001d120b010910783c02005c40500d20a11009840310a102070100161000340000c0c04160700810130308141044c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 275142500 1250 275141250 275141263
    0x405012a1b060e01020705010504061d09131505090309010807141908060d0b0727061e020c0a030b0a020c0d11010b06120103061508010c030f050105030a050a1202 71
    0xc0040c0c6000e058600c5500070306000e0402c1c003411001600e000804500f80d40002a10001d80314142c4801c1d09150410108481100300d901840b403400c2e84070301d50310051780c4403c400d07140101d0202c1a04130742c03110789080c54407280d400095245c03a803a19000400c820120003005803010f04009103003401c55070319104021104445090304200800100282c11039400c3d2103000302000c92540f548507402d160340ca40341000074003040fa01028010050a0b000a207072940b10b5082840c1021124111500d64003c0e030000000c4410507802c86004540d243d42103040040741c04556010041061008114284001c00441d01c1c400191100038440700ca06804100701d80ac0b107070155501404003908030768500148010003007130001c4035414100e06520b4805500f40a0030b140088610900301b01d585c90005d6461643e44200a200ea01c460498460100705c003c40c2c2c9002c02c1c050581c0044656401081d2080c00308000300840300180d0100f4420360208c04048000f40021400c00e000a4102040240100340040183d00300507 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 275143750 1250 275142500 275142503
    0x507020307151406010206090604150608031b070b030c0a0825020c090901060311060a090f0305060703050112030c021003060512060a0e0d0203190903230d050405012a 73
    0x240b0501c12401841c980358007082c001000d0340550f4605407100801661074103429101045240c2050001a01050800712482d5407260341c043c2c0050902da80741042811030304108a01c0c2e081003800101140321200400825000e030940540e9079240d4207003050740012522900504001b40010341c40080c401000b480812000313400d40a00007013041d21400c81c004d440c1c1c091000700034820383d0030001082c181c00e414811101038943c416112600b41111074100b12013a04054400010480c0c8003c011541c01d401c07002500c000c40c0b041005001c01c1c1055a409402d40d0780c16003000e440315001d42441c4c0e0102ea888891041c06a0301a10584070189803201d08401800c05038226a422400010f0b410625010001d07400e440343c0200c4004001701140814440d8540f4001100000140d006101703020580c0440f0100b440400e005042c40b0700c009680f6510160300441c2c0c2d1017440301080c0030264800b21110144840324094801d071508500d41760520002a00e04a00000c580c0e400c504501c4410390540000c90f1404580c0b07 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 275145000 1250 275143750 275143763
    0x2702010e060301030602070b01060201050601020d08040c15080f01080307020a0b03060f030111042d060f0203070606090209010f0c030f1b020a0b0901021605060703050d0f1d01060f030b0a0507020307 87
    0xc3da100c0c00c3c410065400210203e0f480b02109000280c1e0501c1823056500441c4142c1c007804410000c907000f265400006442982c0342e46801a0008114842000142c40c031420b544640340d11307107000c2162501a2005a10010300c1e604100005801aa00c5034402020b543c0e42d50702864481d2180c00120b00c0203031001c94065010341c606210703510041080300251040700c102c03d0b026810401044074030b0b00c0240070781d441201d140310f00100c00e0101c90b000d008500a8101d10740704603030905115843d20340a03126580e20401a00f540020240040d5900c28590301e4050882c0c20900f698050cd594000c0000e0310f1380032900200f0244804a0301440c4010187c04144c64000b04000c0e0341c1900e601c104003071980801c00090141c440c004040800c05500410f150172902d004000c282401d103243c80903940d562001d07542c802d90513528000b0400c0f008291003443c0d4203440b00001180c460000c2003006007180d0464003d03165150310f180007040082c180c5500643d0085100001090303a0322500c00c00d0740303140209100200380 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 275146250 1250 275145000 275145007
    0xa0918050a03050903010c0306050d030507021c0f03090e0f0a0b01170118051e0406090228050102060106030b0d02120a08030c0d050a050106050a0804140f0a05102702010e06 76
    0x24168080003410b0245000c8008000e147d103a228280c0840b6218400c1581240421000002090007030303025148550000e0800b07912110140411240917032003550841c0c00f5502412031105040c0d01c0101e40c006424000c840086508000d446640801001400e40e140c0a486e540c003540c0503441340443d14001c030050442e0309910750716050780002070700303626146811440c5003100040c082281e144200c84000b00e400c841c80082d4889443d180060011800e00b644c00c00c410a804422800400320140704181e9000b86000160303042000080c01c011041c1c0c8180c1c101404c0c80c10340022a510114142956076046a041c4000007034100310600f8030545600103054100088200400c0301e940b10020081d180b5516420400350742c941c06180100e40c001c1c00791740c1c0006d205000b6000c10900070340400d504503003c0c04420403c1d203003015015107040d05003051008076403c407030340800800c07108112124501003030303d070f0034450b40b01001c204001705001c40150a0000c5042d084520659009501c200b5880f01c0c0508059503 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 275147500 1250 275146250 275146253
    0x614030405030d3201050f0315010b16080307050c0610050f060313080a02070f12030c0b0a0f051914070f08150a061d09010509061009090e070609140a0918050a 70
    0x140d901c0c24820a8040d112914460241d0310b80809c0c0e43c3c541400741e103684e0140342d09140444015030042411b91890740014920107001c105080007131441804541d40760340e5901074072070070709040c544003070510a2444807844042c821a5030328070028140302d0f81500c04139100d9594401d207a41d61036181e2009480e0100002d00610095408aa04801c1c0e622042240700300c0c1da41d611134550540042c04010740060405003030440098021401c49400580541d80444c0d05544000b8480413074200b65051281841c08000041100c0124051640480907c21801300245801000a42256980790341c840c01c20a010b0000303001d42106034501d81840300302810040c0d07040d45403a406003170398035944e407000010704031800c6170401c80c80c01c90300c028141c48018051800c6a2036201c180302000036150030660130320200706408143c80c0000e22882c41e04124140040400d41e1905c10040d040800307903084110316981000c42c3c04030300d840d00c3d4102c2d0f0032a8a40341000034640c4220040702204000440300070002d006140c0c0400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 275148750 1250 275147500 275147591
    0x1404020702190e070503100b16020306161404080c1005120c070b09030a0e01030e030706050a0603170307051206040b1c0302010c020d0207090b010203220614030405030d 74
    0x1803e992030f0541d0145151680c42e0252990700080310b8548490707080c00c006202d6414007902415041c10340e41c4583c0480e001d1540020300b4002c04a40941f0340080500120000903880140380c2c000100501e20350346001e04200765503441d44448052180200d0005803040f450501c600700300c51400040f01c040303504c00e007400ca112102c181d20a4805444070035106000c5801305001004a4112011648800080756910340c0190b01404500c034203005180002e20141c4040303005406400d01c100c2240a0010300d02e801c5151407c0010100511642a11030134401c104410350000c04a0b91160010304d0300305141d42d85e503000030b40508150b00c441c0e500003200d080f006200e10002410494010b01c02e400030700824080700c404036550b0030a0203903140183e2009204000d440f41c550302c10300901c503040c4180c1c4d10340044c1805040807542400f0424080504460003000210380c80780301e007680140c1140c01c4a1548c1425158030b652401052443c0281550313612400b2002500100c4840480e01800903070607020380c0d90407110 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 275150000 1250 275148750 275148799
    0x90403030615092402030f0a11010c0807050f0708090406030605070905010f0905040f062d0806070801030b07090e0c0405040e03030f240303160203011a030303011404020702 76
    0x812004100c00e011034202c900812002c41500c140740030421020103102003081056030a41340080950104008040c11038000c0301c004e050545440c0c823030b042c1840394100042d00b1107a603140c0e00d80410081c0030a1180c000e610204480302c4092a48000d41c0f552054201880c0c1e52040600a6501a01c0c1a40020402c00690056403044400e0344900009a6480c0c006450400080e0340350360000e800041c040c04245847d80c0002008211030f540011a80d4403440c0842000c0d42e01d211551001c2407402120b0101009807484070041c091079006000d190a000c01d024100d11410700000703082ca04100c1c002800d80d413007100c2c07a0000f0049000490080e05001c0032000d46030b801401002e000e6403c00d0040b4480c2c000c00021280035102c54144c4512603540c100d48042c0b8881d2040c1c1456052000d4005001d9560b400c0000c2d000704048107118605200581c810142143c1080400c0008901c03040c03034580e840d0b907011095904440044001480c2006d40c0c0c1d0000b0024440e681009602411805900340402c2401200 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 275151250 1250 275150000 275150009
    0x8071730041e05190b0a05131208120a0e0d1110050703061707031a070c080309100c030b1e030102070209010e0a0e0303040b01031b03060911040f0b06030f060109050904030306 77
    0x4c42c88504040643d0803002e5801140c00002d020841c0d4041d4034440c2008142405903c0e40082c4100d8031201c255040f00c403403010a44070590003013000b507241c2e1280030b0150742240300028100010040e070b140c1a0f1315407490322940d07006c3c402c002d94140304200040c01030038844400001c041140c1d20340031501800800841c00340244907220f0107a5004403c1d8005040310560740c0006070030311440840041c402c0002c1004091404220b0420441000503039518003442c0207440000141c5a00050400b81c14221440d603074850b810982407240032740494070707480c00e0440b0b404486681802d03807000c0003010074064450810001d41007401500006460748217000414080c280d130311024400d088030031039455684c1c0001e51307010b410380e031001004000148203d10189101d100161004c0c05856603030700c2c1e110860314081c4050f6141d4141c030402007114942885101500d1320703d01410080810341601003043c07404010300c10080c05024101160b42c0782e00903000840140b80042804d01503140c1468010042e1607103108 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 275152500 1250 275151250 275151259
    0xf081b010f0e0f07091a0a0602011a0d030e040510050324060415121502071514070207090b0607050106030507090605060906070602030a0e0708071730041e05 69
    0x1203101104000b04003440c3da100e42c2c00040081908000e510002804615a40076005112003601d41c0b807070300c0e01c120300c0000301119000020754440d0520142d03084059065001d206031007400581000035044414503091a00c150390000c1c81f6640da1440e560301d02d807035402c2994144100c003a0100e0110603116002d011943d80200010192990814070041d94101841d42e11001d07e60242444040002c00d5030318109406270342e4842c110981511200101d82c0b0843d401d48034102240243d001e4043c2c7c1e0b000b4003d201c84070000c416500d1030040704c001d44400603801420106600c1d601e401d0007070703a548000c0d40e2105401070001c200c0345582c1e1610b590384040301d1280c40f40860401c0300028040c580441074912188003d8540c519211841e0364210013580014681540320f0703510780304240000420030814018061707110040168a0070403d01da0300251140c1c3d10444103a00c00550030100d840480341c0c04840309020341844002e20003008c0503420034022500800c4161803808602408801e0044584003261010303103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 275153750 1250 275152500 275152511
    0x6080f0f010608060133030b1c03140d061a0a0f02010605030d0c021c0605011403010203041e080d1b09060f0f1206051201270c030f081b010f 62
    0x400407400d03a003142c0b01e05002504100300400c04000d0b0306288020a01e203ca0010465a10411614105440b5501148002641c402d100c01c46801c02054408203108908552586e242c4196001070890302030310642401114013040c500f04ca424960400e801410106c18100d24150b1200100078140c1c00c00104103000840f4402050f1b0b8083c010b00c00d5005541010700585890106503505480c0d0f0b0000c414126000460a00c400c0c04000381d14069010540c426080400c465244c400501629204507003002e1099104105010020f03507103801304022285010380f880280c01960404150070702030050310000103424030384422038200030090704a09044881d00d50321402610780c24202c442440b00044000891003441a0480355405180800c81c000c200c440c0100e1034a840d140444c414840810b80b0f001180c1d1a86000070b00305211200d01540301221102c0b20b00c60310302688401500085511010b080603c282c2a80c9061010a00c21034014410b05042c1d024060000c0c003019000303180042c243d184003441c01 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 275155000 1250 275153750 275153773
    0xb100e0a2408060d050c090408040824060102030f071b15080609070509010203030a0509030f04030b2d01060c0302011b18050901060f0e0d020d0302070e1005010c08070c080106080f 79
    0x112021320750b19070081c0007050910220020320072000d10240c02030300d00c14000d01c0002004441044414031224070700c56903d066956140e51000481406441681076420070301400303031080c40201c1a500501e030815042074006a9000e00307000d40011230340040d0380300340194241c610402e4020740d14a00030030095648001c2a0365854003220b440c060441744a005800420201341070701c2403034115640200901d13081e03a140c4883c00c0504d007800d5105038400c64082d01e0f000200320075025104110640000e2800300b0700c0b400d80c0141349402080805000b680284000500c4900a051003540442c001e82c801d2036460002003a417100150400070510401e15085001c03800118150518032400b82c1250513940b14a500f40b101204191120a0f16070031903a0454610703142c000250f07440303801c00300a142c02500034000913818100c0c0c822141d40c0c0104102000e20100f04d040141ea40d0040c0ca480c011a00302d0b013101d031581500e141849540046601011043d82894004104031801240000c00043c0c00003c80b480340454 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 275156250 1250 275155000 275155009
    0x409022b051002180603060f0a080106080636120d06031e15110c10060513060501090302010f05090904140d020a110105030c0c0111030117010b100e0a240806 69
    0x110161098a040c4c0340e041540d20b410503801a540114000706201e00c007007614030108407540c815502c00042ea03919a842040407503400d20000707030414500d040700030070710711901444c00c50902035440b8054540f001c118003005a070020b201c5090301c00e90b0305140c80d554081011121001d00024002038a03188038034011710050507040e001e0444016400300015040880320349080000b00042c0c21a22108c25040000d01703000c0300c0500c1a540381112503003002508505241c1444402c0158504c885a0f0a2414800344080c1c0c1c1c100181c40c08407942443c0002480c3d034a03100803240c0340200c02529804c0079042e001e1000700000c1d204a81504031a00007201c0e5020043c0c6000c90ba1284030b11800741203030100054103002c0e07502c06e80065900030800740e4650726003490030881a003190100080200706000200042c454080032003468103d42c08018024001c405503c000a0843c00300c104002d401c0c840c00008010312510b600d501e0b80024601030410105500c0081d00c03841700c0c0e205064580c0d0005641c6800078221b460b0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 275157500 1250 275156250 275156257
    0x4090e0129030a150905010b0a0605040312110a060504020411040b0409020c150103050d080705270a05040f06090f02070f060c0302070618030216140409022b051002 72
    0x103852149000c1621070480d22000e5903814803a4a40600402d040c41c00424040c821109a100540c240040d080c001070809908495408c800390344104064401040441d60110a1303030290f036042a480001030180040c103640e1012000c2c81d81c0380d01c1c0a030544140502005a2043e80326034000e83c2c6c00d001c0d404e06400c0c402030030310403405400c00070882031100788004401030340a0b02c4410b642408803402d8400c6d0340c16480c00c01c0403da10841c0c50b43d002c41440c2c8100c81e400b600160b003002c403608280d402d02a203030501d040141d51002a001c1800701c0103112846a50f10310070010010b150280080050400e1044108040c1050380260460941004802a26001640308035441307160010755208800c0500e80c1c503440035010700403400003051740078405d040c0490100e11170900c400c48110400c1940790118503001e0305001c03818000302e680c4950601300b00183e454142140c45820002c960004859500d84005907240c1e450381544500e020b05c640c00c00750b002080040301000c07035000d0030441313001000c010b040308140d11 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 275158750 1250 275157500 275157521
    0xe060f1308030c07080415030b0103020a0e0d0309030606060f02160609120609021903031e0806190e0a0e07090c02071404090f0312060515030c030c040b0f04090e01 72
    0x290351191502040300880a160400c0328650441e181c100c40da11654200d400c2038104210030008000039002e400d4140c460400002d40a00b07055003025590719001c0c04200084081ca0b003d540624070800c2054860b034525005503612920402a09031180c1c4003c2c003150441c0c0c0c042002d88521010500c000800c109507800702c50f01079036000c1c000750601601c080441c1703800707a04555007903c98a90100503034800706000458400300111040341890341c10014a0f0300000443c01c0c02c0c1c14502010408003d903c5405140e01402c20380d550004100c4c0788800c0391203d40341c0d43c000220400c451080c0031443c0b03805d81001150880840031a09400d80381da54a00c1150f01680844026901100082090180c1005400e140c044001e000244201c80303500c40807009190010118006180000300401e0085240329030f4024001c03c0d500c140494081c41c404098900c40680400421400480082d01c000641c00449004d03002d410009a11054421408826501b182c0580c1155504000c0e40c10380c455414403a410005 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 275160000 1250 275158750 275158771
    0x1150e01080307141009060b28050f010c06020313111f1b0813060912020a0b030406061d1006030e100c0318200126060102010b10030e060f 61
    0x2403041c0e541300929010b4402000841c018040c50603100000c612076450402c3c01070801003489080b500402c1071a21441001c50090004102c204602c00c102500502c01c3e0740307003a076030b28074036402e1840140e0303080e0780e10007006007480c0c0000104010384404151307540b0f1407449500c446128080f20000c1103800200c03000c0c5083c1032240307a00501e000c00c2c0b04180e4020301c0b032401030302413010f0460398480c1d00f8142c0c0071600d0341d1a480340381081040441d078015102001008481600ca0303c10f0f03690342c001180c85085125143c00d25102001080c00d10645602400061230050003c07010440c0c1c0d2002228003039070803100c4951910701010000f403598064003441c5110340c43c1c90090035070941d030b1010390300c010803008419000b003565400001141d202c071460307100803140c0141c61598040040005010044003000521410011600812101400105044000c6201ca407030b0b1b00090b0303030b105c00040340108034243d442d80e801002040c690f407080360140c1c0140154a4504151020f55550b4203a1641000080e641c14088 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 275161250 1250 275160000 275160007
    0x9031b0d0b04030e04060902030906100f03020d11030a0302060a05070c0b011203170703020903120405061605101404050607090b030a0e0f071d0a0c080c0901120e01150e010803 77
    0x100d506800c690b00030b21034140341e00e1a0080801090441d0304c103403c4182229030010510213001030070002158410031004a501c5441d0406d00e0303801c0003403000d01c4001d025000c0600500d0400082c40b0b0810540f2001a04444000c40141002999410152041c0c82c2c03080c44c0c2030100e061140708103104003079a5001190741c01e00e6481d0403003103114540d815105504000750b03a2500100c1101c100840c07030199800d0303900962103845400c100b506040c00d152034031280b480c0401007005a900c589054800c01612889000c21315030403801c10b141070520042d03002c01134600c1d00d40d881c80440c032201c8000c0e0103240160100c450903a01c1c0c000c1942d03541264047c50041420a1000178103920710798001c0d0302c50141410035588480100000d5929005c042c4e0000360072004640c080100c0f02080c0b4200c140c1c41a401034080c00585281c2c070010b080124040d0540540301c0e4005054850313139020f000c2141000d0800b160400c07420301c40c24030550080440200000c00d08119140000d50403015500c828140c1e220703400918036 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 275162500 1250 275161250 275161253
    0xf2805030603121b070e07020c270907030c0b0406090824091005090304030204110a0e0d0609080a0c06060b0909180a15050108150112020d0606050604090209031b0d 72
    0x3c01c0d01320381d0843c4c100c02194101096503000a00011008010006245200381408807001c0d00741280025082d026244042600750b8030344800c4005c40316031512030700755030181d128510303001d0520f0134580015212072264000001d45064010003031003200d01c9665103000c640e44510710f050310380442c84040d160080b034225100c580c001c2c400120a8000d1a110215100050301440920076500d0442c0c0841f155080410304100754101130064101c4800c00315100c40c50721611640241580c1b40c01468079001d44c54050101c0c00300310741540311004c0343e0b03000b070150b645403600301c3c00040855801304d004442c0c0d070f130070048000b42d80801e082c00d66143e480010f021444a940300c41c0c1504071011004101003c41c030420340100046090740c20380c07000544542002150750f43c10440001d280c00d0451050720080c403171200042205122140312901710f5503040340e0500076560541400700150203580c00581c2d00c840f0000e80081c20920903801032840400c140c05a50701004541454a000618014480e812a566801075030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 275163750 1250 275162500 275162533
    0x5040612020f0118080109060c02030306030703140307240f060f0b0304020301092405010806070f0c24060e090a0803060909100c090509092a060f2805030603 69
    0x70402c01d0603d001c0c001520700d00074046000105610151480c1d540381c0111042c000140108480900f80d8002140380d0b00340750000c20351740c4019110140040454400304406121f060048440154001d14040c1c03002081c40010303d041c11100601c240c0d00c2d441d000903480c1e09145c0380204030031a20031140c0442c035140351410a0105d54070040c800c0b03a05543e10032885c2d0000341c007181c00c0104400c0d1aa2030300040b104401d50b10f421190180c0014101d80d001c0340070820040e500000002c901141ca1500815404440c60540c90f040d46800004003603584104030080034181d127034000811144480e684d03000ca5103417042081d0301e46010540237410b2001c200f0024040303080c0840b810340c1240c00c0804407500d4048400c900000c444503684084000b48846034100400d18002c03084507040754026028109014502041c4041c01031060b1500d074503a010221009056034405084c1e8407130380086507440707035180741500007200203184a00d4840c414002922044070401c0c0b01d4010350384900c401400411482c0305600c1041c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 275165000 1250 275163750 275163769
    0xc120509071a0f0c070513020309120a0e09011403070902031501110f0102030c0706050a0209132f073008040f08070b04030e121b03190c050a0504061202 67
    0x942e01e010b0308000f62040414498020490b00c0d0030340020b808002d00300410400010311906a80f550180103000f032211140020484c1030940c28112600381d40c0da41c00100030303100c040700d4481459004841e4800050380d40025225081d20b100128242c500e07450316140d41804900050b41d000000207078645031030005500070586541c25010540446043c105050407550a9900865003000b2489003c590402002100d0107520b8019517091025820143c038040071525506200d0b110f03180e096151100c1c6145001500d0703885e8503d180c071134111003454009a55480d207684c000c12040340c0c2d4403109090303221600c1d078007100710424014683c01500e000c0d00703001c012201110081d0064405003043ca00100000386440002d104980c0b01e11281e8086260a040c0039148002480c915030107140c201400301d0b8002404900f01440501d445150440e040074040800d20b07280441c802c030303204441400105018404000882001c80e0b41c201e4010307903816120302c14031043c0c2d1420302c14800021422410180186401c91a2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 275166250 1250 275165000 275165039
    0x9040212070906030204060e0f06040902040b15280801030f032a030201051b071707050a030206090d05040501080c0c100f0b13023c0307030c12050907 66
    0x32a03192001404446050844607400900c2c0c542d6124010001c40c00c1c68091072000345101c004000041c07919409281d01002c000b031055108654840f111000c41d035941d031004084810141081014002c68910340381c0b0303980400040c10b00c00e00900003683c1c4070145080020140449542c03407000c16460b40d0348009078402c1c013110440500c003840d0010180362a0040c034140c0305150f50302d01000881800c3c18081d003120006045180290507a0460403000b005040403248039aa01c80034169802102d107640c0d090034001c141000b80140548030201060583c0090910f025560b0041661007520845c0070540b05440b031403007041d000ca180c980003d00d462a408010788205541c00c41510440a041290502159451260300d1072580da652450689030a142404610030820140118680040c0c7d03424500700c840701c0204d200c45020010103c884030301e1502c555100006240700419101d0411100280c00f801582e412080019a030812a20341d0590034043c80e4003441c40c942c098001c450809112982c000090540c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 275167500 1250 275166250 275166259
    0x9020d02010f03201c0501150f020304080102040e040b010e040f121e050a0e040204030c140112050a09020f221a2101180506060402030414010219200c090402 69
    0x32071300a03c050140072480900201e40e0726031340c440c4040d142c0c40855804444000c4124a06001442091076850b14924411400d05140d10700c03c0c1c9042c400c904e113204580100301903500101780040c000080e501d0b43c0340514403c03402c2c6103a6a80314071244c0e0b03d0b44000c940c0541308010804809010605070074140803801c50034602000c81541281540001d40380070026a400601c0009009080135400303040c4101703180e021207040d072038070f03142da105c4080801140c041c2c41c044000e402014506a8092443e44081d030222000c1404031307282880d848401800c50081c264007a00202c0315100c201d00d01b207881c1080c08110a000302002d08c910200d100c0040075a00314250f28041444030300d1400b0354607900c00300d42d1032004800e8803907502600210a400e41d040761040d0740c2550820000a0002040400d02c41d501c40404d850040e104d6030303642080144140300d0742000b4095440001e03404420116003460000e4616643c90382c60f5000c2003082d4585445000001d9041075820030083c00700c8925103a00d0440d04180000e0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 275168750 1250 275167500 275167511
    0x306110f041418090a1b080604060e0102120c07020f0d0b15030c04240b0403030816020a060c03020a020601050a0b09060d0b190f150e2e020a021309020d02010f03 71
    0xb101510f10070540b081001039100280716010040409017210024030002c1c0ca07043c0c0d0034908828180c0d00c0300c014000605e000d490342c034035001e80e40b005d505903440c000c004081546103080c14159242640d0006400b6401120748000f1402030f42400d82240303000c141d1242d816240f81d42c0c2d01681a03044024044515818090903121920640c0d5a0041102102e80c00107144000b40040c0e024a240360107950244000702c01c2404200003103a001400c86902a006c00c03100130710850360322401c9045c4240b140000302500d107130034441c0401c03990540c041c0c480070b00c00d5022a07440d41d0b25441000110311407481289600f400c10410138826082603009060640324086010400000000005200c140c006502030510319640c0000c200ea0480c1203044402803011400390045040d0200c6d000b071850001e241e00d02d002d5003000c1c0130081d10946c01c04503081c84c4030300f440b8020b103520300905009440b51405803040c4d2003108060085503a1031041e126104915500500074600d1014580c0151a01c5168515030020b041d644c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 275170000 1250 275168750 275168779
    0x1618090c03110a0e0406090c0c08070311030a0c11010c020f0d0201050706090b06010206130c0e0c070c0b0316050f0301140a0f03030201020d0f0504020f01111e070306110f0414 77
    0x3407000d8000400346488489000201c4c200344004c940a583c0300f01209070808103000e0b082904210140242d5802400c4141e85004a08007543ca844403501a62910b00c8005a400409a407051a00b1885441415440d8000501c0b0004540a002006000c0d43c46510300e06070800c42d14040310340412191060601608214a644400301140c030b46040551786045500b04209656a050004035030040ca08170a04070046401e0f240d10307498000b20701880c2c0202008002007201c03041640c0a680317403030743e01c0000395401c5601c070f90510086c0e800a1b196105030410800940808a003d04d0503039071030f0302e8504099411a80b803c000c14040b10224160a42c210f24290800b207030f0980ca035141c42c1c01440c06034001695820890481000300c840703c5515600300c91804007400010383c0c0f9170210344100701003464410b003800690f428540c00c0425203440c11111200e60382160701c101da00171400004803800b80000300030360340792481d0b115194410b000c086c280106007004144500714010950304441e160181096400342403d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 275171250 1250 275170000 275170031
    0x30c02010b091e011208180112091a090735070e100b031905060427140304031e080702040507051305030705130504020609030706081618090c03 63
    0x162000b421504500060315107034031090f280203004020055040781a1030031501c44001ea401145104114000c50104003881071303104562801100d00721400c00c10600f04680b13816050900070002205e03165003281c0000d5005035010840b4000c40c1c0b40e6031070400240b800404100e6814200900c05035214641b80c00d80300b070902c010480e6002038140c5c5212555a403c21036041104100b00744c0c403850314a4020070070080305400b0b0402c400084000340c413011545844145c0014040e01d0701d040c500007034250303400102c8003010b400820785140c18000c00e00d0300001100300c42810388910035800080c1a4228400444010034004415040301501810040c0d04001e120745c005400d0b14010b9543c1d000107000130655801880480a01c0d400410003100101240c40c90070020541d12181d110800606540d144006002d5407540c4040310f40080009003a43e00c0d0a8607040094040301c1e00351065400003098101541000340100e01584414a45c0c0e0700082c1d040d032410322014040c00c5480618003c2684461041441008 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 275172500 1250 275171250 275171269
    0x16080a1407030b010e01080c03030405060a030b2e090503060421050903010504080306090a06050307061805030f011d010225023d0302030c070f08070503030a02191707030c02010b 78
    0x1009045c0030115458222250702c0d0403814040c2d60320a40080104000c150359100884090500609002c0340710300b061000290f0103030240c4103e01158003c030084c040400500000d04818801d03e840d00079945032074000340766461400300c03402801404025070350007514415102c04001048980b80540c9032500090100c8c0c2949c400b51405c45074404007000340403461800d500280d45c483d217295000c208941c50103000950390303103082c810641488541078424046004000ba02da02500000d4216520950325800c128000c2400d003090092080401036020300544060003160308410b06960f6041ca1820440612407189000c80c00499100400002c210102d40318000315411400101c0007004483c1a0100300701078421000c0f400d07004251040003006500445041501e4055803c404403014249051807c454240310300310001d440c510010003000406000c50b0014001c2413000107a04500c4584d180d03007941d003001060b100500510a510000b68076502c25404001c45c1d0f0160720011030b6480002c008551080c2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 275173750 1250 275172500 275172509
    0xf053108150f070203030f0a0b010210090803010501020d180e0606090301140106090510080c0313050304030f060f1a300601030b0c0c070605180406090e16080a1407030b01 75
    0x11202040100b1900c0315529140c1c07098841c0080c2d441c600d001c9014044800008044142866451344640358591003040003055086101c042006001ca0030b0800f420302d600244520f6006204d203009a04015105010641852004100910205081c821500600000146140d8120509200c06500c603513090044242078102c000f000030f0740f941010401000c0f840ba80d0013280c080e242000000c0c40c02584044910360140c88006229241d80b07500d400322041c150a034802400e030f444040b8021007480400e9581210a9104080c10444d40104a50010a940103400d030a582040c0600400300d03a8201501c0306000d03610810443d22918214014806620581c540c6640f09a885000140b08100c40848000d82140240c2103071420002840d480a60700c04090107a00704105001c5002150115500e8049900c3c2e0790090040c00850340f224405402000c0745a540c00c1035205401c040403403490828101019221290064100300c05036884d000302000900c482e0710950b100f06500000420480c032151030280 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 275175000 1250 275173750 275173783
    0x6030a15180c2715051207080102072001020a020f0103021308070f031a061c0812070c06140106050a0e0a05090708061206010b0702040905010b09090d0f053108 70
    0x546518501d502c40e542c00d140100511454030314042055104156031300200c920031500c44254003200181e032800c0504a40c0520625030011403000700f045980f801404152450042407041c074001c1c4001240d50304e05658020b07400c6214030042d5950755200741c0040007002d24180583d1042940c034004145080755a03441140c05003a240c2051040140c610180d000e404031214000304e8605201c00000c41003409502d00c4050040200004401c000004058602c44206c440111085140410001d40003600d6202e0450f405842e1041d460490900c0352040d5046e1403066640c54281031558105030b0382840110a490761080a0f44000100c5030340c2c0030080c500c01c030306540c0d500c555410400c0a002c2c401031882c4900403a600200010b0003641c856900f91500e1a4049031701252803802c50030301500600071501c0640e0440340e0f14040001c03102c03000501c82202c1e0345644c1d5040745002c0780c003421923182c002c003041e942801d8a4407100014000c840500036207062010b0301d40052081e41da61820340351890403040322084 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 275176250 1250 275175000 275175029
    0x3081e1c0506040b06070b0a0209031006090c080901020a080613090507090207111c030305060d05010e15100f1701390302210a06050a08011406030a15180c 68
    0x3d0415000e0790320f00ca5825a22203040801960313400c201000010910504107a000c114107050740c0c0c00304a001c40e440340b020002c0003040e4503282d1002c0504202e0b00100301280c1c0030404181c46401c1482204d500040c5135986004a46404003000205c4207141e001e808d45507241d0362220f002c590248a000002d04503c600103a0380c0384145440c1d00c00b41110072140f0b1180c0d000c04000d015015224011469040d07151030f001855036207410020750603401561020b030442d032034107030010018a000120820030243d200c20300440b9130f039440d10315189143c090040c0c02150046c5001002403030340314a140008500c40c10001700d0510800d607148044c1e900c0b800c400c3c400d40749400802c800c207200d130f100f10411201ca051130190710b414800020b245400b900e0300c0440b0701050003d00010021291503200c00060600106444285075594041c40d01908640c8503040300b2200f0f04d40410124940018001c0d44194031400c407240940b540c000d031030024210032000c10581107450000c540042d44114048024000c503a000c2c43c0c5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 275177500 1250 275176250 275176261
    0x20a080f0f010b0103060602100b1804060b040b0625020d0602030f011404050c0901180e0702160e06010c15020906030103120210060303050405060906210103020306090703081e1c05 79
    0x3d4500c41050340d030525113840420f2054607804a0700307240000311103002007182031154010036003207101000311203080d04126080c0010407445070420500500d04440603c00300c2d03e480e08100d42d5100d900c600100100c1400b0b6451201d103c440c108205650000700892130520301b0740c4580081c0d034411250b204820307540800600184800c1000c00b403000300c00b5031701000145848128500c0d14811102541d05101640700c0b8850001e0b00c03100444050060203181290341e05019901960351922904100d410103044031012800c40807512801e8800c4c10141d40b0038480340000d4a0303008680c48100c01d896581c603001c20202c65580c0b01d0b2401540290301c20085e1004130365450400904040190b540480d1450030400304201083c2d00c082139909850003102e60f59070b909610400691705100c0e0200000103d1000c8031210600b00207100124102d0b4001c0d02902d045030341c0c150107580c550b0704c2408018500f110a0040d8052103485800c0b4071100d0b50780703480951801d00d46400e904d04109924071088802d0343c46d03408116 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 275178750 1250 275177500 275177503
    0x609010e0f060c0d020f091008010501030f021201121401060303050d05011d0403050d02071703040606050105040e070f0327030201060504020408071206090803161d030604020d020a080f0f 82
    0x26007a184110103001541010340c0d103156244078003000001101d40114107140403c0c1d00b2021103884403001001c0200d8211086000361000c2001d1141030b010a00d46030307040900003054021505001d49840d00c0700c0c2c8980c200501501c590b4649130742a1401c03120401c00700f660980902c140006103010b80c4a850f110b901182e02c03d025600140c0000e900302111554035008406a400001d400a074142003d03a100c0680042510081c081e140c8050708228840e00902e103c0c0c000d0000440c082e5000300e805000082d00d61005580701d1050f4460441e120111030009042c15110341c168840c0c590407450042680c504c11901c4100c8102c007031a051031829031440c138a0007019024440c0038000d220a03203095040c030303180400031900d0300d50f075120b420a0948107603244800c10019500075170a00d9801a505912418004210b016401e460000400880c4d2911407610750004a105c59244905004004140030350700c56084c003041e543d00c00c40898000a50341c0010558140600116149644c0040100b904244002c110b5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 275179856 1106 275178750 275178763
    0x61e010c021914030c04060f03200a03080912011107060e1e150604060b030109021c0c0c06150302151315030c080f09031b010e0609010e 60
    0x442d000d02c0c601500c214081041d812030304d0b00c0409a0511045508600500740030f504140f03000c00002e1044c29040245890f076520b01e80ae41181c420200f0401c00c03180d0070448800c440030a10300002d06041541100e0f07580624000d000320702c601c41e0740c841c0600ca1000050706180d2204620319800800308051014800c40040304002040b51040a9441e04a030140001d6449a8100801c450749002d00489056910050740c0903c2d5074684880c00000394800030824400282628200041c1000d91240c281e11580395254680c1a00180c0740400442c0c040d542403071064010a079041c00541c039a010a40070b940d01001881c0d540d1000c0200890310402554045100c912403c1300d0002e2041e40360300095840b4903180c0340e06540b031b15003190441071040103c034003015513072042c0b0031039103200c2e603175607100001d0000a000001c0c011030380c184c00744c00c00204a0b0028040c1e03441d113084243c1704008002c6e1 = true := by decide +kernel

theorem cover : BRFrame.Cov 275000000 275179856 := by
  have h0 := BRFrame.cov_init 275000000
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275000000 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 275000000 ≤ n) (h2 : n < 275179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
