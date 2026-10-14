-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0995
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:43:03.907292+00:00
-- url     : https://prove2.me/submissions/1f8143aa-6515-4d2c-957a-331cd8d35300

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 178776978 ≤ n < 178956834 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 178778228 1250 178776978 178777013
    0x406090e0114130206070f080f090f0d03050315040f050403050702030706020a120309080904061e0e040206030a021b060915090609062206020c0a0605060a03110120030307020a 77
    0x102c880800c20380c1004421007007a0035506030341d22651084c0714100f134848030381c04020061140c1000070303264005444410203880900c0003201e106041c4a15802081503a03802500000d011900500c0000c10382e504607940c6080c1c000c07000d00089001340030611007070100e900c00c5a0440114a02050a2043d810200b00000141066000030040e10600351194090240400c61410400d500ca80b00c950400150400342d0702402c2000e001800843e448081a014101c0480134103100b00e440030b180080d400c04c0301c1d001e2901940e00a84600e29644911080002a612010303601e084145001040c0111840c104203a42c40380358084040c0429a1a0304055060351402621100d0207038014400e0100702040404d00a420585c1c2d5500660f04051007449249041c1113004040e114a102180c520340384503000c9104030030940b2a181c20001a0354100800a030380103580005040751001910031105540074580a090f48901e194101d07000502ca01002441c641c003c03140040182c10041c2c4810030413102e40128200e800e03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 178779478 1250 178778228 178778261
    0x14010308070f03050d090308010612020a08040f020a0807030305030f0c04030b0f1506070609050f07180213030c090b0306010905060102250509090f060601030911090403030b0406090e01 81
    0x1455a26618918001e460000d40355003a10303a5801d040500030801c650002d00443c4043c01790090504000e00001c209104800c007080c4403000140511816200b1201070b030406854140482d261910b80301030000c2540d0080740c120080da02c0104882104000c068020340c441d90701c15559140c00c03a842011b280000c3d0445210f1907040c04280002084004025400490060250380596075520a806582e202da003495410240000709042404800d41084480b10700802c1240e2280c4074000c1d00070360b80d11052040490303001440c40e034034982640c0342e001014568010a1260075240d202c2e1105008460650b1260340c0899884008540a060900c011801010700980800561034810b00103503c55030840e81d00d090002d03020083d9041e00250200b100e0151101801c6288280344c4807290f10354404032502021081d00c2114000355207984a40511910542c1c046030034419940c69606000c415003001c0e00490501d41c6a05842909445901c04c01006185250020401015058082d421103480d5104644901c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 178780728 1250 178779478 178779481
    0x40515060105070201110a0204180203010e060c09010807030f020d021b0c1f0302041d01050306160903030f1115100e060607030804050f0115031101230315030f0703030314 75
    0xc0e0b8000301500c40454082c28881c0c07020503281385081c20a000b60340000d40c071502c2c046e0300010301021a180b8168051003a070081024182102c0b03065528501244d08a00ca00c0080011940740e5200d050031a8100d6114140400d98240c5d03501c44e903040e6001210010303050313030f404144600780c00000b1041c0101c401c01003001d440d549024001180194030108600c810b00742c80086683c060030300c01d604413801072002900c0c00d14003403804100500c0c50b14081c8900303803080c400c12008c40d014200160402c0414146d58807903140340c910315074064070003652030f0f0310000a101c0384000f42800000305200d00b01c42080c0311000031800346000c000b442d0360060716402221400001c10200403442c2c8a02c8100da50042d0141004039156555280c03840c941001c0c0ca103005025400c080d110f445501301d0019038010f13248140c80c201c0000d60040011104d4001111181c107251f0400540d19420084420040d900036401d019601c92903034641001c00c0c905003c50402c90b01c2d5600209080040c1540b601c2440d070030f00c1c00e10307900d2a080e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 178781978 1250 178780728 178780741
    0x130209030705060c0c0d1a1e07081312020a0c0602030405010c1b0f0f060318030f110f03040b0910050a17100e0f1b090a060e03030d14040515 62
    0x101d41460048500400c0e000454450081081000410007070b0010050440c9103158a000c0c80a410509045050010040c020655a0b8024110740240c800842e103a90301035510301c1d1003107400303d1020b00311580075001d0b20301000100b501070400e0f85210401c0e4009204140c10391401521040303842c0e0000f41150410310003400140c1c5c0c41080d07490f00c45d0b08110490b42d40d252140101911014a034004070348046a00000a242c5026040081c00c4a0310351311b0411145c4810007a0314481d030000c1c0002000a43c0421084409a00502d450741d4501e04481c00c80d80c680342407a028a03d1036116401c0503030982c4010510348460301e0103680380c43e80400310345005801d241038001c0c060910003960700011a00c0d01244001030382000041d02a20042c82078042144d80343c24280040340003100d0964640e495003a0b041a0b200070240705804440c0b0030340c0c028100703840301454101f04440b00390309403d4031603040c0400c010b0401542400c0c0240224494080c03034100305800d25141082c90840f24100c242183c0c4a58010840c5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 178783228 1250 178781978 178781983
    0x30609071d0a0e0304150201050a18140703080f130b0f040b1606110a08060a03050607120b180118090b0705220602251202010c02030f01110913020903 66
    0x407507465a9010600780c9610181501900800b20000d00b548004100003880458070750700f010080300c180c0c0081010b03444010900042da0055199000c40607a0b103c410300c005817110302041081c035545420b44019948a03030304e00e14260300c101c060480700d07040451030215070404c858480c0002c0c1000d0150341d113081d205420b20074086c013942c441d0049099000c510510342c00301c0303646484804c40d44805d081002940341080d4500d1500306d080c142c000103c4e044000b8016003000a6008160b0f07811000070310740e0742e0f9040b0040345d0340500079021920441c5c46001c0e030011a00c42c402c1840c1501580680c1c000c15604101120000c410f41065040c0303c1ca061402d440041552200004d422481900d0200d030748940b4000c00f0800907044040910340410503030720020f000c5074082100703008101a0343c41c1004800501c1c020181420b2075002d26000a180d1344580780c01507000703c0c501404c6902c040e0559105104001c9060300711912a00e041160402c000b0720b480c06842c01c045803100040c070905085003820310340004a41d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 178784478 1250 178783228 178783259
    0x11031b030f06060a091d010f050103090507090c1209140607020a0f0609020d0510060905010b0a05030a0b0d08070f1211060f04142505040203071232040203060907 71
    0x5009820010b04d030340d003042c403914103000030300014100802c5c00b500309800c1d115040300074030425196158900010510751f100340141030300c1980150051801c6030605400e0001080da08000c030040c088e000380d0340c1200440710b004403c507040c002c40e001c00f002e03050020264204040140003800315046001e04500241c0360f007000041d1150048000510102d15102042903148030603c050708511070884444c140c800c03290081410348004c21001d00c03203a681c0d0155003c0ca4041e10070f416000c944180700007610181c45612444900c2002002c0c118112401e403a03c0394070b5070140c14180c880c151000700d10001d11001200f2050088280e1030b1040700030746c0c1d1411903511050061700400a0141c0c910200d0280007001e03040e800170454140035600000c204226184084030301c2581c140b030440e0108000202c0c0d14241c0700b030b648208601e449100340c20b040712140800030000446400d1010f20b000e4400d0300c0185580c5030304000f881c00040012124101401090b1401034002e104c02041c1e8807901e81480552035030195003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 178785728 1250 178784478 178784491
    0xe070335030a0504020307030609050c0307150906080c0405060a18120b0708180f0c19290f0f070201030b0a0506090d03050d0e0c0a06090b03150d0611031b030f 70
    0x3d0142c4462000a003001c0060f0310250000d8240811002031041c0481c2010b44480304804a5405c01c0c1d9174142d0701182061020348001013800c10700700300200c5000b05c018542c0b01080041880c07800b174881d000a40030b81c101c5074600002030083c1140b40b0b105015400c060014280c070303051109021919aa0342aa141402880703502040791050100300580c419401c21490700416400f5280803085468403d942e48100c08000d512a902400c1c0c9500f02c800281078913000d403101404400800311a14558010103812400846aa901d08000861982c4605d50140c005521290a4640d6078000307400018181c46071400c0c1c061017234045000c1040f0a641d8401103480118056401140746284c6040540d02ca001d02d0f400310b86400e04005002d80c05280c080780306100c45a007158071101e242d480d5a4101c0d1101c4040c010249413140420204071920400000e80030580380041c440700d58a443c981d1846d0039141c21440141c5c110001001340a9982240304084291218008106041d8502100165654440901034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 178786978 1250 178785728 178785731
    0x1f0630110301020904050f0604060b030f161101111c150303030f06090f0609141005010e060403061a120d120f090804080c030d0c080a030507030e070335030a 69
    0x640305988080d01681c510580c0244100030741d03d020761a070f8400c110200c503154811840c143d00458120358000550340560070180d03a038100c2d5962441d80610070281100c01000380100398410f031000050901a1040300e50003400c0c01034035204030100802020309080b550b40300c42e50801254040d20740042a500040340e80518001c14140e074040342c80c600070b059030341090711041d0600c071100348403040c550041c00458000460800204040b01070040036032a082d21001401c0e000783c44100600d600c61000080104801040d05191540d01c1d03941004035200840040480042041d60b108249840200c0c16401200000908425004550010b046001030480381c1101a5a054034400341c100f107031705c03032641c01d0f6024011550b104d071038180d41c40d0758200c800e5409200c1e104c0c3d4101c401c2c14903c80c02800c214180d12407a61820600c480c0401d40c0603050042c404400c05a480c0f90121140300c081103038000039405a19007031204c0d2036090300301800c1c115580b0740e81d815400c014852148401c4000c101e070b42c860340030301c3c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 178788228 1250 178786978 178787003
    0x7090b091315180f1502030118110f030a14010506040807210203010509070f0b040506090907030b22150b190309121716051b1f0630 58
    0x5048001d0012020f400b1124803485801c804000b581103100343c0c1c42d030048581030000556a0303600801d0344824050102c0b40d050300d44d189502106581c01c400500e80c121a50305040c291031200d110700b141c20480d0f8000303185481d0207a140348000010911805403070142c80c014606420110200c1e5600700c54440e0101c40318141805801102d200083c0c4480e907940100240500c0c1040d5240a0b6600d110b8002c19030441c042900018032000c000040b242102c8024002c43e0402500c84104684280c00071300a400b41512458000102d030b036400d00320070200102d9141400424201e282c240100da100040310071401070382050601204e118081583c0028482c1c40361400d0f0100c08d01801c034068514941c00038035000c0341c035580c500403640001040b11102072051a131101682c65a01c460164440660260081001001b12207401140720f4000946e00c0300c0c000844503012100b0030411106501c0c0703040465104c0d43e4000a1044d40242d044a9002401001ca80760950b0744501c1e0051040c4200d02c00201071396100b05 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 178789478 1250 178788228 178788263
    0x2030322050d02034501030902030a0501020301150c0b1305070b0309010b01110a02150903010b060c06070f02070e0a0504030318050106051201090b0112050102091207090b0913 77
    0x4080d0a041d80402a01d90454041e00d019540e5000782d8207003046103000c0c9107000d40016411600700341044069018118210b03080f10568801e02410144904040e1680803540c0580c804100c1c400d8103621801c0016920741c9802c2ca00c2c01e0144400c0010b07010840000b442c4c1011030b03c00c2e501d203504500464201c3c4058402c40c6030042c5400d41036405062400004001c1140700901940002c800744820b803203603040001c84a4000391100d01c0800c00a5006110110301700c00c50f03d40d03401414885401400003c0c1e000c942d000001c03c2a0010350940000d035000f9800c101409a1086513801c114050740010003525007031800d00c1e402e41c41c0c01480540034560340c800013000d0600c00d070000c4508424944000ad5440d8403800d00034003800b00350044c14000c0100c409001302144c0144a1a4502074102c040c41925908241d601d42090701c0e4800d069900d0b40d000e008030926940c075039140c050005803590040c00074034035141c8814256510303034000c184a981c40c081044403070328000880c040390540c0034544020118021 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 178790728 1250 178789478 178789531
    0xf0118170c1309023a0305040f0b0301050f0303090a0303050304081902060402190b04050d06020903032101081b0103090224070b06060304080702120109150204050906010f020303 78
    0x8480050b44010710080706110100154400443c090080d9015030142c1c0b007098060207404810211884001c1855509440c08054a0b41900c1c41620911342280b91581d1002082c4911442c0c4e0403035403a1081c00030040000346041040400000750a5000e07600b06038441000400d1100240300c050103000000001504103c40035003101c00c401140502d48820000901d00250b540c0402c440880c01540502076541c40f004051540d64201c3d85100d0019160908160502c40030644200781105c443e9020f010406c0e050343c0c20b00190118080c0d01088c0500000450140e03003203224183c3c0030100a80165409510108021041000c6400d082c20041580d4860340302041440301511401d9009a41c001c0f00001c4031a0a680240300c6140201260741e140d807102c03003c2100c90b10082e580104020400c01c504001401c02071050b040c0e01d0740c80c000016414026031140c207241d02209a180c07a00310b41c0098213005c0340c030f0460800d1b50060b8003031910180003c083c00c03019523284006441101c0180380d80c0007140108100d0f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 178791978 1250 178790728 178790743
    0x31306090c12050d0207030215070309080105150a0b0a0525050609030a030b0a0e0711030c1f05010803031902090f0301020c0d02070e07080c03130503070c050f011817 73
    0x3400c1e07020400e555a001c0c0304514400e100441c1c03d4003603456542d060324070000c0c816040e030750007d00c0411840d0b1303400c03800c084980c0000380480078050150b0000910440030b10895110316260072820615552060800001030401c0d00314002c840f0007400300044003544801600c6030041e03851400c040c030405064845028500070007008129110782020001032841c0400903010304500f5407014019044001c04010700f00d00c45004030001128040d001810b82c51045070111022071880c01640d14090f40564814240046515008001200805400c2c1c10110f10304c074407401498498040d608500b000340820150055120002c0002ca0b004640318070540d6404000d1100204c000b40215590381c1c0389280242c0340c00000702500050f003e04400051134200407940180f0070002c55841d072180f0740d50100210070301d07040604101070304034980c4e0445002850400040102a020760080040c00d4500803c00c50409400700095040180e48203024078900000c900c0c0348151a00d012046454000780321a0600e00b036203 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 178793228 1250 178791978 178791983
    0x8180f0f2b0c061d070513020a050706050705160507150912030c08040504020a0c0606050a080613030917160605040803090d020301111b0106050103020310031218060f020c0307060503130609 83
    0x70086006131303050002481e101120000d446484250480c803110400300e0050041840111310100710794400680c41740d1103550f00100302d061207401e192102d2141440901058000c4440d07070300c030300020711481d078401640d42c044512625103d0641810000054030002c0a103000809011903000c080e8200100c10301680c010304030150046440d800d20410040089003c00c2c42602d0561606c04007040906044c086142610b096034000c1000751540e0310700c100d0350744512006500304144607501203030381c5290f10030f4102c050050200402d04008181281803800c03180394069010302000b000f0401c1a90340100c00d4400a4204841c401ca0990700e81c004070340504076140314801d00700c800042c06071080300c1c1d505844402034420070003000210b80324001507040b0f100030380e0040c40c090a0307610300700000781d03140012920640032407030b09480503c04000c0c80940c54440d5007028001c42d282c1003014441590400020b041c1c030b2022001001010b24050010702248009413103101c98550114820041c8141d6401c0a05202ea = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 178794478 1250 178793228 178793261
    0x1020307091403011e09060e0c0306040b0c070f11040c03090203190503090604150801081b2209060c030e0303010308070611070c0303030204031101030203040c0608180f0f2b0c06 78
    0x141d501217040080c00c644508841e520319104014007251b1001840c02d1104102500820301074580e5161000c1c103000c001d01114042c5000c1041c0c0e80054541c406a43c60b003441213034582000580c4204100030b542204140f2801c161400c1d4400c1e01581c0c00203624400c50f1501c01c1003152000c0c0c241030003825442040885074201c000014005509122000c0c00e5207050b10648d500d62050741c90380d14854540390784040003c59020003890040c7c2d185000e260141c0344070500211103000c0382d244140c1c1342c00c0c0c03111540705a0b0300a03664104400c3d002d070140281d6014006000203940740d98115591410540100303400a018241c0c2c41c00c101e1508010102110b1295030403255030046141c0c0d9240040103988980004c17540300d0030558241c9a070754001d0007504d0049a000c000d60b10b01d030b414960120381d403d600400e540403c0d01d15859944142c030003481003480d010300c48030261041103c6403400d075242c0304019031a40f85000031400862111070181c1d03403480d074454503031a2040c0440414107003900540008407030072403900e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 178795728 1250 178794478 178794521
    0xf05040804170601080d3515010306180b04180c21051b190807140f090703090807150f0b030111040920030405100e0102030709140301 59
    0x404007420403034a014800e140c1c259404602030740c07121020b2182c400194041c1c51400070480c020301d11141e03d15400c1c0090441d06442c54190500003070f5507904580303040c2001c001d1084902c7c000c50b10344d207144000e080074091a80781c5010b50502061400488081d140d0b5032074826400d540301d8000715003002101c03522082400170f500b0000c4c10510580724100004440080083c11103100780781c0031142c40c1c2c010018150b03058001881041021514003056449001d00021190701141c005c0f8401c060400300300203000c91410802045400c024000c40c4603c00c003482c4011180350741c0d84200595105d0340b10311380803c00ba21246080c500340e00078480000c01c42a00304407081401081c0c1c1d0721010f250404044203105101504003814202d61540c1c3c0901880c4904100038445030030590843c000e8280b00822881704040795556140303403900107803021511500086036240e040c852502076001d281704400021403842c100b1180c05044080705101d0010026820350403220701d681e0039840328089514401100210 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 178796978 1250 178795728 178795733
    0x9120c07080703050f0d0305040c0509190f06030203060121120c06051e3306070507030605040b0a1107020f1f030e161a031003120c0c15020601090506040f0504 70
    0x280c03180f0145c10300c10791142e1015410480e101e4052540299000b0030139a10142c1005c0910404070001008022100d0110201e290381011921899200014a110000e280350652040605040069000300c0c040030580c10180c00006d600c6000c41245039010004002c005006803040d0750035688008040c1505250004000c6200c0d001c0d0243c0c400300e0050a00150203550320380192100c890364000303120740414103a0f241c681d0b00415241d03500c6a00c000900301803d2000d87d9443c2803600d00250030441704241c480c410320081003200300e18650440c2c0858000e125610b0b2003140340c0d030f8078002d100c8083d00c50008524040d4440d100c4120728034481d080f2050501d44c0008114000d4003800310904003103914418804083c042009040c1010244c0e21519181c01d01d4841101012081d034001030450215030306140800070020391401c1401100c04000e48441c00c08444504002c4041c0032941e00c00c019008241c0c1040391403035070218229064034541c18000966450b1080420020f000000c8100491480c20052005 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 178798228 1250 178796978 178796983
    0x30c060c0903150c0c1509080c0f19030e040f0b040504060506030c030d17220501060509061206072d170a02090a0e0a09150c0908030309120c0708070305 67
    0x141e83c000d11042c00d5000814100c0700071030700344e0681380d000141030070410f800180070b05806000c0341c50040030100d45018130f6111000c03142d0041114a001d9404501d290190407802d1140e240c100012a000c0200302d141d54502912090300d003080d191103180e4070310002e11104e000740d0141803500005402001689014a031180051000b41c070003500c64421441c1108813483c0c00141030000949a6031aa00c10b940300d00403040b64440d01414604445001800c042446c02d1400c0300449030301e001c1e0001180c181e10301424084070300c0c00079010074002c0c80d2001302c04250301000148290040250f19000001c18965500380221032418006074030b614140b0350300704408035809121007501c660800c1082045480c1c3c5054441207200354000160462a140410850341303284003491036110003108008a40c94140756100e606c50b01c071517641040c1705641c0f440b40d114111f5101030018040e0060307000035032540c1031215030f55a440700080300b1010000350000c0c2001d82c0d4007043c44000f00030201041140e000c607403603252254 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 178799478 1250 178798228 178798247
    0x604030c3009050906060405040216061104091802060f0a02160b04081209100f050d140712050903030a0c0e03010c0f080906010e061201021e0c210405040207030c060c 73
    0x1d0018807a5180400c65160401419006110003815a45000d180c1028000a03400c20300162000c0c1300714a41420120720280511016040b410044a5071281800c801c0d5041341d01194046100c0c8491149c920016202e407000c84180244d001e10407611418101802c070b141104001f60800c43c80011803000965000c008050310644070f00400741c0344007003544645c0100d24080c540b01140c0c061603032001c02c0340e214010313608030b062401d86242082c43c100c1d04078010005e03110018142c0c80290500801c201160303a00c00007441d0103141c0d16405019600b00303010056581e00001d050300201c65a0344058200c80340c0100c2000c410399501030b0080c030030a80307044005009002c60b9405000891359080c0050305003840030032100e050300d07000840340c509602e5882c180100ca600d45940c00c59990742c2001001c160f020034001401d8410084424a41c0e500184510302d4141000010003000000c80310288025136840401982d090390003d841c0180c503403049040c00c03580d051210701c001e040203180641d11244290301c03440e0b05 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 178800728 1250 178799478 178799573
    0xc141302073908010905030a0c02010504030c0305060f06010302070c17030d1104050306010b040b0a18120506010312020106062001060e3405030a0b04020903030a0302030a1a030604030c 81
    0x1005600c0da291030113826130341080c0d0010701c190010080045603900481c0a801068010714089051503165500c1e00000c40307140e00159141d600c240200411031304004960340e4040350a1800b942007020b9541e83c1d5040c000103000d44001001c44900804241c14100185c44030300a60003000d100480c035030340c0c1c0c07403001d0752080c05602e00a00850340003040965445049400302c84041058924054051604681000f00c1003a5180401c4c8003403000145442a00c3d072100280e401140a010554510318002a00e00c4c0505201015a414400c00b00110740d00b040000e0000742032035a0900050010103c1c4d907006103990b0f0000001c07403016100340181c54a4840c116611800421500d081b80b9003100203204605209880000c0085c00c2000061801e001c241c01a0b000407802a04c054100051035000038255080010000c0004ea804402c01940348464000c101c0d04800314049148201e031140046521500d0050020f824800b03100d51000400805103003001840d808004c0d102c200b0002d40401118403051507400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 178801978 1250 178800728 178800833
    0x70c0b0a051513051b090315070203070c03030f030b010305060d08090402120907080d02030304120507050c040204090c1205100312020309031c170106082205070b070c14130207 77
    0x1030b0101d1001781c41250514036008004103041982001c08240d032500c020030f003908600050146100080070710300380c840a10301c281c80e05200307540541e1005007112300c84621141010b04040601242d5142ea00c090b055080d0440e5903996a881c080c40440e004e40304882c0c00e1480316803131a0030000000c00104441064811104c141c440301b02406001302c0e600d0000360b070003400c40ca200b10a40d0010314050070050040318841e4065071242d0440d080014200e17080390384182ca02a49980311307444010740c4030307080000303401c00706d20100814182620361400c0802c80d40001801000d0201d9000c51590003007060710000b08006044a92192511030842d9800d40c0c00103844011611616151070824003003070b891070590784140e03181405991201030003403110205584841c0380255058054010400610001014090075140c180e0340342204c0c07500c202d1081e1154880e20035581ca0201d0b8510940d11000341024400c0e0700000540c680c07186091046001c90390112003a0445d440d03100700d500743e044100280c81e9102500d4030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 178803228 1250 178801978 178802011
    0x3180f051c080601020304120311070311030106090213050904150603060603120302031b030c07080c030301050a0f0e040204021b0613140a0c030807080405030303010617070c0b0a05151305 82
    0x2010307510b220055416074056001400141310194007000440640d0f402850034001c00105074042d6800c0c5100c2d80c1040c0d0f02c410181045d200f4904090080600410b241d000031490810120141104144580143c602c91140c2e840854188645100304c019411500e504c10801183c6d00e1405200825045c031003101d080d13108820607800240288282d80c802c83d92140040b07111000305180a0302c9500041001c62000c50030f0140380040342554016055864840000710b9503541000200210844254040240040c00c1c900a201d89085104840c4d0415416180503841c1c4c03d00e0301c005003010408a80c0140300b40b1443e420452901c0c2514142d90805001d020011100c0c00d0003681e0949030602030002920601004204000250102004000d0382d0302404d051403d00d0f0301c41001900f0740d030003070f0f1004002665500c83c00f0861110b04038025007002003410f0550944150b40d464005140b00103040d030502076900c900051a41c440b80b13813003010300900200340c442440c11403581c00d00145000d4441504081003202c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 178804478 1250 178803228 178803283
    0x3010801060b0f0a0e0301110a020f06101d09030d0504050c0f0901120212010b040501080a2a03030f18170c0f0303030c070606051512070804020a0603180f05 69
    0x504072007044610041040c50700c0058101a904402c05e090201c0d055983c0c0d520103000505184040c120400b40796000d85621400716010915056010703295038035640c0d03180420440d6009810103100c8100219031880c00580e43c04060703a08501440c0301d0394038201d0500c0200402c201010030742c034420f00001c030f8017040c007216110700f0b114800e082400740c9141c1e4424006001d01500d04001e00000a04540c40042000220800814244d0b142a40640c070191f02450030325041245048402000301c00c201e40601c030106e0007201c080141000d41c44081d080c003900026820207148204800f03c043d0414840310303141a0340c0c5060101c54503246400c000d4071740c000d40203904824030b01100d20450102c1300500660031a200ca120202c0c00d41d00039001145c06c255070744000035444e25284008482d10600410071904c03014070700d8070f0420180c00200030304100501c4804010050755164035a2003640e60f2072400041003281c0d22242406a1000d5001030402100b510a06080010001e00d05d0058039101c0b6000c690f903101071 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 178805728 1250 178804478 178804499
    0xf0c0f0c0e090d020a150b1c0b0912030615030618010b09040606080903370305040201080609162a060b0109060212090d02010e0414010305011503051c0c02100201020301080106 77
    0x4090007880c07116100d1210703861201b0340d003041c5468040140300304d1a2201580d91021000d91003a8101c80c5149407004000542105006182d0800e0030141490f00d5480c2002c0000c01e6a081a00b031000310307041c0400813a8940c0c40702461540e10034581a0000034550b10380780414201e800c580501c510640c2000c0d408103000f0300c03841c002c5004d00003200045003010046250314035200300c0100030600b64507000c01e24140c90428022800c2c60500c441c1c8002516052600004100e8440245003d00900a05043c4484644282061141c1111511381104100d101d841740c0da00b02c0384e68440707400c00007600c41c40340005d11080358000d038801c2d0400d0700c9507954180c5e5208203a84600c0000003690824109000c50581c50034841d9581400b00e10502d00072038699551070010b400c8404800c2c032424030025400c01030042002c24881d148520211590741c0410926503a905665501c40360451044200c05400500110340182d05142800d035000300144013601700044000c0c000c0d08244070300500c80d1309111002a42500300e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 178806978 1250 178805728 178805743
    0x200c0715090e060f03010209030303010906060311090d1209080a030203030a051005010206010b0706060b120a0b060c031606090803010b070501060902090117060a0b030901021201150f0c0f0c0e090d02 87
    0x851070ba01c032079075540d08102958948a5405030595003c00141e542540d00748025800b8041488001861a04140d030081c00c45e14000e07600c054a040c100041113095440d40a841000c0f80c2c0460511200c1060040c01c6640010a030b000b102c09104400d1014101500800598800c00d40c2140c200f0559542c0c40690310b845025105490250300400010f001180f40c0c0c1d801845400d000700c030003150041d81c130111446158000c006201c501d005010900c80d615515001d0b6000180c0210780486c1080559540f094903442206004003000350100241d03001c220094000c9640907400c02c044603180d6a6941c0402070a41c4241c000b20703074651034013101080c10561442513414540c8103950b106902656003000b003840d008050302c010360000314404005030682e4180c00851041c1804000543c940440d5014180a680180c02c6081e10a1848400000281c1d00186100340c0c3c0d40a403a2898044a09045c4101c40c4254040040c1c92080015004101c2114103424203000c3c2d21400210790640c0c00110302261117885 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 178808228 1250 178806978 178806989
    0x1110f03060a18241a2b050108011b050d0207050a06020403060c090f0e060618090408040602010b1e0402090a090e03071e02030d11030c1902091b0904200c071509 71
    0xa8902605c4040d244240242650f80d0300c030ba890601a00d9042580c250040b03007007010b64a0b40307844200500545800f8000d03032921607840c039138800c195820003c1c050058090007220384041030b80450382500b031060030001000050740000d401c550f22916410660080c06042503000003051500c40001003150206500740c04403600400341c0082a00c07010b003004000d51014003100010019441640655654260f00701e00071413280e021665510314100020b425070780c102411038410051500340c01d01840424103160000041207a00503510f030030800000700180b4290300804e501c40c5c50203640f10a0100000010b040042c05074400c032a40c42d040700503121444442c49802901900140115901c03940124410414a03207400c040c1c0c3c1c2000020780c640d0b480d00c04000c0c45415a51220800ca8042d400c1c0080c6042e0401d40c00c41051400b0b503141e004a208a00c0340e50521401307035030b603800036100b0364022a1210358814842c0c4100c0303660390f55150403180d68030028090320440801060b50200300302d00030101e91040f0390 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 178809478 1250 178808228 178808249
    0x503030714030412120b0916181404180b040606030c05040902031c0e0d03020102190201020906041206021c0506040c03050601021504050703020604030312060801110f03060a1824 78
    0x13003112008850311002c2c080d044201c00d860b00b080e1410740d907031441c540c4d10803598011800584c040d1588000d25004d1202c0302514181c0c140034062100c00307078400042d0000c0d40c050350b01003003080002901501e12980c410340941596800d20a010030071030726410007011a4000c0040c2c0419684900030801103c2410800960503400b0801c03401081c0c06480280c0d41071112810314104100c40c1c4008541c0c4081c7c0ca20040f00141d500103410400803441e81440c079841801c44c802141448078000214027540f0880c013500a00c10805540c800030031140c0d030110344074015130000c124040c2d40d1a0000c60081e082c10b40c0d4241c421410f0429a0f0b4030075100e84105842100142d0082070131200010989407480c9014009859902170160b0210141c0c4850b002000214407a0703071110039200c0955100b5080390f08941250403941d0410301082030f00c0702281c0c00e41c0c2d80c4411003002540c1c0c0362102400500601c403941d01c0028007503070001c461901a0420761120060240f003840300c2d11884540c004034008a0031500030650204c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 178810728 1250 178809478 178809503
    0x50702010f1b05220e1503060c0d0e070510020109060516050307201f0c0806090105100309050102070305070b0c07020105030135030a02070f050307090c05070507080c181603051506030405030307140304 88
    0x110032504031040d8103052008cc0d03140315485201050148282207103410250303440380411404c10400388649070380010324600e251003060741070301c00a0562002030312210401040e60801d030900c902d8000fa0402c0501b01000f110044640ca0550301420310745440c4a02c1110301c3c01040901351070198000c03501c10341c0c000300a1019682024208800340307071201010300405540700c441d14000340c0700744010f0134518085d85842d03484406038981002041001409058480c506005250050340c000040d030741903901300e441c0104292008010a1082202115190403c0340509080e1042d50b0000c8010b05c1c800b0300c030340c3c01c0c0d41d001c2c1d0311400400b00d8154a0701c1119095440f500040011185951040c16110300d607140079460000a925410700c0c100c4a40c01c2214590020418800340b403420102e07400d130012a0041e142d5091800640c03840b008a0048566000d140d103560001e110b448410216800050000b440d050f1a03080a040541c0d903a0004c40e4104041004010804007100000e8140d80c880d81e400803250b56034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 178811978 1250 178810728 178810747
    0x91f080a0e010e100c03060506030408130f060206070c0204110a1d03010204060c0615120602030708010e04030503070807110708030405030609160b0d060302040e01050702010f1b05220e1503060c 85
    0x30117010f0000d01c10199546004100381c0d90b65402540114021898251a0818481003c0c60f000155128080c071a0004408103c803540202c0c42951041c00c40c00c00003010034050000c100540903c070800c0e001404000b80b10029140c01030400000d02220403000748450441200740b500300d10a03801100b002c41c12440b456000120b00c0c0d004411404c0200700d034074000690303030300d0460000086400112800c503004801c000e103440d84001c40d180145071aa1180e02d103030a01da240641184000b5040d0310401c007101e400200c0c914011a00318403241d40e070f5011906400d9880040503183c0d0444d0140503c02c0c080d040105086000000d286c5c00d0142c045416101d00900d0301010080da0760010701139000094442d60700002599842c425008860400710000c1081d24001c0402401c44e040c048071845950300d0170901e0941c0003607800b0040585a0345042c006c1c0d071141c5051104101108221b40d20300c1441c035141010900e8000c4d000243e0160103d0404254400c030b148041580311001200d8081f58401c040c482490b5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 178813228 1250 178811978 178811981
    0xc061d1017040503090415030b06030102030402060d020a170a0905060615040618090f0203061804050607030218060c070503070f06050f160f1b0918030302091f080a0e010e10 76
    0x4100f0721a0342101c1c54480320390003003010b882032035110072260064844104140300c2c0c0c151416600c8003044008618600e0907078001116401800c2040c8103c980c00b082c2e41c0c030301c540652b88a98a078140781a00300490f1802102140192906003002c0780c1c54001c890104540d418900f000f1030600c4810f40c2c050b0308241c03c1440c102e03110010120480010f045100d40055900041d1080c4410311504241c00341c5d4a03d0500280003d511403100010845403281c010000440c10104045402c410207240c00b5a40d40101070401c3d40004243c41c1640d401140000c0c40114150001118411107200390180c3e030f0455640c10001130058858031850010920402c0240c983c181c1690050282c20400780222450b0849500c4107400452030800c1144c0c6020080c1c0003c02901c2d0490070440109a03581c0300340400c0c940002544201621440002d09164000c900040d9695480b501c01411030b60a110342e400358402c01100800c00001645c0d1524a180303003001c406040306040c050a920f058400d00280882132401c4003090 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 178814478 1250 178813228 178813231
    0x605030a03111501080105040308130201022a0910091b0206010312110102070506060109090e07151b0302010b01120207021c0c0b120907060305100b03040804030c061d1017 75
    0x801e030103290003080920348111150f902900041000082d14038052030060f10000c800350007101d402418095a50040c0c1e400500102d02c85642e40041d000c3c581d5a00c4840c0d00301c00c80f5411306a008218404012489400720142c204459072244c4c00c4c01629047d28440709009c1c1140306040040c0c20040051000c43c1e1860003003002681c452404044003504ea84c902c3d0300b26000b80004450719048041070000641e031199900010f0b00e071041c03003080242d454402c0700359200d030a88030b00c05c3c40000f030100e207002c0036000f00844a001029164082107100440c60024000c08920b100c803400316112007600c80b01c4615600c240e48400b0740c0a41440101c280c400ca52201050b5110411910b110046d140469690b04407800340130380c200100300b00051030500d22001414645079400030002c040c035000800842c8400e140d40b0301d040342c0c40600e0304c603500c1c1c0707650030401c48600c02c03034001520680d40d10b2000151580c0c4130042401e02100c04248682c8403000310201b10880425421000014040c000380c94500721040014a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 178815728 1250 178814478 178814507
    0x30504090902030a17030603010e1c0e0a090c0c05070b070218130615051507031709030f0a090e0603160b1606090c0302030d031b26010e1503010605030a03 68
    0x80b1a944800d41d107413841041c0d0045d0440350150044280701c1c06080034025140884241d0340940040942b10f120b420120182031018010000c14604010700c0d0f444110030a0098048000c1c140280c0403400b00c040c0c0390852600302115140318110001468004000076529901d500901ca0f04143e40300910102e1580406001c0e0500d12200c01c0303281001a0132845401c100000700c603e007100040c5440204600b08507000040145907c040000d81c000a912001d035030151180b51902c1c0100303496548155140d07000d0035691000b1480c0024500099a4000d0754820481e6810510a04240c1d074001c281038403038010318100840751840340c0044c8101d0384100c000d010030f00dc0c054404540d9503a0741d01d5941c1650223424003502c00203141241032007941000d101c0e801c0042858102440200f1044401e020700c503680300c90441c104068100f1115003c24a00b485d48218103a40d0505100c651311881d1100d0500d0081c1c5985031007200d4580c60121504042c010b02c000c07180010302500410640d5101130b02c21044080c801c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 178816978 1250 178815728 178815733
    0x1d01170a0b0909100e06040210080405100509010605040612050a0201030c050f031602010b0a0602070513020c03030702100608160b0f0c060414010506010e030d0c08040807090e0601050d03050409090203 88
    0x84191548400b004103115103804002000d180203045800004c5441c614401003442d000441000050b80f80d900000681c038000b40b030b100715203503614181541445d11b001d00c031400b11800c0030203104d40d01405411950944a040341c00b0088103a9948081d10990ba600c1c40003409904680050f8005d1344c043c0e408040e2450050400d1444e1201c83c80c4100f1043d03000b1100214030940445206040c40d030709209045c1a084142d0703010000c90304010010355240d8903403246903c5540540913008004c0c1c0c1d16010749200c0948a01283d440382401d24005c0e44540c100048102d404e403403c0030004110100103a550031020401405651140c1080c4038030505611951940b01460030070482603030682e00801c00a0706c9540541c02504010005604c0d050964002800c4103040002404400080380d4005c00d08001f8081d6506010f00503010f1450074070769038000d0313074000d050798010340000280d4001581c100c0c411100200342951340720703a240c108102461681100103000070304c050005100400159102c3e86650780001e08 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 178818228 1250 178816978 178816991
    0x9290a1a060f0d180f08090310090f0b070306060e041a0306070513050406140f030f01050c0a0207091a190801090809100207030b190e0a0b01061d01170a 67
    0xc100942d10440c403420031032000081070840342c2003a2058541e9500c2c4004103450a00e902c0d240c14840c15460759001c1c0003194000361058046d9400c1050103102d5002000c203000070366950510302e40c0c41e103000c0801d5130060b5100c000035540d24405d200e550144c0d441038035502c081c4c01d01142848004c20255011411480540070708501641d0200a03003441610255186039683c540303021580080ca0302980101e0246040c41014003540408002d512802c0c441030340c401d00040c4001000034940301d50007907410f28035480c1c9828400e00c914214010000740903250210b451190340c0f55030800480350034407000031151054042c00b522524059001140c50342c1e42c00d49400311561601c0c034060843e85458000c6517400000a0420304a0805180d019800d22050010b090a1880c603100d24040b144014a50904080040303401c000381c401544c000c9007005000c604445124005241000c042e503004c0c00b03000c0104000c9500e802105c295000b0101d0300f0041a5a121255841d0413070450305810050640c00310750b0b0322841c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 178819478 1250 178818228 178818281
    0x120d09030224071d010804020103050613060b09011d15030603030c030a0509011b171c0504300c03030c0e0d051b040606051605031c09290a 61
    0x8003409001c1d000c1242c4441c2c0d8144400b0240000101d040948a44107080402c0c0f849a03800c4429036910a80a0a000c038043d510140010801e80d21001d0f101903140c60b00c000401c41e8440c070000b40c01140c40a807901c039000d2182c5180e07040c46000101d5140d6205001c2106005940d0300750001d1500200080c0c200d9050581e4400f00c00e045d500040782c40705c0040c6001c00d14808039039120502c0c0141034203044400d018490b10303848801403a002c079120006210700001e81503540c003122084c6100d85007070540c01000641014540142c0c0510805102c420124588201c001003641c8520340000d0034074581c840328911092030380d040d40a454074000200c14000306011501e070945607106114141c034464800380200f000c4550b4051203115030700d004180560f2804909010340c0c1d42250413a0071f04840464a55000c0c051403510501c1c41c03040a4001c18681211a11505610165040440a02e10444950310700502020070301050344103060010200d82540c40c00f2408642075944100e100d16817008904180340ca080 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 178820728 1250 178819478 178819513
    0x60f070b0708060f010f080703090c05060703050d0e01022d0904140a0c02010e070b0d0204080114040506060102060f060d140d052a03040e0709050904080714120d090302 74
    0x22034081002c1039105080000518000d030034907520b418242001d0300c9000c03141c0802821504014003941c00e16954200c2c042c01c4c050203080c40b800034030000b0500d0740e448160f480c00612503040565051007041c2460030301c442281060094620b8085281a100568508422140d5400880444076862a1020404500e844e101c3e402a11b0440f4041d4070000c4050030401181c50840b004500c00004692401c1035208401c000403c28a080321611408181c032000300345841c80c024803496125042c1c43d03103401200c5510194600001348105d0043d002e650290f40e640c1d00682e00c603003003200c00c845007400140c005a1103241040c071f1505424003c420720320340f0f600408495031a14a91882d50800b003040864400c5060402e43d204c080881c0d500088001240044281e145c0d40c1c5c01a800f4691803102c100340000d9500e446403100314000c04006140c1d4a0030700b0141003810319540b292400340e0f0100e50600000e40702c1140092009000c0d10a900c0c241c2c985920036040d0b10050005030403c4045000340c400700d04050202 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 178821978 1250 178820728 178820731
    0x313020306040f150902090c07150606030b0a0b0901080103080309150702160501090806040803040503130603060e130f0b06010219080306091f0608070318060504020a0609030c05060f070b 82
    0x41d8251120f0f450507040044d80d03003c03c064404095810000b00da00142c070ba80d00d9180d0004480c0ca145900ca0059180400c82d0924061241d41e0341c2c2d24140c000106541c3c107130011034040c0001c0e03032900c003440d403505440281d511810a8090104904030010030014442c1002198440c0703032281034528030100804040001c00b002ea85000040e4003908200144d80656540c2000600c03003400d01140382d51408030b1145d2510b900038030161025401100007400c0c05824411903041d18200c1c0742100c1a16181c00d4098014010382c040c16901445010000c0d124072148090003603500e401c54000c03a950034099442030f43c40400140b04604501400326041040449003000007129032141c804282c0340d107014010b000e42a01c000b0a0100040342c00300c01c030106c8445c2ca202c0541540c43c00d1501103120781d81c45000f80c0240c501c000491600440c440701120a0158542c8075a000b00c0c03007102d081510b143e403090700701c9544e04c1600010300900540181000640b8004000702010307040ca2007024284801c6072213151032890b0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 178823228 1250 178821978 178821983
    0xc091309031809150b0a0905030a0302070e010e071b020406090204090e0c01050f16020a17030a09081b1216030f0302060c03070507030819060801020c010e12030606031302030604 78
    0x1403407a580705918240150800c0a00050a002c0180f07800e18401a4961004ca100700c100e074001c00559001c2440c400d120300005003002070300310340313100f18230340f800945d2080b007072060400c070a0366a40007050340480081800d0081c132050f5285000b40c0c911044070f100d1402600c104903405507a0f1600080c02800038006403009113540000011503c40300f804032814003c4030074049041220030400021146a0361050711242d41030303420050000d40e841e20100305032a10320b4000701120180c000e1001841980040200160001d55403041d001546c0d42100d640d86030a55040c2d00f182c1031219046122030304054103100c51100108045070211003826110022103980d40d0003e071054000701520001345038041207100d4000d10001c0240c6d103181b070200070040440c020158000e0802143c8400b140c064890756001f016101c481040070884196103a10041c000d50000000b003059500749105a152500d010420040030036031098683c1c40c40e42d0399401c1101d0b50740300808140e01c15006000480150310101f294612461 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 178824478 1250 178823228 178823237
    0x901090605360a0b19020409050a0c020f030a03020a030209060c0d0809071206090201030b041415060304150b0607060609150b09181e04050a021005070b0c09130903 72
    0xb4070407040500c6449004015048000500201c080c0070a4001004460355402ca641d44449441c0c4400c1000c0082046403200d154900228006c59102c2c142e500450003060020000c0000300d8406d1401e907250124015a104213802c24845051003600070780041c030711000c9903e0014500750519001408030303001003030303000141e0380602c01074441907401854258001d521640107140704e030701e4082d000022108005005002c1600d41c41540f00316402034025a154810060047c0304101422a28102b1940112a2450207507003210f100d00e0341c0d0038144100ca01a94000303900307503014658888140060401c480d2500c2d084076081101401042c09403241d8806001c603400c000c580c41c40d69640c0c00b0003100303a58218075406a800c101010042c0e50b01040201c403201c42e0002c8030f071140e84c1c0c4103c0c2e070a00011303800c03901802204d9100b040100503021072103440551007110200828000c8003400c803500c0c01280ca00804010b03c64010031903510420014041e108402055418a0791501c400441943d5041c8022004107 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 178825728 1250 178824478 178824511
    0x406080a0614010f031101050c060703051501030903120515100315061418031002041e08010902010f0c11120303060901170c010305040602040306110a031b170901090605 74
    0x100c40c0240c55204040d0280ba5900d5410b144d686440003c4902c80240041214050701c41582d02860554100c0c0992005680f00c1c3d1174600000b60107818210303040600072440301c0c0050b640d58040d100710f6006c41c1d01507407285808001124060300420000c1c103001343c04034010070540031960f5000300d254048440e95501180d4012049080c903075031040c0f90402c0c0c0074060050030041070b08204a00b41c0721011100303002c8807207900c0790b100800c2c100000c40a40110080c00007034080303031000c5040d84c850014817141011142440d900d8001e18221000240001d00040d1030340b10640004d4403444180c902c590140031218203007404200041c0c0c103400d501200000541012040150b40d241c81c000c0180107142c40c034261030314881070213400341d01c59000c4030709507040c191b031400410140020b617410340d0003855100c00200244003400700b100b0305980042183d0000281003450500d21400304034410814030300035454501428904240701b44482500410381000b940d665100100818280e00400d4000e07007000c60102c0c0079 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 178826978 1250 178825728 178825733
    0x18090414010e1b041e091403180f030c15070302030f0d0f0b12100c090803070f020a23090415060905180609060c1b0601030b0a0b0d030905040c020304050406080a 71
    0x11804200e10f02c0b4800e40c6007405000410500c081841c080da8403104000503400311503c0d00b0f00005d203844040c2100d030703c00404c035405c116060b48440850291b0440e039640328010390718109680c41c400e500102d07800451200c50041c0140105d00502550b80c440c0c010382e400c1c030b8880c520702c00e1149c1000600000306912120860018581441000500101501d07420401d100c0f0140e05c2c7d50380c0c842e8902d036091881c0d07555240b50b0204d00c5190284041c00c0c0303c0d01542c0c1d40359600e0a02796425014148140d1090056600c0050000b9a00d00004100840f4104540000d0844030402680f0b00d030013002a105900c42d250103d45500240c072850002d4294800009520700b0800c52441c1c840c80d05c81c140000c035030f01000034480e404000096840e1310410341c7e580140d03a280e8203600300c0703004030b4075804031041d610410740040100301421003010303c00e50142c1810007890039400108241c11104200141c0031880790304092005040035004203400e440240100c0b890f0550f03c0020030101d91070795110900903080143c02c0000c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 178828228 1250 178826978 178827013
    0x15020f01111e0910050d0e0609010905010b030607021c140c0f0f0c0117040f080f030702100209060702092e0312080601020607050c1507050d0c030218090414010e 71
    0xc1e542c140c40304031070411540c100072a11031003034844181d050000c08034a210f010361080d000341440741d0081c01940d1850034080c0009003c1c180e00d880c00c80c0c295080c01c1088e80b8078140050010708c1401c20350300400d0201c2c0c1e203007408050301103450b0901c01040080883d039000c0d8815000204101e4140708001c0c0a02203044001c01d050022188070203240350043c5d841d54106030b9110188292404d80380203e800315407264580074904c0701d00003800524444d03001c41c00c000c0f40d58800300036520400a680903140d008418216942c100e105107210558020014800c041c054103210b80065880740d054079014507840104c0c1131040300003403c40910b0203d207074810030520030045c4903200390711000600d0400c114142000303030010f03440b000000d01181c20882c0109012151030420095140303202880e9690101e54142448001c10320f0340840c000310007044c245003da1000c0341c0f19100729041c0c010b1f41d010010507508241c04102c6007030f5001c0c1c0195903102504e0150400c0a03070a1050900c240c00301d07802000040524aa4643c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 178829478 1250 178828228 178828267
    0x303020a110901050d0605090a061d010e031215130e0c2d09041106040914061917030c01020301140111010902030d2708030c12040f15020f0111 63
    0xb07000b0300580004024503250b0019060b0302c16402000410140d459141e0b0b18a850030100000e055241011107501d802000a6180302d0b06030800002440f43c0ca50151400707551381b0404083c230420f9682000060100c0a003480e1081c0102c1d001400b21030a145031801c91030035610800c04040b456044480250607510303000c54103101031074070307000000100c56401b1a1a0540c014101c5894040d08600b40081c04000d00e0300410700740d4000c01000c080d00c2c1c60300e4240040041201c081c10800e44030f02c100100f68146085690040401100941454000c1c10b007204100418460092071a440c03205000b0401e65080a002550207018400a000e02c0441c40b000010400329007086460406c1e4508900c2034090b803404544030451004c1800e0010002e0910300c84e00703070104070110007107a070400c0032000420100d40c0403000340440403040c011180030b40359103900c0e45c40c248103e02c41c2c40f02e2801b1480040010781c08034034500300500040d0040d00c0c0030300581d141581c20354001820103d035920300041e10340b2050500e83c5051 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 178830728 1250 178829478 178829513
    0x6030b0109050307060c020114130e010e0f04140f0109060b03060117060703051003020d0c03061a181f17120a0f08100825080d0906080912040303020a 66
    0x50407151030600440d407203181a001e0300c2d00304a5400340130402d690140000c1c49021042040a03981d80413030404150100d10715000b43c8141c0c40402c0f0000803044240c8040328002c81c12002c00441030784450b618a400c0c5071481c5420000790149049503d1000c6c000e21409802c0d034002c0002143d03d0103001d04040c2000e9058000000303010f00300003a12a500400140305031310100314100041d69032929007003480042550741c4002d52007280b441307a071000c20040281050889104034800c2c0000c1802e510380ca42084640c0c103030301e50414500c1610b950301007a010251500507645041d0402400f881d000d01000f0b0030329903003060103003450915810f1202070341080f881c078a4a80c40c035419400c00705c000000520a11240c01260208841000422a40301d007403010343d0f0041003040111005100c0641e10407029107211545200c0c4214440000646c1c0807001c03450030b030b4451403603841074200350030a6415074440c1c0700605100e203d449110304100000403500000c00c00b0754029001400819940e25080800701c1068421 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 178831978 1250 178830728 178830737
    0xa0809190807030807021615030c09080a020d06090c081c1d090a0b09190b04020c0c15040305070311041a01080a090201030f06030602091215161106010b0406030b01 72
    0x480124003a81c0a49114030b50518110100ea103404404a20300f03244584003885014201c0030014100d80102540300203424580c074148142c0c034035240141c401c2880c511a40640d5007000120100614140b20300794102445000001401c06031034407000c5d010f0303a00380c204456a9015040c0310400c03468200e032020341281a40f518086010f101452000780b00340e0f41203040e00490a610104070800100d803c60030022402624400081c0f0b03101c14414040700035040400f41882c038142140c41d1a04250007140c1044080100074402000c0341c00520140840c407100d0022030750405c2c8800b1000800500c080402903000d600c03071010806600c03040100300e07071480112040b46008400d04001e1660440b9031650b00c2909100005000c08081c00141d010b0314524180c000114584540801003203480e5001d450203070404e40364905040c044c0740245c0d644041400012403d46143d9000407500100e840758413042c844640361120080c400703100101d00e002000e0b00800810000428148408d0380d0501c620840f0b00720901c1c1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 178833228 1250 178831978 178832023
    0x6030c0e190509030c0a20060f0405011b0804030b0f07021b0f01050706110301090c020d02030d051909030804050609120f0a09080601120c0e280b060a0809 68
    0x24070034280100a01801c0d4250b032684006100700c00140280d95082850030183c4100210503d070000481d000030b00c6102c00b403110710700b040d0003900b000c0c0246c4241c1c10342e61203601c0c982402c20b001903d411a10849030481886041c208000060b06140074100861064003486a641420b515010070000f00412150856000ca88007010707050450b40311340418402541c01e1000c1c54540d00049902c2d01c11051301a0030360b030401400051000c02a001181266400c100402c0401c4450704100d8881e425485142c0041c2d009102c0000d907407450b94411601b0001c1d48416070f108852082581c4155140d0220030740c082060441040f040c4001800001c1d03120302160060441364075100300c414903038000c86d031046801c40b0380824070602580c0034141c40d50182c00a00110303042582c0d96144100007880541080b58062f0000c2000200c0d5450409001d0040041c01d1000d10640340803480c40c0844203060380181042a124078a09026858003002081400140c0e5035042542c42c240904e14548178408400180c407481c40715 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 178834478 1250 178833228 178833241
    0xa0f06080a05240102030d2f0a05031609030f05150f060303040308030a0204050405090706030606030b01050a030209010e092a12040b0a090203030a0804030f020c010504060c020a0f080106030c0e 85
    0x45090210854409000360780b4603400c3c00403882c502408072102016481c2030241c020a8210910020842040184602c400e5480c40b69000b06030144205005c04240103102041c000400c480c07410703015088901e403640035595a510741207115043c00c4402c0d03501c0d0304644c61003401c0380100106c0035030041825191150700d0503c0d801103580c030f1043c0d10010344099008000300d84024403540444000b08001072050200c2e042c039a21594642e01c0b180b00b9400400c1c0340c040c00048543c001d008201034840142c40e40c07400c1000c1d0040a4000c0e500c4024280d040182ca103804502c00d80d1204281ca010b520300c069441644840b90f0b480ca503a44d4004c0e61424081501840105180c3c1c25002000340e109074400a51881ca07103410034039038040c00c2150402036250201051410708681d00c511864801c50080c1d4440007032205c408426030701c54640c03018060000300304010602042e8000d0764024039203803000d0000701080d517403003079903800c03030400c0d504021000c3c0d445103c03c005020b20f1400d000e024203000402045c2c070381030a0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 178835728 1250 178834478 178834501
    0xd0906080105040c03060e010f181404030c02040f0f020913150522021204120e0a03060c0e0402040b09030f070e0f0403090302100c0615030803040803090a020a0f06080a05 75
    0x500c1014440c60301ca1803901c011318030a03048031004002e000d040344013658541900b440b51414034050301c0012103140b0044140d00034980200c0c80c81c5114041258500d84490310101d8880345580c5003030b40c1007900c40c04100031a1805106c0e86056040c080001070711000135030108400345050044900800382890064900d5241400140b42140e2040302c64060000b0035041040b04010398541c1207000700d00c00b158940c40d60220042052140c1e2082c8040f80c0d038101c8040d000d070343d07080c0e103111200e4024485100c2480003802aa00010100d6010b00b032440d086080d040004084e6403040e007003419100760200e07071a6490300b810450003180d092488042e007a0282080c2c880d0080036002071070707000c0c039842000201c3c080c1401080c0303000103980c01500c0200f00320382150740640050400f06040303804620303181426200803405112201900d0340103e42a2841d1100d40390344400e60405405016603002c0c641c200f0300103a0b16014001c000301020300580441c546040341c050003c1d44018012408a4105402c104000512 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 178836978 1250 178835728 178835731
    0x2070c05040906110a02160b040e070804050c030d020a0b1012030e04060504060905040c06030501080312060307080604050703050105070503070c14070306050a06140409111005070501050103060e0d090608 89
    0x55a002846241504000c3d028000110a080702903100298662840c1c4c0d002c03480820750014110300803482590790310700d00128801c40c41402d124050803408904814820360310b1540060150003282c0c03201e2038000001c1c2c10102d80034a2000543d00051800d420802d41d5242036074010b02c0800808045031401e0202501d0361626030b0000c2c1008001c502244007651386e40e201501401028004101e02a10307074000c0d0300144821b45040d1644007002c0c4001070814403a0160a0507101c1e000003460611031070810b0f118088602804807541801010700106011504001c174a100344d02500c0180422455414180d08541c80601213000304102041040500c41c0c100c82c00840f100d0740007111322160711403601c01c6400c01c41e080d00002d00c0725003804180007404803e504a0025201ca2054102d00c0205400801045410b0404010f10244101802c1c03500c5140542c1c0154007407040f130802601e4140035544a0b821110709800856406642e000c0107040401d080021100006440c2406000341d41801b0002d17092110 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 178838228 1250 178836978 178836989
    0xb0408010b1819020403080d0f0e0105011404020f090303030901090c080c030613230c040b09100b0309100207060903090501050909010e090a050307112805010c020103090f030e090106020102070c 85
    0x9980f070403034200c00402ea049400035500000c4c040d803500c5040c101c1401802c041c403038205030b490812840c01500081231003428100e450105001000078540780600005e074001d15814003401c5000d0044100e291010301c019032041ea201d100002c1e00200601e04540500100d4101008a52091005030f103180c50005202ea00060b100149500110003454645901ca005c04112101143c4001c4484001c140c0002c0e010b4084100310303010700c2486c1c100d500348207020301d08482141d0b001c80078903801c0242c021480000c540221038102583c0da1600c000828800307981c03001104a620301c1d5070314116402e2662101510f00501001d2804a162421700800207801e40e8041c0110f82804031a90041518600c0400a40011b503a108040d6510b03202641059000101c00e044014081d405c0c3c00c04407102200c1c0800c208034032124003026040214280001107540c0e030720160040303051540d15110400419000d18070130924030f20030b41c3c4040030400c1400a0011107035061b4000c00c00e580c014000580003a103050032250944a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 178839478 1250 178838228 178838251
    0x30c03070b100914061011071a04120311060609040503070b061c15060906030201020d081005130b0312030709031e020603040b010602010b0a0b0f0703090f0b0408010b18 74
    0x100c2d0448440d031180081d80c48a0000c91500c584640d88044600ea0b091040d00100c0d4419681100d4540039900c0c181014050f105c176070880c12091014408040c0e84074412403c80301d800e82003a030ad0314200c160701150341c1e01c282c0120380c60325081640d1070810011b441d80010191440c0010741003e030b03940c1c1d0f600d0088030001420380202600003081030311a07050403c030049032141d207e290350100d410509900c2500d0703585031300b215080000104210903280503100c00c4a606a008007440f01d2681c0c1c044a05140181010884c012a4800081c031907075a0f041f20020b607103e600d00007900c10b1300304081500d881d091000c40c6203002c109004000d18030780c11a002c0380c210fa8001d074a28020720844070f00d9045898054170020340c80172002c428402071002c0b0b420300398140c0e501c1e9002003080050150400081d8003480c450343c00240c1c010000f080d8829031480162040501c2402d000d0111502c5400c104212419504008100d0902240c100912078090182c80140c00081d64481410708050410180742540200002500c2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 178840728 1250 178839478 178839481
    0xc080d0e1f020c0c090105010c03081f03080c060609220204020c0f0a05071415090102010e010603060c030c0315030303050c0714061b0c0618031b0d0908030c03070b 72
    0x20600903040308031190103140641c0407111404000a4024072182c441d80e108449445440e8240340c5c103601d0584d0b030161155502c0c081b01d03507812200008000d003003e03100740d15203000c88003c034850203600b40075501c00c0c003605031120526950a45000801031802d03104245620034000c0384004500c00c2d90110b105180c00348289886800410041e114031107141c006840791181e422503c4001059903007400e44204183e0308410303a100036452000c2144600e8a5018a40004003d035010455000b400f4090040c000864502020b021135400c44d0000e60003500c1080d141d01c1036980c0a80e1600c150703401d8009600b820062114040000a1369900601005091541d5040440d00e00704e8040c05940502d0f5224000a00300d00b07914010b252103c00980b50481100a4403201c00c009958a90540c0d514251140040c0700c0d980d00c0441c00b64103125030380010651400100315000110440c44000b58500c05914000c24a00d0615100184402d03600d034002916500244002c1240341d00120440b1100342c2c0121180c1002d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 178841978 1250 178840728 178840751
    0x12030315040e03070803010308030f01060203213c060102011a0402181906021e060402040b0f030d020313081903080604180317060909070303081b16060c0c080d 70
    0x951044e180080d0480d00302000000402405800852045440209800490760f80d40c005994900070100c084c04481d140140c0362428640740c1c0b000c1c60703109000b0b25007809441050301d540b43c25060600e1001101070b410000712041fa40f04075201c0b03604802d0038802041241e40308109640c0314404101c005104540010300d408406444d14202902e1050052001c0b8a642a80b00e91100303164482c85804003500440404c4d403041e400c824081c0c88504186009840301d55a1507080000805600b601240e0114241624900f2a18200030070114003880d41c00a50fa5a094064100d1000c0000da104448640c00180350003d04880c0e00348110603540e0505148070a070700d4200000380984000074014a904900140cc0c03402e16034030040e0754032240c0525402c40300c0c40d00d400003408118841201e0840f2280d200c2c54040002a20450700700781d01510601c480d0fa00d038218078007058000e6000c580e0942414072410703401c7c814800107108422000c01c4505040f0801c03809550307490441d00a6199005140d41e6a00700800d1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 178843228 1250 178841978 178841983
    0x1b0702060d110301060908010506010314060609040f020c0d080f0601020703120c020411120f06151602030304080c01020708030a02120a120905031b01050402060d050c0c01050f0612030315040e 84
    0x2090b4640d4800345450750f8441400616041c0c0c82c2c850b10407290f0800c80410340c103500038855028000701c494032200c80c90741c402040c40086c7d40208100c5421650b90740701d1071840c403142d00c06040003000c244003070071001e00030a40c020700702c4030082c046070a825042e0080c42400ea800191b40000c49501c020a00481555000c09840769071400b00043e402508150082160080420040501038100c150020031500c03512001119914201c0d030341034120030001100c1d5801403400024002c40b400100c0100220320300b581c08a400c581055100c00707120740c00851048a9580c0500c082c50141840764011410481500300017503595000c01c12650b160800000c0c0c1040c136a00c904031048210320b0740c0d0b805000e10329052401c2580ca0340030000c005040200301c0c5824001e6901800b451303014940003400c16042102e20321528000300b001518034010960704025070102c0038028010188140281c29400016140030801c0c404001c41442d00fa4166030402c0040120580d1a0100c0010181c000e850004400d03072640050761 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 178844478 1250 178843228 178843241
    0xa060305011214150a09060e030310060509061c020309151303031104240807090f090209010c1a0106031b0807231215030708060c250305030703051b0702060d 69
    0xc1319110b501c400c220b240c1d19190003000b40e0030f03c5007000f00a54280c1380056074503800291002c0449402e003490400034a4810700180040c0d03c402413a01d031500404200b50120300034900f82044140340c01108010364440d0601009030711146050300711200d40f4204520203181843d0038402410302d681c0c0c00080103031402c41c4080e074001e03040440d0341d140c100c0141c1c0301d4149054000e0204000145100c0c0c00508224800e1840278111605540d4102d4250700f04803008000e9042445801c0c108031100081c400421152850803c1c605050b0880d044254140301c00101900c0345011058203007114002c2841c1e00543c02410503500402e1440d080302034008003200360b80c0c00000150885155a004140c41100d101c0e0325002c18002c0502a00300d09109001500349a110007051080170b4560300305400240d202e00701c0d04001e01d8403035608a4440ca00c0160306284010401c00071034250700091010042202280d00361103040d402400804600f80d4210f00520340c03401500c10fa15000f409140003080d60040441c0b00c0d00001e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 178845728 1250 178844478 178844503
    0xa080c13050406061502010e1605010f0809191202070b040506030f04060b190e0a06030b010612090602040e040b1e01060c110907050901090f140d05030915090a060305011214 76
    0x200510b01103085e00130f01030310441ca10000e2a00410b60988030003080103540004491040c0c5410211001107003042e160707181d00508852003409a20280f05001d40c0b070700034020009200c1d13050542900001c8070700920f0804c190b0003000340e0300d804210034005507a81105403075121211100c90400b41e034403840d188020380001000300390003010908221048041c03550b04031090f03510030075000310250b0314002c088040c1c070264030001c0c241c174030340d8401405018420f00d641000700c0181640890303403c4282d0740360002c9034440c2e440010b0500e0320303000f40410000e149100907000845a510301c1e814406514903101a242c061003102e0620070785440240400c0b08070031010040003001080d420691804402c0601254042c020444c001121003901040005540200d5000d0703500c0700d1182c81103c5481014000096440001500c50f4801805080801e60b20f04550100c0d80c0050415a170701d9030565818044407400d1034221109150414006100c1e0350040c0d60207009407900082e0b01c903006502c3d0052036091003c0d400c041d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 178846978 1250 178845728 178845749
    0x80f0708071b090e03070f020f0d08030c040501090510021203130c030507050906030a050d0c02011202161112151803070b091e0303040f150207110a080c1305040606 72
    0x2d880110840e151a001260f510340000d10420a060400d103482e88a4914014400d01070562140051b0400880c508502500a0f003c104862901d44803490141c004403012034010400040c103000b6075030700170700c01401028140c40c6a120780d580203601a44400d9080810f007080d41c00030000034401540c0485000c500c5812140171400c003500d07810800c0e150402c0e809410b0003459039201083c45420001034020310650090080c140c040071000c3c3c1280c40342030301c2d84c0680c100900c2401500e0002668401090482080030a041c010b0a451415a9415504415480c03013810070708401a2450000f00e14009200e80038400302c0d03070f82c1c3c0d2000714000c40b29207001c3c1c8154180c803010270703240104450080500d00440480003186ea0070314a40d80c84d540d00b05490070b0030640c103030000d01c0400c0c002032224103007500f800d02c20000d138101042c08140f003c00300e812032001500d281d0b04040301203505042c541c50007009050b54501a2244403040c030080781401e0540801982c0d010742d00d0f00064144585a0700c0500900688820f = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 178848228 1250 178846978 178847003
    0x406030204050f1f030f110c010905060901020307020714120a080703080105030c010e19232704140109020409110414071e0903230712080f070807 64
    0x10001c0d0001d02a81e07000d22480d85003440140b5280301d5a484000702078401da030514030a00801c034050500e01031440d03049030301c03181251502e0380ca44000e010411b4508000182010301410418a001c60240c8102c8559104005010765982d02007280c030241c0340d400e10070210308044503002c520082c20016658400740514035100081001c0303080244100f5020341c3d224080d41e47c8502c1010384400401c26418041a2401c581c25800d0400009107205802c08040c11268156500c40c0c0c40303640b0450300700450300d104140804416600d800007140101112400151900341d9151075102080c54000d00058401d2460902200000c2802d40007040c00070790242c8148060845442c11003c10624407030300a100d2810100b661103a1407884013414400d0070030b582c9103079115500d1030810003030310400199007042060044010010841585200f20f45038a00b40f040080c0c2c141000d91141005040e4000c00c203034001c01d091242c04551610281d483c0612459156a84d8065074940049244100c0c0002040701500b40da = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 178849478 1250 178848228 178848239
    0xd020307090f150803090906041a0405070203040501021002030411090c0d0c05040303030c080f040204050c0f070b041211030a0302130801150311010306031a0702030702060f03010302011416151104 86
    0x802540941e00581e1454200716150000e07a174403401140300a6420900030b000140c5030385004e8001030101c4008800341004a01c3ca140841c041e64011a00a40581d000103002c0005503810460013201d841074400450850a06680798420003420340d01b282d110790392006c08942c240420303904071941003588050420089116a0001c2c1081c3c200d03200c10b03000700c1c0c5844020301e00180542c480b14410f0f1040551244031b03070356550130040180300c050700c295030480c41405110480045603000341850380c09001e50007d01d00d001c1c50b00701c043d040e42c0207660041018100d040c9558481c00815500030100504003d0b84039451604410f070521000d5124007055801c2c03108510404914190342d40540f4084c020740c0400000510054003500e019201c014070018505640300b00301e04046958940024452041d40d1500209400044c00da030040c0000b0010301a000004000715030b00078a04001d822000c114950409401070310405154490440252640311314040c14444040d050b8080c100e440084c240d1a80c6807509e64 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 178850728 1250 178849478 178849481
    0x50402040e013303050405060c1c05220503040302133804060e040501201c020f030c13080105070509100306050307080a060609061412031611040c18050d020307090f 72
    0x3624240d4142c025040800d240c41090822610ad00c0016000311860104440b030100044c0001040d01483ea040111001980c514050440309840d01400045448509500411500100c0d0504400000c2d16001703415010504103003613810081c0380f040c0701c0d415001c07035414400803000302080c0e0160700529104000c55813007060400940140e0240700208110009040c5800550001c0e8580403912202840104902c0b07905114070405011103150241c10101407101440150300183c1d00c294002070040b40340100320b01d9600004009040b5031001348501d0420b108050200d111390043c140c0140b03290203610162601035003007000144405800c0720241d076500d001d610786440c2031a908031109410084d0000e005440c5002e07000036200e990380078684444800c820454501104101414039000c14001d51001c0030b1b4881c15110198040c03404040b40c540a4001c2004850391600ca2000b0b120240d120418001468000102640d405840241d858071203400001c2c68a85203034000d260607401c0501686840409 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 178851978 1250 178850728 178850731
    0x3070b04051506090612011b021c080f040b060d02090405010506010e011409060a090e0a060608071b080a090909050d02072705060409121701050402040e01330305 71
    0x26505482d124840c005880445200c207442c00799202408002142d81460030180c0303203400c0e6144800010b21841e1000c100d00e07110399440701010150f00840c10f045401d0000c43d43c6525100035a180c0fa084621704035680c135007032900c0500051b0650982c0000074003c0c0c2c8031050300500c2160000d08120013440c1c64501540a0300d0212000d50001e080d400001480b035001e0a59043d500e400340d2540c41c00c000341c1500b030040c00d421941d0342404005610b040004c11243e003507007040c0035001c2c1c86004101e060034a030024107051005000c00b070801c20841c0350302c9440e1a80700015002c01d644004400d135107080f0980200c0e900c41b010b82090051b10b00d4424144100840010502c82801e5180c0a6030b008a6482c059019244c0040090b007291306c2c0300600e0747c4e410420355800b09500100c02000015408615140c0e1b08481001c01c03106400316201c5003903c1c0c0362032103003031a80e40144000c580c154034060405a5640060106104101a096000725000800070305070700194010209ca030200c95004250007402801703800d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 178853228 1250 178851978 178851983
    0xf02060c100e0307031d01021501060f0f090501020a150b031009022e030509340503010614040207020604030b040b07030e121603110607090e0105030703050a020108100803070b04 78
    0x2805241e20303440301c0040f00b55101c00d0380580b21080c0651801c032801524410207041d00d81117014103c40d6000138003001c0440780c007030182a6a107200710000740402034081c41c00300b580c40040c00503400d0104501daa00003191801075502008804070400403500c444003800d40385002c01e0b8140242451918590342c19400100f10303d001300c1d5485141c0310a10800011103405840010100c0803042d158840d00303000e0f40285402c0204bd004031042400c05c0d005c1c80f503210307000218001c12100c464145c100508100b001d42d40203800e0480082011034174041c1c4102d411040c0040c5607000d107402044142c150756484003541c00030f503000340f01000f4926040c50060ba07080340c01c942c0f020100b45040084224440c000500d81412000602c88501d00a54484c025101c10500f4401310108455004086107090080c4401030198200f40c031a8285a070030f0280e803041c40ca00582206019074494103041001c501e00045480039180c0a00b0002126250901c0c0240d4806840e00301c10320303500c000a104010031100c140540c1c032460 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 178854478 1250 178853228 178853231
    0x50108101104030201050714030903151e22030909090501060303020609030a05030103020d05190b2d0a0b120109050d0f0314010303050d0902030106030b01080d080f010b03040f02060c10 81
    0x40088450760401d004a010181c00240140421000641030398203070007949010004903810b0812507400285404003031800c244041940c1d100384200401c2003d070981e008020107040c0e0400f46081c1b40300202c1030000c2111074000324841d19036038051500403a4036401804010105009107411414510702811036480102d0062080100007500104040180c801b0080300390386407840d603444c40d020000300051840c01612140158540c00c0540c0e4180245000c1c2144a005c8043ca01d01d01811003443c1040590301b01182008480d914050a00c111540b41c6c0d4040f00c3d01a0000395040c0060200390b807038208000070001580fa10742c141c4c1c00d201000680403200c04041c3e40741d02c010801000d048085c1c2d0750301011154240414001071000a0141c030241882c1401024001114070700c83e000203080d1a00303a8002c2d1480c44502006008145d014400c1c10780b00c42c0c25042100850070640d802981c540d00c1480f4000700128040045020800b5240180750690340080c211078461a03503401143c0c451000241c2807028a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 178855728 1250 178854478 178854491
    0x304060908060c0a0c02040f051801230a0903030603080a0504080c04020c0a110402130f05130c02070e1302041b03060f05031218030a03050711010824030a050105010810 74
    0x10080000e81034400c06410743c581e4108546544150f90030b64043c0e03400c90340035456422100501015110310340c8105907030f22400745d5200f54441c0703550855a000340c045000022a90003401650344581d0901d42110340031070300240c180020b04044000388aa5000107180c800c00040c80111a40d2200c0034000380d54491040e24001c480c0782c7e00704400c0b40306034070001d03915800210314000491a00c041265100401800151610307080340c1006030081c9040e00b24941c4150551810b001c1c904000340d078200c07a0026503d04204101039050003079500d0440348210309040120f000019500301030b0000e6030307210a038054401d0150ba500e10785035a003070308601d0515000091500f01d00080a410342441c0004664018020b05011440580206581d44c407100a0440400340d10140400035103081000c42d50042c060360f036041d21000649002e60041601000081c10031030010305100110700d04561800850350081c401421f0014118082401d248802c580940710354680300000903800d50101d00003000c000c0001c0104051b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 178856978 1250 178855728 178855739
    0x60308180904020a050603040311061608130b040807030903050312040b090705090a11090a0e0601020d080103120c0f02030a0302060613050114060a020f030309010605040b030c030a060b0402090a0803040609 90
    0x3446802c5401941c04404844200720b0360a048004503089800b91601001c03602961071060700c0c0c2181550b13004014142c074824444170503804080710b9041b820200318418049641d17151000101c20241020f0044c00000078464205402028608003c40d4001c0989461714207443c0d0407440c000c4115001d0f40c844504500213000341001240310b10980300300030020741c0541c4602a1400041858641503100b1402c00c00241c92155038082070400102100c41890080d40340c00c0c0d00080c01c1c601101c21030f4040c020142d0040c000200d10001c602610340e03c2c0d1070144226a00390034190000a506c038006501406a01c1100c41855030104009104078001da541d1000c0f040f00740c0860b400c0341d41c24454000e00100b04000451240b0342000141807080c6513104032003110411070079040c03c650064415080a0399248400c0060707007440d0141c244181c4d01100070744640f10207200800e455850700b5000400d1281d03560001c110564403a03040e2100100050b09190f503007a103400c0160343d01c0d445401250086850075000044 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 178858228 1250 178856978 178856989
    0x507020a0203100f1112181204050613030618020907020d02031204020609090106031a010314060d15060602060402030f010c0906080618070513080c0616060f06030818 73
    0x50481e400b40050440c078100f8001d54004100c100300560000392034294180000d10024041e2600407162082136045040c141d003035204c030036500710142c81e00740c0255070b09050101c41c02c416502202d4090340e845584014030ac130084425480b40c0c20080400740707400411005024004004c259044c82036540b402d442d00e600005907604c64100d01a400103900400040b0f5800c0c02030304c50340b900144060030781400d0110a41c002154072400360006400207994469003010012070a0045011210a081c10000d06242159a44460200600c42e0740a13082070311046040040e071f280070540090500340c080101c50b0320303101c000391a00c0c0180d03170a80c8244548000341c2d20900040c81002c8046890b92211800d0a2038100d0644181ea00280703c56400521a4030010000440c041d80c0c6118405695030265a54086a203034211054250050b07441640500d0090740036403034090485031000c482400d00107004481e07113000005085141c89164034a401c0c05400410411107402800400380f41906040001800710306004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 178859478 1250 178858228 178858243
    0x91a070201030b06090a031b05060a02030304050601060503101e1715060603010f03120203090301020a092c13020301090f1a01080303040507090b0609180702070b040b0417030d0c050d050702 83
    0x354013086c0107504000081c4181410214061840c120444031503031240011101e81242c00da000142e0070000420007000340500a29025210a003441801d505014419080100c0c032030240869000d4200110190000f101a040f00240011000130060041141116489118203001800b591003414003003142481c0440680f81603d81920643d80400c2c59038560000004103400d20b4420f41c04204450b0f20561428002000c01003c1034070303022102032030700d41c10f6851500c104505030340d4400700c201083c0048240c4048141c02886142040c0b032035503030030300009004050240f0014031030700c0d1412041e400c020b801c010080032140c0324a1219403ea0780e4074142c40d201e10080310b005205410100082c401204070b64081203401e14050710050419030fa0f038000c150140e80f4100f101003040c0788841040580c0c0e50400207040640381112000781403501d4660050601d00460040070103800d51010034030440c14041041e9103402442d04010f00030103081317000183c801c3c1d0101911074441818400044d41d218000500301 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 178860728 1250 178859478 178859497
    0x30203040618050607080f040905100509012c06031608010b010f0f0801060516020303210903040f03020928060311010801050102060a0f020408030c030d1802011b03091a070201030b06 80
    0x3178a40f81c4a40c6d01c2070700f1a80501d0240981d01421301c070208044806108651280340f030203c0460000307041104006c04440141e0055440b82040074403d04032034110035981c03d100544003081d101a07126040028144154200300c010310012a40e4002003261054000301c2c1509030030380700d1480340700e00820111288018102d43d070b03012075004401048942c0c03044000340b4098003030b640b08680f1408240d00103401c40d400303600c400200f584030050012402420a92203034000800000640c946032400c030300c2d410313265440e11019110310326120028103502e45186204010b02d02880b2a0306400f1088201c541c000c3c078036404192041d058615010406501030341d851030680e201600108803581e40c4101440c090b003069494260034540034400090341e0701040000d41008014070340990780b10b60002c13000c8000c072521080228414001019044007613600417804540c010703c1c01400f02d204c000c1e1ba050613035010010b40d2003000034190025502d00d602d6854400361000c14402da809012200c06d204c00c100301e500030250311 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 178861978 1250 178860728 178860739
    0x60e030a1d03071814070e0307060c08160b07081e01050d0303090203071508130c03030804080910050c0607030507020c1e06040b03220305030a020a02010e0a03020304061805 76
    0x1c1c4200841d000403019200340014112800c031034652500c3c04c901003107484015402e584828403c0c00c418204030030702c0d034004180d1030048141c600c2900046c0e6203100c2d40c480c420900803412414400d02c0b00c14011140300102802c0001e203580d099103486901c135101140d100c1d0000b4616004581d00341014408428105a94801140c06900f054200000751002100c11000d165840d0700460050301c0500c00352004001c0011500c2d0200012600a8550100207200311110003110300100f002800480503207050703d825140103d40340d652450716448610a0705c4810f54030111a050078408a58890010071003000110203541858552410650a490701690f40e000075030420346c00d440351410058a011107118802c0c01c810103140076000460308651117504468803a01000040054644c280100c0010034540119480a60649514000d0290102410041780b09400141c1c1e001514403d40140802188080644519410f00c2c42c002c3d50340c2e4458424403010562160700710b03c00c0c0c1c4083e5184001c8410242c030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 178863228 1250 178861978 178861997
    0x6090601090b090a0b030a0b0c0a0e030c0a032a0f090c03020c0604110607060f0f06060503130813080105271912050f0304030f0801150507120908120304060e030a 71
    0x3c104c40078020f4045107982600c6440b0800f030128400d42e0110707008460310319505980e02c4139901c0040034802e88111080c000c1e8490100d48046d0b8075020003080032250003095400e0407a40303078008441203140440c2c0c5100b2400c4081c1002c200000d800b07540303030210344441204002136880d1060603826030041c8080d11340300e41c02c00b0000402003040c5c54540c0c000c041d0700030850b615240b0142e94080c02c8a40e800c094040281c2d84442c0f540c6411160711411019228a0800604504d003403420020500e44540b0000c101c03160200701030708800b1001501c1005800c980009025610381200307014008130500f00c0e0100c03171000d0715100d02c04442c404240310000510700c403a503d400ca19281c0b030346260344034132190002c1081420482c80c00d0b00540c0030040c1d809548250b43d90b6800081b400c00080c401201131f00f08240904803c0810021260014100c4802c96480200d41846c1c0c11720000540d0f5201841d03000d983c81d4012095082800c1c0c501c038008620861180c007080002810b040e03119940c9010340c42004010825044 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 178864478 1250 178863228 178863241
    0xf0605090a051b070c05030d0201063f110f0402040612020f0c06090706080702010212070c051c1106010e040203030f0d090f0b01060f0305060109231206090601090b09 73
    0x4110b240d00112103d051209019007955002c0c8a070300107001a580e5203001c42c0107001c0b40c9800c0c04610000385207803000388900f0f401c2c015001a494141c0c500b9800501540d00c1022900610701e038080342c031100030501360000490608101050000d2221080c1c4215201c0c0041d42182c50107109039000d407203041d5190020b42d40541046002940b2003034a810300c104040c8102100d4210030040c8620401400002e00710603807418602409406003c6d15690039640144075851400c04803c4559504c4280303072410b081c00c100e5230700b000307400c0c0b51851601d004071000301168281243d8100c1030199400354074008407101aa0703990103044111200f0350703000798160001c005100700842d00c94054018104888000070350312609503100521440d420742d0031540442000010480d2a81100781c00705020302604060043d8a844030000304a03420a005401c2c1e000441041e401402e41c0000303003d001c0c040060060441e95200715015961640c2c200c60340341d003900c40c0700b002150a00c2c1d00c0c02556100306020784603041e11784403003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 178865728 1250 178864478 178864481
    0x30712020f15010506070c0e0a1413020f01051b010507031506091a030c0c100c17280f06091a0303040608040b040f120c11010905090408030a0b120f010f0605090a 71
    0x101707550001d095a030200e004503142c8940c601490f5400c9c0300041038241c403030303d03148061002001c030b950303a4000d0400a00940c444070224202c0034424a46141c0c2c40740014042d00e840c54503000090801d6103058100944182c040e030100341a00300c40d1041c40032940e40c4001c22201e043e89402120801c007030000c43d0b8000002e50782e02441d00410242c60050401900e01d4559140256064841d1186070312503180301c4030140c2189134260300034403255804009290034414904509145003801110b500314a420060144c95a400144c3c4d0012a000500490340d403448003030b018000ba82c2c0c414461481500c00315a0324a8008110380403241075440742d00090365140c40314402440014070035180b0000b02007901001406400c4241400102c0c1c2e210b001c489641c0303080c404440306032010710701c0c14020175030000e006030398070030202755445a03012840b41d40c3ca55130611085c2c0a02081c400141d0000c095855201054a001c0781c500c403c0f14220f4000c010405441b0035050039101a841515041a020b00210304142600d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 178866978 1250 178865728 178865737
    0x14011412100e070333050103020108070f030f11040f0f05030d0f0e0a1712090d06150b030c030103120203070c050108060a05060d0903110f06070c0c08030712020f15010506 75
    0x20300180c41c070441d43c84e01c0b01e1001985826000c00440c41c0384800d0f1750030307885944461900d6801382034204003960450380003030001500589208180144100e07901030319480380e041600d4600c5000c41c00c0c0498040e20b40782035032540090003000c41c40400d00901090134101094140c0071544020010b0041d26008003080c0c42c2811207a50700400c000d034003003011f0150b80340c90040070002d001a00124a1640313400103000d0801d82070640041e140300301080103d102c0d5903291000410107401100005d15521b402c801184158159030142c2c10100010040007030a1103444040c0d4100c9018925100c881c0c0400c4401702d80701d10442c00018030102160600707005035441410751a5010801070300e400043c6403210f0004005410450031144559201c50400c020960700010003d0882c44040040c0310f040c051001503605c030400203050380308110f244854203052080c0c07034030094014542641500d50340d4059003085070043d00008045005803003040640e142520000442c2c511030702421800241c1079090104020040c0d01 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 178868228 1250 178866978 178867001
    0x5030406060e0f04150e100e070e01060e01020d0801080d050f0c0709020d0b0609090103080f16030e011e02070e0a09080c030702010e060f0304020402070f061401141210 74
    0x1e0300e00000c1900303440014040d0152610400940040c642450003800c0214264000800e0900b01041100034040000d410f80d010b20308180c0c045a509503000c8034a160541c15484001203091510000540c03079044410820703210001e0b8203550080612402c103036000f01007071050641540c40881d000b06120321501c05045c12122040c4000d19011029102614203200b680100d443c099000660084440c464441c016120805440d8942002401c00c0019186e0005100c0a02a8240010304410003100c80f0300f220666110440380d24044206810b00800d41800d410304940407031601054011051010805003400800c1c50b4001e240e030b5802d0141d03d940f00c00010b012a0001612040402c00054400000d000724908440081d234035102180001080140001600ca0050004000540040429001301c81d4020340607100581e843c1094504615550300c01e003009000146000544100100e040100707074100c50304442d440d5081d10816003080550b03504656141441da2041302c90380c0e42d1a078281c114081e580c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 178869478 1250 178868228 178868231
    0xf030903050412110102070812030402040f020c03030709030b070c0f0f112707050304020d120c150f0e1f1805010c0206250525060c03021206040504030f05030406 71
    0x1035a40b9114070043d004890200c490f0501c14207540d03038a503410001c0304010980301000301905002042811424400580040c1c0940e49a5400c48558003082c0c044440343d5104200f121398a283c0f800c401816000140000c175442c519007404a07117003e00c2001601075194115030360340c003c000304d580c0c0d0704140242030700100e8243c2d07030500c03400301c2e9980d44140108074000782c0c01180c84000314400c1000e6013010020001400d0004c00c1c802d110150321110344c900e05c42640711840003a00c5101071710a03504d280d400240100010080840020305c1003184e08176030b003a43c4400000b88814500c1e0072002e034444a801400d0704882d680c001201c0a100541d821800760301a041c40c1080d00410b00381c503031900307488110750700700c01582c04a4184036005201d81e03890b0b198006401100708000d1183d584c014514407480328000035072480181c0203403c0d256641a440780750380c0d020400f004484c9a40c0e81c08ac1c0a5000181801c0340c0a1141001440c10b0030503000b402e200d2641075075480f04102e08071a0980c1d580d04081c00036100030b03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 178870728 1250 178869478 178869487
    0x2b0315060801050402090d061e060503010c050316050d09030e03010f110f09010e03060f0103140f0615010324080d0305060306040209041e0506220c05011209060f090605060a060f03090305 82
    0x721603100d1440c0703611100b0044044172103101c0b45270050300c60035405a40a689410f0038818100d5010381902c2e00b2004100c0780c240300d4000450100c940e4003031001101c00040c60440c1300410180c00c503402101c01501a002030113801c2482145004440b04841500220501080303044170b11001400102901c00050510f2480c107101c0d600404d180401c1141c01e605081001c40041c01804a01d03041140b00c1c3c0c0340340b0020700c02d005040c6022511260302802c0c0023000c19030310705c8002443e070203070704200da46d815103280005c6d424000310100003140542e4407910020340070b445a1181c2407840390003414460322014008042584490342841440c4034002d0064604402703c0d6000e6008440f000710b403c100500843c01400d640c200851440c2d80644001080401e11500c0828140000c3c00690b055048070000d08282e5040c4500888800c060003280c400200194540021a20880d0f250f80c0700b07229040c000d5a081100c0c0c0c3c1c42d01c080c0f00480c681c900604001c2540008001c14144c480d030400c0800724420b00d4003c0c1003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 178871978 1250 178870728 178870733
    0x70b1f090b0a0306060f05040b15161a100f050312040302060306030102070c030803060307061e030c02100f02180103061a0306060f0a02030a020d0201230402032b0315060801050402090d 81
    0x5c807030142d0400c05440d54072203070411031460300d40100f421000b030885080da04222040440180c80c0720b88002c050940c803000c003891041c800d11560076006905170b103a079a2554641030707580d090714429a000740d0050a413008008201c41c100018616201421b00102d689028115020003080c2e03003005100640c19034003001250b0008030f10381c0c0c45800541c03040f40c0c1940c0f6420001c6c101818001e40c0e801c600100320084590304100c0d0313440d12504074080b007a810001191051020100e081c1213030300c0c200140f180d060400c08484040c46500911484089005401691083c4001182505c2091103a448202d88909000c00314012450081d500f01c08000c1c0494a840700d080c640d00a542c200b55010320158001240f00a5901d0301481810881400391008104444408040d0100c2c0c070b6003000c950b40e94100c00c800080c1151010412020006040e231f03400c1035442c0d090b03150b080702d81c101c507503541d00020f0405000c840082031140d6108181e0301140c40d038590702c0c0e00b400107100081d080414019400380702d65aa4402 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 178873228 1250 178871978 178871981
    0x7080f040f031505010914010e0901091407060905060f0703050307020304120309090b2b060e0102040e010f120b0c0702010201180803101a1602010207150203070b1f090b0a0306 77
    0x442c851041c0000214452a8903c22620140d02000d030160070524524018668805014103594100e44100c241d07450f1881c3c41f0380141011103000b000b494001441c10180900051040110f0305160754203c101505c0c0c4040c000d680c0102c041c00015083c051000c540040d00441c007540d4403032003910460b4249550b500e0061100c020101099010400143e024084002140166400d40c00c2c107541c007600900d010348410000c81b1303075a110100c240e80c0210301242080b45a800c24a1040000002591a1511030001c0500898280301c1c2d00700c1e5140e510000030b02d03248002c00c04802d154006001c1d0070b26a840406604143d0301c8600100d04555070342c0368000e0705a80500304202c6480c002c4c1c2c110741d01c03454a41c100389840182c1d9006500f0203600c20281c0461400c130074040764000701c404018000b0130a01c0e44010b030316001080d04402c00080201088160059002024041145c00391643e2205501c1d00b00b08070711000c4cd044404001039020102c1841a015150000d0f40103250141a60209035030f00d032078500 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 178874478 1250 178873228 178873259
    0xd0b180a080a0306080f0705102102090a0608040302031e090303030f0601081e1f03020901090504110f0102190318090914030415080603031e070b1b07080f04 69
    0x7504660045041d090080c1d241c441c0e50040c0400000804500d0b00140c2d20340c0e5624514072440f0b101c1c0040710800c3c2e00c094410401c0f001f80c03a034081c031491081c00702c06081c01c000c0e410288056009900c0c0220000c0d59511894000c1d0007035405030051860500c0103044079150280c0a20200c003a401c04008108181d1001c0005511030b004d80c40d0340300000e0800000042c0003c201804015181d002d400008502400f21110b494010000165026411051070300e20400d550b1a0751029512a00e0040001404802a0882d07449903200b5141c020407140018204440e03424480aa6070060340880030710707113204603211140c40d5854000d040c20100c00c1d84030302040344810101c1e00000f58250701e074502d41c000c0144c984602502e0200200c06907040c2801c11038030714000410a400c00c002c00900304045040741e2024000c0750881410b02c1c00c00700725510804018103aa507c0500b00726a00c0010305c0018400440c0c1d15400403003802c40c0f0003a28580300403900d41410f1500f0180c2420b044c0301c4108000516991481e5502 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 178875728 1250 178874478 178874483
    0x1104030605100b0c0604050d050a020d08060a050307030503071b0e010b0721030606090b0705060f07050c03030403050715050c0301050d060f0c211e38100207050d0b180a 74
    0x4040500c1c6c80e250185c1841021000001404001d001130142142c0100d03c0d105090040c0c50550750f180c1e07500d030000740350034415440380383c00d4018030b540401440710110040815a02440080301c141d10707541c1440c0d44507a4144524490380710340900611403c0009401001014060b0401c440d9821803903d008018100301e0140a005c40d94800c420401d580e0456044d8008000b121882410712801d0b88401d62241001000b484100f400301000500c174a00030010f450401220904482d00d91619160142c00781d408030005440e4a40c41ca900140205014060148215600c005090940e403910f800c0c441181186071044441a4a804410800408600c10050564803913694540700f030140380b22103980c8140f0410403400b400c0c10602003000746105040003c0c001d196208002403111018845c0000e48034004002c000300300190a0600003911220100f0f2242d071804441c04084880f1600b010390b0303118107511806420010300d045400c04101e0040c1102d03400a0b0441c0c0a0b400c200301c10b0415424081401001c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 178876978 1250 178875728 178875733
    0x10215090304050f040b060405040c050708040f090b030102090a03110f060c0c0f030f060705030402010309060c03060602010f020711060d060e130c050108010503150910020a02010605131104030605100b0c 89
    0x8220f50b151108041000403425501080190322000100302c01d0f00c1980203040c000c58a51085482c4544548100c401c0f56030016441919140c80b00c210700d42d81ca00784c0c4959079229003080102021403406100300c8105038002030104001758656552580d10b4201c04d50300c20390205200808104030b48a0100401c0340c600340201501c0401c82c071400300001c03510f0a081c0d50380268040340d480703000b4190009003c2d4000c03601c0d0425a13140c0d540d07880100d015203c0d031a4020100c1d42812410103007240c0580204003503501c00e4000b48143e82c01d120b200c2041303004d41000584040b0f0500d0303545a15007000300080002d8071001c400800d0072500d03a800502c1889003030fa00c1c40c0c008080640b00c44140100901c6040c00b500e400d18080100354541000642d5031000422121100041d5101250741400100401d5980c4e1301041415034132884450300c00307402401d85104060245400c02c00661282e605445000c1100c001483e2031030909045d621104010301005001781c2c4d04c3c1004605c003080a4904002400300248085d00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 178878228 1250 178876978 178876987
    0xa030203030a050c072f0604033504090b040f05090303010f0f0303140a090302040c11060108011116030507020901090506120a050606010518150a1704030509040b0102150903 76
    0x612004483c0010701994500c00180304440000344e03800c00002e050041082c2d100b2010140110810366094011a0b45174040c80001d000020048503400031024080b0344805810794900c0101181381d442d682050713020007441e040105100455603980451442d035009030002440c0905148003000316402036800210b81d52020004000c42c09100074400c0c003802400e02000c040710318582d4040e00d410580d00c64803407007540203e082801284102c001200654000b002404000307a0032a024010410582c122241e5028480021070700c2d4005003d2080c1c0c0040046c100c51401d250038a90540650b600c050031002c0040800c94800981d0f546242540030b4182030000080e02d0802404021629104100c0190709401c902610320200c0c0e00071031020b0b400402070800503502d044003100c80e102c812076810307403c0d4051410040501484040e10240100c41103c2c3c50340c40f0720002c4030409182d95142150000c0c001081008a2446400c19070270040511006004a600e640c140341019443e03840c0c00c442d0070b02294000304 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 178879478 1250 178878228 178878241
    0x303010f090605010804060209010309050a12030b010914060c0708070b0a0f0e0108041b120605090606014413050607091217070816020301060f151409030a03020303 72
    0x180698010039620070100111071070040060017800d001000a0b21090340481c551031141d00941104031003580c0711094410004052a00060290303044581c100081d1512103518040c5d4060700c80c64040d154081144c0d003003020300d0010409103601180ca1044180241180003c1070202000503601400e042103045880c1d10070444010401c800c0070307e0250030040605192010b690704101407030341054100e48070355003d9a45e000c00d120b03108c8032a07014000d030701100d581810134010641d104902940070002a204551112801120000701410301941101c4140140030001c600b41c0c1d401700c1c601010510141b180c40070f5a03961170b007a080c00b19180b40309920480d441d0000c00005002c42c5130b0007003180c201b0610303c40c1041480701d9901e00480e40104507007100030b000b500e200300c01d4007030b1685154400803059a0b4003461070f1410041560040403030096007002c0700400e80000001c216000d4602015508503d02000c800440ba00025840140b089040c2080071030f026031014000c550486009400856890070000d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 178880728 1250 178879478 178879499
    0x110f06070e040504111002031c0203010f09051b03040c150e15030c1c02070b180601080a02010e0405132319020109051e06030103140f0604030e010f050f0408030301 72
    0x94a07007031181e4940303070400001443c400240342003914283c2d5103034076600102200360700c0e5103d000c101a07481c0c070000c03610341100d42c180c1d0005c605851013034a8414078145d0f90b03503054041c3d48080e140d03d007016011b40200b80b402c0c482c00b006103a20038080c07400e1a0780340341e407205070348280b00380c4501107000a020310404501e10b04000e523076000a10340490100e45580b40906200314580901341c1c25049001c10711101104001041d0103882140390080e030300013541d06000d0001d9901110340d41100c04140100303000045e902601080204000c1d4068541c8078020303580c90100401004002c0007001b032402c500f1081340119128a051340100d02a603141c00c400034510f410802e1400e0103407151221030010b5220500d0050360b01800510440314260740070340801e5070750b281141d6448000091150041004000001848809050307050a40042c10682d09684079801400e0f8646000b22400340110f040a0903541180d44180701c90581e805440c54a541041007400b4803c60591140d40040d500e54000f20040c041d04500 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 178881978 1250 178880728 178880747
    0x30b0d060e0d080609060105130305030d0b010f03090206030105220507050c0f0106050f061321290f150d0c0f0602030309060411010c08070501050109050c090d020d03110f0607 77
    0x1681015041413030030300b0001d6514000184014104480030800707000c820041e241c4507003d15407000c2030f08d840b0050a070740c80d0024403151307880a001618134500048014000c0c803c103442c0d25000380c0400d1540e03081c1402c0c8514403100641d02e02c003281d9036581c2c1c0c1c408041c0350700c1841d00409240e40c9041c3d840310b5103c2180d1522804240d42d4000b039142000400142da556402740e18060400c5d5400c0d41c60780030b18030f80d540d4110060740c4038154034480d006480b07861580703c440308040544140c81d03100c8001030112081d1458944980004240b240020104810218003215180c0c40b802070000f110851000030080342c24030301909412200b00c8404d070401d0003000d810750b4038200544000e200039811840d150400c15940e040142001d44109064000c0c601140d00c18090b410f02160030800566440c0309510340302d07009000912680b183d192400000c1034900d40c840c0102d0b880310301e0080c4001c0303607007405808102001c1d80840c82101400680c4441410601040c8410806c1200c40070141c151840c1c01030000d4841c014 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 178883228 1250 178881978 178882003
    0x10e060a0f03110c060f060301140405060402130c081f08151005030a0b04060207050c1807080601080106020706031505150a0905041122080334050d0f030b0d060e 71
    0x3010300805264513000070340c030f590024013041c00417180e07111080868010144100301000584003001000117200b80001e91074010b81c0309030703002d2050304001e240230404c58020040c9100012080d4010807444d02d80401c0e005084040c000d18922402e0303503642094501070706515103041c4c4d81c42450800403042e201007041d0f0003d00040c1c000d001d80c0c3c109c966510410800c0200020b10040d804500c0c0800e0020401400e450120040d00314400c0600c40f140310740030000111070000010301c0820003d07107c0c1d441000729a0480d046500204a01070401c213080d0040d040d500b001c10418004410002042c0d6180703240c490200e00d003900384030b940c0d0b076900d4002030800d505a023106004504000b503e405800005040b076042014440c00320410b05003008111000c11903541c802c254901c40494401c2c03071018034412480109002c0f130260420f000e011040c02d81c030044101005001d07504103644801c0b060380108655480603c3d50300c0d0006540292800040100b001e071201910300035078468400c140c03000100b100f440b240c0d2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 178884478 1250 178883228 178883261
    0x80604020303030c070c0504020409050f0604090804060f12020a0302091504030f0b06030c120f010b010e0d06180f03030501260a0213090b1609060815040209010e060a0f03 75
    0x140035008a65248400380c656000c0a000241000a00c14049103031070181c0402481503588030703900c6140002400d0243c401403d2000c2480116106180511a2120f101c2d400781105081c00d1400b401980c41d400000c58003800c0c0140c030402c3c8072816503284018895030003280c600503141c01c148028272a80134690803144100700070030013003400800d21400c01400c103141d2011f03c2d5225651041c0c0840d003400b042d291010f800440d011143c011014000c00c44092000f041d10003007051407032250044030705602c2c080445402400d200f002101065941e0803203072004010491101550300c2e160b8548250410000301030340000c0c2e9660040c0320741281040320240c4122400e40703004222041790011a1a0710070034000911416950240c1c0c149180785400c86248507401a907100c0040c0b4102104401003a00e80b202c001c00035066004c0414001d000d22480740c055116a1481038907008030000713000003540034210b440c0c1440346404008050340e0341c4400030310740001107585407040c1d99400d25010b010750303803040880d00800 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 178885728 1250 178884478 178884481
    0x506010e090d08130804090c12050a0204050607080a03060f0e2205030a0e1302070501020c060708040b31061a0102030a2703120f02160311091b0c010c090806 69
    0xb55001c211036030012601040025201c210f40b0300401e1902c69940a240c900d400c140700c0c4901503802800314440344818080034803140d940e52000d43c00728071490152643c450f1040c809200400c25020141100f846141400503180340c80d050302c03000c40911544040740801e855400c1000c22100465100004001c0c14001660210b5642c0c440b03071a070107101855010003c07680032210403980d603007034860b00b2003c5003801155100b00754100325002c0d51004404801a11032000458041c0b40300d81d5520b445940c2102c080a0140c8800e071400005600611030308501c9012229100c0410480039500c01000744151400603441602c800c0d15400781d03c40b503454506642080c4a082c22203074000c2c645c0d203e41d0034030003d09117001290701040304a8440c40c0d00050166041e40742c80c54800c2d038104101e803010704541d8085808142c81e040e442241d04660303000041507421001c0c0d99800074103040d801d450b044107030446a0740050800107000a00f0390010b031403418081c1e4440c500784441d6a045040706c405446042c005d00002e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 178886978 1250 178885728 178885753
    0x705010e07050d060507032417070302011b061e0605010201050603120a1b1209180204080c060702030f010c091a03040c121a040515090c0a060509010203040e040506010e09 75
    0x14800390078001d480ca545640000b06c3c0c10b803080c3d0001200300600b51042500b83d0700300040009105140c000e5036200c5560030004080c0340300008031042100d030305035160b0312100c03840c01905c00c2d850468682199060313107803003000304c0d25541400c200c00300c0e101c400c0001968910307000009007540c0001d04054001d03001600c443c03000c100340740c04541020105040607140b04112040d10002e07646510b20190040c0c21405100e4005548048290304032416402c44900780310660b03100700c04034031076841404241c0d44420694580c0d82896000380a0007030000b41a2030540784c0020f035103400e40d40900700b0800080c1d641241408140c48100042c0107111000c5055800d61070243c1e214403d8094a014030081c00003011b03140010040f035141600d5010aa0750088481402d01d403038203e82d03554030310030650003038080c2a000450000c000107140030700003401090002310301d150103415a1941c3c061480c140c1103000402c008139040483e4410180501c1c8650014903596240040c3c4500e0504040c2a0f0720302e51b084010b04101 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 178888228 1250 178886978 178886989
    0x31707050307020c090709030b01081c1b06201b060a09030503150d02101706150904050c0408030f0403140f07030308091c030504020a0e060a0e06041107080705010e0705 74
    0x60b1080e05c1c2c84c4806d071242030707054174062410b82c0300511030074a84002103002e50000c01d00c1c0d850020940b01c8002e07819580c1000360740e21888042002c03e0b80c200c120b6000d0100d0b03100d8008140c0300c3c0d2040107228404030404200d83d00c0c1c0d4003568245880e0a80c0010010300400c003008030036031140b03554104000780b59850390001d100348006030240c8030500005501c0714695482900c1429190f9006191145584020704007074051030300708015020401480300043d82c0d90400b164604010380b4150b80c607514141c0580d0811004243c054110502660140404280c02004100802007196074801c1162100c0c91403400c00f1000160071020301c4aa040281440c2d45618005040710550f1f602d81020100381d91260307052850010303544c1041c07031000c50a1074607100d0507425038447c501940c005d480c10764030a921000e80d070001c0d400a940aa8204141c200c04210900240c002180c1000c4d00500c04150ba0340c064103040180d400c545803d80340800000380384800c01c03100b40302e040d008032150401f0744a820b1030000010f0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 178889478 1250 178888228 178888243
    0x50a090504050a1113081903050d18121d0612011208090306010f06110a0507120f023c030613030e0301051005131116031205010303170705030702 64
    0xa0041c2e480d4008610100159046100b81c400c02c00203003904d4200080c01418003581c54465034000340500031406034259481030301305181c0354041c0c079107910f00491105207000401c0d145280e2104110002d40010001d4181c071811174203600160783e4000c0a0320a00505403d09803201c100c0703442041c0800001d008540e03e03076500b9044442c4a03100c0321009129082c111030398030400c51780590602407040080b60700b804003d100300941d40799035078444110703c802010564441c2c030b512015010394480340e000c00c1040101118000c419200e481c0400965001e513001c035502040350740030300070000740c1d00d5502070144154400c44500c80c540140201030a030f03c9880841d4951102801d80d164115400300c41c2c0051500402203005400d401600800591500c03081103c01c0709680c0c09007500c10036070301107000003c00c050b0248030180718243d4001c0b403030225880c0c8400b1400c0d150340012401c0c8134034044000c5d0b814140d8402d96008600944559130350028110b5011760301503000301144e062100034800c0c00016540040c911 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 178890728 1250 178889478 178889489
    0xe0105160602220906090608030306010903060b01050408030309100b0316090b040b03100b030c0409020108270706020604020406060f020a0f02030c030a080921060f041a010603021207050a09 83
    0x607540c004001c00d07030300544004101900000d5003c0c0f000103000c851030388000221507104108010f219203a5011645a20050394101d0000351046401d10200b482c03a4001c404e41030050600c0ca2a082c0d40b80c00d0141140c00c21114540541c115041d1940d2440140c0680c41c42004124085d20400004080e4400501024081e0129460ba512a2031100ea04c035940500c20410004044800d0040480340c20b8008d4001c45d55014041d00448113613110720b0902d40144480180d050311211490f590320f0402d50030080c3c1d80e00c242400130482c0c0840b014214414850240a841140d0248c030361440c01d070040c0010350f6181d40c028000c0014442605080c82d42c04941e440446078407401009104810b400042d10b81225600b409605025901881d010451044001c0c14540020f8a107069000084101407014161030041541d032600f10b000001c000c0c10003c1c0d00950b00c140b040c80b44c00c030141860300c040c43d84003d00741c11890100f0341c00103015807540105000c031544025503182180c0f41441c10f04000341041c440d407048 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 178891978 1250 178890728 178890731
    0x60c021204090e010f1404060b0105031b0304020301020d09200117060d02010c020a1203030605030c0102060f0a1b0c03081018020f0f160c060206331206070e01051606 73
    0x40301484001e401c00c2c402d4007114a0184002e8580041b2605c03001c90544084915516204220308194080c40903248120080b0781041e00001242c0c5a00c041c0d13500042040381c1c15582001030780320701115441040001c0740075030004100a81800b02005040301c000e08018140300c4144080207540081e421615403101c000d40710150300401d83d02c0184c07105084100020344c005c84003500455003290581d007501e1414042d03070301071112595440c185a01c80500707900b15030060704200c0000c1d10180802c051315130821104c1000150035201404030f10f001d641c0c0304486000040c2c00d41041810300d9444042c0c9508521403091049000d03251400340c00500f07401640c40741d01c0380d0700402d03200e000306600c1c81030707626100600c114203989012594407564541150034045917102c0d50640042846880069018402e4480c211040c050b212007035030300342030000e020100080c03115800d829244a40c0f10300c542a0340c0300036880c004220904150318050b1454100154041c1000414040300c141c83e60701d100e40b000c1094000c0230 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 178893228 1250 178891978 178891991
    0x170c030103020f130c02010f0f0b0603070e01050c0d05032401090302011407080d0501050301140f0402010c0f080c010f0501060e090c030405210a0e060315090601051c09060c02120409 80
    0x45140c4d29100782d0780842c0b80385030409000360b1075010341181c088240403460801c86010402640b0040760ba007c621240c01c61000c2c0001070303455000707100c3c0902d141d60504002c0d08000300782d000d6a103800000c3c444000010801300603c0400c40030400c1b03024407040e0506100944507400b200082c6a40741e44e1001030b0402800410f0705000518140458842070f1b000b4080d01c0e91a0311780811203001e040c007131283d075000f0761a1144001034070a02401c0345000d01d00c0700c64070f204a41c0319600112a8580c1406044c0d401460b920384000c0058414001002c9a603140c00010034003101903000d1001302c4105078403c4060000080d0f2203103182d942c410200380c2c070010140c0f000d40c07079441e5810031510744004c0120103901c0e04142c042983c8404020307400380504800342d648407204100e059080c03150f00d0006892806404030b06240c1c00c074892410141e03041e440b00d010304d8804d05103180d1802110079486048032840000740d40d80030b18014484140500c54902c0d0721400207020592841c408840350348078610908080907555034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 178894478 1250 178893228 178893259
    0x3040b04170c06010f0806090d120b100807031409070302220903020703061b120c0c02090109090204050112080901050307020a050d08090d030603150e03070f0f03170c03010302 77
    0x1d03801030031244000c007907840b5550661000da40b50001e0003100b02c0d150107120002144240024840c0c40394030544060614848407240580380c03c0081600010b00548030ba07840d80003515100c184079403c09a6a440c0501810826806021101c91003100314207180b15108000d142c2c440040c0304001c880e41030300da01804400d1065044012945481500714180c1010b035100207166001410340f09032030155000f000b044c04500c0c101d4150110820114011507107004000500d03483c6527104031055011400c1060000300298001203110030b09030000390071190f4900c001c1096090a2140c240584142d4a48807488500384e12280c4650042a00342c2d8100240000002c050b58402e00030703181e03516800000c543c000121900044c140020031070303c41106214240c00305210501c00c0c0211802c803130700aa0400c1c2c0b581c28504505010300200c1d80c3e007034070b5032004010101c0000c1104400d8450903000b0b17850340954861a140041126540c04030740c4174115000018080403442c5041200d0440c0d40c125018240e10ba0801c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 178895728 1250 178894478 178894493
    0x220f110306100e060307031d0f120309011b02030c0c03340e04060f0b1c0201050f0408030408030403030e06460e09011710050601090302060a0509041103010b03040b04 73
    0x81d43c0d074540148020092009054140d0007101c0b4114440c007907a24842078041c01d2641c0c0e41003800345281c0c00d90241c6035101000d690301c002143c100c89882c00205105000c0903400302c603040c00130000d80041e400016003460080c03040c8169241410110043d00d09081c1041440301e124081c90503800d07044919001116480640c60008001408152211919490141400b0b001000021041550242000445031051628080740e234a080ca400783c0e000d4400940350011209a0001003482491010401011034405020000b501c010826440103540d15410f41c07400a24100c0411101c2e801550280041c000095240e9103080c000d03031007020805130121040c800c41604040520200c00d0755800c044901308034039488210800a00c1043d030b00000a641e9170200e0840c814403a458440c100e400401c00341d80705080c1e030b8110580010b01454101070070742d102e03000640c0c0c03580b00b4001c3d603012560000b1203503c1070406001c1c0c0b4007885807914040d42550b140441c0b200d00380c40014002000340300c8420000d01005000c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 178896978 1250 178895728 178895747
    0x30f010908040e180a050303071206030210180f031b090b0303030a0c020114011707170309040e12040602030301080106121e02010c080d2003040807020907090302220f11030610 77
    0x5100817509034030b2850400c0354880d4001c1d10041c000607002d100000001076140503400449602030884a1000c1044a003241d40c8550400202d091280c040f0300000e18900e403180c4a0003031409086204041e602c4042c9039002c880459014080031030402d07010140c01c4e600481501e0780000d58400104080515803001ca00418222030400300c098132580c0049a011210821000404040000caa00507512071100070980c0c25000618042503004000561a506141c0c104000001081040343c40004481400300b0345a0440d07003060700160305c080010410040240a840001c0c90900f41c1300c441d122003901c84103084180203c1215201e04024800011a449a5912a21035402c4209036444a41000400000e402c024016085a0402c003007890a80311209044034021076201080500e001c01540c00d01002e080000e0244092110612000015032240750641c1541c110b954140c20303022141c906030104480070034004039a44e518001041c100d03114040102d03900311404681c50000382d00e03251411151100b0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 178898228 1250 178896978 178897021
    0xb0405271002030a09050d030506090a0207020409020307030b160c02010807080c09030a0c06020d05271809100501060f080106030b03010e07080706080f040f080d11070c05030f010908040e 82
    0x8008104011300140303a200205d194415400c1e50200303030b0345d208101d0943d08190b075031070740c03204907040403588070121503006001c154409003011400c15280d400080c10191715a2080d6007203e0072504020300113801030720700c404442c01c509000a807012180c0008000f000d000309000280b045000104070a0307150003080c0d0308600c100a00703c418841c05894014018601c0c1e200b41405449658101c2124a01a200b601e01b05580780c41441481c10f003003d2000b1450b01c01c1400c2d103400000c580c1d02e118200004040141c03040c0075680003070142d0907240d80c400b0200c40c2d0580c803010800c0682e0750810002c66012189604541551070003055010700c10380042d0043c5140c420b8201584a100b00c00184900041907810856003da191203a0343d548054142d40c14070012200200280080d84040340052910303400740c100c0c01104600002c0c454203902c400005680412400c1d00c4140181c18100aa450208114050010880024800c441c03035991180207030301403402500c0111f83c0487c0001c3c4c0c4083d0010b20b00e0846030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 178899478 1250 178898228 178898231
    0x9050907120c122702130e060c0315040209030c120f0a0f150606020a140c12060a060819061a030303010605130501050f030103060924020d0b04052710 66
    0x420700c0b80007030038144599000703210b81070415039205031264840d4007100c1e005400130140b43c3d1221496080081c0b503800c180d505040395941d01d5411203001010001e0600c06d1140680442d5a403c201014501125501d09a2403103030b801000340f2201074034003081c0102401000e4818503001104004040e01b00300324000c0e42c1c4c0c01803194510070010300c0340200d5140d0f0344500803484940d0b0880501c01260541c1c041e13004034800f5034000e0410b0710000d80720070400c41042c0900401e442c1340f03130103010000340c558800d4200c4031456440903041c420b50710840e1007003000400c280c2005182d50300f100007401c0003194841c00c003c0c100aa80b45190f4840e40161090042a000014182ca42ea90b86030f60740540507800c41d04460020b8400340002203280d5004404644036200e00f8038165045a195543c0c0304007810248000329215043d05410784085a20080c410b000c8030b0844c000580c5407662041d005040310394071041c5520071401c080a0002c45824110103c0102c9540c10009000c070056240c1300e440c180030054981c01c1c45 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 178900728 1250 178899478 178899491
    0x71406040b07260f07020103060509010e0103022710080d020a030e0f0312030403021c02070b0f030903070609050106080d21020919030303090b130302071403010b030f06011e03030905090712 83
    0x3610913000500300d05200b62002c01502d6161001c1c05528002400341940300c2c07030904014800743c5015071018405121158903c41e000031280c0e51203c0e08101620b40040582a09000b484115014003421110710f980d8402003406801c00e0728000c008003040c9080c2401002d044a02e41c105490074050510880348a50340950380e401c052030f000b56200d490807014031440841013000303084d09101040c50000c03a0103108100703041c4003080c007c0d4030745a4000f814500a922007040f0000c00079281e4010b030030b2818020800028124603003d40541070180e828040c00170130047c12190144162500920720b910882d182005880f80000b40225020380004070600e005080031070400400c25616400460ba594810b0800c00210385580e624040b500d010800d00030007580019109221443c882880010b005400030f001161491400c404207061100c5040090016005140140880e45400c607040d016000f10003203c043c40347ca540c0340101101d45a00496229802c8480413417891845401d21801c0c2580c03071b49082052 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 178901978 1250 178900728 178900747
    0x1120b030105100305060f01080a0b0604091407081204050303040e0a14011503060b0a05070b06060405130204170f03070308041a09150f0105010c150207060608071406040b0726 77
    0xc00c0b00f9202c00c4915104a00025092204e8045044d0407206020001d144401e4955188100201c0040c101d5030000d603035035280b5003c5180382800300c810310a20310280c1400390601c41e01d41e040c6098003c5030b0f0072241d01004108400d071000811502201d10040903a15113403036039030044010b00126091501d00d82d40c40d00003c030b03400d50400044c0e414038010361000c204844c0e584911203554091406481c01184040c0180d002003002e4440c8141d11441c0100414603044d20b83c0e00003101808019280411540d0100d81484020307200c0269100307071805000100b40e8104e0204c0070710390302d104d400002420442105c000c0350820040d1030300f4070100400071202c440c41e031504101507035448141007985001d0a0039200841d18040d582c0c4003a41c140d0342d040e0748004580000d515141030308042c20710380d1f818240d1308200d144041400740c4504000b800607140506901460219040d1384040c80c00fa48610440701040300708200d050725412a0f059035440000700e41c880d01124820410060140000c6c00542c20000c0ca6a06 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 178903228 1250 178901978 178902001
    0xa051e0708190801050108060f24180906060415050d06171504110621040b180f1005041e08090a12020603070309020a081207030906020609060601120b030105 69
    0x1c11100700c40d098584110014003c54a030302c4288a40c5000ca1340c01d0002c1440c5040c091240d0302c0ca105c01815800f1382229810403464130300c030b0084504500001c0031810424010010384074044102c000c17335100c1b0881c14403c0003e845072196214440d10410f6480c100c1039603038041d5058070401c4080348810032600d9a1650703284c0c8603c54020f9400b2540c066001701c4008241c0b00000e17180110b421814000ad401d10000c02d0000c42c0d880403a0450200c503d0142403520011050200c0d0300c00c604c9020024120b09002140009520051000c0d0000d031708181a428101080040c0c483c0003001c0d1454013040e1510b032400c01240b60009107254441903410440344605121307403900109102c060a0701c0a4a109a440200d554100005d001c001e50120f810400325003181d1086d0040340400d800145100d09440c0d80c0e41d02a45803040364201207108040c041203a03000e01d90400140001049240080e08061606107940c0ea200c00e00180203905201d802e011440d100074855120755440316000d0300800c60340c20000b19602 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 178904478 1250 178903228 178903237
    0x3060609060918030f040906121205090d0f0f0309082802010e180f0a02040609050402130b0301080d030c030204121202010204180203010807050307030c0b1602090a150e07050a051e0708 81
    0x9081802c141c0b000528034409d40001b850039401c002c0440c050141041d04a4081c0c0c003c00000f980400d42803c4103020a0800d000a0103240c03285075044a0100c052901400007070780c075403200f0030325000b2010100301c1d151002140c6681d540703070000e00d2861860510041c1c40784800171004030780049201500c0310b85800000d0b0ba1078003c01101c440d1074080d944040400301644120700a501c00140c24440400503421300e40c02600406000d0301c6103007441a11010202281e4001740e00158041d88100b052400c8140c040c0301d008030a10707240c90103507e4030f410407c8000b044070f2281e41c010300324120519840b150a1007035042d03501030541c0d05042c1070380c0f02801419002a420070301942115015101001860b0b1800180c00000c80f9032006c01a40118034151814442d03030450f0b00c01200145040d04c8010042ea1906242e5104201c031607000100c221400c40b015181c180160851503524502d2003e20691503001019200200094544151794055030088801da000c0d01802094480d100441c1002c104502e040160 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 178905728 1250 178904478 178904489
    0xd0207060f0f0b0f010923310b0a0311040905061501090506210a02070f0c0e151c1b0e01030b070801060516030516060609060503060609060918030f04 66
    0x51107005400400c0103500740c54029618040303003080c0001c00401103261001110307043d803690b03903131f0003444e184010901d104a902c0e20203065201300007405000e020200c0404030881680e80e010880701d64240040340071081980805010050528a107801d02d80d030f0b6410480010b80d101e4165825818414101003541e00300b40e100d503011540300785001c20a402c0820a60340c8240c4c103d921250794410142008000240180065101c20340811544000c502094190703448180304021000600307160100684a01c00040e000042c0070b1030450b104802d40d52078000c410481e034029806034528900790b240c03010301d070038200d01c00c0c408841c03a80d0310000d01c5803804640c0354105e03405441d982019907252241290703460f100b4000c00001c54001d008002c991560f0641411400d8406d003081403501d12014100c0c00c4020101c0d00803208507496000501a140f42c0303001d17180041005030000c1c80e0300d081c1440010071900c0c00808041c041d041520018070311500c804840e031404082441940d5448041c0740846100d50b101e070043c03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 178906978 1250 178905728 178905731
    0x1a1e060d1a1614092101140a0c020a0c05010e010306090501091d0706080c03191505040b040207020a230603090f0705010c02010f030c030b03030c0c100c030909020d0207060f0f 77
    0xb88940315001c2e025440c01c0300f000c2d8400700d281801050400c00c40b40b000e2030242044264014603100011801d104607800c108541141c80d0380d5141402509081d51403c035400c0c4115000482401c0004100f041041c041d80d00034205000d48100b8000105e00502856103c0c030182d908060000906154a6000022044440802c0342d4140b403649000c66443c0058410400058500d00005824662050186800080315600500c00200b504c0201007034502c0c8400800003500244020404c82c03820303105100d00b403a0b00795025400c1c91160b8001580740c030603034410700c1c1e80c000501240a51103d003101c88010000c40040401d0b07201d0405c003a0865550303103111205109403040d031501060640c022418003000e540c1c141c0d2001c00840803890101c01900c1e0a041a005140c1c441c0c0c40181c1c640c1d0140050080c00500ba001401200d41e950100148881c03400d1202d01071200c604a14000b107075009036540e00342c514484025039960744070302926001703104003600904034525046030155028242e03080300c804813052910 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 178908228 1250 178906978 178907011
    0x322080d0e0c06040e0402030c121b010507060614131b120605030115090f0203040803010603021804180b0f060609060f0d090305071101030b06180d0b040803041a1e060d1a 75
    0xe000105030110450080341c0c1c4051a2f007d0a001492040c80840e04180361903400c00c5150354400313082c0d94241c2c01543c010694181180c02c0ca00300100030300044044004148554880700c0680d440e405016250311007000352901010f140410306070059802844007030003c11038015020110b002a1400d40501100d05040980d203480c0c015242c02501e02490304500350615507440c1141c194001d60100311700380071050300201864096078461050403d01d1164080548418141c2e15104111240007040038411840e0002844002d44840b0b003a10900744007a603840d5990440e1000103112805a010109449402d084500040650100142290900ca04c00501005407620015000d95a080100c80d80080c070900c91000c14111035087c080c001c0c03001409034024002580c56050301070b20126425a44218000240410028010b40d14040c404211041c541a03003072048080405020804101d2070255011000c95403031f0f915103095990490780b1a105d0802c008060716054043c0a0468181911078143c28 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 178909478 1250 178908228 178908253
    0x50606012303060d02180703020c0f0303040b040b09030708161101030b0904030e1207032109080624030a0f02010807140405090a0605060f0322080d0e0c06040e040203 73
    0x125240c42a2041040050840c0d807140700f4001c454031350801c1a03070320900345104914030889990413a4000e8680b6500560b844114400036480c003403500c0142c1000d58400c0041102140078452020340082d807001d5404107540b180187c0501e50301605802405075a00055001030503100e00e4500c0f0b01091141c00302d00722032411000150200c0764154006a044603002c00001e000903c140721382c0c0700e10032004101c2006c3c440491005450808590011261310000e040c68940d00c1051100e51045817106103014000309051100d450b4403044042c0c003101040c000d4101d240a003140a91810401032400341c01c0f640450450f0070442c440e4203c00364240d0200e80c14001140340c2c18480d02e0421034003802a0090380c60146040280078034074800030010030030250f490701d010172541d44140c0242444113154a640ea205d04001176410003010807003490a568011030804040000d400d00d0554090303d192000000700c2805856815007081c90040c0829407103640042d010074040071010f01c060180c0d00a4003103845c06c00c05030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 178910728 1250 178909478 178909517
    0x5010f050a030b1b1c02030f0a06051003020f09041a150901050f0c010f020307080a06051c06180b0709180905150a090204110304030e030a0b07140702090405060601 72
    0x601000e4050110720f00024110380704035884d0040304078020700c800c0ca0081c403444c5544845201846004465030004144016160084417041d0040004101000414900000108000304c0c01d80050140f540110300741011261200a0760009100a0014001c0000c1c0c14000c030380314514500e4480c818220101b0243c8148031640a5500c4c0701c02c180c41c1c140c40c140022a9400980d0005400010b2f5903480d462410304214040c00614018000c94503080013074280080b0120903030343d817070708880e0003521142ca1803d00102d070300e01d0a5040700d4000c50002504610311540b84c01a4040b80005410000cc40c03080c0100241c0c080c98840440741c0f164494000d900c100002d80d42595544540038080707501081130802504602d40c0e01d541c03c064003110028000c000c130741c04601502d80d2000c1322111345a01008100038190040f03850503200108801914008465681d242603031000030701101d08000303100b0382485203e140c080c00c4030341e5640c00800442e0343c1e01e46450040c1e1ba40f0000c0320500c1c00105030350460003070f00c21030303 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 178911978 1250 178910728 178910749
    0xc0f0813060207110415260313090903140309070b07080c0109080a030b0f0d02040c020708010c0f1205100b03060102070e09030703031121190c0806040b0a030b1602010213080105010f05 81
    0x1050214160076147e86c4140c100c00a9680301d59445d0302042040900b107000d0f692603007000708084070011a0060640c10050301701501003480060110b03040081180100b000324081043da42d1008082d92501c1c05800d10402c60302802403501c2e1745618016088041c0011a0054050010561382c18410030007010184a0404042c541350740c0c12800100d2081c0c0185003940100d03060402c640304480c3c0840d50740e064542514600c2a07030f003000c515a14240d0300140e0788a402c0108503901803c050040e4103001c0c480d0048810301d8400c040041e440030000c80d910342c0c800c0c0910300003083c0300e0741c4490941c00c145000e00c0c0ca90f0301142088010920b4080260340400140c000e0341c940714401e00c202218800303190284000048014440d00f481400702c40c400140060030f1040c0d07050424581d40355919858003405100841e5000800315100b500019800c000081841600e260f2020740110300a80d10380d550301051340603010b0980c28280c0507040b07100c04540071105500182c103e440b032440035409140c0e504188000070750b2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 178913228 1250 178911978 178911989
    0x603010903080c030603010b091005090c0301060c2411130806040203190507030209040311010509010204050d080c0102040b0c030a080a051312090b1c0f0c0f0813060207110415 77
    0x40d4040050481180c0f603000d16030020010740081048401940003840e90901190f4004850392503a4050015090202109510105a02d20686194103181d07003c0d0610801800003080300c100c001441d16004c2481c1c40079840703482a540113000505160b06901141d030860151640c015450860010b404000001c00c140580d4014001e0504419940e9601001d40f10180c0f00f0f803080d00c9014000001a2500503810388564007907a01c2d810780324602800d4600b03645019101007010707801408140300d540d540c3c05901d0410303940030411580c0c44a608041034064080c550208a640030013040307500d000c9802100400e0580013641e40d480569807071003060400c5550035038044509001c401d1071140000e00c02480385400006906002c07003002c0d80c46180030002d034001565180c03414088114003040605500030300d803088141000a001074049090001d28120800340704004110110001c146059008c0c03200d45070403a003040e020742d03075050035040001d25075070745010040c040d52605040640103544005400d06652 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 178914478 1250 178913228 178913237
    0x305040303050309070b0423240d06050d0501140c0304030504090525120c090e0705092d0108061e0f01120518070b07031715030307030c0b0603010903 66
    0x2800c50700c0c1280c442c1c10007080b09155108200000c030304030500801a0006001c0038003a5040b8403513008150710303030042c0c01070942e01800c51042c0d020419079010009040130030010080310f451f56180d22910f00544503a51105410500c3c1c04d81c210300380501074012a283c0c02000f02490040d44070480078003000d2000b11405800210b0500050001100c540c0025803c00050001d0a43c00492030b070181207103512407400540403070108004400329a009014000b00e00300c83d4103198000302d141c40031100c101030004054100b04940040d054a19699014815000b1a4031806103d04666031a242c0b2000040d03000c1004c3c003040b4150000744051a02c40610079444003240100303950305281109000210011188544c1440340314010041005030034814180300c0c04803280000d400030b000c411454104282e5070403154080904000c0303000465048242d02001c8512044c0301440d9030754410a0070314007101d501c2103d80c580030010b200e07000d045e0321481d0703902154000c103188441038840070700709400c030382e541c410080114 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 178915728 1250 178914478 178914487
    0xf030f030c0f0415030608070609050609061e120a110a120c2105042108011a1314030111040810092a060f09030218250c021201090305 59
    0x1000301d00d0190000781800b0002d2030400391940038000c0703071040c495034110020395107080400407541c041003120018012810025140d41c141804154a80b051152290242d000001c443d001c064400300000050110f50320341e03a4980342c03000140b002060059480409950408840c6d040d03154002003110481c0501d9210708003030150490f4901c0203800b140c44c180090056240ca031100c0501c81c0c03004641610020741001600d0703c1c180c40c0c40200380d0315401200d5410800c4244c0c4056854200c090f1038195051846500c2c040444c0480c8482640300314207001403a50000c510001d402e83c101d40c80c80d140da05048009101d01a86104800800c0c0103510420605501010070060204069400701142c103009034075000f940d031084801c4040c80040700c070769008441286841000181c2e40b0000000f002c203c3c0340b41c610f8109240d40c0000d400c01050403002d541005909010600b120300411061110781c0004485111023200c0c3c60002d4014440310b10f05034010000440d008904c0382041c801e10138004d03895180c06040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 178916978 1250 178915728 178915741
    0x934090c03110310030204060905010605070b0a0908070605010918080a0e190b0a02060109050f06040b0103020904051f060801032a030c0f05210d0302030a1503050f0f030f03 76
    0x150010041040c24595030303a03030460030442008015071054601c80c0004101c20710710300c180011607070207038000342c4441d2500740140486903110084400081d0412040700a030707101c0304050002032241501c0109011000503c9404014154204130f04858281e441089102002c503840c01300f500250600503d00002046080d000500820205504203400361180150303028000c092025000c050f04110a290b40119050300215810002e4074090003500c6828007560030718409040705e0f0a00504038502c980e44408550001c1d0344a40d050390b8050740d008009020b1414021080002c90100d03c443c11045182807030042107c900450000d4122640100e05c2c58030407040080c002103094201036030302d274240c0b0413007000030101e046200181c1c042c2111014000c58607290001f00200d0103804c00364803480a90003200742c1107418000c03501001400346810050303666600d0f0000034004103004200007244501401000c014414001030101100c3d240c0d0089502c039001d489140c968074003608105101c07030304041001526 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 178918228 1250 178916978 178916981
    0xb0906030604021003200301090905010b15191202070f120c051011070209040c0801060f05030c0904030519030e0f070e010303050a182411030904020918093409 70
    0x3000e00741c00c01503580c01c1041010011847e4000c0e407000300c130552610f038940b05002082c843c6090080c405c075112031815074211400c0005000d03410121196025000040e00c03564042c00300c00008401c0d40c80f0031551103603030f8600307040f4404490009640840000c525980801d02640c012504507420500030220141c1500030f0308090010301c1e0b0141b080d4203061000c10016102c03200d00d103015038410059540454101071600382101c1c6079901400e0b480318600350400150b00c0200d147e4007c0da00580e01400c0c6a6500d00f019030b150302c034070401080c121036180c2c000c1807040c0c0d056002c2844114510180c1d00d1142d80a02e28079a42c220354021040d4440c400401000001e003c0c40c000c3c08160003a0500007405645241c140c2c00c40f1080d9407154643d0201c1c008036459404e0020180c030b440c0e00c1242040306013040c2030008942e0701d01030703000c1d440c3c022940024040c0c466a610405480c480c0030800e441043d034a0544816502c81d0041030b05045c0ca00c4802c000d1403100a292810000b0715007503244083d0b01c03039203001c40010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 178919478 1250 178918228 178918241
    0x1413030f020d051609230c0c010902060a0e24090d050f03070f0311070e16032a120c0e01270b03061801080303040f03021603060b0906030604021003 65
    0x268000381e400580340000743c06004a80c1c41400c3c441d408540c1510342940c2d00e080e00c0380490f25a142012504110020410360184960404c4102500c191a20750003400240101011600650700a402140b204401d50340103c280e01b06200546074441d540740c60398a03c011480a0190720500c155041c00002c050b820f10162020b4028090400c852802c5540b21800307003540e000000503038900031005400000d042e0002c805c3c4030480c0c00000207001c1c0505d02407003500703091300260034100130307120900000507070314030a400c40d150226003505042040c942441c0008481e0f16841c2120001c1191320a98a0907103000384170b200007105542e110019048042d100448000a11444c1c2034000140402c0c1981d0007011050181c0c042c0c20301590315603680c00c0c41d030204181c05240100d83c1d0104429803006011311350000c8141c03500541e01500b9004602200d01c4c0c243c0c20480301052107108071003600750010030300085410480260800351000744003038403a00145a16114200c50182d0009540902541d1941c841d03403240 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 178920728 1250 178919478 178919483
    0x4030209130c03050703020a060c0b06040e15010f090b03120a120216050c130603050c0d020103110c060a06050402040303020a111507110306061807050a05090406030501020a1413030f 80
    0x2450400344079a034100e90350405410980703017a4070521052045080c070318100d9014101030700b0580032080c402e80d50040001c4009155034040c035210108140d0f042c404101403021040805107512040da10707034149240d01090351203842d80190501c00819202d06000c2460159031000c501b01915100401324280c8003200401c1580c1a19a07080144030b41c05a0036402c0881c0451161001e4884401d07000200540404101800488286400b104000042d00003c0d03801c0505000c0c2e1f80040d00c84000c0c0010380041c881041a0342e50b000c1c0c000f80c809007800c80071800da07100d5481c00702c041240d59212401d1004034011400001c000d07910240912010402411078914160002480080322155040041c00070307401180b401c0f500c400003825881910301d0148590341e40004103031241008840089040010744401620900030b014000801e8400c4c42d10460445503920310180081c02016a01e10b001d6000354003d500c0e00c40002e001c8468801003550310000c0329800709a044401d50442d040d038540d4406e522a00008 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 178921978 1250 178920728 178920751
    0x9020a081012030c08300f07030e0c040e01091a0708010b07031d0a080f0a03083601090f0803090d1707050c0a0b041103070803040506070f02010e090a0c140f04030209 73
    0xe0302141c501886c4000b2140310002c12019403800e080421041c00c210291100c014581450400100341a000468010303801040700d011428001b01643c2c1401000501c0028040b02c0c200d68030368115440d445203943c05103807103581d1621280e03601e564410050088000090015055070050290030058040c180f102c8035004105001482e038445011345003860a40f004003e64024011440034141c0203921654402d400c40040140008148090507200c0c0340030003c0322040551480c44d0801600940c00a02c0882d0b00c50309040310b80320242000041030b0401c449607142441404c0c0c0106210303106840007070007004400c0c80c1c034140c0d440d5580c09441641041d81296101e1007041e07200400300706810b912a00a5008000320070360410a64241810b02815405c0b244040e0b0080000300a10b859800c101c51038540c0240d00c0301424403041c401286d682214025140d44601000b051080c200c03804d50041030321030320544a400800c0d1608200e03492900807001702c3c030007010060000b0030150422510380d56202c2c424015 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 178923228 1250 178921978 178922017
    0x1e0c1305091504060b010f0306240908160e0a09020904080912010f02040602010b0904030e0103051008032a0f0a0f05030906030703020a080c070b04020409050709020a081012030c08 79
    0x82c0c106140040b00c0503111a0f0f01d0700d00020f50b9503000302c0c1000d0106d0070381c03034240861800d01e9103180c01e1064254546400c540c01c1c031450a140e500c05d11052011f05010000d030303882c2e803078221111440503c860080a42259030b58010490a1009210f03140259901404403907a81c0d40d103455026190308416000354108240000144c40700100380700e030702c5010304103007001a103075403c4c600000d085070504c0482500a0381030308140f2011a4201c4001c8070030174002d207000300e590b80d500803030007521144503400800036200220f100007240140c1c510165000180c8400711543d0310740b2100d150782e42c0c0f9804082c034550340c000503440d03404502d0008644c403100340100c00310f0b4905004400030401c05c0e4401c64518001075400b0990020300c66004c0c5420382c121440c015690300305240ca0306c400000400c06440203102d103541e00c0418080100520405c0e0040240d0301046442e4800681c01600c0c20b0070441d043e010035503032180c0215103c01d81440598510b80c1560350200c020740940d072007254542c0020004109494080c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 178924478 1250 178923228 178923253
    0x60f090f07120c05010201050405150c2119060f0501110a02030a290c0a0509010e04050114130e031606150603020c15010b09150f0c1e0c130509 63
    0x4840c00074600102000100c80940c03d00315036005141c0c102c0d07030440e410042480042100019501e12858603121580c24030b80395000c03086400c1c0300b03038104003040c1c0c0d01c02e0321001100e440c0b0048035032040702003142182d10000118481003c40d082c1d4055176121a405000034042548203105550896076102c00300c8680900a400191810710321003400c40d68501d07110780c82140401060401180d1030300500d241c07507050404102d40c1c0610701400c10703c1400c021000c2040300690703225034040940081d02030310811482d40c6030311071a0560f450700e840b0303d030160404d01122048544180b08140000342d401005d1400d24011010320300700e018892034180c9000b0340300e903004e1403100e400c10348540041170903840c016075944001400c1410f049948c0f11072010a8852030040110250748412120741d6030f0226a090f000d803c0b090b480c2d02441c040c080900290a40118400852080c00070b620904401c142e43c4800c02d844182e42c100d070b5105100b440c00360300005001c0000c0f1301150550003040e00440c1c00e206403401445442d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 178925728 1250 178924478 178924483
    0x70206040306090f03020f0319050304030c060608010203060321030112022205060109050d05120c01060e152b3c350a05040b07030915030e060f090f 65
    0x4000780d944d0311141c9100010907404026440c401c000c18800782d0304054011040d1040550408900001d0000c008006030401d44503002c1081d0305c5602c82c004000c45900d40444600075041140c1a034007078411048841c4020344217149a02c40510b003290240c0c135581c02d100041d0010700d00c1c41e100700e8002410300c07d80030380650351000b01e1449088a210000c0c4928155000405240071a0700107030041c1c0d9180d12501c00300b2008100310441c2080e08048a0340c030780d003410490380100781035880f00f00803121070420300411610000c03d00075600740c08c585201d00341c201070b000c03601459441d440440c200800306008400149003070041d90761083c0140d030a140c0b10b590701075490030391180100007042442910035401c400c1100d4010600d00301d025031242c0250300544084284107081a0702000c0941d040081003500815200303030b01300d4025080d0070f41103944078181e52074090041e050134090302525040788040d940c060340c0300784607501c0245100801840203031100051454600005004803407580503000740d120f45041d04 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 178926978 1250 178925728 178925741
    0x1009020621041109010506090405040c1203090e07030b0307060309020d0f0303050f2505160203150906010504050709050609010909051006090b03060d02150706060b22060f05070206040306 82
    0x1c2000204580c682407400c1c412405000c01c160348119100401032080703407522400c0d40c070041401d5400103243d80380c9091080e042640c1e948204010310300d041d988000c040d804003504049400c007030b03122030319600c030755105500395103c011000c2d4041c1d102a40801040f8800c0d0081c140450000c0d100c068075400075124045180c91450058010075100d80c10321031919401054140d101413520107403600c5810050220124085207100c03103040000c04988100c882c05010180844a1350050032600c03440d10b0584e0501f0000003c03100c0d00d2031f0f806104000113241c2800c3c024244249090390f98086110f0a11041103c260050002c560400c4443d40e0040f4078000c05100c0c003401547c80c0c00301200708034074204000f450946103400c203041c048014002d2282d581c4503041ea29403e95812556100c00c4440d44520108501988102030070560500c0d4002611400c03403401050443c451002c900c200c6004072007038800c002e15501c1183d0015181c00542403c43d845140074280c4180300070542e03403030a592906e81c4002d82c0c10 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 178928228 1250 178926978 178927027
    0x706060e1501260612010f02040e0f010e01080a0204021b2a010c020f09070c08030f0703050c0a0c03030f02040801060801023105010c06090b09160f030510090206 71
    0x46a080703144142d82c200c002e0500c01d04491903240303078020701c5141100000b03074098440e5024041c1500101c280410a401c69400d070f210300700c401c545482c3e5980b081004603e01362030b4125a601c04034000b0400219404be5a41a10b0400c0028464441c590f400d000c000c1d805580b6880c110149070381e108415010a01c9a5004403880604444203804020100111210301c5084079050144003400d15006848030380c1000c41d0300074101e4004055907600c1c0c000342d88880e800400101041ca0010801814904036150b16000d50b0850b5002c000035621510b0701451403240588a00c0483c5a180246000900c241c010b00980c41c0500700141c00d1a40d900907540c2951003a4110001c41d075004600345500301900150a4003101061544444440d1800d544484850441c01540e0401c41d40003080402e10041d9040481d000c1d42c0480480304600d0040b500359101c0f451490800c11881c0003060000d0008403a4040d1029070360040087c040440f880c1c40090300410008000b00c3c0c0083d018085484520001c020800d8403d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 178929478 1250 178928228 178928251
    0x8060f0319020405100f14010c020d06060f0905010602060402040911030f03070615050d0605090c12010203070809010c121814030a0f140702040213050604060903020306180604080706060e 82
    0x2500b44104002d883c0e0003003102200d503240d5034080200918074000b04084955810280500e254000b0040f01d40641103200a508406a2140b9070100069644000c00703e075010540002103075150502402501e00038410480141e00c200e02140140c40c00f60302c4440c8882c0301c0ca841810000301a00401d0130440e0001a00e401070f040404d2006c240003045c01183c0025607803900307442408d428030002500001c1204000b518040d43c400003c0c1c1c081300104110485128018604c040a05462125a010794411145480041c020001080008605015500040c0c61545420301c0c080300d07075080d40b4010301d0342d0017100241080403082000460001e65858480e4072111019560341d07208110042c0c00300800d03580407010440340011a038491112001500c0c480307a412940541e4401c0140800250305105802290b400100010700141c10740d000802003048903c26010b90b0b2107651030004c58078455045000e0400e66070030000004000411b000300074000319120301d8000503c3c0b0b407202d00305090030004940c00c55082 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 178930728 1250 178929478 178929523
    0x61303020a0b0c07051f0f021203040c08300901021903030b1905030d03020c0c100305060301060909050604030818010204090518030724020c1002090109230108060f03 73
    0x60105000c46400f0700703401d96814200034194212141b60080e0b00a125042001d070601c410b220034428844003000201c4000f606847e4205814600a00c007058403407042c8911910074010046011a0340000c4040744002c0c0d506c0312a1001c4007991000e61241040da0b0440c0501c8140b400b0745070440c540b100c0102e0180c0d43c00600e09130780005014084510410501100c5907041c003c03c420764001820310618622072801586a0044c20307842071612400940642e0300c844001850580d00d540740c5c0c46288104d070114002d12100342c1d82e440c81c02c2221441c031800381c00b64018a00250100b40103c0c441c1e90040c1100807003a4a03640080942ca08a13017054015a2207642c80b80184804040c0c100da4880c1d808440c100a1854240690380e000311700c2d13507140701e00e003020703421710041c00803482036030b4159104032001a050300c203903100c1b4090803002036201d85440c03070109044500118144101362800100000c254600c0700309615408015550910700903ca9030348150003010081c890780b03040c02585140b01c021403c4541a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 178931978 1250 178930728 178930747
    0x807020f010504030809130b10081b0f12040c1d10050906011d0f0a080705120115060c0606090c050705011b020a0305070507030c0f090e0703030806061303020a0b 71
    0xd0449918159041000620041c0f0106420504a481180e8100c5440d101e001d081c9403088054140300391050f600080540b8484c107519080a151407044100b0b04203888181c584d0f0048214038015000c094146440520241d006004204142c5030441d02070411681060341c0c608103c58505048010310716641111002c1c4001004202c0d40140075000481b001d408a14005000074850200c1d51044d2240d00c00d1081c01844a49403800d140562aa014240021458039032100329580c013481d1103420300419140c0c11803a03a0240c10310034040741d030851050042c0c04902d4014100d41e41d1030020300039207025540d03010000b4501c6140c82008140745131912001c0d158034107814201d0031200c668010800003040302403040c140c1d69000c40c2841405615050551b100c0c402410321a18201154000030043d41101d0700100c0c81412030800101241c1d0001030a01c84940a40c601944420300c505c40140031924402c0854070b03614040000c6d00800d444215000d000e9a40d90b000180c600c0721740c0e40901f80c40e40300016207004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 178933228 1250 178931978 178931989
    0x635030304140d050405010c020d02040b040c0215060316030b0a0209030102070b070f0c0b01050103020a0c0506010303021518100e010b220e0714190306060609050901060809060106120f09080702 85
    0x4007004c0c00c015041600d0000043c261604400c030086c8180e4594400404650715035216500300c142c00b07801049034a0b0b80f600b01075640c0c11100c101850030000b00c800160303d8680081c1c6806100000c185007107071a4a0340d5991688580060805015941c0900540c551514244040d004041c042c0320040200c0c1003240000d040900302c0c2051504010501030381c0380120300c0d40c0701c41c5811038400b0310b00142e468030f00c1c02c1d04079000c0c450307400e0061060103000b0000050550008075410703800c1d841040003942d0703151001a05000ca1010914080540000c8098041d000c0e05901c14550307580f80d03070000700d9101c0d0340c0000141c0b09072000920300302c0d20f8a18442e04103580e00d00d2080309408214800140015402c0441200c0800900a0064800c80e120400c00300c40c45010080200255800041400119100c0c2c4000d0003011450080601a50990b03000007400c6100d4803845000340d42c02d0025003056428100308440340c44c0310701981d80040381c850000c060000e809100c6e11203054040c80d01c035078031405103104200 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 178934478 1250 178933228 178933243
    0x141e011b080d0e0a0c0314030d0e03071e120e010e030d0306080c0d083004030201020d050f160807020f0f010e010f020705030d0e010f0c03021903063503030414 70
    0x103a15501c443c100c0400290059100303010f8903040100000075007c0410701d946940329034140034424034104116820001800000303001154420081c10b0004003d1005402c00032041b1500500030391040b041070440345001748550b1100d51818501040ca440c1d808022074540b48414000c640000da50b030504200c8140c0500c07948000b83c00c21214a040102c864890020fa80601045c002d10055200710243ca000c64021a4030305070b030103041c411900d070b140904001e4000c3d00456085c502d002d0621000131582c0124803a114441c0c2d1011440900811405030200c482100040842095219000800700781c400100700310034059044800218a216510f0441420b4505e1200038440d100e0040c84000d00017040401079454060b2101ca0014040340e2035010140503180395080000c0e510302d044141001aa03064004102c0c01035400c0103143e030a00b0220085040320715502c10a003400482c11040d00c0705a0b0700180080071040c07258204002103c9201041d419a801511300b100c2d5001803040f02042d0000038880ba5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 178935728 1250 178934478 178934501
    0xd0e060402031e030706020306030a1202060a0b0628020a05010f0b0316060503010e040f0f1a0624091216060f02010501050105030a020d020c120405030106141e011b080d 74
    0x640540c3c2c0c03800085580b40101c003001801141c0110014645840800c03215001c560440b0803004040c0d00e0041c00788d180c00d402d503461018282803010b09036280c10700c0380c1101c0c58501d103500e205252201c064510051100e1300f10510085000301d141d4000411024064a4481d13030500c20300140d400c02c1c403020188bc0821901d0001601c0115030800c211041d04042503a044880240030760b0b00d42e0ba95860b05940e1200800002440c0f6080b81e038480c410f1241d403182e00c00003030740346940000e995101c54081009240180c00a601107512610020a05807020380252001050150003a80710b02030f00301c5c2c120b0405100041b900ca031440056001c2100f107501c61007181e114030081c0020841541003d0000b0213620000341408821600004c0f00e49010b401903046907030144044050b03428a142200403408154010300c0340c0c0e4400c0d0309060b00402c03003014a4652580811004020700140c00700c600300c1801c004a1038019034140180841c200c038034131003643d0f80441d000d0b1044000580c0e039030178000c0700c20440e185807024 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 178936978 1250 178935728 178935763
    0x902030a1b083f0d0e0606090105030f071a0f0708072a050d140312060102010f060602030706230a0b100813020910090606111009020a090b060d0e06040203 68
    0x34084100035002c6403000c40000ca410f0480030407810740d2280d810303200d50398003401d07820310704402e0010000e00490b503030b40258022144402641d0341c0da010075648404901490f909078100d40c1c010800c0f0058030340800555030b0011042c500f05000d074030080c009030700166000c0c0c80100c070026808003002021041012800403486c02405007100b14143d55100c00c005020300d5000342601c8842c5400d010a510094000e401550101c0b0350b100004000b03240c910500360354142c00b56080c00e640006a107803e006404c10740d05190b004504210042d2074003005840341e00c40f541c0b41301c90780d27000c10b005290303c0d40d141c1c1d03110741c5500d1000701c0c1500d032503003e0002035020328200c03000b00514001445134a0120055401c40c05804423000300040e25104d001002103661548a480c18600d4180002061034100114040000c810030940310061034440300e078000e440709050001d50041070340c402404880540d901140c1000c0303001c1c200301c2c20400300901d1001260b01c0400d90414560014080000f1442c042000020740b040040d403 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 178938228 1250 178936978 178937023
    0x708010f050903070311030f04030f020111030c210918100909030c0f060b091005011805095b06050f0d090b0406060f08010207020a090902030a1b08 65
    0x140161207003d130a400030b0030800f030981e000c040d091003042500c01e00c0c40b400c4200ca6071940d0340e1030924002c2c0d07444181240400c5070001f80c285106804015110f0340008200544032400340c0d03011100f0001d0803440c040c54000750034002080306440b410340d074508540d0046054240c43c00d041c031912070782d0481136010074070903418268603400081d48141d80215051b4803214188143c01a440c1c168054124071003a40c0d0029481c8080058544075502c2e404211182a00e5182b0080c00e101d45c6148400c52500480340c00c9004da40c00706050078a00002d0700d020341c16492407070342d440750b030329102d280d0007029804070031841c1344002c1d9501c603444404000c1040d0502c001c0c46104000d40780000103030980c021100150410f0101081780034210060b5005558056405100308030709141900d40301006000c0d0380201001c2000c12640803554540501c00c9a0070290000d03d80302c0d140340381502540c09010290022a00741c018040c0c2000007030b101e240b501e2051201001c5c04445030703040c40030980c5000c85154011455240815 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 178939478 1250 178938228 178938241
    0x1081603030c1211060406021c1404030806031002030709090c0305040b040602030a15081501060f050405090a060510020f0d230306121501080d080c1b0709020a020708010f05 76
    0x80700c4a4480e8040384000100c0000c1c1c03c00d456400c1032024240d49806440b0400c401c02146a0007002070b10303850b0011941c6400d00542200480c4e0743c0031140d103032030540ca4012502103400f4541e465804a0000e0486240c03118203009c400598000703803040780100b100201c00340b00c1052140181404204681382c10485c42c41e040e102d21901d040045c00260000ba030010100b03c44100320340150314048154882c1140740b55a8076100c598503c0c0302c3e000340103205040b00020800501c1059065503907002c80da9800e003058200030030400200c0000d020298500d50382c41002940d80c40c0c860300c81032114800d402400c4e2801c2c2c2d0324401814800001140802c00411900804000f010140e500003a8406254003e40b00d03070f152401305104a100c601948018841d600092400d101b00301d483c00e0607511003400b91001c4c051290800c0d202c1c240f003036841c021420018020340405080c4020040d4803502403804441c0c0e03144d41d401e000400c036481011600d0044c2c00116090000750024045c0d60a003080c4000c0400041c608078 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 178940728 1250 178939478 178939487
    0x120903082418040605010b0403020312030c130b0c070608090d031a0406030b01090f0504030e01050a021e0102070512030c091504030b0f0114030f1905120a05030108160303 75
    0x206000035120088000d01910410070415580310040a050014410425041c0b203511240450b8212552410400007144082145060f00d040f02e50190040c00c0039042a40c1200c0c1c1600004c1c032421400c2d0007440355414201400e0f1b8201c0013042e0103850550f594182001050074200039070000024030806505000d640600006c034089460f000307180008200c3d407540c240c94044590000080d6100342400b8000c418052200f0740241200d03660a001c0000030031103000c04003603440c1114041c0201c7c82c140d05000d8070f5405000100040c0c0c070304c1c1c8141c616100202c501c1d01c0c41c501104004c0b490302da42c040b5801e0104402004400e00710502103a58905600c2c0c9403030598118801c11103200e00503880c58284000c85040f230402e0b100038644c00041d401892030005141c0c001050f00f44110001307400300c1065070300d6906001c56984051382c5100060241440c441d006180501801e8000f142c0c944503c1c007101081500300005801c1d01c8141741d440c2581c07035151a01451419484880d0300c4618542c0590800009401 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 178941978 1250 178940728 178940731
    0x80f010b0f0714060105120105090d050903150f1603090c0504020a120608010f0c0c020109230324010515030403120f1a0316080303010909020303090a060f12090308 72
    0x200109592024041e04141007402094801000c1c00c4005414240308040841c802e816584151140c2c0300200401340b00c00e0036a0015241c3d4942a000040364401d480e201e000281050741010341151142401c00b10f800e04d4500302120494241201201405000c0c94540444251100309144c01c0c004040140c0f16500d040f441c0784034051045600103040080750340118041030490b900e00c1400c0055980e15880d250290850b0611081c2e10b602d4241515000b074011040d9208071501a910500c0b00343c20252103626a04e00c644820440e0724001524a0b0707640e404003c0c01d83c08012020000740c0b400035041400c2034185043c1c20140c0b0071403029842207a00307081c401c01c1c0c030760042e098900201d02034800204030004140c00008560364030309001c180049143d02e041c100315042000d40481d1400340404003404030215007401510240d030010401041000219044801c2e06c500080c2560700e407050000006010484c0e9078441070214000c0e2481c5000036411615950110224a100388258a42e070f0394001c0a0f03110 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 178943228 1250 178941978 178941989
    0xb060c1209030118300e13150b070c060305010302180a060b04030303150605160303020f09090f07020f010902090f070c05010e210408120a0509040204090608010b01080f01 75
    0x101203180c081d01d40e403d4004468640a078030070080c201d020b5081200c031490b148000d4140c02c212596410f288038110388a00c400400c640c3c1d42c1c44c1d83c0407203414100130302c503443d0014007080381d84c4458080140c2c003c01c00180d8000c0919030500d030780d0386101e4900360303e546069a201e01e0625150000400158442a0944004a02000202c070403540c81813080b00003000c40d5007000c100c80c0c0020902104150301540080703400494401c90107180c980c1c403441194640318024001600084400d1a040000e00a40290405c400b00c0310b051810b01c00242c000c14040e03203045800d1038040120340140403141d0340500100800c1611200248800c20064022071224100900b1064010401600060003184101c01c02c01300725a22400900c01240d9a468450b030710002c3d003410220ba004802484202001c418040f030f4100c842c014042d200c00030040c08058166008200e0003002c2c4801001600ea55a40b240300030805003030321040000d083ca0621640c0c3d030840d0194120541403100c01c0062010b040640511b4904540 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 178944478 1250 178943228 178943263
    0x80601030b040614010e3411010f0c0905010801060207140909010b100207050f06190305070507080d0903080606030402090f0702010f090b0f0903120a020327010507030b060c 76
    0xc0342c518084008252200c1c9505207810040000b055801d015076036903001f1303801141c4100c0d03460546c8148180301202e0340003241c0308000681e0041505401001d60341401d0018100000754010000201c200b80c502404082c0002000741006220301e41c0c10084860141c50300d84028202141010000d100c50100c58050f54800c031500030028a80740402d400c404482e4002400700c801000748024041d40d00e03081c074002e8038032407044d00b13041c0c4400d400c0020030f5803507034030440d5100d0028810000096004207000b07032000302008810042d1101081d0040c0041080d110300140008518006041c010301c0c0360000703400c1500c202010024040541e0310084542d400800319100702100b502c80a074141d0061071000e40c481503a50030140d580d024440d056017034500c940c045140e54000c80c1d49421240d6201c4c1304c0c00600d0313510001c004010034000780c0350f50301440e40420003825041c0390310f05000b0105001c00c40d800200c03e10760346030400c01c030341554507003d03a050b0702000780e82140c1410600c10405d82ca94400b0f141040000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 178945728 1250 178944478 178944481
    0x20f0d05180604080312220b16030603053702010e0108070302160501090c08030a1b020a030c092009030c04050a0b0405101a04030b01060507050114090f16080601030b 73
    0xd0b551242160f006181d04801c80c0e607905c801c00e010002d00d55049440101c814002c80c0414119480d08003071001565100b48240304983d40d08a4491103500c070088001c080668641c4e01000058017002103001c10140e003002460b0080c40288002510080300c18040d01c5031008803c2c120050b60000d051040001e001d0800464692b200b0030101d00a0064504050386028089064024800194070401e11540141c03190240c0c0350320391408981d00d1007555070b02c5000a00686440d0340c1000340c00d4140d403c5a1004085c0702c025980d98944800038941a004060741a54965400c81c54400d40312031452406038240102d800c2200b1500000e8403404100302e618080e40d11180040c0d0608410341c002e0285c4200203104220b64242028000c4a84410b030080c00c01030f0301c0181030130800a407060280c40450364020865006a802d00c00c08480d1034001da901100c1544d01d47c50102811b0303040c0801e070362003084104014100740c0184c28080c2d01c0c14003000204115505038440c1888444404a100c40c1034075000781010085 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 178946978 1250 178945728 178945777
    0x60f080a020c1c0c02010e0f060912070b0d021902072409030f24050c03150d062906030906012601020705010501050a14030a0b060d0501060312020f0d05 67
    0x42640d002e01d044040c41c403c10032032840d00c0d00301518488a50003030380c424101c0e0b0814010301001409003001c4a9001c5400e02407900940380c8012244150107950301650861070340e81e0204495070704244480c038040c540206d18403610000340091480c00301014402072000910700b20002c0005890540c2c480b10416194000288090080081c04015607006030b0032840129103081c00144048400101c103034800c12224030020400303407809224016030f05100054903586880246404204c200700c425030b0445540c100c1400402d03000e101c0c800d14100a1018049011401d0038200c504400c042d00300b40c0304086c140144007180e440040c515066460261521190300752002e04484080c0c0c0e0018400301d04e60001888008100043d08004c0c120380d426241e9100998481c0802499440c08c800c00d1038045e4003000008000c50702862403607800050141058003441041d4a41c1d6003900c0d0303ea00b065441c842800f0302d1010196040100340b4410464401400d500045c041d401800c920035072a14022014803414030200 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 178948228 1250 178946978 178946983
    0x6060d0204150e1e01060f090b0a03110c010b03070512100b0312031801050705070807030807030f06030602041508010312050d021c0b0406050f01140313020d1506060f080a020c 77
    0xb80c04042450f02607480d280041400a00c003038010340001d8a510000002c40a019403d0ba4140d400c1e83d44800d141c4038140080a01c183c0c0120340400300b015112000e401d89a12401c004103048400c07600042034804001d800e05241160f56440709004920b005e4002070511408103841e000ca016074203011601d104010002441c0c00300c1e0850a1407001c6002040c80501d04200c2086c9100f04001402405185e91f0754805030780358041d00c0d2015000910402040001920501001d9070045c8142000221040c41004845c2118000c2d0021500150b0004040c050051114140a5040414030b00040c442d8150303510480d61a00300c00d43c40c800c1c0000401c1e84aa044801e8041d19001518062030000d05040c4000860140c040d445046000d01d28200c4042080d09200000c1d00c03800c10180c507005c9041120f5000c000c0c807644020413400c05c00092031071036401640c92020a05c101c90044407011414882c103403c4500f2609164010f006000a444038914070a0700044902d9219105000060b00e0f984041c0b0401e0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 178949478 1250 178948228 178948271
    0x70b0405060f0c0a1a090c06030f010b2a1b040207080405011103160c030209090a050d0c03020a0605040627020f040f020702030f0607030c05040b160201020a05030a0e040b0306060d0204 81
    0x300215885c40b44031104020280320b0610841a0320100c9000c03a8456003400b03030340d08c010b554960f184032451005021150012004009200ca1104900c00808200440c0c0551300e03800c1480c5451600b02c080503200b498a443c044520206040300c08510300755003a0340d5020a8411442003e0600482c0104007004480510035034260a00d40104902c60710881d1605c5001454030f07000407489012103e011401c2c110300081c0c1045001e90010040070703240c0c40224190350341c103d486021000c52040307214070720016905000c0e05014520032100070440030854074804502407d034000b000d0310859801100c4000d40d4401424910505003902d00142c0b00d1304440c0c680340644030b48030019405128114800ca4102000502248501880d40c1e0801401c101020110303114804d501ca4440041c0040c46000c006024900703280701c200c1e20500490701c80070080e50300c1c40d0958101c80a114003207007031582d1442d41810301d40121043e6500880103003415140c1030000908070071090340044d01865403001d0300da022401c0b407994078 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 178950728 1250 178949478 178949483
    0x311070e13021207090614040c020a050c09060a0f090b01030e0a080a140d020c0a1407140f01170a02131a0a030504020402091203072006030109020a18090c02070b0405060f0c0a 77
    0x18008161074a40f1903040c42a0fa03209075001e00c1c54400305268540c400700304072808bc0e500c10064160111507a0030070094010152030749900564400001680400082100006107014100443c5403014040050110340d0f1105140045810000d48400060403440498603580010f04082051300d00040c40d01c08240582254007100510019013801c0c001c400040d02840e40340b054401c80c002c144140780198803482c0303510440c494010304880704020340c54240903219010310189000100c80b03800c02d18403010301030251241a6141d600081c403e10540c10314608002808080c803c1e1003201c0c01d940c01c82ca4041c801c030285002003560f40c00106045540380c0c5c04607149410014001d6200c01908842035440f40e000c203804a41c035915012401804102c4148001403c20000f01040d00b0760f0700c2c02c01c00d0400b07540300301264004c1000c450b80c40141180d100c0980c1000c1c0100800c0002d611b800d0302c1020349041c00300d800111258100340805c00c055075401c1c08640e001048146401e803140211345c1280c0c500300341c10000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 178951978 1250 178950728 178950731
    0x90321070e12010f060512030406110f012c030f030f0a06051314090607050a080903130f26072303010f05040b0f1302010c021207030311070e1302120709 67
    0x412220b5801500138008a10b003000080115039520350030021203851030b50540400e0b8100f07100070010346000f2400c58110750003c0c41a12910070280060303d00b1541c100e07013408a0510140030704618448800d105618040501005500d4540d02002c0c40d61140401420945041c80d40c00004098070390a80003100108030107411160b4102040800901600140d030808030380070f40d0300001401511000601900412103600d4080c076007400000d045452000042c020035907484204504254203c070722122200401440c1c074951821070404805500103444c04141c514405c0d400680304908910100d102c004445a0700001c00c1c1201001004e104c4e640c4220000c103500d5440d018000040710080c2d00070381d02c03540c4a9200c00074255a462041c0a101c801555184458440011010300550184000782c410380c2c00101001c400b1100c04d81102e180800e250030460014410908070105010f01b084007030091320300d041a490700b41c6082030041802f445c10000180c4646071451880381845414000c1401a000c0d0000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 178953228 1250 178951978 178951999
    0x9080c010608030406020f150c130b0c010b040c0e1e010c0c0e040309050102240a0e06090a022b170f0c160509060f040c05040510080f090321070e 64
    0xb07074035100e030007901c036850141c054a02d0305221045c010030308061a020a030302c440300300d4840c00440780b15500860003641408034991000b242c283c6a60000d0700210304440c001080b5811650b091205450009603102c0522800c0d40f815602940d0307444401c90700040401e1601c050302c1c0c0480048801e030098490142c580e505042011032800c41c8030220031320407070090300c50007645036482d001280c0c0ca20b8107004901050714070f00d014030920b01c0c030486165008514240d0200d4060700c4000e0076410a1400c0da07601742181e01c4034000508604010090441c00d6400c10b010144014140ca4a0a10031521100045c0b0452100a021507014540801e5034031018903107a10743c0d100c008800c40d8135a68043d0201c1720390040580e406c000742614207840018400c3c140074103c0e035500005881030001a00300d1085600a2100612002c102922410b002042d85080755581d4000703801c0013200400c5041000d40528141c5d00100001d01401c03200780440c281c00190400c04080c159109a0119000c2c640000e54a52081c1d0103038 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 178954478 1250 178953228 178953239
    0x9050109030b1810022703030310060e0d060f0209010908010c141312080c011b050901180b030705071707080a08070306030b0a02030103030219030e0f0d1e0c09020a08060409080c0106 80
    0x1c0c001d1106e444014a0903003600b030300303008141d038070b0004541e4090341b0070060b90240030180c458102c180f03114002501504a41d100741d0307510700c00d51306030604079000c903503011400c0c150300d41c1c1c880c9184000303107400c0c002000441c1d0390b42001408000120410301c0090400034030001211105c603101001451105003103240409180f8001c2d00c1507118a80e01c24941d800e1145038545820741c105901c10341c00c81515590300c3c1103500c00054078403042005503034000001fa508005210700064000b180710380c405a03a541c0d6508610316002c6044c54644482c52500380c410b000f90800038000310101d600e29210f5040500303075a668940210050103480c0c00007040b112500040c058541c640340c024505036031098003507581d001c0d001104581c24200264028000409035411408541403001c5880c400c080060100d038103480845c1c0b04c01d412001d0014074041e00d01c0301e040900d01404205c46954003e041c1080d0158030f01f494074000102440000303003c5500c0b5070399070508041002100021210b00050740c10003400520391300c4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 178955728 1250 178954478 178954507
    0x150c0203071d15010c020d150e010510060e0904020f0604180b0a05030f0a1202071710060e151c0b040f03090503030a090e0c270109050109030b181002 66
    0x19a81040c00380708030804540d00320f514418000351180d0607903944000c211036408208504001003c03c5c0e580f2100070380008911440c0b8040c010010302d4100010400e424000348105c0d180d050359001d40100301c0c6400821055544041c081a04107804880612040741d01c00e00080035417145074851128454100100030460580c0e402ca00c1c00d01e1000c5510001c10b5076580b050507100c2a0340c090490790707600a201d41d040010001040c0c003080c406c0504c1166181c0361141c8081c6200b0108480141c040d5100040447c1c8a00b41c902a40707025254a045d074020300e041482c2d210440075590355140c0d11030084070030303c00c0701003000d03010402100e0b0700000400312900f8282890440c3c0c542d04002500000d00e40c240c045810b050000456080e0521551016021440c0054140d81c2c900080c1c01c943e06240100030300303140c10301c0d0118403485e0030454410a0304010a20000540203001e583d0002d4107201040d402003010170070904520f54030251030250f9403047e81901e000a402c05c054940c3d031041c486d202003085051140321 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 178956834 1106 178955728 178955759
    0x3071b0602130602030318010e120a020a02090703051b030c070f0f0c06020708010b01020c1005160605090d080c0705060402010c08121e0a06060207150c020307 70
    0x40d0b810218400c81260b00c8500140d00c04010f0145900c10900402c4511400714002c000d84403003640e10a403205110b6034403e000c0070f404900c601040e030081c0600d1103c10740c0140f10180600e031040c005402040c0070b40d2004150f1a082a00806040d000e4044a010b00e1001501a091004c02e80d241a0410480c1074101c0305030b10f422060b400010700c4108001c0c040c00c241d80140500d282015081400c50f100500b0a0741154828030503002c103502d80390702e201c0250b0481d10340256180c2505038070000591b513500740201303507030b1411081149000010400c00600702c87c03a81c0d4511943c8600ba0f005170540100f007400341c03c030f03042140403d005600074440c5e0903a952144414a0030030801d0083c0d8100c20350102d52211080e603007445401003000e050301c3c1e20341d0f002500308002c00c8441c0c01c00704000c0da140c01310b00503200c2241c013919402e401d071405041c0b000e444540c01000c5803140c40d194440340995126 = true := by decide +kernel

theorem cover : BRFrame.Cov 178776978 178956834 := by
  have h0 := BRFrame.cov_init 178776978
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178776978 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 178776978 ≤ n) (h2 : n < 178956834) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
