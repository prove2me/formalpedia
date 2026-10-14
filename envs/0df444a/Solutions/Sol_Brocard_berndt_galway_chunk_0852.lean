-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0852
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:10:42.719126+00:00
-- url     : https://prove2.me/submissions/e10e8c25-1118-442d-aff7-f742e234eeb9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 153057553 ≤ n < 153237410 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 153058803 1250 153057553 153057557
    0x40b0402011e09060908010b090402060f0d05040f020102010e010605090c13050307031a0c090108130302030c0a0b0105120c0a06030e1608070e010e041a192c03030c040504020a 77
    0x5a0019a09000e9145041d000e00801143d100300c0c0610000e5000b802c0c1c000208100b030002d00003a4420000f0404030320000c0e2000303000e1031011a0441c01c21003010282e5400c44000c00d01004140f40505041071230700344181d4140d015520b403104a08140006000e00c030250b0740c010380196160744502012606603400004800c00341d604030b100105003070307a0a001100c000c5026030000d81c1c103c00418801039800c030300900017403190401000f0482569800c0165240e100d107502c0d00e034520865090500383c1c203601c04c516a4038074900815280c401005601c0c45143c4c1030301c2065509800402c201c00c0c2d081da440c1800110a035000e075400c801005070902c0f030340000704049000c0090741c910010208000c1c0040c409a0041b00c16608004400d12922408124440c010729848041c0c03001e90030140c0f20b004440c15102100c04c1c01c400c0400004005010300141d40042c0050b9103400c10520a441080004190b16100d0000000100d08882101e543d4000b054a000f2144158420726091038801040005d40c006946481 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 153060053 1250 153058803 153058817
    0x6010513090b2e240909051305190f060c0c050a060204080c01050304030e040507090b041403010e060f0f04020102101a0112020a0207120206040905010602030a1205040209040b040201 80
    0x100040c2080d10283c01035000c1034940c145040505020300030021010740c82c0002540d90407007081288002444e40100c140f900303000e882003644241d4110340e141001d81102120340c0c00c10040c01400c04408540d40d041a02440648030f828080d500701840380d1240032304c0a030a041500354028041105540a0b081c8199142000b00d403803840f55890904002e1800003ea40140e808901041010030910042c0001a02440e01e940fa628203650b000d4000641481168041d44d07440c00020211802020403101a01c4080209a00da658414000c000502a9143c41c0c2c0654207259100c0c40d40c101c00142c40e401144001d01024040c0d0f10300800565001c0004d005034110300c0341d0051010009a9841268820503202120008030300101002410f02012400b0328540030313204020048200c0e0b4045161001d03611401752038020090706000051641c011f40c0c011300f20700e5141400005440e6000402455454500e80724841c00301001c18440d012510b046802179003100d001070003e40003d1494221982c0b007441418015 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 153061303 1250 153060053 153060071
    0x914040b040207121115010506030c03040312021b1006060509060a05070b04060605040b2d040b18090d1704080c010f0e161e050103051905040605061f0206010513 71
    0x101169070118900c0046403603403005145c01079060107600083d00c080038008896501d4040070840a02c0020505542c40102102040c10144180014204101444d0003076440c0c4104000c00c4500c06a01c403098401803207150b282e004460341501a50003120425101d490030204070b1018005564007250309a802c200d0304201d6800065104048140200e000b0100054020700b03040c02c1c0800c88000b4207109214031040101d00490300c85070f408101400c0b28000146048900c6074001c0780180c1000c05250740e000070106c1b00d030503085008107a61403040c01228210303a00c45501410581e140300240f168440e410115100103000b1803a040c000342a01e481c0380000080310030300d00340703050300701c0b41d0600f5030004a4000042c0061040840c045201c080c005c920040900c40e81001030076684880188142810302d612500080c00c90a0401c092002e0071522080501031480d00d0b2400c2d00c02040d0446207644a844003138841d8610000402c840c0c02100c41c1d41c0c0081c000c0340d082608110401044c1142040070340c0c0c4440b610 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 153062553 1250 153061303 153061313
    0x4020f0705030f0d06060c02100f020f06040b090607090f09090f0605040c080d0f090e10151e0507020102150612030a03021b06060a0317120906090d0914040b040207 72
    0xf440111607244281d40c4400c3c0400d5140250b0350207600c000104010406010096901d0880c060810700050810180010703031103034117905101e40301500d41861b0041d84200700502061003200f91107a010607064528558940000f524950310502400c01c00e00c10002040c001d80101d9401952818060b0340ca500c00c1c04500d595044c2036a40444d01102c0d83d5058101c108404802004080780c1900c0b2070400d414242d02c8090005e20746446441801e980c0540300300803c3e801005030104c00003820664103040070300702030602d0241c01d40440d05802000801100d004134495407040040c0d590f0715030305a000d0817854070384800c1200d4405014080582c054154950301a4041003000140b480700c4a070307240540c54030100360340c0110200c11001040c0281d0403800c10407280d0f0b61029010b41c01d40c0d03480424800c180e014034042903258002c0c00e010003888548a410b00c80399020005500d84100060f004071045a10b04c0d203c212840a580c0c030400190310004010750000b40b4054005100180c1c000d88018100601c60300d403 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 153063803 1250 153062553 153062557
    0x60b0406050c010b060307050d020f07060c02060106080c030609040b060a150c05070f0803070f0809300a03080c0a030e01150612110307050901053114060904020f070503 74
    0x120101d280060410300005080c020440d950b44100c0d03555046281c90040070341648915490244810703030004a100c0f03060201e1040c0c2d01e5003074202e40704002481080748040d51718042030044c41c0100c3d041d02c3c0003030118800a02124410368001d050510561960780e2036090140c0050320a80c2c0c052040d44c1d000c41c0803444000750031920902d9030344821a00321241440c0d42044200d41141da500b04400d603041c05015000070844541f640d0003911801c1f84132150a02030650f018031018a42d102c40040e0a188014a218091030503c1d89403c00c041c50503c05040c1440e607a0002001c0207001c00d450000050350707180c50501424807251281000718241310f01200060031640d20210700060321101c407405001199101c119180845407500713003000305071344c0c0f651050018040103144004104000444040f03070b074812420341d031070746140c115042e100c019844407029401c503e001e580000042005000103941050000ca000103000c0502850316103203840c01408081d501c219040700c0c0480080043d080001c4003040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 153065053 1250 153063803 153063809
    0x30c0221030406030b010903170705150108100b091501110703020316090b030a0302030405090411040e010903110c0a0308130b0a02030d0609020c0c0111010e0f0322030c030f06060b04 80
    0x9560b50314104000501100d00c10000d850400c2500300b0280009400d1180c10707601c0c4d000407180c0580b21401403514925000c0d0016400c04022140e00001500d513a000614030482112440c00b400218070a17428019030b42e00031038001e450b80b500c5002c0d044240d40981814095140300310161103079180c41b038003c40d1504143c5c031042406006030700400c102006161064000550085000d4510768100b600c0c000c0d0307207008034052035203d54000701c085400c01c94002100c89042002030000d00c40c11245094107402007140000c190049205000e42800300c9034040748043d0780c0c60004100003070700c0342140c030780e0307426508407902c000700040e00c450022800f00c0c03030034010344003d03040b5a004594030303001c00c1d0280c000e03500d2580c403200f00140103000a6111280c08228080c0c414406c0c0707060020b000514180f1805804007441c8c00781e2a00660341828410039000c00104144115403140048104000c9100240d0702d43c684406006281403110520000d02c4120703400301050f0041c2004503406840711044203241c1c3c8940c0c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 153066303 1250 153065053 153065119
    0xf1e0d0908130503070b0706020c0a15091101030204080304060c05010e0618160f060813061b08060901051503130515011715060103020901050706050a060302090f0402030a030c02 78
    0x300d4040000d480c003040b400041c11041c1c01410003945043d44460950007282001480541c006c0b1b141c02009200b00a903901207504001514450000b2110000060030580401d4503014071003040342181394064001c82d01220003440045140501d841c02c02c03544074402c3c001c1186c05540b58400315080040c00c000d000c0c09805060400041114107000c040d1400640004225112000200c2084074002c0071708814100d604a0418052a5540350103c00a59241c5040100214648032200fa11001118000d08560f000d84d1a0700000751291820020812400d1080f44d5020207400d0fa21240c1601200c055a005101c640401864048503a9014100851a6401001c820301e8a0042040080c020803420b892007400d0050240c5110210b00c5000c000002410a414144c00049070f004a0740703d00c0844042a40024080016007010b80020300540901e100980c85880703101c0100e4900d40c83e5007405070290798001c0051001c80d900740c0d030555802c4c560502c2039134841c5141492590a019402039810024284 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 153067553 1250 153066303 153066307
    0xe03070c1401020d17071b0506010e090115051005090a030503041d0c16080a11030d05060f1e0409060902131b0311030c07060b1504060e0103020f1e0d0908 68
    0x80024034041240040100700045c0240400421076070383c0001e07400030702900c5e055051000d0040d099454441c4428002c089102e52000064000713074001300c060040402500030700a039560101c2145400300d040c0542a0b02c80711040302c10070594051402800c05040107081207120b0741d920b441349030841c1c00c143e10410028020a94803a960022698010b81c40140001d80608040b401a07040444036000d880c001c102c1440003070509802030140302302d084034079003400c2102d030346a00840001c0e0140000f9038101d1f0003690803a2105845140410005021500ca0020958401285410007014001007102654410341c0e4000000168445607840e80c48054484404100204c20440144000340b05022150815141c68151f001110303c2078100d0f50410881d400c0591a400c5a04002000304113004e996503003c96405424504000d042e030281045a00d5601c507903101e4560a4015009d030300c81d9601c01e110340081000101d20b900003403481c010303e0789502c03418541050007041c4420120307000c0325001e481410700 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 153068803 1250 153067553 153067589
    0x501020601470a0302041404090f0204051b04060e100807080a05070c06020a050714120403021e1002070f1e150c05010c0e03160509430206060a050109090e03070c 71
    0x90f080c14540c42c964141c500304501d4189c0d44134602014403005001f4410340c0c64070089080c00e100c0c49051100480c0440744680e507145d85100c040c02011007014960302851030807804070103183c01603600320b01c070380c00d00d1312920104d5403180f062134000c01000b04801d080c00440b00305240420081c0c40a40010109601c8040d904c1029047c0207002d04850359600e51150300402046c00c1000704641a40e04032581903c215001015940550f22064000c08540b608120103402d40e441d103550014084007160051058000480c0d100c0181a41c6680800b200001c50707006c40000b0000c8000307610544000903100d2401a200324859079030345007943d0740000c0c180d000076036010041032203150a010003405200007003440b10f0b10502c0c100c00f0401056004094040800b044038080e410040d8408103003c58141940301400400100171541c880090078909000052080380002007003410400c0c6440141d0b4416106d0108262822440382c0c0030b01400850240e03180030602011000540807840704014082d20856080c030502c0c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 153070053 1250 153068803 153068819
    0x2701030c08161a0d270b07050702010207060f02011d0318030105040f17040305030a08070305090105151504080106080106030b06030d05030408090a17070501020601470a030204 77
    0x5441e02c044240d000c0341010807200d02500c4030a600341c90300d42203594840480707500301c83c0100350018410444084440c00c41401d800d009142c00d00c0c2c035118402c50403560312007903000c8516001c4c00703400a01603845100d00b40304560058042000f80003a520000c90080440450000340d8a150318be0b0b1801e41d4000301750070642202124001c0f019041c158020041031030300380c4803c03003444401c04010300140d160041003000351a801003200c0245803c401101e98501f00c0e6500200f00781e00c100c450b0700000e8905000704800e400d041c011f442c0035540c080c00e84043c1e004c00c4020800310507a514140d504441d41040000f500410a015a00081c0035038000000c1035071031400c000c4544140103011078407a800c603003825640c158000e42540d40007a041200720762509070841c040f90041c0c150341c000034804201e480f03405032440f0b0002041c6090b640d083e401d4942c146d030b8414210f103405803224003030035164050030001ca502c402d10368411081d074030004402090000703070004032a440c3e500c012180000250001818031201c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 153071303 1250 153070053 153070063
    0xf0f20030d02160e061801061d0904080714072d06030b01020a150603020d0b16030608030a0e0f0d050610060212040b071b080c03010e06040309052701030c08 69
    0x1018a0001c0c12400000441c4450f0f00d0f4103030300481da10804044080b84c1940c0b01d00d811601d02c0302404035403065075611903001503c942c00b10354442c202080005034407100d60400c0725529004e641d100310040c4c1801819a60440b03001150ba0303024109214070003002072a18036484946c032801c152403107489131941d8942d81c0202007a200f600710205042c2480b1501c0703d41c1c0d83c0000e50340c0c0982c0e0401100602e00010900c094050001c1341d10281d8810701040c004000d0003040041b0302e000c2c02e09101c2c0c2002c107405e81e80c81a41034601510075504c00350002c0c40b926038490f02403002d070060030800412402040700c001002801040d484071082e1090384c4140b0401c400c03220240c2549005d00100d00040c501c14180c134070780c40b500f80b084d40181d1034401c00129541c0c00f0400303130b145446a400d5409221581460f120f04c4000c1d6034071002407040d0b11941c21b1420980b06442c001c118036000d503405d9915191800c0c140b90500c1042003402080841d108a404401c481d141480c01c52a8082c0d8803800040700103d240440f158504 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 153072553 1250 153071303 153071323
    0xc030e0102091005071506060f030e0a0c0504020f0c070603020310170d0c05010f050403050d060504060506040506030402060d11030106030b032406030703060e0303011e0e040f0f2003 80
    0x25a00c104050405030b0368400612440c8a05450038a55500c02440c01d5100c100e048a6010350003402c1c0900803c0e6181c102c000c10700f020b512541c2c100490040c00c940030b1b985414104c40901440800b00f014040d5041c00c1d00144019600240c01c44d03c2c0212001003d0714016165001c180066804010b12540130141040c0200800d07142c801c0384814100740c0915511020010416001e200000841504003d42034002030105844400c04000d00d1505003005130440e4009a91600030910341000422039281a1140e08182c40001c2d00c85424241040240b00300360744090702c1031780d01400070300010052910030302500303202d001200070341522940743c030101600390341010f5110351080e00004004504564070300300100030144000e5609082ea120500440d0500d4150381010340703080d091940d814400d5400200460480b50b030591f24684405080401190340b1001d8000c0440320100403001c6400f14800c0c481014005010720108009001503641d618010a90303014142114804503c0300300d0149418010f98001b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 153073803 1250 153072553 153072581
    0x9020411130612180c060807050c06060d1a1018060b0304030e0406050a08011b020c01020d0305092404050c09100302150c030301061701050105190509220c03 69
    0x504010006503040249035018400420a9103485100000040c1d003040c02503140c13401d00c0314410700803824501602c90342070051501103240300000c9000580326608030745002c51030001805541e1610420060400300300316055070222190000808110700c150782c01d5001d620b840c039a17107c1891800413a21680380c09001006211481c0400c10400100030700203d070740c402d91510384848440020360024000301541c1c0c0040b80c005200b90004910500158400384040d910798281644410001c10200c0c1e603424602c100500503000710203103051181c020740200340c0001da1203042d140c1c0038100940016940c0c0f1030108800c584001b07141480140007081c412030f948404140c5200c0b007d854080680c044001d44c0e440001d002d111101d0102c06501c1011040c1c03407000705040140d80d07480d41c2d0348000800c00c5000039122004100142d00004140d809030080b0b0301e81c40c00c4600b24542280c00e5803001e49141d0028181c0d6a0000b482c804181008804003240110400540c2c1e0006008405c090b4000d080311500c1c40c070181 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 153075053 1250 153073803 153073807
    0xb0301031e0c091e020c030901080a0b0a0e18010c0507030f090b0315030703060f0902030601060c050607110c030106081c0801030c1401121a011707090504110909090109020411 77
    0x201041905030034070143e80c1d00b0f10020441c91a0182005102240d8a90b984c40039071021803841140c5030301000900c3c62040990b580390301030f20740030400c44c1290480e1501a522800b80700d410450b00140070310720741d40328051b002c2c0d2101a00d1020201800c1d91907220b050b000081001895004064020b8809003010400d0b10340840514144080034030107100150480ca43c0307500d602d0001c4500d039000c10489019681c480e40c240400e040c40071102002d0f0448402c01c074428080d240020940d5442003159144481e040402000581c9aa980590f0400c10b41c9440c00e00c0d1307020350b43d0540750b079480074001d1000030200c2c10010000c1110080b40c101c142c0b10381c40e00d0402048045001003021541e860580300c10f4600152441d003840d581800140c03480d40382d103d0f50011031821300c050b504825500c4803080007520400e0300d0300f101c2d07507146940455031640d04554000100d00d01070414051810942e0000555070031403540c50f460944148002148102c0442e101c07022a074440c52182d045041c41d00500c0d44000e60340f20514 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 153076303 1250 153075053 153075113
    0x219080703030c1b030e0f0a2301050a0c060504031b0c08010c050901021509070e040b0108070e041a070e030f03030108010e0106030213050c040906030303051b031e0c12010b030103 79
    0x2800e6981025009170030441200d040a500e562030882d00e52001c50020580f220541e648c005c060384800b1544004038202401004e1802e15500450444200e04040d542e08507416070603582d050020701000d041a8108030321202041032054250740d0160840c2e00408507041ca440c9002e08107401c1d0384800340d0100c2002024051207071243d0300050402084242c1d010850100d03501c0041c42850304001d41d00001500b030074442440180181804410b05860026090310059601d564024000c090150f030010700c0450100d400240880d01060f8440d00607245140200600011400207403408110005001c442d400010041190990034415040c002031090000c1c000300d8070319000210030a900d0384026054a0300c4000103035403000360100f2a40680140308041000d00d8490070010020310085400c1c0d504a990b05001292504104080c0c13446007a10013101c64809403120846101414060184101c41009204000b400c0f1098544a40030b46407400c0745d10340341d625608100c045041e004e44059800c016030f01c0b600c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 153077553 1250 153076303 153076337
    0x11406040606020c060f090901030804080c01090321020c03120d060806010b0f1305060d0203070318050607050f0d02030a091203020315041e0c0305061305060604060f0219080703030c 80
    0x5010080411071700e2503240c000e045802186442081035044d4080554400481000705800180040e11080c904854030310700030100544d02d0b11274034003028041802c101010391080314038811003030200d102c600c1603c00d810036040c08685440f58102600307413098404212410501c8043c0b04680003442c1982c018042035142c0301480c6981d116480700f551100800080000104040350480c0006000c0500625070305c0e60b010707440d03030001d4109441e030301d0020341080b400c071160158180d035031903c480d0400c3c0a4451a00c07101010340f00c1d54400341071f2560440c014080d5400d10040c0e4800fa510070b002c1c00c1c4020035484147e1911503410408032048009152041c03062064449100c0301d00c02e14100c0a940010b000807103451040114602c8210140d081c90170070704a143d10f641d054100714044c850550750420309004504403070060f1f60b000c544142e00404140020410544a4055a51400b6450060700c4590b030000200c41c441410403072054544d41c070001221410154944141919140e55103043d102040c420650 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 153078803 1250 153077553 153077563
    0x5030f0708041a1e0a020c0717010908030a05180307030f031d0604061401060c0b0402060a0905030703050f0d0804021804150c09090e070501080429040501140604060602 74
    0x241500708510100010100290b100c8282d6400542c01e14070361180c5490300c204c50307000140a5401002100d07400c08904440040d000f40e90010b4448400303010800c3c10301e880030000b401c1001c1310042d20340d01d50448001180341000214018245140d02003901c0c600842907885440d8100300762416070b8000c01c401c0c0003003580041c030f0301890001840c0100d4080220750440c41c030003c10354149402405880c0610003001a10303403084407487c80b411a5a4890713a42c4003015100000e03210000342c04020444c00040040c0307001001054400282e0038100032050302d0f0008207140242c1c80d0801c6030250b11000b140000d00d5010028615586800c3c07a044c207544c43e20b540031681101c40d480c0c00441c41d2407107101050802540c0c04025a050032201d1080001160001d0001d10050041c4070305840203250980c0d4003200f1501148107000d482c1e0684401324251a59501d00340300e052000d01450f4115424903030803060140301d075440c50240b4080d40001c0394000025041c10003c0c1e201401d0203100d035282080420805802042c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 153080053 1250 153078803 153078811
    0x3010b181501030902040c0215060f0d111f26101809080d14060a1d04050115032a0602120703050702030f06010f08010c0c0809060d0614040c05030f 65
    0x10088801d807035400c0050303014203085500250302a0800842c01061a40007454041d001c5d40b0008108481d02c6c0e40d010300411100d10200190001c000708a42d00211300080052890b180c000780203640c60032846099190480d084115000000b50290400744000741084081c0d140803100b13024804103401c01c40c0002648482710320900e246500d41245070384101e08035a200740c06213504200706a50710000103d111004180b00c0301040e0f441040c41c40840e0540c14507140c0307201a148401003c01a104142000307014070b410060080b9129921522450491210f100001000310b100e0401840401c400d42c0c02c51101c543c0400c14841c0da18a0448100f050550000e003daa9001c10706400700c0d6945a981011111031080f41c4c00607405202d10420f10341781050000d006070485002c903e41d019aa51100e00840c26030782d081030701000107800d02d0385250210720701c1c500420400d00020b10041c9005980344075402501c0e851344c401100b0300754200b08000e40341003602604035003019070f1410a00c2c51425401411034160060 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 153081303 1250 153080053 153080071
    0x10f030b090a060f15080c0d020d020a0b04030606090b0105120f0a020f0f070203010c05190503103206040506032202030304090e1c05070f03050415090503010b18 71
    0x4404181e840105008601c07189410070380602c81030b5401c0d207902c000740040d0842c0741c0710003002e03101c00907000c1000301d010180341c0d6009107142440c10b042c0c5c0801c0300680c500503040e68000450000055900c0160f00100005d510649003c6151441c0621442c00c40352041c41d000d05028003000304541e08910144490344c00241e1841d01042c4c0c3e164450140c0081c0110f80030bc1c0d140140c00144284441600406004501d108070024407054146000448882c0100050700c15015503031024201c08901400255611050405104174200c0ea1201c00d040200359641541c0c0201f640d24025405034a08000c6503291200e05031400c84c80c29113400f001c2510f92000038600342c140a0f0840c55442c25a1000420300c0c0300740d03002802c484c0c941e501d41c440c02c8002d101c0070410840c0c900c6011a03200c48034114000c2e90560b00c41c551640d904011315500c85200741d5104100480400a04000118407001100104208214103a6441a102d800c00051508580c2c0100f0302611841d4080e1340350707000d0043d4010341a8461624 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 153082553 1250 153081303 153081323
    0x40f03030c09090f1a010302041d0c070c120213021905160204020408030322020a0303031508010c0203070c091803260a1406040603050303070f020f06010801021b010203010f03 77
    0x20704007154240d81503001008000d003440200413568440b500700007480012489a01a0040304400541c1240f240c0d1052065110500300010002c0b658245160750020049100303d15080700c0d596404003203405034000d502f070800010198029820305000c4a004008090411441c0201c030f088801080000554407000700040051440751420f048003406141c541e0250095444a03150317004a5200d070011124403250051707600d905441c08000d415008172940e0050700c10780e0130a003985c4044020b49a0081c4240505014180010f1181404d00c50106070080d00d03800b554032801e01e468500051402c60f4000100241030000a8080780ea07901162000c0541c181056480001030a000542e12050046500764903143c00c010410405180c0d086980e00540c2100314041960740d50082200301c0d0340700d0001814a078400c0c0001000350b405090818029000d500464284500ca0b6840340c0c9007036002d8024024070394001c141010840320740c4800f099145c8520009605540c105010229080075510000e024000c013 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 153083803 1250 153082553 153082571
    0x90d03020a06020705030301080d02012007061d010606020d541410020d030b03030f0403080a080f0c070201140c0109050a030801050105090a1211030a030f0215040f0303 74
    0x1c20500421035404101503466030110308050752aa0000d1162020303601811a20113035051043c440c4440fa001c801454800800d000319045220380c00c01a01100c0c03041d9501d0240300341405021181d04035044002c0007085142c18244000c0c2005143c10200c0e050049590100c17041280240d241c003401d0841c00001740c461810f8402c505141005010398510000e0120010402c25800c3c414180a582806808086068101007032020307191108840b14010b8003c9003400554610a804c41105e02600904907404c16000841500035076026610440320700c02c002805c00c8000da08240940c1c0d000403c10b540c6e001510303000804800c64801c0c170390004d0401c00f14000f1146201b91110039510380075000c90082000e00c1043c54120340c2d800c403200058010592110002616610640407111092405000e92110900e03002c062901c541040101b29030284032100301c54160344041124041c201d01950b0b0308504021141000307814083c405240c1000c46500004100106403184881e05415600d441d0000b885072f4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 153085053 1250 153083803 153083807
    0x6150609120c01090b070812040c0f0b090415050d0b0a02070c17120c0c06070c09021c051515030402030a08030108010903030e010203270c06030c04180e03090d03 71
    0x81030101199000c20452462641d80c1000181d42480710000e8035820324550311003012922078010b03201c0041001c00d04004101c001041100d503650464403808080741d4480d100c0040c060141c80641050006001c0070502805501d042c1c0203c11f1078208610180c1402403e21001c241000c0380a24040c1c490607401c40031510a1225034100d50744160040c22801d40750f51948501c42440d50038480a40c2107111364260b04040b040d0300d0044900010324003005080d0142c00e80d080c050150000c190076140c61031034210001d04011103000511111050303440408402a0101c140c1c1c0494034051320030b0400b2401c448442d0700e21b854440201e0410074040741d141e40c480d034840c80003914100d07613400300400001e00400001030b0201e05420445805110791814001c40482d602803d00301e000c11188189070345004c01901f0403800247e00c504262002041c155030f0207070100c0000c982d2980c01620032078000c0d103000a0070040c03141e001d103850010003c04401800f00b0258800003e41e4ae014108045200b100c0114961701054 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 153086303 1250 153085053 153085057
    0x1502060f070e030607050903010b04060f150513080304030c080303160809030702030715030c0809030301121a1e0c090904060c0314040506060a060c05060114010e04021204061a03061506 81
    0x24000f4100c0c0c18902e01074100a00795005220a0341c0258281407104001c0d2a0600608080d14030785c824141106242007140ca22031800c0031100824000101300b20100072160a1018000e006020000c582ea40d2562070071a1080c5655880f0888036001801813007c001311013941c4d8404a00c182c5068010b503140d030141e041c294810704c80025850312450800140c40350903000d90000c401f00548042100c02c41c040d01c00d4400c050b0845039640c0b580c00800c0140030030046550129140780c0103204500500c0c05503018408050f00a0b41e0800c420b00c005130015104001c034500741039108004401007400d188000000c00c01c003410203030008110a45030f000b20340444d40310343e1156024070b9000c03081c850542024280a605d558054815a002e80d840460203c0c030a40200c04201800354440d00070949a0702c0d04481001c5401000c020030304021018954050356542c600150201c020541c20f401e513207046c649094130480d42c500e00600420580303884a00c01e95600807500c280c1c00508108065131003201c00c8000362485c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 153087553 1250 153086303 153086327
    0x160201030204080f010618090b011206020c120c010507031107060e0c06043308070f140d1a040b0a0905060415030f05070b070f060c361502060f07 64
    0x44c852800d85030b1000c0b0b4150004800c940c00380b100304145050449081c0d080d01c0e210403000d421040004010088410969401d03c42d03503000c3c3d50b00500f02012906c115091807140303812040003940204912149100a108003074110b22281000c03c4145184007420b443c0303004001d0060501a515510340704010024001691310006c0101019500e58403100946241ca0711203400107090400c04410940400b01c800002d911040f0740e448514159903017440031140404081c4d4000104000b80502c900c004981c00060710001c641d4000100d07118210802900300e0017003850059210781e08088103200f060b21203d840505941d100100418650340303030000310300513104251204111042050f00082440b030000d101c0c92180340700e8400c0d2103009585141d040100d00440c803028150020701490baa001400992101044106c9800c01805401c84900290a070311008004000350724084038220004001e6004031501802c02003000c2070b0032041c0c2801c02582e070b0030010a030102000501000c1140e060041c407000060b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 153088803 1250 153087553 153087569
    0x20109080717120703020c15090d11030607020c01091e0b0301080d090b04050609060313060e01020c010c020f0303011512020c03040501080106230904020d0e0d090803040308160201030204 82
    0x40e555480c90301c4200d802c60380c076881c0749020744074544100c0080c0b501215040398042d40205a5126204c00304048041191041400c0200c1007001342c0c0306842d00c0c00d14018503405080e005101c00c10310b400307160502400418881c110b420403085009142c0c1c00000c1c0c1c40c04c0e60684200040400e224a020308246c1506400c50746200d8000b000001e0000c3c400601d5002c6004141e0700c20b00b0740303a600c0088051310701440c0220750713101409105020240c100708014680c00005c21030b04c050200711541b1450111001407603001100d03500040c4182001009005010941d0006e00c000d0030726072007483e584c3d5240d00060141020303d03d202d4055450700703841282c1d40c120076035480b10115621403c4d08840d07a40e943c418030841340413a0500b000011298000c501c0c1e8101c0d100599040e20112080c0c032900c050a61185800c4c1c5d0348140e00b880f0f00c0d10480301910843c41d07403008600062541080c1290094400e540c150b01c544203c0e0700400040c00052001e17402e035450003020501d400420070162005070040d01580d005050 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 153090053 1250 153088803 153088813
    0x80d09152717070f1404020d0504140f03040e190902060a02030d050606030403051e041701060806091204031e080a03020a0815060a12021909140301050103030801060c02010908 77
    0x110406018420300301d0345400c1c0100c6490281c0c440950b12480c2c184503182c4c00813080700f010811101a098800d1349400c0c024401460000703215440e41c12202c0aa80580e06c4465100d01c5075039410003085a4140c0001c00c1d8011410245045040c11101c50000d1040401480880803420400746540002c0a0268014000d40d1500c0111000a43d01e07001840d01e000864105004141b00d404c042c17040b603000c0da0700b642d40c080c43c0400400784400038603080d041191288404020000d98200c4007400c3d041840040d10010414525000340301e49031110180010301103030040c07204690004007000c12a021a5400548820300382c0e80c2c01c100040d40074a1031700103031080390002201e100b007a1341a402030107169100c1e21004899203501491212481c402c490aa0308502c08020a02116018071541c12400040d01e402528141c0310003500c03018018060348480204490070310511403c00c0c0060461190b08084d40208450740c9903444c000c20761081849040c0a00145116100070369105200c103001410b45603003119 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 153091303 1250 153090053 153090107
    0x50a0b040b04030f0801050105030403180906062001020f0702120c04050c041d06150d09060c050a02061503030d090201020102120f15040908030c0a0908010c05030a06080d0915 77
    0x340500710300712422000565620355036900940200750444c10b0380e8045c0e41d440d00b5543d1700e131750544a10f072107140d40004102504200240c032414038094140a13040c140c1c0d807807100c01c810707014140010205882e800a942d0040c0034000c2c02a403a4419035100c0d90701103e052002c05e00c04101c16040c10000d61145d5001406c0c40201300d0820050001042201e1225402c85001c002402d40c092441c40181d801590001184100134040111000a00000c044c4c2000000e04920240e4503181111120716109000ca076002c518218507039018442a6400741e64600541d828946540000c1d4a074411604d081400f43c1d40e0313010020559100b50b040e82d00c1841e28000100c0541001d15203014401d9007202c0c41c00d0354450703181100600b03044c00e00440c000103038024011815500d8541c0340c2c1c1c0240d0030045036041002043c14000603175030700074002d28841040e1521410340e80d0900448041c16207901303401c000110f5220782d102000300c65001c01444121041100140c81940c020502182c1200c0039070812020260685605 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 153092553 1250 153091303 153091313
    0x5010501091a03011a010509031f090605010e070203120415050a0f06060e010507020d020d0218070e040207030c02040b01051908090c0a0f0b16140f070806150607050a0b04 75
    0x10807610500004060022840c0030070113080c1d039420b1030314049004030600061810b50140b00a00a44c0e00000c043e40e01902c0160010340c1a140400e04001e402626041501700f0300016104003030240c00140515402490003000284d40c81c428054030141600080c0c0006003405203074692402c11803040c0006100700d0801c01e2541026003807446009449520303000002031003c7c050443c0281c16101072311001c1c1003140310340800c00640000e40c4160b03006003036038850a0059039400d60740c6941801c10a00e00b1554200000c00034a10b00206040500952040116001080d0800e100102c0d0390340c1114003050076008580101e80a0080d1090694610303208203151280c06c0d08032110504c00c0c0c410340c00311025032111800304070001425100e442d054070940e00c024030034661550000d0109048082c04880b40b0909599200d58140082444403c15080021041c00030941440803400400c1410010886130800d8803001c0c5d9405e00b804034061050340f00090700c8040000900040244d6500401e0400403840d00c2e00782 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 153093803 1250 153092553 153092561
    0x70c080313110d081803010b22020d11120919080309211213021804080c03040e04140106060f052203030503071b0804030308060d0204090507170715030b010504030501050109 76
    0x105c021900385c6113502c04407030405100c3c0c80100940205003124910901d40303021042542c0703089184d074858003041600341250441c080e05001302c580d40d404c02e03624100581e65450f030b41d0028003480490b0708079002c050500820209429402c0f0381104541d9036036140c8014a511b082d001a00c10258420421030903030840443c1b07005400c01e0741203504400050750311140791400e81d5601c080002c1d805050000094400c1460315100c1c2e42c0980704490140c90040c0c5e04000b546540c10135800f40380c280782c02500300420003100312481110406d80704c00902401d42460f601501c0c180e8400b012804008001c2000c07441140303540303c458603119140700c070441055201d040051155208981c150046034103528030307d41c844109c0e202980b540c0e401c00d032182d081c00c1c2540d400321400040680001da10080003070202c400359a540c420108014032a40050030858030700700b5400300c040e610b41c03075591043c2c20001003004503020308100869003845502c1d00003010407013040180c519006582002c0c00c0d0790720389070003c50109402e0340 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 153095053 1250 153093803 153093817
    0x3130219080f120d11040f0b09040b030615010e010507020406090608010509030c0c040b0f0303030f040201140c0c10020109050f010911060415030b0301181109070c080313110d08 78
    0x1074070b078451005400e0941c0c8081002c0358146000b020050a028162a58840d00440070000d030714910b02552024101030b20b8005400a55401c00c1c0050084414035051090420910781580070f01104e00c0c3c5003e4109181c202e0356840c9041c0070103240e070010507a02c688100d41150b50b000300104506612011804014195802551255841c00e40483c1d01404004140c81c40c85c042c02c0000c00d60b0030f88050901c0041d000c00c803003142d0001103550740e440903983c041c0090751283d900740808400c24900303030000524401d43e95200e813480e08410050390a03021000308030a60304500c2940c3c0d001501c50b0100e0100d0051000044c05403480c051307980d000d0710740070040d00b10000290090b6602007145070341804000e040d1146116001c03021410142c0440c50501a402004440000400002c0d44030742d550075170b11211904d060b046524200a41c500c4c1c4051801401142d00b19100d49051090340c001540d03104814440a000c6c01a49108850660104002c00b07016200719200904542086c001d64034010941d0f4108803 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 153096303 1250 153095053 153095069
    0x60506070b040c05120d0509060d06090207030e040b0607021c0f050615060f03070804061b020c01120b010512100504061805071701120305070807080910050a021203130219 75
    0x1e030000f41445d0115400801410b0b0b0f2000d0041280095402d442d01d03481b030840990001c0080c48410500d141e14440d41c4010550001c0c05651580c080c500289410111946107201b10300e008900302080e00e40c202a540c0e0707154180d032040301e100e0356040481c0d0025807041d0000d101a804410f0103081207400700320302e40170b041d46c110403407154000c80042212034022034000ba44010000c0c000280c8581c820b59034503400c5801101c2c0042e02d208140001e02d005820b0055580c05030f4051080c0c0a4256031041c4030b410010070f082000c202d11000000001c01da07110344800b4010f8024000041040b46c103080b4001001802d0007030081000c540d65104090f07001e0710303103104e070800c1038070b070100061005005030000b40c918520110302c1e07420360707003010301a0200c1c0d0940c1c01d00b81c080000038056800054800e0f002407401c4d50042800588424a51041100f4040214404800c00400f0302010307c00311380008102a035140e20a1209880390b5a8031620524100d5480c2c0283d44410300c42c08003003070700d079454541000303461600c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 153097553 1250 153096303 153096323
    0x20a0b010f150815010c1a07031508030415230a020a141c140f040906031e0b04030c1509060e160303020703082802010f2702040b04060506070b04 64
    0x2c0025200004119119242c80c40b0300c1c800030500b0741c1300d0388840030001e102e171904203056082d1280a00070485c046a00901080e81c903031402485541c00182300004240001c000c2d841c20b42821248240c0142504070b00c002d1002d1301e00c41000c016210940940e2559602502070303122010300900030350b14058000f09842d40c1c1600c103426080040301190b40c4860400c50841c200c4d007603050280450f00c1c1030390315180980c2200c080c025228036841080090000b00408807000c5440343c210304000408801d04000c80c0c0d1054030034540070002031140d280007a48035806041000c4d81c000c650030458640600104030300c00362032800344d5a408010040e80301c407191203400c101b119000c00340140324000342585400007a000d41c1c000b2000b00001000c20008001c4000b00349003500540d00d0900741810b201b21401d14040241c0d448455000f404916031042140e41c210000c10b0115468590702d5061b203141030004040d00403a100c280b414071984948e00706000420020705501d03a0ba1500c0c0c01e0500d1192800da80468405841d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 153098803 1250 153097553 153097589
    0x180308010302102d120c11061312030b04110c0102120c09060405040b0328060e010203011503090c081b030c04020403110d0c05060a0504030303050f0907060f020a0b010f 74
    0x400c44c000d00070110000241c04a00000400c1e20142c049140301590802050345003824120761180603440d1000d1281e110a0158031586440741d092100c01403440b4a080c042c0031007880410423100040c00b401700c003403d001605036406070200d0003801d2041542503104400050069107408154018821b103000c140521502d0b494180c500a01c903c50f503484182e1000303060001303100c0c0e440c26901160884800800b04c814903081a80d54201654410b40022000e0128207000e80030300284e80130350140740c090003008510359814038840c0b0405481030014072040650726100801040010a202405000c0c2d01c802c4461010420b80d000d010500d0344103200f4020300640d032440140703060030300a590940e68407566451010303607e40c00780b05100352a400c0580b001101c8040018868458000402e640b41c0d0039500c481d0b9640c2507090140527550042c01d034620143d44401004500700000c54240b05035281864201d00810b840d01c2e040745800e04004020b0002c0000100014809080c14111070803500070881c01d480c5092 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 153100053 1250 153098803 153098807
    0x40c02070510031505090901050402030607030c080103140f06010f151b0206160602070503030a1802030c061c1e0e06010e010b03071b061a030f030d0f18030801030210 73
    0x203851040070341111076200350718040b9000c1d07003242c82030b151480c02c4400010780c1c41c4009551004140e80c0040d00765540c406000542c24140005540821141014042422500001800520140b05c064507a0000e24030b15a00400d061010319504056101203c0031961500c600c28a010681c1c82008416150f00e280c407540c3c540100303e0404c05800e080c84403451241c15409003c0594001c3c9405042078070340f100000000f139400d10143c0140e50144c1c00458403403030414051000c986010413041031180751005102c0c0140e40014424004140603a640307900c5d05218041e200f12000b0344c1d010320441900300302281d01c40c0c10f08005a41d00340e0749070160900c021000800110b071161428042e03040b06061510041c48031000c0c0d1001590046414905841c508055032203480041c06084011036280d601c400610443d883d511402c10310f41041100a04010920030b0211941d91090f8928940915101c03450450030000d258002e0381d81d100c0744c0011030b0542d0502d26000344039000c2400120b10464103903000411040c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 153101303 1250 153100053 153100063
    0x30705010b0f040e0304090e0a0b010e010501091a090f0f1c020312030c071212090b040b0601051602040506151605100207020d0809040b0a0b07230303061005070506010311040c02 78
    0x24808401707103180500701140c0202905625803610980d100707a8103680700150751a80c0b03250081950038003900440d4100b800040c1011503c4d8422810b0492103500c006018602d00203c40107610b04881031101074400740040303403528082403d016400450700980345464201003004040300f9208500752003a40d00c2c260b038241014041540d01e682d0b668030034086000012800001014400c0281c1451585101a0660342e030980350130410440e03d03030501d00c0030f0204005049000e1504030009007061800c0c050340710411012480c05010283c402c0703488001080058072000d01302c003007104440c00740f02e5644011a2070601121440e6808032a6481051903e510358251403081c1d0703927116801804401500303a1034031501c060383c105a032490752050381c44030b9900065550f4046400240700d841300441c0c5505142c10400e00414a0700034004400881843c4a18505404412681c0c001021184003812140488003122640112540280f0b18840c03400048180141041d216000110071541031004c030080314403c030b07290 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 153102553 1250 153101303 153101321
    0x1050c12010509040c030c090603061b02061b040528060c020d0b0405031606060f0605040b0403140f03161e02130f020d020f04060905011403040201080c0c030705010b0f04 75
    0x40c0c00640050145150480303000744c125000d4050031038101c1e140d460b026100413070380c1e00c100c2032181d071484200300300301c5140200483c0c0c12810803502000070003200041d4175000010311001ea151503500f006c00b14122a0410364029010180c0740d01c0f1032200c0d0700170b240c80440e10070341d01641c082c1d55110009100c5101c0c11290791030541c040d0454034080501d036a03c00e0b5840019008440500092140304140e20440c1d0100d141640640310124503c0d181500444890500f03070088030810000b04030501080003504111401c5903840001c620b03120341039000d0507050651158400c0000c0c00000751079803403d801400b5542c0090b0280b01d003084204c030280c03081d408120000310000e40190f086c004c00b20001e025a48000c1c004a03004030051b1400c440c121241040303a006032400d01480b0004201032000592103101c0e00040d10702800e20650b65200c60305400394502000708000c0c1040090b0000030881400b5030141c6001e104070308104d903100c056900e4224044d02050030041e004032a8001e0f080c01078901802006d8107 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 153103803 1250 153102553 153102577
    0x2090a2403110423010908011b120e0304030813050613051903031d0301110a08010e0609070207120309050d050a0204051b04030204110405030303070215010902070804061d0303190201050c 82
    0x42d0b01065100c14440380c3c04d07101040c1440b00c00071001411410a000d00c030111540d040c82d01c0c0c24440d0740f0f03102a040801041b000010f180c0303081e1101174850400011038051b0303500142d5060301c42d540c00300d0303a144a4400c1d801081d000f50300850b0002c1d40308a040070341401c0c0c5204640880c80008604507112202005200140008201e003196a82503410018680d40428000d400450304070001012a051a07004401020010300c4400040044854000205402007400c49041649080c1811300944c0d035101800340e075444a400e481c60601b05070082c24454010440036000303131003010a03420016101e282641d0140d0065041900080108065010a1140654400c250b600f082c0c1507400b0b000040042c41d40520220340100008512650104040c6114100c603500078031403c8401113202c1040b84042c1d00040040d0b00501241000894440699080d1403152400e080107404040420703100c042c0101e00305030140800600c01c414030000200c1400b08140c241c009000940304c10380c03600e000b4401e0081d003000c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 153105053 1250 153103803 153103829
    0x109080304030309020409120e04050906010605070b07051c1b020604080f1803061611070b040303030b0102210c07050d0b0a02160b0f100b0a1202090a24031104 70
    0x3070f020303600a2050030b001900000b00504241d5403203000381d9055900f02e0104104000301a110f05e410300543d030380141000c0160035103524191020380503003d511001003a145110002030f040354410300940d09981c0044611820b0031501d82804030081c800c3c046500141d50003d0100750303081c0d00016500307001d81c2c0d201c0341081c9089828118500103400c02a0540c603101c804000c6640540c1c1c0070000c8501a1140580e044174030241510040c10794138803221804200c1d002200c0411030b0720f13001d03801d84007100d4040c1400315002200c100100d01308020303040764140204c902c4010038889520354003e00980800f03141100c20320b98a0350200440024241d500410460240d00041e2400d44640c000d8500704003150400441600d00381d44000701540101d0340189280000010480b800480407240002070100741169454000c41500c000d16a64001c0d0f20084000c0c0c00044040154840c00d000400411f0701034450200c00c04540c41207100380c00c09a00c6d00c00040e083c207074190350410f0941e048070112595074000f81 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 153106303 1250 153105053 153105061
    0xe1501180e2b0c020d0803090601080a030c0209060109030812100501020c061c15031a0c12061005130b03010e01060908030a180f060807080c040f060c02060d1103070e010201090803 79
    0x20250801241560b03040104451081005803604585001010301c640b40c0540c8914000542915052050b8007050140d482529031102080d00941080a501e8065a06002c0d66030b03210010b82d9044410f0b40f00078050780740003480c2000f502c085030752280601070041d45607035090fa680c07004982d128961189154418801c00c400004170030b05800709000404105004998500d440f182c43c0000841c0341d000b501c40f000302c0741d180360400b103d0700710321980a190004c480342010080c04041d004004028000f0303015090b01060951011f0065041d00d00d4452036030709800b050b42d180c51001906800a10a4081000466002003440360007100301d07a05039120400114140f074040a401ca8610311886480240e4050031070b400b068440769008514054030454589410600b445900180000001419031200010070720050005a000c141e000c000c89105207002461854180000340180c460703c1d01040103d0f01c1e020340340078030f10b0103a00a103114605984a0100760744106c00164240c0e00f00045c028102a801c100203 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 153107553 1250 153106303 153106363
    0x105040e1005060c0304090e010501060e0d0f020907050a03140105150f1c062607050f01030e030703080403020f0109030909020f0c06070e150f0901030e1501180e 71
    0x120380c1c010400c08007030100740e03915000310300e80307500007441c52030181c000240c1801078075024020074500d104414001c001541c5813290083c004034095924a1162964102d40c206104048410107040b680092480c1800c1c00c11042c00340ca0ba90100b00d400c400b09003440da80d28881c0d40c3c000a200d04999010700340c212400e62803078aa9400d41c4c043c080410b407944060151010b043c10724450700703440c040e02ca10001421410726407481441100710045510290010f90f1540700e5034030102d2201c040702d43c1a1007900381e101c0c1d0400141c02404480d1003030b164910010850344141584082c40700d014a0280c0c00751f400c6200301c980c1160036510045405400306003940310800a15100340e0041994441c0000700a00f081e450384c01450920000340c445200040414090300d44603e030021035182c80f620742010881c5028084510050b5500400c2e6989040c1950f0704244240c0300400d0140e141d40c1061402520883c1da11824a100c810b14001c0c6044020b902c0c00d41e80113003001000585411558520001d42d603540460f01f05 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 153108803 1250 153107553 153107579
    0x402071a0403140a02282105121303031b0f0e0a15110c06071a06011106041511031e040303060b0a120b0621041b060e01031406010504 59
    0x10031010404070050301c1c411003101001400382168030345d0142c0340007055aa03228900c1109041c00a02c4200c00b0301d0200c0014040e01c860083c032000701150089000038200003075441d40112500c030701084611b1410444c00e00c034000340003c0c04034401d031000c010104400003401c0128030020400c0c40070500c0d60045a0445004814450041100a1960743c1d59074850700c204440a88046c145404601d9407624010802000e001001c180d610a039001410480162102d443c0b28900c00c03031300b034a0301f0554400f10300c1591003650f11411a81c19101218080c0c10704bc54000c5400d0b00711040016203510303160100d400c0103140c03003c50b0300401a0a5007040300b140c4820500245503000384c8110140b69440c02c2c0000d00007880d034090f060040403910382c40d03281900040e440301070751030308856a88101c0b4208403446801950002c2c000c01c4155031140c1d00c0d59a5201c3c0780404644a40b540d080084450600000031101e03889800269208820f07a428000406150035525020506480d000e012840a00081c0000740034802 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 153110053 1250 153108803 153108811
    0x1080c03060604090c03021e0901020a0308090f0f0f0606040203010b03061309060c031e060803030c0a050c0601030b01051207140d05071706040c0f0803030408070f0b070503010906050402071a 84
    0x715481c3c01c2e51480e681c0e00702c4001480410105e500841c038120300095201541c2c102010303000c8128945596000001e44500320404000c040c4210710004c54007100381009660301c640c010b0800c60309142d030031690003030b44c50b03080790550b401c2485020b000032480d05141c000d890484020000b41401d5485040800280c1c03120301c460141c10650350551140410004d020305400e05402c0e840c0001e4100b091880820340c06d5001d902c003030502d400c2203410440410004100d0740c0c0000c20302010340d06d803030695100311203d125420784408184142000030050291418407581202e00403074006d0000303180d200046440700d02600c00c0c1c00d4400765118038104103040400500012601c10b1060b1020741d81c07070f11a40c80b10180c45c040c0d0521550302180420007000b10f90b13040340780a800f00050f41480d00385000c07542e6540303120081c8000d000c0040030a2b090100600031030100e61643e44161006030502d010b21006200d40c200340310b0388400030304020000a0718100f0307208686c3e031180c0001c504c00034611114a03114031400050 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 153111303 1250 153110053 153110059
    0x30a0213150b030a0f0207020603070c0201020a06020a021e1b0f0105160812062d0a03060e01200903060a0b0612040602090306070f020c01030507020106080109050102091801030201080c0306 83
    0x1c1d440e00400e8030036065000340002a80c1540c49003440141d060803150030644540c210f40c4104040d0f070260341c610090320b505c5451460200742c1112940300407402c000155100400d03190010881d5803407c0e07004220070749180446600d901101c600000f03800c1c3d0703850340b030a5500407423070268000ca41e080c100700c024007920300700604103680b0f00307a00303038080340300c2c948548030240da000c600440c14810184d00c005100e41c12282c100c070400100d6110198050603910210948a07000c0c84d090401c03030103501c0350b200b020019908071a040010540a006190190418141d0180441c1c00d421140510aa801c01500c5001d000a00180400d030748560140004080620302c0c940d010a0030300500c039101e110581094800e80c402d14015803110012070525150a00c047c100d1403d0116800290034442e50004088045200900e000300c0c482e00c03480c3c0182d00410300c503080440b0305e50a10104605200054004040c210320a846c400444246641c0400c80b6110038040240051981700104e68403241000c00f86811802c01 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 153112553 1250 153111303 153111311
    0x3161e2001030204080d0207140429130e0105070206060108090c120109080403030504030c0518040b0a0905061617070519030e160302030d08011802071b0815070905030a0213 76
    0x178804842c0381082e014002c0c0300503401350006210300012030b05c0e1914500070a035410700c80d04c45420100144120711b40001c0c200081c00c1292880d503996010494511840019820014031039190030040c042c1204840c23540143c4180808107460707501c28000c0724890008a030140250a40070010403c02401d544400c002070341d2111800303c041110707080104000c611039154599202c4c034516140740c1c1c440e0a079224510a03800411210300704500200039031f0b4040d5100c2e403505440c0d0b81d403401c50b40007010108030142031442500c0800003a89030811008001d105161945411a03800900b240c107090001c8418600040003888035250940c03040540c0c015002d2541070100345a010411075600d0b11040c4901d01c100c0171b2000341c040040d8101406030100210661801000d00d41c100204603c0507203503c5040c404442d800191403041c0302c5040c0440c00d150700035051405411340d13a40d0443c0d90351440ba0315010381d00c011760b0000c100d40e1801124600d08070341d00580a00703000c0c803e607020050512181004100e14a0b22 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 153113803 1250 153112553 153112559
    0x602040f030209150f0f19141915030504060e070303080601170103050703140f1506010e190e15060301140307230402070c05041803020d03061a0313020303161e2001030204 75
    0x4010315107c0a04202c021000b00d038801c43c0200102c0706c205619440300c0c20050b0106100d0306180c80a000c29440c0b00341004200c40d203542c54124000c0900050409481c0030301d000100405030302c01031103805a442640c0e0b00344120840100480380c1f0300b00713200041035a403000004000203801201d600b00910364050603100c403104480003007400c1100707800c060b41c202c110510400940c0d41c0c00c00d00400300410155401032003040100140d0400c41d420340640500c0d11a002c0010b400c1d21888070301c806113035501902e01900c0f569920340248110402d2940c2d18130034014004d0221311400381c00104c41c040e0121801003145540c03040b00b8440258003c2405a8008000c418042201d031070302c1c00340140101400041441d11642424000d05110b180e611800c201424203608100600b903001c54801c0440506c0340265498884a09480c2482d09800c8000d400d0302022070b41114070300390a400032038000d004010103107040c40038080140da50119808024a4000b00c000e01203880807001c15007444020303042c1801460641c03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 153115053 1250 153113803 153113839
    0xf03020312040605010303170403120f0f02040b030414030702010507030c03030605040e0604030807031118060405030106030819020706050f0921100b030706090302100c0602040f030209150f0f 84
    0x1e01201c0a488040d26030004004155218000b1008500002c0f030749402ca0401e60340c0180060003c0b400302e040d81d5241c1d030803a401500103910103944040c0c1c0200c1150744641e0b45403c061a500b0403141619104016407000f0841000441100c107482c1d0b050b9036079860800c43c1d9605603540c085c0300c803091b010165140c02c08146030f10307184103400c103894510000b80000d1900d46030081000c1c5005048a04043c2003601025030340040d20b0680e400d0144145000461402403804500b0300c1c021940110751540c02e015001051041d000028000200c0d02410030b40e4842003d101a40e442c445031145400042080010403040d4002e400900360303001c4020a0072118180d04c00e14864a8100003800180907007150300600000782643c0b055164454095002d80000d5103030400107810120140310103409885c000b0b1295801922400d84036240c50760040341103460380c7d20346120b42641116030000700c4c0503040d20000700e4003d0041c441c00c50040040145074041d41c210700b4041c403011400d08248541c01c0610381d2000d5100d44 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 153116303 1250 153115053 153115087
    0x8070c0504060e0103060c09030302060c0f0d0f05011806050604091a030a05010b0103060906030c05190905131502130b0c03040308120f0105010f230712030603110f0d0f030203 77
    0x85410402041d4a5045046c28801c03101e05601c0c2c41c0510102d40020400282c002ca0555030050607885d03040d1316400384541445c410f200392841d00308554074121070a24400081e5004a060f1118004200403d00c1d00351443e00803202507004890f0300c50424082003004018a40050004169081900b0020105031000c24074001580070202c4582c0d44a41164101d547d041c400d1200a0016100c00e0104c0741c610340b80d00e180003286001d50b50248880c80516050700125041e200020120440e04100c1e5140c441c030b001c0d40b85000c0b030100f250400700350b00100e030003141c0754000d0b03a000003c1c020290354814a04410b8040c650700c80d1000701110f00042c0000000328900300b000e0131400703801700161f00c4207241801c501c07040546e0581015051000b1030b420650b0203032748254a00307041c0b880740140c1d1040315242c00280080740100140100a00c3d0201921002c060381034201404072485101d070060080f104104000c1e100038140c115a8001e070048e208000420b01d5000340101041c0280192880c0001c4a04001540 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 153117553 1250 153116303 153116309
    0xa0b0f07140d050402010806100804170403021203070b010608010806070c0302070902040b031e0708070c0501090b010305030d0509030f1213020604081605040c09170c040e0714040b0d08070c050406 86
    0xc0740c2d22010403003175513007245030254440c000321022440000b004001409000d4060b1000c0c00c00c00316800c5a00c8544030340421074019640080404412442c40780410ba565805000102d48070591034000142850055208a060f24805006052255190601201c0c03d180f403890550842c820700b14002042d070b01c03510042c00500240c000140c3d59141000c0c40f0040c040307402601c443e80c82503500421000d16440114190400c007949030041014800d810031a0242412200241544600400000403c50008004c0c0091a0409001c3c401d1f9925910400d4980c041e61200c10820320042203212490322050101c41d501500300700c02116100440e070085205030304203070440000d42d0700044c0640240002d0440c1c007002440e084406100ca1640c40e80010242c520501ca02c4002d40e11034282d03140c0788c041c03d10000e80103240160040180c0c01028401c2603a4143d10702c500781034007000030341070200760900e401a114143c502807d039140c0c05090769100d0500b9405044195856421060f0200b40e554a07401040c1c01 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 153118803 1250 153117553 153117577
    0x607020a0b030709381b01062c0f01170f0a1a1026030c0a1b06020303010b040314030706090807022b031116090c020d020a0b0f0714 58
    0x8600c0c04d00d07000d01c401e03010600b141175030030340c001603030006518411840f908140d26080d4250b494808913040058151442c12510085d5401c040000c11854840400200c0780d8126018076a502400d40411292072a020750b03a411003e0400d00040c000840030030391760464070f4a003000315540c03c0c420326401c5050001a800440d518469050800c7c00484a27042c40e9402840d102c1009100525044100b114840000d5035039807034000390345942a410100784165022920000c05036914241103107043c40104c1c3d1040c01c018030003140c604003c1841c80c0b000090303e050742c2c4810742140c6480e0840e16207000b40070011854001600c001c1280c0302c00682c0c41e000c0d0300072461050000030b4407201e5503c100329468410581c10340b41140005080d0f8868040314020012283e014201028048a680c81040c00d103424034041c1d504880a4207070003d030300080390703104020a50140d801d580c903c1018000407038179040300110141c43d00b04142e001c6442220030100042e0882514204000f21200001a0b0b864a0b0000e03030041d24 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 153120053 1250 153118803 153118817
    0x20a0606120302011b0e130e03070b061f0804060b04091b0f050f010e04050903041a090901060507050615030a02090a0213060e0a1a070803130519020108060607020a0b0307 75
    0x4201a02405000d045d0011201a01001d4014031802460305003004440391003800d0020710811842a240e104c3c030040b05028007070740e42e034008504100580d1102035407414040c1c6200c5103c411181007402d1800103980c215603408040d1b4540d911190301030310818000d01e91284d40d610440e800100c1c00c502000b149a090100d2160311840d04408882d00c8403580c0c40706008510807103035031034a81ea002c20f03681070303200c0e003110006801c0d15218150340c6180919001245007269030410849c0b2622540d000e4213040104583c1040280e03252a011a181d0003130039002003495103c0404917405094a184400c034080c805812120503081030b40003d180001c06070b6010001c6540010f13001a00741d08407441d44040c2155050082d5100c0b00e403004282c02031060b108200a5808a0320785c940c03030481e0300d001c44a03c6c60308401042e88038202a49145010600500111201e00c645514031040c030084801d400003654050711000015941d2030140110380d4807650040380d1140160704045038030300c0c54001560150b6101c3da01d0301c0c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 153121303 1250 153120053 153120089
    0x1e06040b010501090e0106030f06081605030c0d0b0f130609030509030c190b0a12090302010b1806030304050603060d0506040b0618011815030b0103050615090f0115020a0606 76
    0x80040e00d8182c010504114400d2001c0c800e018036020613604503940c034540054080034410710b0340000d04443d006958640201080620f01c21003400510080d20001c405480c2c0c8400a14104480508407941c001d01d07950714500054680d12481d00d0140e480f500c10441000903c17410359418088610036142180400c1e03010401d2040740c2020411070441001c280c1d01e200312114460314105a00440d480703503143c0013400150034402d09116009003003441d81d180805025a5000d4070340a03018086045501d03000c0c41c401c400c040c0356070003000e00030303402690050091440d013030500d01844070039400105410780040d8400124400a00d00b084214465030040351048114245042040a03441d2000d110340c41044902006109182840381d9170070506840341e40c0040e60b40c6a00e608041c4015561748041c113454648400041841808070740700748907510030303800303491815040000c01400300700958404112100c02c0c00140071b40c0880514100c0488424012140c0b42001e640c2c40a06440c0c2c82e4110400d0b6084254402d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 153122553 1250 153121303 153121313
    0x140706090c090504020f040b010e090c0d0b0102420a0905060c090109121b030308061504060c020108060411070804090b04020c280b010602010903140a050f07051e0604 73
    0xa0100d00e0b40501290605800048102c1035001d100761145643e00c0b00000c960780242c0341c4542c4408054280b1042d45402254503809804c40e0005413440ea050072001c000303640c40442c4c075280c042c008160101c000c202c01d54000328140c100030901c501c0031420081210707100e080c0800d0240710b084240030208480009207403040c1003c5001c0c000210140081c0451030742681c10080c5002603446c464149060424a81070041d02c00315007203103890303129502c20f0380801459808030b1801e2040b10141c40ca04150030b400250b82030584294898030000a80700b545410056220340005a0400e0005101150500841405041d1a13110620844801c01c0c00a02046031403461302480202c6e20782214110700701050014055140c50106456500091000c0b014006051300703d414010540d0b00600004038035a124000640200365008081d0003080e0124050f040c100c41c0a01114034802d102d9540700e05012031907040c3c0305180c00c070880441f00f41c02540b0604200e40701d64503c1e00008190a00208400e04207802c0c8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 153123803 1250 153122553 153122573
    0xc080a12091b0e0601050f03041511030709050306040308041202010f020c010606080105041505010c051501090603031b080d0b06090402030c041802070f020f010e040c0e030d0503060306041214070609 87
    0x89401035a1401c01451780e0300907003500c510342c110a007040d0b5a650f480c5401d00e00c90762840350035000503144c0301c01210f0b21607680024501c81d49140c0c0350004142d44800c06c041d0f0b503150444005001411a000082c00110303541c1350381c06419030900021498144602c031240c03d0360400055180395030755611041010320f9018110600510b0296400c004400d014100f04603000c0303c3d07014039070603c400b001c078500070090104111204801d51551a025950b100d42c80500508050b10040d00014020b2448240000c03601c0e41c0b556540794000320a6140c00180c10103100544030780382d2401e6012000b400208080d4440c1c2c00154468021504030759603403402c3c03203042d107450365581400300b100501c18080000024140d111503070314a90110340d4031034003080080048400c003198200503a0450b0070402944020707504003207103820700038084080d03a44208001008442a000441b9150b61541c072940110340803030b000700a110361502403860418501c15003580309103050390200004070b030355960715002d1f00107200400710 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 153125053 1250 153123803 153123809
    0x110609010f15050f01030207050a060207151b0206010e1008121b07060f0503180f0f010507030903020a11060c06090304231e1908010902030d08070c080a12091b 70
    0x100c1c040140c1401d020801c00401c4c0c0c140d4605140d03000030154148441041610003881c0d215009666030340880c50700e1880e90580c08070b101c06441c00c2003000c0c600d9050804020f43d00540c154001d080b980c0c0303424070004400c0000f401b5582c00070004030700400c0201c01489031009241c00110320341d82c5c07051900c125290040315184810183d4110b418140030b8594002c01c203060300c5645103040d03500c82e101c016002042042c0703d2181c044520414410341d04070b200110b03820301420000c0b00204138a540340b80c01036040e14184140180140c002074081c00018408813580e200c03558001c0d12031410910494081c2d4540002a50401c81c9a4004181007001008001070909014107a2000d00308159980020500d4060455a140b1032422a80b04c04169a161b21444010f4682001ca801021650303c07100c15000b051400c0c07003640a4090a21100c44060240c002c981c05540c00741d035010400291a141d00d99182c00046c2880b0400c083c4a000d80d00044440c0108401d25015840003010b40905203080b01100032654 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 153126303 1250 153125053 153125081
    0x50a1101050c0303011a19030f051506090d060902040203041a010f0311010e180705090f0307080a2307030803012309160201020408070308040e0c0309030307050703110609010f 77
    0x90081c80b51020040d241146e0b85413900070041c0e84050640300e614050780508030301425408612030b1806038560030990002210300c600b0409034403101d1004030040366210311181c01c0b0320304200c0c013441410003413441d14040780103c0000840c036440e0343c0010b0a903400de032000e444a100c2c001d2030b075107540034810550340100308100d8000c1200c0d1655841041c43c03144004a64107109089560702d0681e107500384003600840009041d0f0740785243c400c102526641004039614011b0031103150f903150340d0500190303c00580300200000d0503604415912a06d020401024a08900145030b500b111940d20400039400034521400e001c40d12507041c40400d85110011004103914080d601400c84075503105e01d0101500204a07840c0d10202d02141541030380039205650150065200b8450000305010717408011b802915080016402162242e011190040c0003d4501c581e0b540c00800105880d540030b00001c107403061183c1421010f0b45000e0381d10500789881211007004a94440b00c50841100103171150f001181518 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 153127553 1250 153126303 153126307
    0x605011805070e06070314210c090904110d020d03030f0b06091305071202030411040b010203070f030e01051209010c270b0711120109060506040c09051509032b09050f0f1309050a110105 81
    0x24181403001760002e00740280150150dc095110310310940109600540345010282e01c52800400400a07401c0c0c803940107150069460303003868680c007100c0d03064600906004100e0070f4400d541e801400c019014030700b403240b171807001d14540a490000e544110f000b089160b604038804403c2c4010384003640350840c1150420070035000060441400d69005030340615007071401000c40001626248100b00142c0204c001d81d500f000b010070030540245d02d24404030355a030b040216513914a20f034501c80f1035041910f4101203440c18008600b1a03005003800300d000701201042520510003003080c101c502d010030031459444200300c200f1300211b0f004064120740e05440411400c0741c1070100514081307560165600c90040b49455070950785500342510000f480c01416203140700c40c81e10011488140390444402240e00170b0a4042c601e9010780c200c1000c030383c4040c2440101c1d200400400c03a81c80e440c028095409031402480400044442c490420309512400042420f002d217408e0108130702c1641c43c2424100401 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 153128803 1250 153127553 153127567
    0x105210307141603140d03020708120a02090a0602010f2d0f0e010e07032616050f1204081204050105071e0f0605011805070e06070314210c 61
    0x20000486500d20b4002e440703400000c44400c145402e2254a8482d4410304428103008800e204411012401d5082c0200807038070310360310101c4142d06a0040040c040c260fa03105105403001400d2500b0310560081040c4401450020081c0c0065644a07550300301c0e00040c1e568055015046003940318064280b05404030380c04031200707403810310032074258490400a00aa12041c0990220009400c81340b803500c2c0b004003e11035080c08010040c0d50345030703502c41500c1d6002c100c9292820208042502c1072090250900075190000040c400c407441004908c048500d4405e80340607000c47e0300184608038107080d81c4c40480b030707440386000c83c003070f141810000c07841d0325040c410031080055a0b00042120001c176408420003410380c00e888564151099012000303130400b010318000d01c04121180d0b0110b816540081200f1101c0300b100502d51040f140110744100110300410071000d481d00e0100040c20030140b20740b61803920511100290b07620f41c4c00041216581e0850141d00b0b0034891030401d0701a0740860b0000d815810608 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 153130053 1250 153128803 153128869
    0x70f02070b030c0a0905040f0b03101b0818100609060504050c070b0402030a060603060203072705120708070801060303080105010c0f110d020603180118031e180803030105 75
    0x120183c4403071140301001503a40145405000709400a1000030f208010803010100400050585600c10b548280144044e400c0c0e0b448a501c034180f000d40343c1121420070070004403820380e40100040c1c844c2581580d004502118014100810409181d4140c00441c215241c0307042d5200f0b6810b941c1126102d1420081000203030381e00f1609540707a441c0c00860811058a41c0d00100b41171010182001d0142820100c0c0070013841100d07002580184040d503151644030560133150031102442d030b03407400c0c000076159108121030b150042e0a07003041800d03031040d20b1075180d4541945207010800e600621071a51501410000d1540109415005142c2070030400d090441640d120040c040c03072004000c1070b10740c800c1442040340e25172000c0c024060358094a0142d1301c3c03d0001c00070083c061940500d10341582481303520740d41040002c1140c0306d426419140c4c184610381000d0f00c0c85402d00800010420022852141c00c1d079038045810890040004001443c0d50754109002e000c8824041d60059240d007558030f1f80001560 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 153131303 1250 153130053 153130057
    0x1020601060c1e0303090209070806090a0605130c09230307090501050102030406050c030409020a080414120f18061204060f050403051b0a020402040803040e130209370203070f02070b 80
    0x540841c40f801e01652451130181c00400894001130342003d2a030b01081012a0401c13502d900801c821620140f050f501d00c3e48050995006014682d0402880320301042c000e6100e81002010405905101c4c00c010f4440c44200f40c0004201c02407000d1405440b00103025083c1403140c40068242c6040500056040c400041c1d620b00c10744c8150000c118000031313a08503566041c01614094201000c003950703110400741d40203009110954040e50f4600a06909800d40800040d00c007c841555240240c142170140345001d000c0e4210000c110100501c0707209160043d91030500600810b00000d00110340380c180b502b054006c42c0d41c10103042c100146003500380004250400c007070b200707007418007000727000b10305c841c003030401c0c105036640700000d400c20300114022444841c08000b4000340d03505800c0a007000d51b0307034480701e08130f05011800c040d40120031600442c440107905010030200c0d800c0700383c1001c56201c41513995424818201440c64100f64084240b0040580c0007401c00d1030803a03284014a00070b41400b008001d28 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 153132553 1250 153131303 153131333
    0xc04051815150d06090603031106010806010603020705071d16020601180203150d0302031b0c281a030f1e070509030a05070315050105090f0105060702011202071101020601060c 77
    0x5035200350b408285000d401800ca940301012980700380051603480c00100d000c1e0900d8007080f0089080300f140d09201840c00141c0504a601c9500101550791034000203400075480708009a8850050720703400718258101280401d0004030480060b0070f0b43c6000da80601e00c0280000c603010071504a80c0042103d00d142508140c0d0034140404010381e03980720400502900d00484914a4200960807c0c0805141e00070025040c82640d0302c940c0201c00c2c1241d641d450b1122038070610300d46d0004000c959024116a0760000a140000c03030f01a424403030340c44100001400c198194003c40601d400000c02451005640d880e9801081001140d800502c00c401920b890840c010250820000003152000c1b280d5400c100707000402d5046000d07544410307100e00300103c480001400d801885814940002042d04015002d00d04c40c0300000c44d4203038140d090208020342c0740c0c002081039040154900301d01842c0c100340d03c001c0c01d241c1e110301c0103444038118607400641016816444041800180c00081001c00d0358200e00758a4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 153133803 1250 153132553 153132559
    0x4080c010e0607021c050105090304121e02060d1506360b0a02010515090402032a061902010507031e0b060d090302030406030b0d0c050d020d05060c04051815 69
    0x4103201c070804501e0a000e4083d011750f001840c1c101030146007429201c1e94018502a000910840d82c900341182d950744668031034160903044045420b80821401d0240e1048003085a40d081041030701d5400180e486d41018218008580d9651450b000388502c0c3c141003801403001d41014009010520701c020307100c0c1440310280510928a842807051506c0c280c00c0300001d8800c0001898441c07000d0f2000074000d26003241e6140340200c10100745101c51801351002d5203d030754020300520402840d9840301c0481c00d03c0b412103450501548010003650743c0c440b40907091a074007074031f00e805010b10000b5000b829640007500d80e1041c075207008000e05c0706c08450f0001c08100041b8000108000b0054008107803184101c105200a07645412420702c10168044002c00c2291404d80e800d01c0002c20301d0301003141912103058018600c40c1010350410260a140702c09000303980c00181264240710743c0391250341c10f00740c0454090040400000f428001817500d1a4100303941c51000c5440c400303600c1d1640c00620381c0700301c0e203640342d01c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 153135053 1250 153133803 153133817
    0x1110423010807140c0a0501020a030e16030f080703030e060c07050c091005060715090b07140a0906080a020706330302030303130f2906061306030b031216140304080c01 74
    0x202175404000151002d0342c00b000031507441056000050007000070341c43d154a03502480e0440044401030b00042410340b50030443c0300741d0100300d9076101a00c03640120011018140c4074600c03010100c03020b1060500c00c0005506080d070302c0f240da151007824a81c9420381b140c4960340748001c0c403417500003496004c1e003514802d5a03115920310807418642405401c100c4845030150a203c0c0901c1004206600c445c0942c010380c5400f1410440901e00890310701900c0c0e201d0001805180c0100111403103010390340c2c0c021b0385070303400186060011380354902070b0b81c81401c3c0f062a288010644015501c2c01b04000c45851801a00d45842c66043d5030029840f444050b0012151074000600d107001d00200440240c00c3c2e6501c00101180c407143e103072083e52584200d0404c0350b069411040000c0c01c90a00380c0c11940441c8600c2c2e0328045140c00c00b036042d0003c19510a0007609445040c03c03418003038003480001c188032040c05041c001ca0000900e03284c840501030b8003000c405a0070500040200c40030000d034040c4140400d00b4402 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 153136303 1250 153135053 153135067
    0x708072a110105070f061d0a152d05041b0f0e0601090e0f060f01030513170d0c0203091003020901090b03061c03050901080603060919050111042301080714 68
    0x701c181c094290060600c40664605c035042000a40c8000b080102c2e01140030b58800c1200c644988510850501400d04599502c0d410380e0290750b9403064116035a4003480d032110f201348614010700c0040682030540d003d035492061005002c0740c0501c00103610340c400e004145441c145002e016001c4d049100e81e1150080140c085440c1d03030701842004000e410201410b0000d4505000e664205c0c88007928424051800000c2c203035415482401101c1c80707820841242800906c082d40c030451940d12442c0401c3e090301060101c0c0340c030282680a071041c080a00e90045841e90100d03000c10000c460900c503408241441004080c515036044481d14080f940281c0c0440d88941c3c079440030610340082e401c01e14411609400241c0c00305600301001d0805510284e0700c0340c26541c1c0f148181a9618000d0701d84c421203512060103600c2c61034404001d02011440b580c0081340d10760707800070141c0103a00300c4d810141c10203100c1e00b03004060760358590034002c90a001346002000340c2091a401742032041c0d90411046102e200141d59 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 153137553 1250 153136303 153136307
    0xa1401050a141e03030307020a03090501020604031b03021e01061d0402030a1509020301020f040305010b01080c0d0e120703020601030b0901110322120306050f060306030c01030e0f060708072a1101 86
    0x54160b240090141d036520304e1f1060b0021f448550282c03040740411007210700424075500c0000c04612aa625840c2da50b12101c0e4986007000007880b0f260b0440031803141000c6120140a14101c2100d0004500c1c008500d2505007040c0342c0f9080c504900691201c0080410040541d400080ca10342561304000d01d03010001c414652000900401c110284d01580002001525244004010b10807640100003c000c241c0d50180116103001c82699003680070f0200323010003492151954842020840c48200316644150008214545030f00b00c0f0405901507081540104180b241d0400d040b0761003d6520020000c0007424180c00d2518000544034035145844e0010488440d01b40b414000b002982001c40320441016010b801400f80119001d228042e030301c0d510100036079041080c2601d0103075600070040d10105105800450050400442000b0071348220030403414410750601420703000310200d548412207803601d0745010306901c00350118509001330307080f084080d1010001e180c0d000d580e4030801c8000d22070151001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 153138803 1250 153137553 153137599
    0x1119020f2506030b0312031003061b030e0d171503030c06060f01030207080904050703150603091e21050421021c0203030d05060303040e0a1401050a14 66
    0xc100035500ca501d59008050070581200c01c2035480e01258001095140c0d0802c4040d14214908203030950320465001682900c0c11001d5076012050103424140103a480e241d441c20750340d6441d400301101180107031503480107525020707545020700c1200007040e204a213150300801e001d03210304004001c5043d200c0840e00c02500c0310281c90b1500401002c403a02c0b10b4121801d99201c65080d04c22510a0100d81e4a540495010b03000340c40d5200d41000c05642001400801c0c40050000100403108140d030703811180104080140d008006855555000604024646460b4541ca6080311940207c1e0042c00780035000100701c003101c249840c402c1c05110f6105a801e40c026039080c0101c0d004000c0d04e0141d51801d20681c540d44003480b10706070003190304d0718020600050020707880c00e1500c8041d4040d002042502004501070b0840d42d080000034003200e14040d42d6110305910444181c40c80400c8948403001e94144003000c1c41801d01500c0200c400004041c689200b4064141e02d0001440c017071003c0c4214100300d003400c81c171 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 153140053 1250 153138803 153138823
    0x30906270d0302010c0207080c030703140111131e03080403020f0d14150c0304051203070507290f0603060106030e0312160908012f0d0f050105030f01111902 69
    0x81180010741c94042c2c041c2c4810961440144224140000c4801000608202d040d0b80940907194890564031243e10280c0840c035440c4141d901c400a400f00600c2e880020081d02a412042c28006800c244a01031180a5008292440c42c648941800070420b4007003194102d82e4126201d0011000940100c2c40703008240c3c0c2c4c080c0110301c101200c02c00c0a000445e940b15001601203030324083e69202c12062045001c2660098130315404804900c0f00d481c0c80600941d00300701d1038104107003041038595805204082518030300344840c550520b41b8000404005034107400a40041d0110842d14060010983e200414400c4204040c0c84402071800701c0000e00881d40314614200d10600f282c03030040c802d502c054060300340810000d030800c0d100040504041c840d0f03d000c6000303158540c503480000707101a05020a03484075504000c404001d8080f0003031042c0309041c00078982541c089042d40c501000c00d410040c041c107041c542a414110b06688180504045440322002d1442006008500c058100e00d4810341507 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 153141303 1250 153140053 153140059
    0x60f050d0b0909030912060907051002030409050702010f0b040c0804023a020306072a0201051207110d030b03071a040e130203061b07150f020a030f0c0203090627 71
    0x8428002c0c0840007200400c00500250b13421000e03004016269035072900110341100e40c54001270b805000a1a00e800410040aa20320441342003d8886440c602100c00c16110240541c1d0754540c1c20640a4860140040d413110480b401c0100070102c030b001410100005000a09c6400c3ca81c11111500030070316200a0035408000485003003100c00c0544404060001ca816442403140000040c00b1910440c15007440400d90840a00c9070b241079a02c5100d003800b00318040741032200c18011078280740345945410b44070303042d2070352a03503554100e21318020308100807000204105800c24420b04050f490008401c02161001d101e41007140480740042e4085001e90780041000868120138807015030364a11041d10308074002c8081e91015115442d844071043c52413601b400c52003500380182c80c0440c030314810841d00100100c5000c240900b508606000300c3e8005124500403c0e43e80c41c20044460540c841d01d800c007003981c0000c5280507528000550307a8090342e4000d014002c285006090f0b0988c49840c0c16400d10809 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 153142553 1250 153141303 153141319
    0x60105040f0602070f0f0b04061b15090b0a0204150509030106080a080a0306080a0308010506030403031b0203070302071508040206070609080a111011092707050a090f060f050d0b 78
    0x2d00c4029182d401501c540c0441110019002c0340200c800c845c200105c4200d00255498280b408106840030402d51065011001d25a18110007040c0f00d004d440b0007118500b140018040090320742070040b0745020305207400c3d00d481484188100400088600320b08009420115280c080600c00a400761241c2d8010700440c0c0200c100203400c0003031000c05080b1285c46a102802039684440e0200da0743c50714141c014000410400c01000315092103402103030058040e280109000320b41088882d403c4000640300300069200061000c2450b03814000103001e0802040d0003203d07074070402c0004001da940903002070311640e40011040e04000e07141c1e003d48060380c0e0111809803110f0701c181c005000450300b40c40c41c0301280581d11220907240814405c000b410002d50381d0309804c10030040b0a00180403420003000c01c5540300d0f40360010700303000803410355427051036255101c5680340d94a54004040c90b540394060022000010003e10110381c0004031000c180101d4a40941c0300d078402c0d1800b0b4041e260040700c168102c2c00d4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 153143803 1250 153142553 153142559
    0x50301140a23090109020703020d03050c0d090b22110609030a05070f0501120504020d03050d09050102070b04020415060206071d0d06200f0405150913020705010b0d0503070605060105040f 82
    0x14a20006100b001118038000aa036214400000c1c1e2050a0004005820114030402114025408a03420589005000741480340324001c55049278950701041e11b000e00c00030100004030049800b01d000f034000142c1138600c150340940e02c0c96071152201281520a030307400f20f0244031a072010001507009030b81007000c4812041e80e034143d4810524050081c2070018800c0c43c01441d5080990040c54010341c1d0203001440392070f072651022507841e086040a5030041e61900d41e1a0007144090019000d4240260b030182e00d01c0c201481004200c2e50042c00808032911108810005690003141c1c442c0e10640d1030070311170b60803060040148002100f8041d665440041c4014141c1484041e0f03020401d401054a80160740c3c002c401b4507001c81e8001d0b1604e402d60301c007017003009100074189031016109281c4003681507401d040844c40081c4030814044407001c1501c5c4c0c0881e1100511500340600f8610034015243c060484a4580b9040d440c2e119001e4054003d68032203000c290380340d210310221001860b2801401d284251 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 153145053 1250 153143803 153143849
    0x303040608100603060620071d010e010801090308010b300a060b03010b0901031104050315041b12030806010c020a06090303080f0603030415050708070f061a01050301140a 75
    0x806031412040b85034406000300e2450300901c2140183c070000e454110590706c004200551160460107541158014424001929821404001100c3c81030340c980400946c18907014050045050380324030426818190060301103a08896010f055981800c40b00e40e03104071480f500d4410001c0c1c8050107015941c0820844003005464901c01e00403130411400b449225952103607d02d050000f801000789040f01000311564940c0691310038007044082e210202e0509031b9680000341170020000c00d42c0c140c0d6424804002c01c020340407811854408940d4000c0b06060300340442c3c02407140600600809228445000ca285680a9901004c0700c40d03004080c02c00280c0c07941001030956030140b000f2000302d19600081400640d900c0c0e14a4401c02c0d018000310309052501c41c42c089205401c400000501000704900b40100f80b81c40c00901d401406981c002c40320400500d0250215200003a095a503c81c0031080c2d0303c51613900c01c040320f0442d845900d00d00309010924002410a05c02d603448505c5603510709590f2095030b4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 153146303 1250 153145053 153145067
    0xc0306020a031811011803060c020a02030d020a080313060b030a051f0605032e020415171e1b19090614030f180f01090c05010c0c0504020f070203030406 67
    0x60558007030140c25002c3c070386142d4004141e000245040201d0065400551044055190003c0b031004081c0250360b03691500e008840c0c20000340703001604004840390030b504081101d400d015600e03200400c0800c3d034640340d92000740000707031140507010a80003465040c00181d0f004106a00001002e941901e0614a0520307a00c0440000980609c0070340d44035007035945e4161181c2c0e0100c510280140c4804da00040000307004a00820100c0010b60002c010900c0119162004e00b02500c01031405205016001d54094007201040410343d0220303810100708940c001030700a80d0811446155010701160b1108a074130001c001042003038240721803012a42d402030088003c00c84858985685841c14080c0d22000221040a800900c00c1250f44080000c2010341e84002c6106034400b14000150008070186440d2a0800c0d07007007428001581e44420311b80b4240302180d40110b0041109003001c1c5452071407030f0345101200840d48a0301380325580c04210050724180c42e170201c0300d01c03d0703008068a968903110030004c0d01403 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 153147553 1250 153146303 153146317
    0x30f01030308150603060904022709060a0c021903030b330c06041e0209010b070302010b100c03050c100e0a06050703020f09040506010e04050108070501180506030c160c030602 77
    0x5540c0b0000b2603c015a100c8a415001d00060020b130301d141c0d50302c0b090019031000500101e0301f007408203ca14101c0481540c0d00103006d003441841e45181c0c1440076543d454a503000c0c2420005174501794070f1045103500051000144825900014018503a41c00c4c141d0042020088a03908010114140307004480c0020008820303600105c05008061111480c50704140030708014040141d21500200c0c0101d8039200940c000c07200007240c04440c900ca16404915801000c0e03000c00c102240103c0c42808064080c0641c001060060700d1b0361541d054200030040c043d04010001a061000c000f500460102091001030810f00c3c44400034000d400300080916901c0401c00000d48225282c90f000c6505680b00c2d0003254001c0311b44401041c10f0200f42c0f81040001c000c09482d0b1030600c01001c0c0c2495140d00c1e10301429008001c840c0240980350719103000503100030500c038440c41d00113101a90030721a559039141504e030044452038102e0385440c0f0030302d20802d66644410000d001a01112800001c002040e0020181 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 153148803 1250 153147553 153147557
    0x906080106080307050d0c05030702030a03110f0c1f05091f080705070b04080c0309120706020115080d0f090b0d06050103060605032710021801020c01050f04060320030f010303 77
    0x240b6601c001c1c2c56103e004520b001404c680010021042051240302040c00303240c014820341e403a0036a00c0d070009207070000002080700481e00415940000800170300040d0540d00002d005000f428561390006804c0150000c0030031140c043c0d4038012415640300d101521880803000e04000304006800003180101c180503080078000600f0383c0f0010303403031b188541d007680c031b401e68860201d0b09079803100e954020a80d00099000207003031009100d51900e603a100c28100c002c0c101c0c88409450311a00300b1074001c3c00e49003824048150448082420042484001440700f108029841c0000c01c50b0307070425045800071800c2d0300503054104003080c0756581e400075a001b001203400903241000040d42d24442900d4038081252048044005284d2036044c1660b00c88a6101601040c1c050b035140001640b0120226000f8040300b86ea14629400324a0055804001b400c3c1e40c11024200a07041c074002000102c1e80b0300c194011a41055240c01901c840e174a03c1030309210820326405000390b200d142200441c49248003d20081d00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 153150053 1250 153148803 153148811
    0x90614090901030f02042301050402071e0605010509070306030b060609030703080c07080c0d03020c04090302190c090b041509110702060a050a0305010b041a07020f040c110d03180210030f020409060801 88
    0x2d410801881881e070011070707803044c0031a030300c9c0c0401c1100a421180060703900600c00702280f4001440900680c1e00581328180004640d41040d041c0000084018840410f15250000c01d0011030740d01b02c0f401d903009000b200c42c0d0350b94a00c0040031a060041d2a030005220880200340c41c0c0146001250442c25a0400c6c4101c0714031384640d20170031800104d040409009a08042031036111030520341c0056030007500034011a041c00141440200032600f07001030650b201402d4480a021a030304600070400c0c80d5600720703414421b00c0b1f610441c04443c003a440c4100a0455540d0000b80003002c581c1c4242c43c1c00c030f17400a00c00c039142d201240c1b0142240e8080d05500c0002490400081012070405054505aa1000071104c3c5000c141c94540d5200b684489001d0b0390200c2c2c92100713040e0b00e40d980d0213038265580e031680e40c043c0441480741105190085440c0034006150a181281082040c02c1d46006c145980440707130000c0341402c21505800800410b0420900365000081c04038090305a5041306045400b5800200 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 153151303 1250 153150053 153150071
    0x1203021b040b1503100e07030c030f2c0a020607030906030b0a0b04140402040f0603090201091d06040b120109030f11010516030c02030c0708010c03050610090614090901030f0204 78
    0x104454041c003000d54407503040140345080f590024040c5911a43c00311281c040c407911030000052030340d801c842510000351a0203229000c190305024070340e074140c001d980c10b00a6400310442e00040c40c03c040748064221400079122078035220100a030f000740540140642c0d40d40c00c42418000c21030302d91800b40102207400d00c42c661015003884040703902155640e1010a090a0426840790300382140c0c45946a0f01c15002d120202d802c1100b078401380000c0103d600d0000e02000d080c40054078040d41d55000681039160031009070b00201002d89503650141741100c000560081040c0020030440a0140c81e2003550702c0c05405104140c0c01c580244ca030081075442c0e81c8600c10812011340e080e5003085801507000301803013060400072400b9821503519510140103517414064580f13603061400b03045038030004541c1c0d1103171128414982c25114441c0c00c42015641c4480d80c04107204e01504a9840e48900420021483c10684809030350343c0588520140041120815581d01c0c1426101c1031900d05007039105904d00b440300 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 153152553 1250 153151303 153151309
    0xd15090b0411090714030601030603050708010606030b09010f0618031b080c0d02010c0209041e052505090610030605060c01020c01050f0603190510180c080102090a0b0f041203021b 79
    0x603510480082e621503005017028032880c5002d40025280314107042c0c540d24007200040050140c0d10242280100004240e4500007000703003903810f01403280303000b501d158005100b10301140c1205403c0d00c079182410b0041c1a05d140041587d050340d43d102a141d140700c19035850b042035400c0300103011038143e03000b122100080c440c10411009400070000780810402c26a01005041c00c0034495441806640c4101c50b20000c1c142d04a00282103820880701608000500407140c00b00048243c440614485049c00040c200b41c0412410039021b01694401c006030704400307040394401d800a80182c5005440543c032880c030050668042d41041c1171000d06542008006034802c1c440b402c01e58070582d001401017020341c00420030300501c4640340006885602903400d01070010f401c18011020001e407030668150f050390b141d05110401c2d0307032941c0040010364010082440c240e44d03400d5142060f60780c40e40c000d550b1088081d140c8802d074070440d03000d03e400c515106220b8007819000314048804200080c040c200e404114810 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 153153803 1250 153152553 153152569
    0x90203010b07020d020a050306070f0201050c03040f1e020a0605070b01170304061b050d080403110604081905090405090309090a0908030f040812040c0f0b16020d15090b0411 76
    0x41c003001401e00340414005458522162000c55001501d070481d02c40c0c862002c282810780c1290040d010a400405042080e942441415030041441014a0840c2429074079050010340050f000742900e2881074040c00481c803084140381201e44d0003020280681e07924103001e05103400c40d00c0142c405100c90760001a100d80c055015940c0d01e030304040950300d06424103505884000c0c0100e1081c40744a2580c60780800280108610408030a5070f403900c1c046072900b4074008064101020308501140c01039020300001808081c240c6181401290840305e01d40c503080b100304c644e4080c01d4611035119080c10184089884080001c0c90600b03c15a50300000f5a941300080c000d892040400900701001003001586460803a200150031030311841c41030b4984181c0c1035409410400903a426600e4504000d001c00c00764044c0c02001c001415640100c1d8142102031465240c492007840b000790041c402c08040404212012101c144801074540b0200800c0141d030400044041d02101c040715402030031716009015207010f0781 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 153155053 1250 153153803 153153809
    0x10b030a1410090501021216020a032003070b100501140304021c050a03090528050d140609030d111206010e120706020102090a12080a270b1309020301 66
    0x3022000250360310340c038650040300520125801007003441ea0015603240900820309000303000160b02d505e00c0400c0031038070820141c103401c41041e154041c410925004a10291400e0705410a00034400c0b4082c40360142c8890000403007102e000c002401e008004150b1007a0307008980301c10310312545584420054800900f40c44041e55034420900c001030061800d00c050356401d02d04c440c0400d401c4c0015681300c5141400030382041303001c6051100d0501043c200000790b10903100b04031007110b4001c0c45148000310101c00b6802694015800510705405025003c1100340800801c24110345852800c262015160f4020803960340c0c07410704000c3c01c0c031003210750841580c0c061941e080c03e000d0303036031108001510300c462041502900300802c28542825500c003444958002c000f6034001503030310a5a0000c010b56440a03400c40c40d00707090001040740c040b804c040151202c0fa8000e040a10303401031120a410111240d501103085400714204010405155a001030580b1f4102c20342507c41650703d810042c01a804240 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 153156303 1250 153155053 153155059
    0x618070501140a030b12030304110109050f130e0303090714090106120c030608120711040203070e19030b0c0405010807090515070c030c0b1c02040608240d1211010b 72
    0x210754046040303850001d00d9200b030342d4140007841c542c070000400c800b1020a91a102d0031f400100800041c0f000f8a0500d029480c401d02e88001207908010025891895070012203005444150609112880d540d10000c0000707102c40440e520f07460300030140d603910641401209498040848440900d040440c0e401d030582e08640c0760400400c15000c200c000402800c18103904040e200ca0000074480c006100e01c7c00040180250242d4625660420700d11641d003111a03d0300542c81002008240ea40c17164449019460445513032404040c0740b940e010500380b982d08007421040100d03080c07182880f1a0390040040380e80a1b01d4a408960310b040d4162403409261140d96040020759604902800c20702d0014180c00c0d1113001c00d541240d44030b4444080c0c01032550040065008001401c121610070144450241e8040000a506d0b05041040007000da51000c7d1600488181c012040d014460182510711031b07041014080030307403003070712402c04503041c0e1001c40e1105c01050f61118600c01503101030040300000c980203 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 153157553 1250 153156303 153156317
    0xc141201050d03050d0903050306040b061606050705130608010501080903120402190b0f03070315291b060609060406210c080f071503050402010e040506060c030a020618070501 77
    0x41428040b00d903031404030440c20003204200d4140c02d140e8070301c40c45208902a40d120f82c0c0301d01c2e1040030720048a50822900b0710550051010700021109442c041714051340c8100d0114064440c60b405940c940a00e03503110030300f10102200403990b83d074849203c4e812030b01e00360707140c44207901c0d01804641c40e4421449144140c8880e031002030090305110842200c200c0740406818100da5880b4807c0381940c111100e1914414000000c0c00442c5905000f07280c078090350600c41d089102d1a10f805807448008203041020076a0202042c245645200002c0d914520303081c01d400d19243c03040ca960280c4660044818038411a144c00120b04c03181440e200b00015200d100c0841031110340740000d800300c42501c5000440e00282d0402c0301040d0071009120507154100c0860090010707600b025002603103003c3c0ca0001a08040c42d040400001d41c0c2c0c80030f04101080029500020f9544501011403101d224690114406120010342140e0080c0d002036083d21542640030300149010842c4c5001c1d4862755244229030001d070078 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 153158803 1250 153157553 153157559
    0x30f061e10050f1201050f031c031107060f02090405010b090112020c01020403142109130b040e0d120b030309012114040320060105150f1308010c141201 67
    0x20846120381d01c010103080090500c103a090f00841c0f00d9128212401c80e41100380c0040040d400d00650b0007030350728800c0300600040c0341105407082551148c071050303508050302c60340c6085200c1090411682c0e510381040c410301143c0e01044036980650300c0f144d80c0c0c0f0b0203145007800000d010540381c01600c495280596820300403011062802010b900940b41e40310a030f560811000000803481c1280c04250b800c0031010f400c0d510201070318580003d510840303c144840c0c0800a400c42c1d9600d028548c421580b00380780020f8082c54405c04540100000b07503400721180b140d0f00d11a120160840c1903441d048045080030321118003d9000d141e128000c2e4601540450888040d590b0f03220880d4290480c0c8610004001903442015041c08040b00030681e0142d02140d6600d044146040f05d02d4050400808084003c10072549004049aa803019841c80040c9880b0046501d00b001000c1c20304403040c5140c40c0e0664021107440f80300032802000282225004580400000000d56840c2029240b088030208000101c0c1d0386 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 153160053 1250 153158803 153158809
    0x10c02031c030609020c010e0d0315060f021e03190c20120106060507020a0905040302070504020d0609020408030d05060a030f12050d02030a0903260c13030c0b030f061e 74
    0x1000704a540525440d45004038030003138644098500da10b044400400d8207100d0b40441c6007489003d2005d002058140380440a1242094a950f000c580c8107180001602c500c2a400300c0c00d0000c045070010f020010840b081c041000004044e044240d58090180202c03204d8000507919007078081c0000b0915860003e02c0311711010408030ba05100340020340b8894101002184e403608454440c0c00600c00304402107484025400c100b45920301415100204100071300301510040c1d03545025200d010710440d000243c40b050240703181c00040040c4204841035456545a02c0c519869402c43c01190903c076150900284403032405440040889030402d02207080c1660988807080202000e1403054144641001000c000c59500d01c000c51103044281b800007078890b61441c000704400e13a4000245459085104515003055000306015042903074070381860f52310300550100028409182e880074001d103d100000040500e05d40700114450307030324541100315a55645040000001100d90f00400c40046900000c8480c1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 153161303 1250 153160053 153160093
    0x406020709090503070b01030506010603060e010308031501050c070e010e390418090510051e040218070c0519030507020907090905010909050f0105092a030303010e15010c0203 77
    0x1e406a0f0650703181840e20785400040d55802c0c0d00c2111340c4c0d4810001008016458840c810141852243c524003a500d1500d51075654040689002c00801c40000340380ba00c0c1c2c2c0288111400028084140c5024540e1030b50304010b45002440352441d80c03500c03500091040103801d140c0791018441c0c11005415034548102803034500301480c0700c600e0480000c100c08034269210020800003160b1140001c00c035860709260003828440e111540409960400c814071001c00c03051410802c0e804a402d000b16074070340e42c0f0b00003e5a001c0f2400380c41110103070300c40107000c00d4560202c4d40500795070007003084841c40d4869040501c040f80700c810001d400030380148808001031510702c0e8416006203140c83c080c3c41080d01c0c0d601c42000c8410a070f0201440b5030ba544003080400c441402404102c6a058008004600d0318203840307525200d402740d411f500989400380c00d81404114201003042c2c64000b030110382d12980c4500e10f10700062000e03608140103400d180d045c1d034025803103500325044081d03015003c0c080c4400d4081e42e0404034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 153162553 1250 153161303 153161321
    0x10023c0703030e070f150e061b0a1415011403151509010602011e140a0231031709010f030f0b03010f02041505160b040204020d140105010f050406020709 67
    0xd6112060b041c8000420090840505080b130000c420301480d2a01c0948090341c2090300c4820302134203201c1f015035a640c01d004d440c4510f81c024501c0a4901c008070090b400d125621000034050705038400548680e180006086030051510728214101d40d8031015100c170002005070907103906502c40c811054919648204113078000c20340c46031000d11035200c0da0001d054047c0036000140140e642e00a00d640b504261301c5c2c440754649000000300900815070101100300c40c2c0050010385850780003d48404219140b10b0f185800ca20365041d0000d850172041c2c0711098400e07451000f910910860528000f00d00c034014205d4010300c2050b111406200c035a4038055000e401c0000e0800070f482c4da1a0b14454182d04e0a00511003000070000006076114100590702d2101041a115501000f80a005a500c2d03000300d04a28403c5035023016a0f41210364892000802170310404081c0c40e0300d02d04140c5502041d03401010b0040c10b80c2c000345c80303031620310300510701c22a06406503110701c41c016031150004001c00d0f0709940c024212 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 153163803 1250 153162553 153162557
    0x201030c0e09090f060a02090604030602160b19050106140909060a0b04080616050a090905060a05060706050411040b0a120c030b0106050301170c090703150810023c0703 74
    0x84100c0d0400182c441082101d0ba04040d800104451180441c140b1045601241400007103080c0305905000c01d0080c0103e0100030200fa40c0050021400c0d40001102d075045580100c01d02c54034541a52040d01c00c221030204031080c1d50a1400108010b401034ae03074004801000d00ca0369041105c0301e0100010044058440381d0040c0b030100c1d0108a1041c8440203002601020300204528201038900c4281424418250b00810000340104686103a01603051000c03501e20140118168490000007120407146600c42648100e0000b040c008000a54011610980c01801100381c42000401400280d91200c01d0050f44100100424440300d400708458954130341c010303105403008a03280c0c1d4a0154031102030f0401702c0490404001004000c18115400c0801d030f941402414810804001003102070348080d0000d030516442c1e13582c0d0103401d40680800801451030344100c42d00d024542ca816002503110f000300302c1000380841d003034140303c3d02e110780754800c0c14025040d010103840081c0c88bc10306541161100b241 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 153165053 1250 153163803 153163817
    0x30b1003051f08030c0c0315040f06020f0403060605030105060d1e050a020409031107080307051c020309100908100204030b01051c0c0e180a05060705090a0911031806010e01030201030c 81
    0xd20302c4550300c0d21002034114803000350340d43c0e64260803c5140c8044580024481e0340035440080c01c00028041c556040b50703004400c000e010700c1502e0518041c0c0601c154002c42e400003c00d001061084680010b812100158020040354840000b40a0105400300014055404044000b801460300c412044075850044054900c1d01d942680041d09460f000c0c0019000a40c04000000180c01c007030110800514090004510300791645e51619200d10a21045a030180c64924505400c503000f4070440f110100c0080210180002120001d048201a40514013a0780f2404003101144011842114281c03500040b01c481260301e03000411001d40a00301d80005805000c8074280d00007800e852040020f401101c85d02d600318548111512000c503602d01c010341d810b40c080742145001c580c001c0fa4540e080307016032400554490880010514000e074030f5110100c110314024030459040c40030800345001c0d4921104070322080d04060b501d1595000c080c02091110b1100c003004100660283d40918004644c908282c5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 153166303 1250 153165053 153165091
    0x6020f0d11160b03060a080d08070f1e17090a08090d0f080c010212070804020603040212160303021e030f031302012a0201030509010507020c010c0f0b10080d030b100305 74
    0x50b550115800258800b07404411710485140c1203280c01c015082400c001d0091140025004040980107480c0101f440313001060030820300c3c4030f00c143c18500c000e05881032841380c0429900034400c2404050500710b9034803110109101341c0d80496082d003c1c942211526040c140188200000f003e11010111405001c1003110300010f035829000c0c10414001f40001a00c80a07460300009408070002c20810800052504210060b40d03803405803604150151035403c401e01240340b0207441c0c10300e02451a841c550382608000300701580052007a15400c1301003820314010300390784031950303403800358900c0108118414000540046910220481c0003401490100c2c80d009003a03000c00034856030702d00141c1c604506040c0c400250358150040540042c10800204018901201c000b03407100400b1039002d0412161a50605c148030005204141d025080030411006040031354032103200d8041031151aa2601801c109c00b002103019101d042c40100c0c0c080d0400b0b4418014441c2200180070081180300380c091101069 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 153167553 1250 153166303 153166333
    0x3040f030302030c0d03060b0706090311030c010f1b140a050702040204030c050405070c0b07050c0a0501020a03091a010e130204020d06060818011a0432010e0106020f0d11 75
    0x1900003140a03070061a911280d42c4102810020b00b4018801454102541080002d00c080102c4002e07035000140015175200a18080703e205511084811480c44003086000007450117601c1211030316a9800208040e00302807440e0350380890005e007480301040c41050100d25500b031000080520b4842490a24541115580002e04a80003900180c402a100480900003410315110712038200c59a810300c01501e01a607a120170341c9110007403007075003044408181501c4c201c0d020003202d4a807030390060095482c1ca12400004005140c6000c06450040c0e080845c0c000203400021054160742d0040c40000060381ca080c0209407a84100780b08a03041a070811100d140350ba150310450000c5d10050783e400c0e0082c1002c2071109141303070300c41408690a92604179030030b05010340100315442c2d070801514007192a619060b0a01300d01d070000740c1105404443e045000b10a0140d008200b8144e403040c0302405516604c07104100e036508406211041540d11807200d040869002d5410025030703406030b10498010044201c00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 153168803 1250 153167553 153167579
    0x5060a0503011a101803061a09041205091302030901151e030210111614040b0105090d0f080a030204063b121605040b010807020d1805100e0901060306050102070303050c0304 76
    0xc0d2030b8946e0341c103803140003480e0a423801404000103c91403103441c01e144d1030b800380301158038840744140200016603001944401000401e40f2070489011901e81c036191101c2400303003038200c03131001c1e041c405400f0115801118100101c510b40d02400c00d00265800c1d503003403040800d1488850000d00000541184400740d0801080000001c0000c02c041c1003464046003100c03688040d80b42a10179411310b4408202c84c0d03402020b55007095002ca903405002c2003142009418807202da800500714100015030050040d805400a1085030003031340d60700740785c061011062088450141c0c0340094002c2200b40c0c0150060a590783c0380204100204003a0410710303054130103071030904042801502091000320400c0b40749072604c80d101c28581e00303080c050110321b86804021f491782d10504180041c401d2000d6100e03100807241d41d0080c040c05003d40b0401d281491400080c1118003c1002107104040070000425080d121b405050100c807010f8000300f201c2821650113441c540c1048034014420710052000088441d200c0c07038 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 153170053 1250 153168803 153168809
    0xa1a07030603120c0201020d0806100302030c0403061404030e0405060a0306021804020313031b12080c09030a060501090e0f030306040207030c021504051503060303160201020114070305060a0503011a1018 89
    0x4034603204010a10001e408c1c00c0b034244200f818008028200822901c8403007200380c09110300e01d00140e03296207e0700600d84d6800b95401c0509540d01c1c1c0484405581c0455441c240030390700170b80b03032140c415600d20208020346208131016a040020750104000040c2d0f0358000d00414000c5e03125458036080c0981c0824101c2e003081324442003160380781c0104001e050b0001e080145400b540d00300001003030504d0316003aa03c0410a450038042107180c074002100c0b2215502070741c1c84180c1c000c0c182da40c6600c0360708007207010300420b0145c4d01505240c40da154015840024000f03004c035407100e000d581107558003020807000b0b40103e4000d40900c0700801d4584010783e101240c00e802108201541c685890030310040c060801540c60303d084200e9820814055256000000e4030003041443c07149486003815803004034050301181d00e500300214205018070850039055004a4882d501c203960310b00740142d0301d500309420785440307507422580e5000e800c804022a042079483c059400700242840200c1140c04074804a05000703a44c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 153171303 1250 153170053 153170057
    0x3090118060c1b051e07030c060905011101200f1b011a0d030212090402040e0f01080d050f0906030604060b0d02030717010501170415090f060b030a1a0703060312 71
    0x1002c0084240c100c0311074418202040b10f40300780840541d8800d5a6a095001540410700340310203502e56a6004005200180d0f0703100604241c0d096403080090440d074902c0c050f09000c10303100005403840c8501442080d003442d190900f03115010707032511810030040d0f0210035804007908080040c104031048001001c0c40040e8200e00010b44403d100c00a00c0c2c0d49210b94800342e106090103c07100d000f2a5000a03e031148519181c105aa81c406000c0010b00a20455100ca18940380703500070090100384c00701000b8101c64007031060350828404908200c802c0d2048a180c03480b010024003207030b101c2c1c2c10300c00051a404040900b0000d150b0761961001140707600401c04030075200ea000020428910390050542c03030304807007200039981c02c2d5040400190200305681c881c1d001c146038810000d000d0007200000c8940f02140790004001204160911105040d088001a10b07014280b610007490380c100040d5526589420400a8041d11495909242c0500340586240c3c1003507110507010003c80c1505000714103005841d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 153172553 1250 153171303 153171311
    0x30f10050a030f0b0109050c120606090901032307080d05070203071e0914011412011d1e0d0e0d0f051b030105100e0c131703030106080c03040c09020309011806 70
    0x925040c0d04e0340d001600708810050602c0c09100081c1c0149064500c202070300f00c8501c54950300d100106915005420380c00c2e902201d440000002d01433110040701c0e80c15112000300aa4800c0e4207242d5584412900c60010039074000e10580d40c1292051010b0506603100406882c4003a5950000c06140c944441e4890150300300c1001c100304401280c40395102440011714201132035031405414403010007800c1c601d14041c10500040c8070f0b04010a500c000600b118848903507400d4554003104075030700d01d01c00803040800100d00d020629006d00008d66050b89200e41c1e03440480c1c1410361001c0c0070ba03804132604112800a80c500044001580610a611b003d4040b540801c40790741603a4105420f4031f002804641c00404200420711003845c0392000980d000340c80b102c0241d41c0b050701c40342000d0400000c3d0300000401c2d0603408130f20074030403000c0000e44c100c0d046943d4000c401e40740c400e040000da22060f10010480510070504100048198000d568000031101c000660311040600c620581d4601c410200d42c500d0396 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 153173803 1250 153172553 153172583
    0x50c06040c0f0602010e070b0f1207090819050c120f032704092f060309030a080f0c03131a090a0506100b071518120e01050a05030f10050a03 62
    0x41200c42c14001d0065200078011012840c008030746078106400340320120000003035a890461081400c880d035071115141d8100c403d1810260060481500307015a0340980604510884041382024200803000d40100250241c1580d403800c100f904028441c001029000d000304010392008280040d00e03109540c0700d080340ca814040c04c2003e40d000c072a030134202d03c500c0c82c3c5104c0c440460000c0401404203180c120035103035445051980c0c0300340c5e40c03413030a50580e2248001040140807030000c0003134030001c030154440c560581c03a501c646e07501951085514114902c400c0c00050749002c000d1a05800e100d0050340318140c0c0d803851042114201e04100d90070f10a030351240150b4001c01c01c0030002203a1001ea902c82005d4543c0c1003030408003070341c4100b400c0505484001d00703454009a1843c0c1c8049800385200c08004100c04140c68422040400f1112c200c0c0030800c550204201ca5003e18100d030400c613600e65030185503a407421000004410040c207400102d4100d40360100b480e4541603107680145015145802200107 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 153175053 1250 153173803 153173819
    0x212120606031f032612070e03100f1a040b030a171905190212091504050904031205070f0c0303020304060b0918070f0308090108072309030f0109020a090c050c06040c 73
    0x403a80c0446075a000003000b081101c021118007941c0c07c02410b10f0700510710740c0c0520000c0d18002000320f2600300d1926124015110030810303401083d03030744141d0799002c2401c08910208002c581f20000e0740c0d90550880503c2d44001140d4940641100c90b58042c401e091160701400b1600320300e044103005000c94030000b003081500f0300030840c261070415070380700501020030aa008800c650213413544542c05001741c1d000b081480c51000c3d040d20040d10340600a1340b550b241a04006101d0580c440301240600d1030306000c26021481000c10491444843d20349101c20480d43d901240258001001503030401da4401c0102960742c0c0e940c3c507980c01000c0b4901494501d1207400c1e407280c00c0c41e803e64001d02003192000790070000a80542c0a8412850302424005440c1c0e1303030f82c1010303900800c4240021840c00031401002c16000890009008080d0040c0c0440d03507000c1441241500302e4055460103903100a0020080013031504e035402901c002c00c0c1610300941050502a8140d2500000b9201107441d10141481400884 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 153176303 1250 153175053 153175103
    0xd05070e0111061006110a0b0f071d060a05031f09020306030c032803210911060711090a0905030f040303020111040f030b0709031a0105010212120606031f03 69
    0x202c5401c0030f80b02c3ea0510b4401c08200180f0383c4505401d100c808015480e6452043c48080116a0040404011480d10641516406404580160125105006103081219405107000f1141000390800340780912080b002c2c1c400b038000503d03004a000d92080c090722580c2046054100510f06520090380340d0070004109070401c10014ad10f03d010f0f50000a2806d00ca0aa4441040b10720f030903280f02c0340d2041d40509045400300300301941505000c01c0041c2c0c48200105940c00040c1d2103000e65021240d00c0c0500040107014031400c0d00c01740007032030301175441d40180c500b8504040d04114000400a540b1580355100340c21078010b03415018401e00e010900b08281a0203000380c1c25007912402089150a050100c440030100d21400042c0c20140000c00007000d450265001c07502445c1c2107028024414004615840030403000d000d400d005000310703004102d80d40d89480c00e458041d140c0b11190760039540e8044c01d100700c0e601300030190300745007161502250303031089158084005140030301800c44603090080e80c144945 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 153177553 1250 153176303 153176327
    0x160c08010902030c0f0103090b01061e030203061f091a030103170405090406020a0311030a090614070527090f072703030e030708030c011d071203050f0d05070e01 71
    0x503906120003031006990119414160190440c0e011854400c50320048009008022000345100c0d107038000481c00503003085040001c2041005060311000200c2c008a05074042592034940004110720300c030744a0748034074516840304100b40c902400926680c0d10340281c3c40c00480c1440004a00010040c000d04c50501d40d83c11140d510041464a402d00d090046282c1100c02800540505da0128203100d90900c01d03040119140c048802068490500902e52002006108000c654291402c4900d5450102030396101d0704c10741301c2c2e8454504200e182e040440103407a00b00d055030f9280c000d00ca20b460282d40c4152401c3d00400d00121901c41038604030b500600707041006030420005458000705080e010900f12810010b481d030503e4440414290f03100071900d4909030760450380482c00f0100d2038100900d015809001e0b6140d00d0340c07441c0d0b02c07821501c1c4088d4640100340688440d0b02c5140703070b0210120780160024048100f500503690b24002c4811618011124140d13003050000e4010710340001150f074849609150 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 153178803 1250 153177553 153177569
    0x102130611060103110d08090a090e06070f050406030f0b130b1005040302090402060a020a0f0605090c1215130f051b0105030f040b06040b0a080c03070e0906070804020411160c 77
    0x2d81e50460b00d034640d002808012852151201b41c85500822141d241030702e255440280085003071a8503100c0c4d02c0064030514a10465074455100022401403013003d0913540d0315180c0d184c20746070508001c8120301a00c0c0714a481000c19440e0041c4421716101c1000000c0c500365041c400203a0790104008118070240b58015040401000740018805a5505c125068026034100ca6055481d100c100d8103130f0400b100310704040c1c0341d00c43c6590030009000350f981145100d43d5441041c0c411040f107a604020320700300e14088411465000300311081c61a14140100e68101d588142c0c615001c0100c0d0b41c91a0110010342c0d0102e440360049a800c205000300c821068030200780c2404c125043d460a00c1c90341520402c010000b0340002c0340a00410201d407199070040705607031005880415004e45910b01c09984c2d400140945010348a888800200c01d01204042ca001d10307c04005084c05440754002224000d8003d84280d034050342d20420000240740090050244e0700b0442032480550401d800e101510700c10aa000b018 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 153180053 1250 153178803 153178813
    0x40305150406111804090c090527030c060c03040201200d0e040225080409090c03050f01090224090a0312020106060e0102150a0b040203010b04080105090304050901170f0102130611 79
    0x3104044c0007020590003441a200042c00c0400c03801c0c1032001c0e0f0719030ba0000341c1403807402091141980e0078441603206180310040542e030114190504564903c81c8810244407030b0400c001060b925203402c030095070403900524000802c0c041d400284445001e540105100f41d611000c100078a46410807145400300c10300319021401c01c00d2001c0e95603900c4851203502c4050031064000c2804215240d0250f601030600c0c1ca07010407682c121803625440c013051038002990b4030302c106500c2443c0920b050083c041d0855002d000c003c00c1c1045071014012028803a0110301c0003080600208042d0307112003071050004c0d030091110342c0e0302d02e2040350003a0031500075411000800c59400c6415159917000551100058901d0a07d80e02a40c0c0d02c4444000410030201d146038070038000000003810304240f4018205544101008000640707980955607503d22440c4a0035800040d02001001010300c405100285103001105035003a070f0018480e81d40c00c907030042d18000400030844100f40300480d44624031020b42840400100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 153181303 1250 153180053 153180067
    0x30115030c08130807060e060a0c0e0609060919090c050405041409031e07020a06050a120911090405030909040b1b0414040e03040305010609200304030f030b01020304030515040611 79
    0x182d0340f012564001d48495030000300c180c20419a90f00c41c01104000d01c00340c0700076003040d110703401c06000b17034107804030004216006a00840ca0f008041b14035161005100d14544100d070824000c000251040440a1607002e840008284200f40a040620144c50b039a1659807400c04082204a5007800201c403040d03004402003040b19100041215100070501c0404461b180700d0058800891050f464000c4d00245580700c005134094020015104080705038130f501805c0000703000002c1c101d80220348054480d41c1041d0304107107907041103081d00d034220f4050701c2540e20301004040850340f200c2c4203603021516640d9884c100810038459407041e040b007a01042c986840c1c6490440001c4030418055030b50f82c442d0756550625130507400200211001954480002e2004560352040c8200030611900c2da620030240c007050b150803036802601101d00c030760b9240d02c80300d040807000f4500b20004c2c1034036040c1e80c1c15840700304004008644100201c00041940003170044231803800e4500a41603a001c60800031001c0d005000d84 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 153182553 1250 153181303 153181321
    0x50409060e191d0a0506040627020105090f120a110102010905061b07021807090501140307120f06030f2a0b07020414010b07020a06050306030a0f0f0206030115030c08 73
    0x200c0e8116403482004241c014500c0b0100350100210543d00740c2500c21107100344200000800c12510440c09047d040185032043d40303969040c00d4280f84460150070600072810010341c0520054004518050301ea900034016510100b540801d070b04140a15030703402030508808200c1620405048020203200a02c00c5028940e5180d69401c0054004070700f0300540042910711801e550f050f19039480e0010035039130001000c0070351b0102d00d04003500c5c1080051580354021079654090503025010300300408280d8135503070314080103c402035041c03c0345100c43ca80362021000301e4030310f6008150265014800c6e00c00380c5c5501d440c201c04050f418180c1032240c1d07804c0c2c040b80200c410451624508031032070000c4959540d6503500c00107000303090200000c0202c000440c00420f00f6201400a80400d501c01c2d54940c1441e030b2508001c0d80c0d64002103540550550049942400040307542c280c001ca814402c084811050b400e41d0f00003080e64009802400320b824800d0440f009079030303043c0240300c0f444540b410314524600300710301c2d1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 153183803 1250 153182553 153182581
    0xb1009050d0f0501151409010e010902090301091b05040518032505160e0708090c040f060305011103070801120503040603020307170702160e01050d030c0201050d0c050409060e 77
    0x5801d100360944051102030040c0400ca034160150b100c8000c0000300c2200c2540004801c440c0594800300d03480412052190401c0341d0701505807559a590740010781c0c0303030150090181d40074110054041d5240c50390b100000302d80d2200e0b0070b003169084601c1d00d1940d00b01001e020072100e00400c00c0d4014001c01c0b074034200608021044850b41203a280b00340c1201051079801e400c403508600001402031003070f8100c0c940e0110084081c04181c9030341495400058443c100203d03079580b0192034030072041d00041d244030130342c0c60154030405489420f0344001c156559252102400c5841e6001c0e0382000c042c0c00403c100b0308980c0251340c0d41c050031091440012000c1107441e507079924000c031300449042c1580000800c2420340078508603c80300c0b0400e0110b01c810329113910000d40300c2c4003a04641094440310040814104040410641640c40c05000c1409040740b035202202c141e50300c03a03420703414040100a069016411409403d98040840d2921030fa95440d05c01c049086131420380c4442101108a42441444c3d03101e644 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 153185053 1250 153183803 153183809
    0xe060708151e09070221030711011a10021207060209030d050703050415050c01050405010605041a032104031209031101030504031209141f1a0627060406030f0b1009 72
    0x40c0440507650341e184144d2418206c1e01010070101c5c070451268000a1081380194071451b03c6588100d81e0b00c042c005c03a18203841e40382e203c00d0200382c00e2550014542c1461818050ba403000ba1045841c4c911400344c80d00074a40c0140070568245400054600729030404000e4001d0020440c034040d0300c0c090440d180282240594051000c0035203090002640c5144100161401000d941000b00114102403a100d4020846882507070301442c249403c050303050141a20030491043c000d0301070206c0303102d401d402e2280e48102c95110102617030180004170220348030a41883c0b61201584915503e141141415010750b2036100701c00b81098140020403002a82c850030790f40f2a042c0810001c41c6001041c50b1030000700190920400180c825410340fa50152000b0014010580c0c0a65007000b0002d24500c4105100107821070281e00510b003000300c0c075025142d40d10700c02d1002402c0456500036400481c00641e247c1d1081c1e10000000352280070540c990700452091254400c001ca44605d14010410800307098482144 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 153186303 1250 153185053 153185059
    0xd020a2703121202130b09010824040b12010c0206100506031501030b030a02030f0a0b130206040605030c04120f03020d02070509150105121e0108070303020a1202010e060708151e 78
    0x61294051001c1d250151150400c15041c603801d170648560007802140c0054210f540058034400204114002c0c60510a8a1083c500070388a0801d40c40070520000d08100101950000300040d50001d1480c400c0c810050b080c43d050f40a000541844000c0c0c2d0a1848207030011840f42508205006080c1002000d0395400c4d882800d0108441c03400000090601c0d0400402035014022100090350702e040120300e0a010500c03501381c0d072400342c807002809102003da400000350484001c02c018002e26010f1006940e01c11185020280b80c01c0d02d54103c5a5000c1c003088085a4076a08a4052820135406000c0d00c0d6283c00903100030b0007944c2ca0000010907003100601241404031281080510f903910420455440304014038004030141403d00710410403003000b074400603100c1410700002c2101c100101d0b4140440703402d03034020411040c00d521040e14019120844a00355942c07000c03e42c410300c90a1091600c1600c1c0303601c035014103162407100347c01c1d82508141c00a1013824204500e070103443c0240f0705110700b0310060f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 153187553 1250 153186303 153186317
    0x7090302010e0117010f181505090c0f0706050f0601170114010302270f3a050a060c0207080a0f0609110307030606090c0309031b06020d020a270312 65
    0x34005039004d400244002c1100d07400d0100110340201c40440c0703041120003001c040740c00c600721043c1c140d0844440b080303c40c804c070305c0000f01081180360000c00c0f1600071001b00d43c920700d070070002601016190302c000b8040b1401030700c5000700010511420380f410390000b000e00300004038544003907036140d000ea014050920400800d400c0103460341d100342d040e941107003150350418440c4201d1031010480000b804101c244903100341c103c7e100b00c0342803c03404041d04440229117410f1001a6180c100303480c403080c840c1403c1451a01c0070080c042542086155016802032130009032507546400024100801c603000300409a001c402d8200020303040071210a0342a4005000040300c1d62185082e905001491402582c0f51082e4040441030180d154428812a008103101300300030341804c40306038242e84400b50058081404450b1480841660200d40007840e4414280180380080c10400a4100d0b000801044000b071104009041a5a00050144403045101c00d1010049142da5603140081d140d1100c923200300051 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 153188803 1250 153187553 153187577
    0x30a09060b040213050a0501030c050319090204050f1e060a1809121101050a0b0609040f060b0406050403230d050c010e07060f0f030b010f0e0324010317030709030201 73
    0xc0d580c0054415000148199075803070070800c58992524030340c0502071145040140c0050383d1f6001b8401c0d011040c0c0e031510b40505550701d509107800c011100000c00c003446500d9015441c0140d6481c881c05200e12a0382c0d0050941d8208030808454a581002103034060384031800c14004036075103503140e0340100c98401e40000c24179455100088081c000d070107070080684105c684200350701e0790000000b4281c201410020442540e505408d5400d850101c00d10360780203c0104603420306810b180e0043c07003400d4249200495450390fa00600f6400e68496800040060320101e4140200b1103001d0020000c1c2d031240c11003001a11005102a440d11041a81075050040002e020b81040b2429040441015010000c0e54945a507030315010342030002050b41c1c3c0000520b1400b404140501a200d042106101a581c0741507030422110141c4079032210007012945841050500d02442808003d01c51243c0c03600369002806514610303007510950381a0482c4220146c05208008046910240c10001c0f0307502441d1580035101c0e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 153190053 1250 153188803 153188813
    0x30804050415090903050309060705030103031d01020a17270a060806030f121b0a0c150e040501080a06110f030c0d060b0a0c1b030b01090c050f0408010e071406030a09 73
    0x2c40e0790240722001c1c10822080103041d040b4010310312603524141960007642d80e0b00002ca50900c070034000100420340d030b8141500d5030f400c0810406030990060040310b40742d400c9600c50b0b007140305403070788030b90240400058080d24180c0348021001030140c0e5141c0102d403000c0355100240a4103500c4c01040c0801000380c0000c2e095a40420150981720b0b409c800740c0b841040004040406903001104a03411203801085003001c10307000080031000c42e42c0081401c1e104504128800325400c18070b8400d041000340c8a1004d18140da154810344d402011828028401c1c2c01103842c2205c140c8407a05040302c0c1c0c0940c188100d00b00d07002044200ea911100702c2000035034415881c030010300200b1242d04203920051010500306041504820040c503213501564045e001c401103800040d5401c10107000007007640c030b5803a004101c101441d8200906003a80c2d0b041007400d0801008030b48000f0341103036000320080d0b0b44400d400b040002c41404a20090200f03943c1101c03241d020040031071480d06c0090510030a003641d484c2640d0a0107 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 153191303 1250 153190053 153190091
    0x1170c0711060705010b010933033b01020901080a0905241902041211150705150105010f05040605030718080f0717070e0907030f06050a0e070308040504 67
    0x310002e107400d07103a20071070608500816003076a049000c105c0c504c4002c121009400010030345072078900301090751400840400c0282c0c60503106200300340364072001e40320303044100d5800d00e0303002c0074242c200304d0441d83c3c0303180040c0240120f41c240459030f139204224022403640d12424465200d2001040811041076a03e002407800d0700384000d140c00540d40500c41400c9400c4644003034040c0708860031100c518010700111608034404c600c1180350492840c60340e00c00146d91f800301030118940050108811202250f40c1c50b051381d00041c800c4500c8e81042d000c040850719030880d082d014040070f00e0a5440c40b4072032403010300144298050340085c04400300c00076150710310032006090000b84420311900300e56540d030783c0c032541d908051942c43c2c043d0088110202d94507000b4060f400b00401803000910b5607d00d8403008600da4030000d0101201806010004808190300104000700c41c1c0c49058006001e241c081d0a0008441c0264502c038450f4000b404104045007804054405440c4101c0700041d01507840c080c4a0512 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 153192553 1250 153191303 153191333
    0xa1709030d0f020405030d0201050702100f0b0607060509060f0f0613020c0f0f07081b1c061410050907080a020a0c020316030507050a03080a08070c0812011401170c07 73
    0x100c0d0a16200500d05290b503005070044980c1a422104c40c84403040d4185d0a8400840d00040164805038400c801c1c1100e981100800c0c02c800000010520b29000210307203940c0c040c02059a1041d1210107215811608004240c0c0c4070520a051140e1030400d44c0c11610f1044000e01464483c4484145000d00701e919030f4108e50b0a1600b66044440d4208411405502c0e18800710550704a8003454200050308000031501c0e5011195030030052461915006c00c1101c003070424803480c5851540c40c180d4a001542a120711099410f1505030524586010510115042c196401250041d41018148004180c020748899007040ca81d510240e1234000d5020110703002003050301c01039458400e1045c54001101d00c202c00506980c011405d8462143d11201400204403403880300511020081005200c0b1a101c7d100d429044620380c9081c4000051a4580315019040210038803040749034400100440840d0000ca010811028205192400c0c01c0d200441d0507500c2c010401483c2c600c00107801010030690307003070300a20 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 153193803 1250 153192553 153192577
    0x80606121f120b01030209010902040803040b070c1809050c010f0c0204090335250c0303090212060601030b03011802040908071208150f0d0f06110f0a030b060a170903 73
    0x40340d030380b908000c01c0320740e000c0c4026030080f540d500000c14407280c54022034003900c1502d4029480c292a200030344410351310403242a0391110a045000c40c5004134440380245111034210041034031501401e0250420b8104c0314158180454042d40414043c0c0045100c003030a80c04440005400c0b91070f05040d6195000d85002403049490032085030740e640a1415020441c2c10741601544081e030341d0102c2da5840d046025505240001060282610300c2c5c4100d00b41c03d4080c0c400c0c50301003445950b640c0825580340c10501d81000d41d80000c4108000c55030302d440b031081d04100440003800420541d101c950900c66200390081e000d9138071002004140300c00300c011280e10562081e01d80d40c0035092501e006007241c03019103481941c2c03480e42401e000365127440706458071040c0008040140e200030340d03a503210320f483c2c01038021606161651702e044c41004081000c0d20b0000f5040500710303629003082000408807805502c0c1c452003440180b084402c0300758403082c8103c0700944100408070742e0b120300031076904e14014044161a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 153195053 1250 153193803 153193829
    0x1101020a080f041110050a03060504060e0c070c050310021803010903120c020c120708060912030106300b0312030f0103083106110d021506010504050904060903080606121f 75
    0x300c91b501100030011101103560802c1400c1c0c43e441080b082d140c2d18440c0102c004080404220f0400da00c2000b8000c1078412604085c08030380c0e900110b802c04a0030200071030202e40c08594134640860080762071160300403c40080160301c0150360301515074004900707000107281d0349085041c400c900801030200074100081c0241d84070710340000b519664041e01d01a079610740c0030781404100d0901c1c000500d8038103078032084011804c60b07080103800c40344601c2c000049148151300d26074981c524504000e01c20f40c0c4088050b00402d400714620241854180fa005007040482410020002c1c00c410b001038981c1501d0780621175980e1070603412a0f1240d22800380768602e150552142c00a081c48401106102c125170140e26800c02d420211000141c4411b4102c101002503005004000d540a001c01c4030300d0f5025005043c600c0c2801e0b20b440100e109001c0803902110310660320f00d60007080c0340e0400b6100f640071b2001c1b43c1840c6420826440780c0a13110018109070740c02c008101c202c0c0b40030051120003c01410146c19000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 153196303 1250 153195053 153195079
    0x1107090501122906040c0903080307030e0f07060e152515020a020607030504170f1201121e020a0e041a060f03070e06190b0301061101020a080f0411 65
    0x1070560400b60811a0401010306a00b41d0004450482d403000c9140c0300c01c000d90541d6004140400b030300c0c1000d810780401c4002d41000c8002244540914061100c50740d001841589415a49280030380901c20380b52581d2090300c0400c07006074058400c100d04041070300d690b4907001c1d01406001c518000c20a0861403c1c801c104150090318280900d1049140101c04a651103608060381008a02c1b43c1e40141300140c021800080b80c48c1d009411542e00a80304007030101031002400320380740e0983c06c40c48400840c1c0c1c000045240e004a03c1c1c1201380d02400743c14020000e00d0f0115601e1560592480d8888616100f05000705015580c6280f0704d8802400401c4204080d890035182075240c1c0c03801c9042c504000302811001c0303105800c0c50007007034800c0800500100111810050708220702e03080181500d1344154494517600c88c1d03a07050080d060050855030f07003085e203130350505002500101300744000d9603441c0c2c418131850712401c1c9d000d11a550000000e1003500007984403070038012304c19230039845140d401154402c3d00b1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 153197553 1250 153196303 153196319
    0x61d07030f0b06060a082d1e0c030907030b070216090902010f09030c0614070501020c060108070e070f0309050309041b120203040b010501080601050c0a1118161107090501 75
    0x1800c0220b1094180200c0d0780d0b90303c41002100c0c001c46600c0c80004a2100004420900640b020b28544401644881d0703c003034500c91200308144200d4142808018140e03180303948400c810320564000c0e110f0030945055141494110341c1d0707040c0c588009048114506c021800c118024441042803202d004110b05c0c242d52280340c010050a100d0ba4220700084202c850000014030070f01d007001c00e4942c840003503002c00c0d00e0400100e40d00d400a2100040c0420200101e20000760244002d015810420b4082d01c01c540c0b501c4002410034065900141000c055281003105031a0301c080c07034250810203820002842100da0400904d140140929203402618000456000e61000401c0c507044540c2e581d6004212030080b0a04400c4c1e010a4800602008440d4010300681d03000740b408035840a0b044c0340a5050181c0308600500d0b080080b90b003a80e2200004c182070b191070800e440210140c0414801d00c1d00a400d10300b8004141504503500320042140350101e040e0071441c1401103000511343e140d41032101d0f50f12a024 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 153198803 1250 153197553 153197573
    0xa0203070e031c03020f130311090106020607020c040c17040b16050a0203040b090411040f0e0a0204151206080f0c031605060301090b030a0605010305160e0c07061d0703 74
    0x252010968501c100d14061500050112240c52880c1c102c8900050150f0f054001e0b40041080180341c040a100c040002c095101e000300081d80108501c1d4001c0040030148250300340d040c1c210500319001503007000581500001c072802e02100036200040c0342c01c40c281085525120110070b80c085400c40c038040c44140085586264080d0103e1049550382d08118042903925100b40400f510143e0800d00040100c5030b007900141c107501390050404a840300c149078003007045034016003000916170706980302800080403c4034510f501c42009401185031508200400c4019a0703815a580200050030700c43d60601c1c0e505402120080100c90100c1d03545013000e0514a0b10341c4082e94825020307201d000801598402e01041c03074021220081d19643c512790802e5804009449550080f6070036100e01c045c2403001174400c0c402c0c14004c6011f603018004098414034141901c07440c6030b01110130a40100140000c0301408021620301540c4054001518000071000b250001030801c801400b5008618000040c014040e035 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 153200053 1250 153198803 153198811
    0x90b16080103141e1e0706021b030c0604170c04021309051305011a03150f06090903160b1515090d11040908030105090903040609060c050a05010c05091003180f020111060a0203 77
    0x101c00d070360034800d403c00a686c07101148640c0c0300603070040d55440c0400311040d10440181e82c014040d070307a17800103000114001d40c0c410380c00881116012080700c0c02d2408103008410607040c04031015403034031a2801c80346a050347c5a00480d10000e9645000c1441502002e1700e440c178150340f100c02445640e00340c90280119040302d05145011f409603101507041d035548116680d2080441c2c60405405841c0d020501c800008000e00004030352008100707414404241c2046001709170710400c01101c0364582150b84c500d0b002d1184180a0080300c020001910308aa41e0055444080d015078568103480310702c2c24512040c0540e06851078125192407026400c1c80701400040d07041e035405444c81d41d45500d0b11b0882e641d85e48554483e4500007866154140700b0b43d881840b1100300707503008400b22118441c0c5ca44599003103500d01141040454400031744018607062260307024440e40c20358101000046001601c000600003a501c000f4030315480c132035002045a005100790701c1c4080c1441c0c225480b031f01c3c019032903a0095001343d07 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 153201303 1250 153200053 153200083
    0x1052704060801050609040336060905120a030302370f0206090a03050918152d0d020303130b030603010f05010b09040f06050d06090b16080103141e 65
    0x1c1c0c0411207441c140246405600003801d019420b03510340c1c504690007568000b40d06c100750b00c06c4040d801d03041030801100071020340744401d452406241c01070191a548055008502405080e075039403000d00030211308a03031002c1d094180580c0d100300c40442c4031110254020400000d2a90707902611019820150303901100105d030f150380503e014041d1060740c1c2c0304011699090a40d01405a41e8000391043d0054000e000300504503803c58450240e02020006003100da01480c440450005100ca00c1c110144481c1141d9842c5d010030044070020083c505620441e00c03da0151007012410b01c2151820003c880d01903038146084412030751270b0500700c9407640c410f5619a10035070030f005d941380c0002590f200f01812100307040041c40c508040d490610000c5e0840000001400d5521348001900d511200072080041c3d109030400030307880c101d80c0342c08120108050510149014181000700003203410030442070660f40c01c041103c2e80300d1701d00200140781003c600c55400c0241c030b07030b0800400e20080010304142403a000b6 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 153202553 1250 153201303 153201311
    0x20309010b0409020901120f0210030c1e120e0f030c03040905010504060b030a1a1f08010e060105070807080906040909110907211b09061d0d060b01052704 68
    0x1060402c420344800c43d0010703500540c10001003000c20008100319010502c90b840c1c0020401c955000121326044126800d40407984442311905403542c4404048010441e80000c0d507000304907008020a400303044054900f81540c1c03000071032000c03901001000300e121042030443c0e603103003034219600d0744076082440386880b401d0400d40040340d14601401a501950b241d0300d5042e00799036032590841c0c05002d10200100400e59002030410868444001800d41810030380454545119502401001d40ca8140e00840401c41d101c01840000c2c3c1c0e12508940007940c00200ca00d0320f07040c0d07500700301416118600c072180d8021300000f800191000c1d33541165450a0041400b02c0b602e034844c0c2c040c401c0230070049030340382d0001c2c80055210034107681011a4100d207115a40000130000c5454066141d21152002c111001c6070354600204002540040c0303d01e200882c00e02400c0c044108440814900c00b402c900c000d00c4c0640b190902c04942e41b169050302c00c07402490f0460652a913021001c08100705140104a0140c0c1c14 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 153203803 1250 153202553 153202571
    0xc0303022b0e030f0a06020c0f0712020108060d0f03020102041404091a100b12040201030c02010902220609110c0d021f021b1f060f03150e1903020c010801120201020a12090503010f02030901 83
    0x100d40001221448004c400e50bc0c1015401116001d600500c4640e000c4599807055000c40c4c0a0400303a5803040c8a07400040e5614107280c0c60070880c03500310b41140d10840c2030001210004084aa406507003007000da400d6109a202d0701420701059006400214412502003203d0103200d0700c0d003845901550007a00d08201d4490f10200880c04d0b200c611402a4000851500c0c0c5000c54890002c00310031138042d02400210075403540d80e01000c0c1c0f0a2210103040000000c580d03000031810911401c9185203182c0010042d541c459202c0300c0c001540c000601d00300e01c0c0c1c003140707024880c01003140b10307009490380034141d90b4809561450400c02d11700709004e540403240392103804942403407640f2042c403e82c0d41100303001144618161004014003605002e0740c0160152203803c0741c0d64800b1002c20300300e10748282c000c0c101ea170064100041001c00f05078400303c0c0c41400a110307080544d8012501030035080d005421048c0c0d0030b4036208161410041d5600258156181c9110003410041541c0518050304180e0000d00096039 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 153205053 1250 153203803 153203833
    0x60d06031a0f0609040c05030d030b0a09140c07050102040e090609060702010c270503190b07030203070e130b0a06090806060607020f1e040204030c0303022b0e030f0a06020c 76
    0x1100302c41c2103241c41e0751500441c0303403840e0003002260301c18070400203034800340d8980c00402e041103400c80410300400e07100c0040c00c801e032804551400141070003100400901e2124141a2034a05000d80045c842070000280d1301c003800000e40454001d081407071a0b00d407090820816065507154119003c59240c05518082200144103024222040c0181e95a003082c0e1108039401c1400b034150240c500250b0800c10320001f41c552400d100c48078004102d034003002c0380b050281c01c090350070450003054841050300c10020840302940140e0392880d41d8809860403040c140121039450024441064070036401081108001241a03200703641c0403c1e60b40c0711098415035200c28080c8601c5006501e40250300c40942c04420b402030030203c00d9510420025690118081c0d01d0f10042002ca901642068501c43e240c0740c002d200341a0104000c5580d52146d202c60803205013102482c004407002145c10000b000660750000701030b66400c201401e12501c1410964100e8840340c5081c50081d401004001070324001c401d00b41c1c400030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 153206303 1250 153205053 153205103
    0x160210050925030c08030a180e0c160b01030501020c0d031a0402220b070b06010203070b150a170106050405010608010b04060e040905010c0201201305040f0b060d0603 73
    0x100074040149807140141c404003440c0362890405950b54650190000007140701102c0880080280c00050b5607a5000e5000003814050707034641100401400c1c100820200182184540e40002d0903440c0130307101d54840440c5d688200e1a0840a80000b0006001000f404011360040c42210a604100d55800c0700e851001d5007030b50081059456944260b500a44460515400030300020614410038202821805050790b000410ba07004000c0303440f00070400908221880b01c1480e005402400114180461035403180205c0c0d00040200c90385401c030035042d0401e5198101c1d410084e1241020b1030b002e0008100c01c160080c6020f115040c42a0700b48400000e1140c007400c2e11605840d035462030b01c0e00d40307030800f10117440d020604a5900d800651380c000020128200388609072400300e00b90300200d2882d0014042115140b120a4004010700c0208429060b0021244289048030340550307001c03403400e00210030350340204054525a6042600050b01404680706640080240c2f0711403254130b000c1c1c00c0c030f00800c1c842103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 153207553 1250 153206303 153206311
    0x30601031d161508040807031b0510060b0355180f030c020a15050c1002040b0409050912070c0303170c0304030c17040906091109060301290316021005 66
    0x1198420b004030717010915210041407964080e00b86034911070078000342a59440b0355014207480b03540107220b003c201da0409015440003064054580f504504141e041d00915182401c00f60011406a1501801c8031210021007030300c101c4080e0325490980114600c082003680c4490940d08101c1ca052542e86000282680c0e00b06c6440d000341840c0d200401a540c00d803586018032000f0b80e171008008600051100d4042000d1600310610b035030325511a95241c40a628003c1d2004001d05a50300500c418801d01d00402d00781c0f4110742d0011070205051711554072060924080e00b0b4480c8007403d0000d030341c20621540c0400b00c0200da1095440102d00e250501d0303589400340054441d00071200041000c034000c00c0c0318a00f40780320a80140d0300303030054030300f4480c40003415881548a8580151107680400c10800e5a200f5002d1864010300c10030714000b40030000803840d110501411090814070285400c3c01c04403001075030380c4001e01400040d601e05005030013404e81100040c40c0300062151503440c04210303046016807406 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 153208803 1250 153207553 153207557
    0x9060602150c0313080d09060b01032f070c1505070c0f06050708090103022115010804080d020a1e0305010906061805060306060c010f0911030706080105010302030601031d1615 77
    0x110303240c5040c4451320b400d401000769081c10050142040c2103401d40308405203640315820004084c96214000740540c0c091281040c10a4822504031006120a00c003c50f103814960284580ea640c540c0781c40105040a500925410f90480c405d01080903081001042194003030b4507003000c4582d84000d10507031301a80780034503000503000340289000036540401411710f1034014100035041006000400c440c0d18416031540c000000d200050140c0e82c400c00e03035121a0301a0070319141030f0502e015120015244107012108100b02c0d030003c2ca1421440c4a207007500401d07038944a01106120004000030080c180a0140d010200d151110001e0058002d8141316941144031074450955440d240800030142c000421864126a04000101203140c0030310510050191480000036011243d0420309242803001030707046e000f61300404040c8030581d009071500c4d04440c001d19000da983c0e80d60500480c090b0114146034100c203800701034080c08804020984251200446800d00409551140c8410108400d41c0b02c81c40 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 153210053 1250 153208803 153208807
    0x91504140607020a09050424020717030618070f17060f0904020f04020720010e0102150411040c020d1107050d020105030406110f0706050901020301030c0b0c070b0409060602150c 78
    0x146040c80d6000c2c2081500044c160244141d079007007000250b5000312011110019158101074409001440ba00c0108100c62030450901001d5525840c40c403825500c4142c01d040d02100042d1169076000048540c90705600d00038604d81030180c4040c01c0102000017450101d0b0300c0300441900d5a2415440c03074402e290040c0701a03141d40352042408151400504140c3e0030190301c00c0c0704a003940f034500042241c10f01c00ca0103107040c83c4080100c00c004156216250b41001400814100d8a0f03074006181c8003141c110810480c0240c076a480e000c01c010180859058005081002203810a33802107859115041c09454400941102c001c0898440f049409174640c0100c00314080405540b15502450b80300f0b00c06c2300005002150700800740d420750442600c8985850b00040d100c0200403043c0112600301e11154003e500310350543d40d80c0021386032507020b900719514010078090400e910402841d00105440309071565603645031011040901014010708000d8420700328891590361465a06502c500c8121030f1081c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 153211303 1250 153210053 153210089
    0x30f0c0625210f020417070f120b070201020c1002040e06010f050a030e1e0c0112140604021804050a050601090503030c070b0a0507080f03010302010801080c0a03230105010803091504 80
    0x11075482040351003000b450352451181c9000d849480288060100003210181020082c51150b10b0b040c1141c00069107211101d004000e882d060160305480c8551040040415a80c1c0d03442c124028090307504c01034164401c8481d502880413042d4000c20030b0305e801c1c40c6005126921f1200541c0c11040030140780001880800002d1445442648031840c50300018050301c540355100d444069014401d038100c009160061484010309680009201c030749454102428404030340203080043c4a040d00504603409aa0001120101d80c000701c210072000e000c1c028401c010504090045500901d4215021400b1a240c8000483c8074540002038580e030345000f100a0031824144103040d103080d001410703c42d0500c0028410316001507150b01c0034001001081041540300d6145000043ca0400d042e40084d1880e003041142240b1078842c1c0f107403441074a80041105800e0a03040f003941c100741d00e50403402c01076075183c2800490000000f02c010140217030300f220081885007010303104604501c03451048903140c0c0d080011903 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 153212553 1250 153211303 153211337
    0x8091c1523041e080f041707060509010315051804060b011103030a0b0f0303071401061418040809060a11010b0108060a03140106030b18010c0302090a03060e030f0c0625 74
    0x26100b22111483e0081c00c249075591845000d03040f4484101e0703842000b041c18000b0000c0302c0b007096030000c404002480114503041c00a01548524803890381090f4541c2d21130200d0240c11048200200030291030300f0104840c5112100704d803002034804460b018100000030f0349940c0b04080340c0000e980300364042d510750349640c03641500400c18403502942014000507100740d196824070180080a0003019540031210400503001c2c210b516540005d4200c2c001702a02e94003a46600c82d02c11b2444d292400d44040300c0d00e0f50f081010386801044001a070101000811400300f9a11441c82d02140702e800b40240700c050048801500e10075000c448450700000052020004900032031a405e148482c284c0000510380e8903a2601c5100a0045500020340c52110010801501d024461100701001c58502141130280120018040c00d01c1440003811941e1240c0d6134504011007401110710441e540c0c1d01c070664602540303038400d450b5001220288540380342c2810f099078034403c048d0141d0b10850345544e002d04040c240514 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 153213803 1250 153212553 153212573
    0x70608071b11090903040305210f1b01020d0c0305010e010e220605041119060929160201110303090606060a02010207020406060e040e0f060408091c152304 68
    0x4142c03900c61110205000c1c54481d4450700703015403805030103180d890f0305504105260206c0100001d2402000d5640343d01d0203250001521044620045016512070200c50340d08a042a10040e05245510004052102041551199000181689080c08240c1c4c0e20034000b055036409205508004c98841d001981c1700408440c103242c54080310100c0c0b40c50440c2c50701c2c1d500445208440071030300004e05000500c4a860010140c00c00b04030030380056440141001c0f0300802d05d444c107119044401012942d0040001d010203001129000e0f02e058003034441c2c485001800010b48040b4050f4041044d804440b1240341d800f0003203a1249482d9402400c05407154030601c40140d00400700c040031950b09101c10030059540d4004ca074000d040d00e41d03c451504079101c04000850f43c51405101030b0764170010300400d0b400700c0031941c00d03401504500035685800d00c01c8007140d46c0241114100800c103010107170070000c20100c0143c040d96850031600c01c020b682d43d04100c00703281b41405220b0b01c204181001c0000d000030792400c5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 153215053 1250 153213803 153213857
    0x31202030d02031006030b0909070e07020a020310060501110d0516020a0915080c10080402100903050f0a051203190906020d061d07170705031e1807060807 68
    0x204992504044044441c1283c01c00e0f43c84034030980701018100703c2668140600303140e5100880e61000c1600704100030300d82d904003d20591180e4620140011b00d414000d11004d1401d940140c140c550301c688554085000780f2290180c940842e0444104c41c842420000d0308410b61520740d03c0305440c0404d04481c0d0300c841d0700c50403400c036440055a400841c120213103000e0300b888200c207109800d85550a1191190030300f01000200c50007003a807100307810202a4442c2c0030a8009405458800c68044040400c96103580d03140c001400901c02c1140c03542c80b90b50005000109a8000c82c281e840c84d0f00025405440341c0b00c1030740c80c080c100c1034040c4d200501034016885661500e2007088010301d014108601002501c1080e0311100507044440104400b034034544030895401a507501d0b1041c524150300c222400d074640302a00d0401089400300c002007101c0060480c4c00460860300a200302c40d07207010201aa0304414070720007480030380981d603000100d0380e01407038070a802810151030380b0114101d800fa00c4021112031324 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 153216303 1250 153215053 153215057
    0xb04060f1d040212040b06040209102003030f010303020c0306040c05041805190c08010b151c2a031e15030803071e1b080c160b0d0c020106030c0312 65
    0x3100d0800d80b42d0315440100520340d281c4a448689280c0f60811842500b00205060f0040e40101304800c0d45035594800010b0b0b04446007001e010340a02500c43c2103101f0080f002102880c4000020300c80c041601e000e02ca030407a0301c00e508840c40c254003041419154501500c0c02062000180c01c10b0245251580082003100703207001403080108400e0700d402c1e15088241202c0000d88041c0300c00d03007052150001c01c200180c600ca2009100001000c0c2c0851903003525400802144c101c041124507000340051204151440030351000d100d00c4194a8a20030000740703014544401c10030901d1100e0b000c60080c052046802403000d03500c600c4032088201c08010342072803a40b16404405d032400101c00204035802560042d00659202020b00d110900f0b100c0c1041010a036407000d0081007000e00b401c51085e11062038401d6400100c2684824901500310320f08101da2148405480d141040414298000000b500d009401c2c00c506001c0000c00d69001c0e82280d10b54003024000426a100910100b840e0840101f0000024 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 153217553 1250 153216303 153216347
    0x5060303070c03030f110a020310090305070609150b010305163b01110a0807080d0b0603090105060112090312110405090702010603051239030c0709060b04060f 70
    0x3503034070100704400e90f40049012854248000c44c1c02030348405c40b128804100b500a02c624000c45e00040c0d82c44031001e0101484940720055481010f01c42c00c140d540c0f00343e1002040c0107000007407a03c02c07490171001c10040030309807a000c800440b070f42c86805900e0040c03000510a07450b8070780e00038046800c030300f6612291940764803042d825180309080301c2c060f43e62503180c2401c02446003a43e07800185045051403860032540c0c004510b0380e010a10715012a50a03070ba114031146d40d42c80340e5401f01e00203003200411550380702802004002039408190005441000240da40700c4040d54121a000304503a4000005030004102c2d8900da2881946588001c2d510700c089843d1500b0140e40d0b400256800700126600360050b5155401041080410012140010172090204d414200900900078018446c140b1a41b03000e8220010a568880703030f40c0c100800d01d10078000380da584150028800c2c3c2d0b10280e500c185009075290400014004854070152001d80f0f585a940348a09a100b56003240d026050170f0342c07842d031031a030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 153218803 1250 153217553 153217567
    0x31005060907081b0a090f08120d0e070f08010203070816020a0303050406090501091401060b180402181302070506100303050906280314060301090201051c06030803010305011d010b010801060305060303 88
    0x410300192096000c142c0d10b40d0545407c01100c0070014441c0d9210900070340c4220140031b6003524402c151040004a62000504104d8680300c40345004c496510440342008a00d01c040b6110206400940c070400c85500d50082c5603ca8100308401056412521001604a07520840019100350801c81e00240070341c034049010b005603280d0f0703030840e501903004aa4580742000350b506e924a0038017901000b401181002c5042018003080c0d440040b00b00303503480e8421940000c3d04410400c900e00b0403200d40001500b0413924000300d51226000358096141501d031841a4400200607542c1c80c1d40c1c10701a00e6040d6030b001d06002d00c000a2201da0340014020b1441e004840d10410076683c0c0309032500d094800701d40e82c04608070030a4a00c403032804a019140340d02a9051401080250743c000044510045520303000c10101e80350749080c54000c01047d0002085c06100000000a11405400c0352920340c0074007002c4003c0000c81e142c0207003210b407001640c501003410712f4010418a8060f60100781e1141014040d01e2520007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 153220053 1250 153218803 153218851
    0x405040914070626010812030402120f0606040b120a0807020a08100504030305060f01021f020f0304050d0807210504020a08030705070f06020f1b0a18090203100506090708 75
    0xb142d9008540014508100c1d484441c03140003626440010b101c82c41d80c00d950510300718540780c5000107a4203009110020204045407030307034070422804816001c2601c2a005c025840c190311010207884041c421400d1840b00740c8030786405050150940f1460005060700c4c1a03981e0365145540208609a9026030482400100c8200c140700c00d0b26103640c90720300098113181926001c0c08070303036020780b40c0340c050681d034441041a80d13000104035100c05c401040032480c03c00144c1d03002000c1c1c843c08035844440c44c0040248000c114000640c040a01d0b0743d503c0d140d64540d9039190407503a40721500041d0540c82503890b080e0071000f205a00160704a40054a1441015121151545580d0100004032000c0d0300003a8200031005440d01c020000d4105403000d454004070900d18655501885e00300f04c85414529408880d07540d54607140000101100c5110125043d6406590030080c03806401c2070380240510001494440c03040e01c541440344000500c10481600c0c2c2d00e0303045030254801030007403100c85911220a00c110f4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 153221303 1250 153220053 153220063
    0x1e0c041a0909150a151a09280b04030b090f070614040306110310140102030d05061906080f0702061017010617031305062809031b06021b060405040914 66
    0x180103004110101280051405d0101c55032264142c8840120504c00b20120b00c0211104550203c0b072000c82641821141c02c140240c0d6038540e424241c40890000380d806204e00030f00304a9014050340425075440c0180300c0e031540e010b1407010300e441e040100d061250342c1c010400342d1505800c0c03044544c2001c0d22a944e82c41100d000704e0504120030310102c04c000705100c0941103080503101b40704a4002039501100003075034034040c100351448102e44460010f2f85603203501e8240d01020282d2303101c400c2000d503600c80c0038002d003c0a0394000d001008500000d4400c900000300180107160214000100515200414040b4100d80b4080e0031955280e460001d80c5603221046010554049006950f44103c0311200f090711018a0b800103004607418441d12610240c0d109490007280080034211401050b01f80084942481c40e0700014000340709440b408044507640d24003441958144c0d001c0383c04042d502e4000c0400620444111540408100405d00150403c3c2c0c00500b03895200e415082e46030798540c14070501b80 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 153222553 1250 153221303 153221311
    0x5070e0f041217010605072105091903050c0103050a0f060b0a2c060901050c06130204050603060f07030b060c030d02030405070605040f030303050c07051e0c041a090915 74
    0x40380300030050105120b400030a0b0070300021141055004503205488a41d0910030512641013442004540d400600680f10080c804030010100f10200c00d01d40400080c2868001003241d600401601c01c020801c04414448802600e03000401403690302400d00045018050040150b10b14544900b1403010282c3d450013510094007180512a840d20390044006010707819144040e100e510391318000142d1040d40c0c0540c100001d0b03040e181180d85040c00d5005a804c1e101e2400442254410482000711018110341120b142c54800c079401c0c80036466003400c1595981c401c1e1088500120303800080b501c1c0c00d01a134881400100b0140400f800c00030382e601900d0540c0c101d45180c0340c82540010030001040020302286010b044981011403d10742401036102d02c02204d2300009090560b51804214030100110079100d18962020468a400c201c158516144100400c0300c20158410000c0d009141c0c135040c0030304402c41c48130700400f2420503072000800ca1200f80181c210000d03030003581c1481d000c103001c1a19035440f07 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 153223803 1250 153222553 153222571
    0xc0d0e01020f03090906130e031206040c09080309010f03150b0d050603160902090d020a090c0f02010b030c010e0a0305060c0c120f0d021812011d011503030c05070e 72
    0x14a040940060704284081d0041e442c035800c00c010400b840e40d6000040ca411820681c3c13604081010580c00100601c51652064554031011840c40d20f6686000c0c0128400d5905983c18400c4000e08071003a502e000e440e020300031a40d04103100700d92503075100d82c80c2484800400d04c1c011429202c009070310800f2503440c1d04070103012800010200380d484001e0150940040703007500140285000040c050b01202854040c24036644d0b0001825507030f079903400b681b14510b40d40007065400d201c0c0c2d40d480c07008000e0045500140104100171043e021050042c421004206009009442e003100202e004458103a002d459540d4440b04118008c80800c02c01c001c110703c01c416050180740c0e50401c0c0500d00345403101c0c80800c8140f0003001c12900382c46d1070145082d26014030091001607210440b02c0c034003d007034102a04005410202000e1046c10102e41500420000e06590f00c01002ca4010b0880341400e0341c0400c854882c9420f4101c0e410800a03109040040500f4054003e403540c0948038001c1140c0e105040e0340300c4003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 153225053 1250 153223803 153223817
    0x909010b040506030604020a051320090f0d0819020703120302040305160602120307110a110a060e0303070803190501060305180303090c1219080d0509070308120a020c0d 74
    0x21641807500c81d4540040044008059500d0a54001207455502e805454040e0501c41c601c03000c8444139400021241c0210003815000440c0d00340d0b0195650403101c00c035441a00b100029036280d00f01b01490040309500011420b24005860036880d90054400c826a01144103a50001011611082041655501694001d0794451a604009181601a11054003002c0c0e1904080215940018003998890b0403100082d840360381c1c1c42000c0e00c2c812000100c1280600800309224200001506019040c00c012200c0126031500d410003113a6403502041c0d0142c00d980100031500106283d000910b07030082d9510081d41d20200720320340d40026200e0a0b8010008603445070305100c0c0b0b480f164101d10000840442c011819441c00380c11403980d030440b42a00500074108400c0078000e105c4103100b140048070340451070040c1c4407114074151500c1d41c040c10485c0030380d62270400031400c0300d20f0115010003140c0c2c204d014076003001d801100c801c1c500c000c09030807201207660800c8001800304050008803500b02c000d882d0300c5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 153226303 1250 153225053 153225071
    0x60f0d020901090902090f0c03040b0a0e0604050d03050c0a0504120804050a090b011407020609330301050a050303070c0b031306050106120e01050717042a030c081204060804050a02090901 82
    0xb9134143c021341400307a482145010001701e88d03004801d407544283c0200068440d40c66210b11840244982e04219002d402000100400d100e000190448070b61b405580800207542c40008428160080e501c400c000140100420000c901c012503c2210060062810b580352643c1c40f0005044404e280c1d21814009845051a40407503030010385040070900c0da951864501481540011050711494191038401c0f0340d0800c902c880142551054130209108442d0401510388415500d407442e0003d1054900c56405803501080c242008000e0b030340030951080d8030701d40950514114071703401c6d00002c0294038802b115240301e0003c1985400b07058001c0034292140380503982d20000301e100781c1e0705e02400400281c7c100824420810b41c403908140c5020a10a01d00280362107d00d444000c42580c940300036440c02c3c0344110aa041c2c0031460b500d01c1143d1059081c0e4100d980d850404984543c00703040c2038010768900744401c101060140f018076600501c520162000d40c1d18513030000d04000070913500c100560799680418 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 153227553 1250 153226303 153226309
    0x12090c0402070326010509040209040f06110c161d09030f0f03070806040b1c060f0f050f010e04050d030216170a0e06090306010603090302030c0607020a0c1706060f0d020901090902 79
    0x109001c500b410b040741310f20b41c1420007180f078416001c0d20003405643c0f4400094188000f245810703109036400801480b000710442c0c10b20240790480f1071410101d010349480c0c031100b820001d85550440c1c008035031100f482c1a03152840f0f06550401401d92211f40070030490351240480d0a00140b4a41d403144e00d83c19124105074030000d00203c0300500541c000c0740b821448003003d0343e44102804140c0c0208441c480750448518001d4042c11410700c80081807030410b600000c1020054001d144500455586c01051380c6c0c0c3c2e90300c1100d031560142c0d4007070310f00d400402c05103441c00e00c02c1e0000c000350f039455070107003880114035036a415584d20a501c410160000c0814103074440c030b40c41001c0306c01195040b02d40fa0704040604000985550041c400c420070f040d61004039a04142c0203005450070456002c059881d94509001d0107925038180f10401c54070845559004907044005c0e00b5001c94103441c05004084995541c000d00c40065a2280b9040d8016020300340ca03001603584680070350180c010b80e9404248103400e4814 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 153228803 1250 153227553 153227597
    0x160605040f0e190221010e04060e030310050108041127070f020304090507110a030c0b131109060102031b0703060c090602030d110d110a0f03060b12090c04020703 71
    0x445040c14481c1400d01600760300f4114200864100c460f00140c1d03501c0b407100e11102c14a01030a0070541c40720f0781000000d481e03402600c614412402020180000b80031550116160301c411280302d881607015032418417040d445801265442072140a0b084162810030b00040c00c81581c01780c6018565419001a0702c841d0803401d070300c0f90040d030030307003001c1c0c600112290020792a03000781e0040c008016622000074041c01c0c03251060b201084150810b8804001260a004080c0741c40040d040d80c183d0001004981e110703103020418118140c014010a9101c1916020840050b4015200e903045101c03d00104107545154905003a02500390801445c84915508d0540d055400c0e0150b98824405013038010040c45030080200c81d86622080d000051010900c407a140e480d0182d409442c440a150000380e0b40024107080043c1a5850319440f8070303940103080784048003600c3d100e00481c02c2c8800180164104404511707001c80d007080681080e00c0c0c4504038032010a08030b820045082d4005201c075502421201c8010305 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 153230053 1250 153228803 153228809
    0xb0a05040c0803040807090e281b050d08070201110303010f0315091101050313050a0812060f01090603090302031902060f070e0a03021309050703060509010e061501030e160605040f 79
    0xc0a5400d042c038090f50180c50b046e8522500300410740b030310200d0b00800c0d03041c020044044404503020107003405ca07514200701500750398000c8401400f4217031360090440c4d50318040c000b01c1c1d10083c50307042035010581d11700c80103800c035100c120705001c0c49900d5102203c000340051030190206000070790205245d400d021241d501c55035080174000349800507000100d80c051550850b00c540c00c3c2070036607803074031094085201c3c0141010007400c14010115214100700d00c8034001d0401d009103440c0901103403100343c10080708115002207280440d04202c410020240650012820036010f80181c9081c1200d03101068003249200c500c09005801c40c0041100c003030700380c00400382c101401b481c1c40082c0c140b622010603c50022800b019229031800481c1c401c0c050841c4e00700c031000f00d51000590315070550701c0c0b402c0c9010702419905038405508006000e480c0d03071400642a88200d20101c22401c5000015006500400c20a917507503545d8002e01003100b000c076004e040000300500c3c2ca5501e0340c0d40e50745000d4401201c020603030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 153231303 1250 153230053 153230069
    0x7021009020306010314070f03031e020c0f0f0f060f220305120304080c030a1220034003030c031a01030f0204092307081012050a0b0a05040c 62
    0x160380c10000d078600141c1107054907440f15030b1003807210011310054989050341c2e01580c800e9010b940040101540502002115030601072030f104034901c4e1040690300c403403440071059000071000695035081d1800303032042d480d40341c4064030110b500307900350022400960200c118034410250001c0c0710003c00b98940c10b4040c2ca09405090041000e0a50381d42c2a00c174201c1543c40710103020040082024442424102e50401e101002140c2c0d940001c0308020b413604902d24407464010f454211612510b0108510b20b80407580b040880e80d2a41d610103008502c160f103030042d904240708140c480c0c410050707100030034000a1412088101840001441c0c02401d40b02c50a42d01c0d810941400943c400b4000c06903865911324409003000300310480c04030342000080c05258007a0741600d040624101c441c880254030941b611080c3c40345440c04c2d65030f0340b0054541c990152070403c00b8901e4041e042086a0329080d003000410b00c40c40545003c1040790721801b100607020b0b0b80412207103554001b4032041002441c001001880c0c00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 153232553 1250 153231303 153231311
    0x20100c0b01120b01031103010209040204080f0c0102030a02070b1602121e12030403050304151805060108030408030702010f1101090b0114041b030b01030b060a11070603020c030d0b0301091a070210 86
    0x30350743d5000f202e0300600c00140790b0300304911102c11a9400390165200407002800c115151070366a0781d415a80d03204800400b185015200c1400e003e5440481114181c0003650010030f1590326012a4080360360110038080b55005101c400c22005a44001c0003454250a040040c24002c10840f00c03446e40600b04072520f80300368008081d1036400070300c03c0c06580d803098142c18a20b440c0da4907424102c200a140b014400443c078a000031601041250002c170104160007a801c0f5400ba80c0c071402c54030b94034481c40c003440c295540300b480b000c00198498203401c4101051460590142c10000c3e155900307442010004880c211035000052240c0f0140c0c004108440000716814441c050400c01d883c11820100d1301c0b070508043d11220051440d034000d8106e40d0905d0006040d09036542c0742040024000748001c2c1c032540d0240900c5800042c0d4074130071b00a5034030504420700a1840e00e035000313000f50024040c4d1041c41c0d815540b40d060440c00b04a42c898001c0d10059100141c840e68602200020300700065450030032401c03464 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 153233803 1250 153232553 153232589
    0x51f0b04030f030c020409021206011509030b01030f0f050f0d260103030e12030c060703140f07050a110d0c0309230405270106090c0906080420100c0b01 67
    0x402c50090040a4050504900300c00d018004140a030001ca080a904280000407440f2100c400141d550b040b03070405291502441d9140e0012250320041d4800988003407010001480800d04003c20711002070f21441ca154032910075942e131a802c1886428000181d904003203400c01981e5045022000d10b0f0400001d805084450040510038000c0c042c0009420030281148608103032320758407007042018154100f12500c0d404a1601903554100c2180c2007400207040c19822400c16200b114218010500d915014855a035a00012035080d0040410042084082130081a1700003040c8803001c6082d0460352001c08003101030801409a107034030b61050024101d2101d6240f01018032510300901d0318000c0b01e0200301c0b52900080c400c0b24800c1c200c280c06002400c1542e1241021055101d501110401401400850240f600c02c1da068102da124007000300f402000041d001601c04600466010700d00f103020700741c0844001c046002d03030300380400b81c1d0007145080703540c40300b805290403055006001d01c131004160440 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 153235053 1250 153233803 153233813
    0x1a040903081501030f020d05220b010b1305150309011407090519080601060c110d0b0f07141c0e01020405101d0d0f121403130507050301051f0b0403 65
    0x24000308102180c00346800e03549040d038440c5c2c01c1000e00040e0907500b55143e5100d801724000400085d5080317103000070403440038007200a5803c032041c84150411a103c0050303180a4950710b095114858040700664400e00c042a50fa07100420f0201c1180e10542d03180e00d92510a440f075085920904038611100004001c03c1301c070a500c024130400344e5805441558148200d4107103070b60024072a4004000328002c02001041c0345a003d90a011014061903030302503541200000e000145040000143c1110315040020b00d04d00310a5061540080c0c00e840c1080c2440403180d03030b41c603840d0000c5440d02c201c11495420408400c0d882c1c01140f46007100034000314079003841c16000035001c07034000704000d040c89141c840110bd041400102251040c00181070700e4240c00b001c1c90b1000038440c0302241243c0c41110a5090200248510b40791404010307560095403541d15034038882014941980c4044409205905000c0b0310781c1c070280200d0f40250800003000b0031200c99203100751544000c40d000340c50300b410700b82700801c0450 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 153236303 1250 153235053 153235067
    0x7020601050f1203190804021311030103060b13060303030c20061b0c10470d0602070c03050c010c0b0a0507030207050d0c0c092009040209030d02011a040903 69
    0x4100f10341c0c0a100d01d803a50303121419030280442c0003c010309080101240a42c004145600c200d1003140d40c00c000740f03e10b0b44c05108454000c3c210b612114400e0006000103201540540e0311180003c2a2000000c0e001a00c042524031680003140000d40302d10383c820301c1d182c00107098224540c00300900141640081489651224020020068008034030f51030b00200c2c0034813007110182104281070750303c501d803403520302c001410520b5030902c61100070503034295240c400350001840a0034031820010032a482c03030f1200010034070403c40d01030744007103103013180300024590307100411405105080800070a031460030001d080060030b01d03405060209a892910000302210f000540c0b0004800b8001907a4958030002c40090144810003030162044e00300da200041d800182e42c285103803140498030110754540c8a02000c1e980701c0020855070b01101810882100302c07000c00741c50302e0340e40500f00605020388800001d1500900448000c0983d54550840e9810301d80804030f0b5031020b40a0340c1c01e00000140780d43c020089 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 153237410 1107 153236303 153236329
    0x71806050c0607030b010e0402180901080f0a030810030f050a050c01050405212b110604020d0609051516020705040e1504060209090c03010801050702060105 69
    0x5510600c11102025580c801404854036a400164080c01c0741a4615052080039903281600ea201d62015210348580000185462040b050501c020264180c00c00c50668100c2d80e91180c01c3d0138000744004040f036052038411100d13520103020b58255142a04020700807100c00d07014205108001660055440c040e00540d0003108a120055030148900d1043c56000200c13980c8140610501c120400c0c40c0c00400410344500c03000c0a61585200143d01452802c800c0b4001c5102b0002c50b07102107151100c400e904010081d40c20310f9000240061120000107100c01c1d1140d8040c0c041000500240c00c100c600c14250f5200d178205501590505031603c2d114500510620900180c0c80c5070038080c003c0702c140118090100000c900359480205000141709442c01c42e001c01c05038400d915941c511a1180c140c2407034450b00c80d410101241e0a54402a00200c11940300c0380040c001591415010710794 = true := by decide +kernel

theorem cover : BRFrame.Cov 153057553 153237410 := by
  have h0 := BRFrame.cov_init 153057553
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153057553 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 153057553 ≤ n) (h2 : n < 153237410) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
