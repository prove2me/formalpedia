-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5225
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:09:40.284318+00:00
-- url     : https://prove2.me/submissions/5235f64d-ffa7-4b7d-9b4e-4ae3105f5d3b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 939568345 ≤ n < 939748201 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 939569595 1250 939568345 939568381
    0x204050c0405030c120c10051308010507140c0a02040f020d1e0c0509180c0d0c0206041703191503050613050607140d0f020408031308010c0c02011d01091d 68
    0x8244014170490041c4980001c80c400d403208200d81ea0300381e14403441c8083d196880f0700300d694070400345107031000f00307400005401c418010724181e5a00501d80140713116040c0140204a81d090345071b040311040401615094201e0200300c5d0f45081e00628100709540c0d5034048621a02c00700090b5050200040300d06182c5c0d105003041c00c00e180c18190f140000f00d40000d400341c510041a40034903540c0c10041082d0141c51000c1e1050b4414000c010001ca0000342000380d03441800700c508482812510184186031207140c0c090b60b0180e005601c1c85040d84400050510107004040e510841e900c0300000b001001c14020007495004803184042c1c4c3e0b203e0206401c1403814001c00400d08003c3c400710656040030b2610321412504a045045000a4039a46920304500684036591100760203110209400042c0205a00300c08101e40050300200039082c01e40b0000c1e101481c040f10041e02003011074181c24084412181c1d020751903101490201101902c9030a200815120100030001c0050b03c401041500b084011700914 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 939570845 1250 939569595 939569599
    0x120327063010080c04020c03070803041b05272208030a050a2a05071a060a0e0606040b07060b2805090112020f220905150709120c030204050c0405030c 66
    0x8500f41058407803990380032016001030007140d002651210743c0c00e040c400d641e442c42e8040700c4540c3e241000d0904c0d2a10350a000c00e0300e0340d461500f82c400a06442c2003081030b45c8059054884074800c90341d000c549588080d0007003019214808102d4107420340c07031402010350403191041c56019140d08000c40030303008071400104455102440d240701c0c400000e000740d4000c4001c0080c6880640a148040d1045403540524280104106c5200d41c03401010268804441c0c402d641c00c3d12406140e9907201030068500c00300780d40294020b1820442408004450002006414001c41000c680404030102041e400310425007070f0300342404c40030146000018040a076a0003818100c986840950500d41c0c4800c85c82c1d035500d0000d00c56059160340c1d965030344549506a070341d81e400281d20860b40b04141c11400203030114102c120350718041c2c00b014a1002d4a41c0110500885259030707a680b0789400d00401114070520140d0a4034426412900000140c1c0c0b1405040c0c03166000c4003119880398946012715107400c41c1451418 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 939572095 1250 939570845 939570871
    0x80d0c030b040905060103080307140a030902040b030601150e300717070902160b180f01060e06061c0f020a030605061e0306060702030f0604021203270630 68
    0x5401300390b0001702d00e03047d030f50040f582c55541d840b588800d0380e0012a16125901000300411010651901030b4000e461329802030340c0500c0703038800007802c040c1c559009000e040e400011a240c40c50485110300c48030b54030841f01509003140c2c1d61051a02d00703541c901b02241e0f01d01015980aa02d01549002d1007068006e0890b00f000c192008410041203032218000d00848401c0c82d8041840600500c0660900b00a160044078261080c28400c40318000540c0301d041b158002d00c100da810041d0300c0814440c450403a072141c02c00344480d466840c1004210350002d25207551030601e566442d80680a82d1040002d12541500010303602c00303e51700d000d01910000d51100740306440c28130040c00705d5820320346045400321200001d180d803a0740700c400003001406440800b940601ca5480350b40041400040e4460080d4022a03034841c04103d01d0050564a2298a1400020b400d207080120000074881100c2c9550000042415051907103d900c00314840f202d410a400a40400780280122220700c080e0040d04400f1550441c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 939573345 1250 939572095 939572111
    0x702031504050c03030f0d0908041706011a16150e0f0d0311090d0f020126010815060310150b072004020412110a0902041701050a2c0a080d0c030b04 65
    0x90390207400703451f00d0145600d0312a200c407810007106d68110340c00740040e00c90990b892640c034441507039617aa09018881151203002060b03002040404245d922022816200006201c0c0c20f40d108400e50074100c68a5100d10780341d101d01c1104c44c0084c09941c0c08103d43c8001060400002e010007400c1c1c49081510048011040106000c030f0340300c00c2e41158401d604000d030791061110030304c01211001d441c0300000110400101303203078a405610b1440d980c101e0700300707800f16035440203650f0001180c65020780d041541640038140c00d07485600e060b0800e0311002030023910504401d56130715402390303140c2c002e01d401c80392102101c02c0700d4804501800e01415010082d9000c50500b414001028001d42520708041c0200300d14800540150b034503131800c2d602400307001c2c400317640302c507900d4404c0d11402101c044821155424100042c1200d050780c4507804800034010300941302a0704c62000760380c038002c040ca01d130055400ad107500c910100d1200001005c0d02d0340f10070030000b000d941405000341210b610680852040e4101240c1c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 939574595 1250 939573345 939573367
    0xb13051005060d03081905071d190612150905190614150408010e07300818040c080105010929090307150e0a1e0e06060702031504050c0303 61
    0x941004650b2605001c5030705c1d1211051140b101b640c84605803044e03070500c000c100d03403030754000664905065000d05c01443d0a210b181004040380440d00310894000e180c22042060901c100380b18815800404030015898441c003543c100104403a8004025040d1504184100e1800c03a0805c045000c0541100b082242d003006c040020b0181e01401651040e403000c1c61003a0308020b03004c1110024007440300204440c030007400030503899a0700c6104a03504128a144c4403002e0aa0091a621120703c11500d0381d40c00c61844c0d42e4090003600104c0c000750000c1160075500c6950b440c4c1d07100d403900110b0151549041c0390f14150004000c5030903034121041d074010240000815031404400704200c185203e580c00c0d1260b452401080c6421410381c0118030f14994034100f0180aa0002c941003c42c800c140d0700182400d0721854050b4201d007540c80902290010601c2c208515544000852b0b048440102600c0c50301a5a40019140c0a51801c0315860743c81440c05200401a0070418420310080a6000d0341c204500f15203 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 939575845 1250 939574595 939574609
    0x1201080d080118060e040f020916050f070809030105151009080a02090601020c0303040f0602010b0105190c0203011e021b0105040b07030c0504260d020f1908070b1305100506 76
    0x40742180305100f81e400c8103c14190368004002916140400c0407076468a030425140840100006034003d05100011070000420307030b0b1000d5840f04a80e201c8a00d442a0101c0e040426400340509588130403091182c1001d946d400e005550084a400c2110005003034220b040100b09014003c0020901c641120304101180000c241103900540403650b441c1c3c21350362240141c2c2002041071605a02d4080020301190601001c2c04100940d81194020441000b45200558a51094400302075080b82c2c04600705c0d03401c0b0b2043c0030020a5620107400030038080c1140310418900700002d8503181c00581c0100b84041614664264201d588106900a10242c1040d071a10754005c10b020b0441d2003015190444514511f01840c1200c0040078041012400201c080c441070380103a0038005001e42901608c42c1d402c0c1d10303610000b03078818403d07056000b070329413003d40d42002c84150901e40c07022034034038109100e02000325001d001e5080c0b04505d00c201003040501a40350043c203104901c1b03040d40c00c60303262106106a0f80c03141c00c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 939577095 1250 939575845 939575849
    0x80a060b13020a050d06081501052403070c0510050f06100215240a06020714040f110a2d0f0c05060703060f0e0c22090c051201080d0801 60
    0x11500148444224001c2500300d501030004072503181c000521561038070780c4240200318440c0d80d200c0420031162074030552925240120700d92018024010018485481d041d15006001d8680440303540d001200683d8030089908200d4188000c507608031560404d024042c0841c03025a00707010010010b41c130f00042203080340c07c40a0040c5014519184541010340d00802020182408031600d00c8000d25000440482802c840424100b0031511452422076500700382e5198000c0e1032054029080c1d05080c4000c0c03000701c44d20344d100f41d90b0041c0c6605030b4400e90652803040d034861841c0e00e0051643c6036040940a0007480144000c501117004000d840d80d4014012140b061151406160001003120301c2c8008403144010064098001d0103514107100d050740d01544047c08540d040c0d8803c003500c0e03a032801b02c41d804802c100d4214041c0703201005800340c040355060702803500013010140b200c041ca49450341031003201d83d85500b11000c142d00050014513905400706950050024000800d044034102000420300399040c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 939578345 1250 939577095 939577103
    0x6180803030a0c09120c090c020105061e2e0f0c030507020f0607150506030d030e28050d05090301050c0405010c11010e031506100224070c06060b03040309060504080a 73
    0x307490280c00c428461305080006243e12659011190310a041141005c030891007011822031405404107000e80c018010789101c1c400003880001d0b60f00da408621000000c0300700f80a98405102c404005038012011040c034500502c0c91070000c202d0302c60301400780c540818803110b8801c0c4810980740320002503000f412103e03a2541521491010440e01c0c01044842c042d01c0c200a010024500d0126211141540302e1442070340120308480340c2c10768043c002d0f0308450030352440080e250426244040304200d80b5640c1501007000340341e04040902c054444070300384088241040c001070070001e0149640d01c3c00340545a0070600009440780750500e4400060a10134400c50000d10100409108000030380c001d80080c0f400d0310303014050b685110002007400b1281001200c415108105c0e00f581c0544035840010b404121040d280c0e404520f218000d00c2408030310714000e00c60020018210902d00028130540204801414500031254403401d01c0d14015144c0c40054100ca001c000c4180000c001408000840452450304 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 939579595 1250 939578345 939578351
    0x308060a120807030507080d240929060c03030f0f01150818010e07140108010b070f0b0c0903010c030507021e07050418060c051b01090b150103090c030305030106180803030a 76
    0x491607c4040750080d4801c0b444014039010404070001d85030b0b03070845a044041e010300301e40c071519400c0742c9044616115641113908800d860750740900303001181c8001c0416008000a0802140240107441d540c0110b48800e44a204541442000c0394809030042c05824140818080da66900b0701c014a801700c010314401c2010314055038940016001c0d8455640d41c0711100c10b039a81a80c640b2801180c3c07040b60640380340020302c400000500c5c60610829105a10781c029807004840c000c0d52216031464030094400301c0040c0e000c0008071210307035007449100c0c0380c640d180d100450b01d407424010107801e080c010500706609560031200d540c0e2010001c25400141e400848001503050840ca0503201d001c3c03007010b0001c026514048100800303a4011001e80810781c09003c143d44007800d0f4600850a82e04d018400411108940c808030f6540e59074094112131507a01850002180d0705c0c6d139100c814003500385510980105030b001005202503070748520345100c1c602c030b03810400c0032180c075040c4e06550700c0c8002042c151507603507 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 939580845 1250 939579595 939579607
    0x24020102041508130b040501020319020c03090f011b1b080307020a0504150305010e03031006020a030806010c061112150f030a11150409020d1b08060d140102070308060a1208070305 79
    0x10501c16070703a605500958178140520b0940340c502c2c003e41c4141d48a003030400e04c0814401091029000321848482030001441c1044880024012080512500369060084035404600c02000000494a1044c0110303000d00001c40202c40c20814214a50400c40702e0750401c000f0315001d41c8800e410042102d1040d5000a21400c000b40000703c1e01c0241d8000410650902d400742c06201c0b0000007441c020100c2d15010040580d540b00283c2e580d4400b4240200460b2505000803c90345c0208194182d150203510046910340104031194a035900544c01c0c00b50b52409501403244202e02680d04824803882682c00c5001020100c1c0044eaa41c0c00b1400f008258100000c11007005d500e4185161141d00740300c00d0490340704c64035a000d4070f019400881d1141003551400080e0045c480551051040c140b0b0b0944424002c0d4440c03c0c00d009030a11060350545410581c082c0903405040c00744001c2c45103d020b6503071885c440c28003008010201f02c00368810301c03050440040340c401141204027141ca0059140c141a41d540b0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 939582095 1250 939580845 939580861
    0xc1a070f08040b1c0606021f020c070f08010c031d2e050708090d02031c0e0f191506030b0f04140a0c08010c080c0d0c0504030c24020102041508 63
    0x120a6400000c0c10001c0404d0031401850f002c4903041103c04c030080140109500c8590480c0d072500208441c030000c51014200e800744004541c018401041100240e82c043c0b81c4800d0b10141000c01c80d0b22a241c185c0d0740700003400045605204103010302c2c0d420191b0405110700d0000e040d580c3c4440c000103200000744051810f02e1001200c6c038083c5031a141c00014002407a00700c8000d4070a17041120b0b40c204500660820f1240c203840402103a003028005000385403090b028040d50790090240c0c8050081074415812824400c1500b00608c2800c41c52103003502074544680d107403d109071118000200c101e00e0801906000081080c0f804c40c0e40205501500c0c0740d00c0d9145c0c00d00840c1c0c1c5404074034440e9180079440340441032156401f1003030309941c20500288070031030041404468480085410791a070600601c56000075210a40111000f00741500d8403a0420746c0741e844680c09a038140c0d202c0600301c4040d42d41220040f03000054080b904000b80021800c00e031903e0a0008500550386480c4100400280090284 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 939583345 1250 939582095 939582097
    0x1203030e1c030b03030702040f060302030f0f07090504080904290102030f04030803040201180305010903110c030c1203041a0a030e06010b07020f04020f0d090b01050a120b040812090a0c1a070f08 85
    0x6c150000c200380310f000c0040100d000104024041680603020304219100c16500c000740c41000e40300c414004001d52842d00f07031a2001401c2c05401207803030703c00400c40d1401c1d03581c0d01c1c06040100d2a0304002000c0d590494504201c9028252000da03056410602c560400001c40d0300980e81141c2d000b08000e0354966031480122a1140186c4c0c860180310020100403040c4031055010001e5181700303807103245807040891a016611038800c9881c0e030b03050703000105501250074000360f17003450b20039400304490800c0d450304c014622130b000340c1600341c070a801c0104040e81d01c141e16004c4c07000b2003d00d071005403059505241c0b42c41054070603100c000c1d004007640e030030518251f00c40760b040318410340301c1c0c0d561107448003402c90b410000390034151416940c50741d24000202e290f140003642c03041103580c110f010a0480d411552011a1810010402c5d01c0c0180203004c2d8140c042c10040440d0700c05d00410010700513502c058a840d64240c0300740e40100007111040d611200c02200240c040f1825a5006850078081d81e4681c134150b101 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 939584595 1250 939583345 939583357
    0x120b0f060a0308070b0708010911090d030311220501030221070c060c08040201030b03030306061b101b0306271d07180e0606101b08041203030e1c030b0303 68
    0x106901c0051808103001e0710b441d107140201d142c7d41e2074410b1030340c1c3d81c0f04180c01d9a800b0076032103070400300400c075403015890a41d601c2841c0c40d11908002c14001d040c0d01d6a00e0198001643d154008103100001703028072282440e5040241009080450a05c12600d841d1174420061005000700c10310784001113124503019582113040c85610440074000300448010040100da8165070481c00b20303003480c03100b02c80c038a0080141d1748640d001034656400c02c00000d4600000f200800180784890150f816020b1a07824580141041c0724064540141051b0389600010100d0b5000d03403140720b91044d0038803080b00e20014201c0d6007448540402001c01c195110071b841c1c000c4003450992400e914400e481e000aa450034040c1090481000001c080062001c4448102d0f21004212035241d0b0012141100441c42c0d0b0080384818528000c00014140c0c68183e9038580c8580d501c690070141c5000c894011440405915000300088510304002400c00100283c80f206040c40c49525202c081c19102c0d610103165890420603980 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 939585845 1250 939584595 939584603
    0x12a0f0e0a140f0337060204060306080d0306030c03080c031306020105070e060403080f250f140c1f0210051006020c0102071a07020d060509060105030601120b0f060a03 74
    0x1038240d07441220181d040d014500b850b01591451070f02210514001c1400e00d100740c0c40081540f8920b5030f06540782e0842050488400180313880035003003004181e982c4041c0002e4461038070002140e0707050a17a801e243c142c2500c84042007505001003030001583c5c032141074044a600c04142521240b0710141039043d8051041384196218088600240c42e96054201d180a041c0c1601c0341d4802010354418042c5510441c0406440e04d4810000380031b11a1100c801058164440c44031000b000c404009080742d00c629130f0200b990f60441100100b8184521040d0f20000003001400030700400820002003811241040350804600ca601d42040400b02d0090020300d400290390403003001385240141c07940340700c0f04582c0555001840b85002440b03103540005640d2054516001e100b00303001d61010030014440c1c0c4590b00480e0040c0d450409100019550f010f198001d4024002034001c660405041c1854210168802c0808a5041c041030b030108000e890042e40100c02c0140a04059803000f0100b011000d031907000030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 939587095 1250 939585845 939585859
    0x40f090b2106040c0626040f0803041101080f010302102f0f0d0813151509050402090901110a050c01110f030a05070e280506040b04030302012a0f0e 65
    0xc401e200001c40d00500c101d103e48024040161610012280d0385051040c81d060841c0003003d10100f05485400700354020302c210310784c50140328199a1280180c00903101120100c02d071030b03000409580c0002001e0383c00031000010814540c50f640000c0d200130400820b05042c000303180381c001090805442460380030b582c1103c0c0070100c9604030105903660885c07643c17101c109005000358000180c0c4620001800381d42d0410200c1c4201e19261503111051401c45840b0074966500c40d0444410510440220000d01c044440041c840c585030041c8442018010042c202d607034940645066065507035021766240700183d2420ba615005100c1e0f0003030042c0b1300c1c0c50040045000c0890440c0000d1800401903100e03106a00040c840354540c02c01c02d0700d4044c400300f1040d600030f910640342011007000c0020140f4030640022820f401c140d56101140003a03000b40c11550075075400107414400e242d024002e035410b011402c4414000105550b000196100c9912400703c2000314010001031803500c2600d0644103100024144 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 939588345 1250 939587095 939587149
    0x3020303040b091c0302060f130606091d06040203060114030a2003150f0610050d060602030d0e0a020a0e13140a020108012c070203070503041503060b040f090b 70
    0x2400b41d003001208612801682d8802410980b100d080c0180390755240e0020401e58807034a8440600c0b040041c81e000c8401d032101c0c0ca4001041003030040380300400110800280c2922100441000c9008074110720810381d00235070034000107840020b00c003411200c45640c101d031000e0035140041d081040652010b0400d00d4060001c5443c40c42c42ea40104180c2c104408a8035201010b006800303524001703d403410564102e135400685941008241d5018003056850041d151290b070512000c100c5440350441e500691001c950030078110090310031107098810000040012151603030000e000101580a0780c0c082c4810300000c140f60080880c3d80074062644044080060551541c06da59125006002039000036150f0b0000244120700311031844102175440d1750f02181002c919005d40b07480034080e041d0310844c0300402800000c12002e20181024103010072001e0f01101d1001c10050984005401c0398107000b1003004200300345414200380708102c50310041e020030800c41010000b20420711082800c80b8013240e0307600c8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 939589595 1250 939588345 939588359
    0x15070512040b10210227070c15060b0301050415030f0311010b010503070c120908100e01150b220b03040605060102010f0b2809060305030301060e010f0903020607020a0302030304 78
    0x51144143c40c5100030388800c0d560380205440507540882d8403001c11000c0c81580c00035040c6000490000f111300740306840d959070289620005428211000c0b400a2002d40d4050104141440c5121035400070304000d02c880349c1849240765040c40706106280c481c0c1d6940c0b0110303116614072400705005540020801c1034021050030b020300f1100024200343c05c19464028140c1096010307400340d0f07004414590794510b05650795500d011100304007080c518103109421400182c541410031480240154459010804c0e00075900e070b07203003503d08200c90400d513a070142070f040c00170400c010240d4405070300715030719030301c00d110501d06401c00082c00b600510704000e800020413081c812035800c0140244800c0c1c1c0200060a4000810b07002c850010944a9201d0107401400a0030291050403840c000306500000e000e03aa51041e03035400319810341c2c0c0101c81d50b8001000400040c0d40060000300310726001c2c01c1078007101c0007030400200a0039090000070300c951400309a035415501c9039004003000e503034013400b240e640d551038001c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 939590845 1250 939589595 939589613
    0x1e0a09081201170d0909021308010606031e0605010e1e0d030f1b02060301050d0302031b01150b090312220f08100e06061507060609051503010207051507051204 70
    0x41c07401986608500c43c2200e0308001002564611580c0e82c2c00009802c20700e14101030f500c402c0301c48203880c0c2104c802040a000078810000241a07a8600050311b040780040c107644404000080d02202c6d10301039003080385907042100b41240060444a200b14a8282c460801c044100c0609040d0001424800802055002950802d0060050b118201d002c6060440143c040355681e400a401c82421310040003241040da08a062482c40390054174102019000d08850fa15421400f07280260344804007690740310301d602c808202038211880c60030310345107142c07000c00e03643c400c66440210309410005080051421051010501000398116030300c004e80d8039a051003d0b0b4200b40940b110b540110040703142e0610040c89400305840741d13000501129641c0c0010090b40c0846003014603600c0da010040200014040d00c1603402030001000005510f0405265980020428000c054081d0f0701c1003120300c0205e900024011800000111604050b56030090111101d0081c10514140110240180410080d10385 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 939592095 1250 939590845 939590849
    0x1d07110a030512160c060c140d05150907020c0105090f030a5703080d05100b0309030d0504140a060e010e0307030516060204050d1203050604051e0a09081201 69
    0x1500300151500e541d080090444c2d5040d000110b9908122000060f03a980c000c0704040300c0c1c03820003c02600350148100e04549c0a589402c1c4c0300c81c0c3e00c42c10003440118080d10384680210958464003076241c114006540c031040515214103101c80410015020b580c5c05c50310007404078028099840c0d010061030700480502203002c006161100c0340315145001c0703c1140081d040510441d02a2154404080d0061160500640315011885d1510004000f14007604010103c0c0e20a00344005206e26140c2c000f006101a250007a000a82c2c00b08180300110170f000094a0310300000341400201510340707290180070348030401c42c13403001c81c0180d11070503007071100c25441503814a00000c006c0c0054082c0e4000d01d038992142d1840240452402d01c804101000000d01c42d000b02e902c22000186499100d60004004940c901001c4500b1003e004075541450313030502800341c10403c05d030740500050a0161a1492402c100741f55416000805070000341c84d8841504000212600204415a591610540203203000424 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 939593345 1250 939592095 939592117
    0x150b040603121d130203090c0405100317030403080a0209040912030c030b1816020a0203010f0c121b0324141203040f05040b190b0a0e03071d07110a0305 67
    0x10f001c500c244880607226a0000e100410760303400195215080f400941001d88000d00c180310710583c0201e0f03500c8612606000e610081c080800c039034510315150848082e440d41c1908410f20a105000000f500030105507081800c5c1080541c6620040c0007207401441c90710703005030404415001443e54160146d101c000c60349540d0340e05110380c0310244140401c1c4a030314004146a041440300003200c000e841c1c420556016041c1c0f040c2c0781e2000580d00021b00751075500410501ca29515000c02e0940340d0804100c0c1c085a69500007440310305501c1920748880300c0f4112440c401c0c151110031b240048103510300c61204510041d00d041e0340f4280c5500740c0c00b040c3c5c20300c022150f00070030001c45090803041000054404885d01015046819070400e802d00002e046821055034000101003080f504001002141c2d0b4060f0651480d0181c0300c001d005401020000d00080c154000d401c501414000401408540d2545102c015100b40140e151804210f8032840030800004041c050080d00c5010994020028071400c0f0503 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 939594595 1250 939593345 939593357
    0x209011211221d04021309230115050102011e11090916090608160e010c082b0902030c040234050d030c0c0b101d010306141003150b04060312 62
    0x1191850b42d05204141c030084d5010031b041d00300041041140d0442c01000b03201e080428000030641c01c1c1c49101c5c0a1a90300c60310980d440c3e10070241515060743c0182c0c0181401d01c005d1020311082c20f140c0c00c1d800640300e00741032f2654072001e00501c8507104000310f4110040c0a0004c3c011894903000121990000c84a40c40014580c404001390b101c0c441c4c2c100c540210b0002c51540c044052070f4600391003051410012070305104c84514210b0129880802901074400c0100501d0301d1000302e4007048840b00d03150112002014500400d040246e20700040c1d03010031800030b99005a0754650310721154440c1b000f03080307104001140c800b808030340b003081d205540c07892174411b0084601045258005800780d03460030560800050708a224000894411583c99400c5800d024800c8041e40c2c4594030003031035203c1e070190704401a03110001002000032030720078a245800e0921f00130166050078071000c5031032580c52001400141c9082400d14454800381e1000590220080003045007a580780380c03203186032510070209004140 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 939595845 1250 939594595 939594629
    0xf06050405150a14091311030403022104060e0a0807030f1703010b07031d031606090b0a0e12010e07140415060801050402071104090302030c0d03020901121122 70
    0x40c07100180c519030b10450715959444e90003900e203400c0942107003c84e160b01c164040d407250b845120601c0703102c69041c41d9040c119079038a03040c20083d01d0030241344020008034464900d0350a00e00049c2c0e0540c1d05541051800e40d040fa820400020742400054201007075030b0082403000010081c1d944a4174603040e1040804000d4003040c0d80c0c0c1c0c051140024072500d400d002c0104051070001c5d01c40c52101c1000107259074030b000642c0c943c0010a16107254810600d900452504043c071206401c0411170000340f845006980c9042d18000c0000c041204a030700450140030420140b20740c228007900308114a0350000300700e0b0981e0355506400d81e9220110704150b4025854950f5200d105408441c80000795141501c606016074078003410300000f92b10612082d11701080000022445a4a60160b4075650303001e0750046846548050649052540501e11842403510403c500c05450b60044a2050780f91a01e1a000800a080e80b5510320b1520480000158054012415202d165080d030001800d0320440032174064580d03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 939597095 1250 939595845 939595879
    0x2090316062a030c121b1b14030a0b1b0c030301051e0f150705061003020f030d08010e0403030e01020c100f021e16020907050a081e0a150f06050405 65
    0x315010390080c00280b410403c4c04045541520003210807881450a0202c0d94400b081080e0141520361301152103160341e02e840d0729100e04911f0100003828859000c2c4044c03840d0300700001e640d5405032000038a144402400100202450f0245c031800c5e01e010301000f9550211040321303d803203500c2406201d210f84120b00aa0000c116280300040b031001e0044d21140955610074100450341429007151404040200407050000b84140101409401804c022400c0e039405e42c4100803160400d021454003035030119211052850380001030034110b49200920b6001e540300c2c2d08040700602000e4200c00078035800003900c0071104100190801140784162400c000014003110608181c1c82407230780498400300040100d403c00c0c0d1458004082d241000503545805c20030942c04195040011600c003000f1a0020904000c1c02c0d821201060303000c035000d07620101c0c0da90010040e040b422806803417021241c2ea1010603074114943d4900140140281d0107072012038a41c0c41000605030341c003034001c0b14003d24801082501c2c2d1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 939598345 1250 939597095 939597167
    0x607080601230a14041208040305010b010c020319052a0a1502030901050d060e010e0a0b0d0f1509140a060e010e03070321060f03060b010e03060a0209031606 69
    0x100d1610318081d290248480d401c40308400304d6000300c100d0401c10000040c0803d62104800e0f921482000318a495074136500307240382100c0301c9809841c144488102d030701e40161340110f9002d40619102e0030007001403400e401c207686000640140744800c2d111001c8520303d000d645180c1200d07911003c44060304116245c1165080019040000c03030090780c07040c08805195801f0381e004d0002140c01d100c001801c540e6403026243d2900080c1d00c5003c174841000184088140c45000c0c80410410948040214900c036070349405500080907800b420f02e15140716490f09401450300004040c54202c55005040410340c0c100e00d40f180b000754801c540040c40d2203480d40320000103014174001601008040c50a2507415101a2144206160581c150160b03c3d4031012251407203200b010050700303c0300ca0301c000725803c61404404030303a101840c013414001981002c4800342d0b40096021f9000d0326500f800f68484a8807404a49044503140104c0c41502154001040c2580d10031800945565203184010b007070341c1404190111 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 939599595 1250 939598345 939598397
    0x180209060f034b0613030804020405061314090c0f100c030512010b030a2307031a03030c0f062d0414010914010507030218040902060c0607080601 64
    0x15003103040503c0d100550454601d00002041104a50b10790600c10fa207080035400c00140d00085124440110740100c0c03c126144d8840c003040581020b0b92042e49000c1d00b01d0740d004000900c141d45070400503c80b51600c002c82048000395080501010603600610101240201d503070650074400c0c1d0042124600d4921408007003184043d09024404003482401c5407000c0c0410016400d2090820403400ba40d4101e42c1d100703000b400c0d8408a0740d00c0e0300300440144c00340c0301078620502c0c0c000f02141d24180040d2990000c10b403c1095400c0004404031752082c48605c04a0403c00581d05000104d42c901c542070700403800c46191246401030f80e2107992426182c241040001501100788031400040041c12941a24000d81284c00b901c0303007032210b550881459081d2484240c08a0707504002844102080c103003400307a5608080300c1c0c1015418844060788007505805000c14071f40c4500e0315803000d10190b440300402c40e0310740303000c613825200e5510b403480e03020300080015110b550002d002c2905403040c403061400e000c11 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 939600845 1250 939599595 939599599
    0x9031d06091507032606010206010e04053f0417010203010b040902031906082103160e0d02060f070506090a03080a0b0a05131e0203040f031110180209060f 68
    0x344000b145a0b2103407103030051081101400ba40c1e155214035102030b040c07048a0100265000170a40c074180300020b0410506a010b141689840300034400000e40100b0051030207007006050f22400d22443c1800c40300408c0b1a1481c0382c241d130740e6044040a0842c1d10b0010300a8030b01c501e11103004482420400c600303d1000340728606482074140418040c0c403105800454008108400c0c800d5002c25100b440422281c2650081540b81e01c040c11003d42c007000420f000d000c07507004200441c00c600d402415140c003480350482c1d030410030407980300390403440c1e0320b07405101d000d140c01030f04258071090301d4811215582c0c00404141d132b142c446c000004110050029940c0040c66044c3d8a400703a5450707580803c4081c2030141c1c401c41d0320541d1304001003840d80314803801c0b5600751b01c10304002c16110790f54034201d132860305c1c00902452018010401c10000c125000c440840840d45494144e00c07114031040c100341060041d08041c660325060561440d00c0301420b881d14400503000f250307900c030310303860745004c10401c07800030f201041e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 939602095 1250 939600845 939600859
    0x308041a0d050709170601030b071809020f0a090918021c050f0115051c02010521010f0e06011d0405070c0b0c0409060b0c070e130609031d0609 63
    0x4002190304010a8000254091006081c4800301001c03400b40ca004803002400502103d5007040008076101008980042c864054083d03941181c4881d0000c4000400100c1800300c4054003081d03000d030b10680c040060944100031915030300801032410895002c480c98900050b4421008074640303540f07215207120408004001c6012400700d41c00c0c0482940c20200d2082043c0034803680c2c60100d0020310800c00420f41502c00003c801c640140034500382000b5400050041110040c9000040c0c4d050810a61031502400d04a89507142040c024803128080042c0310608001a80001540c0307581c0102030060301c004916481c90b40d42e0310001122003610000b54551400000701d850b0325a0704141d40013170b800c0001454110114841034841030490f507803d0360516181ca41c0007500300012110b500c140030261031840c00c4185007002c02e20700300b6503c440c14020b40c41100411004581075a05070468908081d0f0300c0f100c107100a0a1a040203811725041c02c500b0007081002070520b160a207410000c582c44444000c20304 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 939603345 1250 939602095 939602099
    0x1509060708060105270111030f0d0513140d120c320a20070b03040b06041b110d090b040303111002040e0703060905060108040f0302211e04030804 64
    0xc6404600241c81d45041c4401004201400e40da0a45d485503403411445001c089804100b0005202c529102100c10b0b01d80c000784080510350310a10200c42c201c400c80d65002c1a00d499030005400c142d2500c1c00028136132440b00450b011145c01c04641016000910f0712040110085131203100c06503640c2202003000250b44d0309004203060303000890302c06100843c0003900039110f001d92001000380d02c06070111000c070309103461221809003d521403001080c01d51010301500751400340d44110901004c0d000618102a2000081e4191603541c0012216141e190b101c0f00382c4201014060001c44841c1c2c00d244c518029050a041c0300c40c0103e94140c2110781c07400c0340c07500d054510b4078121480002c0701004030003401618061040c00d00c0724000380001c0c0010408038601418142030150444199a01c21103001c1d041208004d01c07030380c201074000c4d4090b0300401c0c40820030046180c101e0904800d00041e07151403003114400c04800030000080c2c020206070b812505081d9081e0520b14065010b648001850b0a100f0001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 939604595 1250 939603345 939603347
    0x30b010510110d0c0c0f0602070b07050f07090b0906010f08070c1506151b021503040201170a0213120b16050c03040914010914010b090d061a0315090607 67
    0x50365400001c5252040e100304880d0a114103000352644000c0c00074104503908000e03c0701d4900c0300300c000c051034201c00030326a20b083c4020f074950f910b43c81580c2003103001041a0f0140401841042c503a0481c2c1e90550f62802e4491a01034024108400c00b640030385000b10010350254011b50540d842e41140b91169210355840900440340b890494508a50503030b109042c181420303a081c0903450288c500380c584000200318601004041445072140301d6912054002a10056100c0383d950b00c410f0040700384490742e2a6200d00059803903070007540c0f40705c0c609080e280400c0a000000da0103406441d0940c04441d0002d43c0d1540898600c42480c40040c10000044000c103002c00042d260400c03001e1840d05060703007030200802c4a40e0454029034012540c0036110840d0b0345908441e44d403400c1c00f6002c109010008001d0044283e40f45440502440041c6030001500c0105503a40780e100012160348070405010b100048450080702038040000ca074000d2168240082d10300608078078035032255000c0401002c540d580d00c0c2d4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 939605845 1250 939604595 939604609
    0x3050d0f41130b090607141201050613030f1401060603020732030a0906080604020304050c041e020d0213300c150203180f060d090c0803120403030f06030b0105 70
    0x102c460450400c40841c0e1001500503040750344100c9090380500350a2a0904010740769040408041d543c2141c01c0156a0884900214683c1561030598405849203900c0c0c8014881d0304443c1c001501402106001000b00510500b9000d1110b42c640000d1000a0740c070f40b4164140d000d0701d20000e10b1003000c8424061484200112001240b049080d039102904002d101681140e100d0000d08000070300380c2c0002d010041d04448069000b50098501b14030314641a1a99901d50241004c00c912640e00d52041460074844520561012028107604655906009000b24000d504c0440820000700c490b15000a60403a00603000341100380d080344605000d00d06c069030b07002840740a00101c40d9600c6011000ca49402d0b00d4580544600442d0000c41d0349058201c220642c0048084080c0d104690400394107442da201d0348256011504a8180030515a400340707407003d4094410f400a408510001c07941d01c4603883c080310494010b9009890400040058049403000d0341e00781d0201808000640004001500f481d113 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 939607095 1250 939605845 939605851
    0x6090e060307050d0b0a0c09030c06110c030d0908100b2103040b0a030c08130203031e07080a081905040209061329030d1701050d03050d0f41 62
    0x702520700198079a000500b680d0320004003a076006951004200b4500d8103441031844454243c1082c02c440f80c0380d9580c1c01101640c074080c030010000710303013802d1046050130410008a036200800f52030f1940c02007030004002d0051031003030001074442c0c140c14500c092401d202e11302008401402c1e607039031216465030403211150440f44242c990f10041000003003045203c80a01035000f01daa0b4041519081400e000300100c102a1800000000f030303216000041e50000100c98071081140c40001e80e009982c0081460760007001c0007d0080b80000484132030403035010860501c40c03929001c45240c1480d00301488070031aa400c6030000c0d0410300c040d001c10700760300d040c1c2050a04107940d0b1a0100340c103800c007103e045424504806a00140210300b842c41c45501e828004540c0a16052400140604038243c4c03450909106105144c003401960500a003031512a608440481c07500359002d000c0f41c452000040020310000c102c031003407040500c1035210a20104220181c0180c804540404008460f2009040120b005 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 939608345 1250 939607095 939607099
    0x106090e031e0d11030130030f0201060e1306050c0a0f0e300c030a0f0f03020309150306240a0f0909090605011e0501020613061d03030402040f0606090e06 68
    0x51082d102c02c07440303d001e600305104070b20601617201d515160340e041c400380b9103110f101d880407840c16140041d4420010130b0803085401d89005196040481801d03170040481d6004101001004410084403507940c06804142d944a16803c22040d50707078109040e264042c00a84100040c1592030301000580b062015100c404002000c503461050f03100302c1f03800d0011420003600907498160501070300840c801c2c82101041e4605038090f0031402c0403503840d5003a1100e4200c1c02800f1150507032100c02414820415500040c201602e0b4000c1c2c4071004041e000d80381c004a845601c200381d05480398803410320420304200d104240c01221424400c11003820790300c14040340145800c2000d40789000520241c00d0003580d0007a4081c031400509075040c03032590140b550303882d580b00c00301c0c4a100008101590340000c07000da10511003119003a078161589801e0011b81142d10100c0c04a03800003961210800d00230008500540c4200da0400180340d95100343e07416519148100c002241c0502410030041803e1620994031a0380 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 939609595 1250 939608345 939608347
    0x70519020102090409030e0a06030c0e122d120403033615091d07080726090c032118090916090506060a0302070201030219020f0106090e031e 62
    0x108040783c00c986200c0001d400083c20489003003402e00301410b10001500c01c0d858207114002c1c1e640c40c06441000c2c0a101240208400dd9410000c1c003001c0c0104600000e80c01c2a14000c001d0210f0b001a01062402a181c1e080c0103000d41201e640640104071400c8a5160315103840b000e021a0314080c442c0d440d89005c1400000010b0a050505501c65072800501440c8004582109140000400e800c01c580c00449619240014040506003402501c43e4043d559190501c8141d880d82001c6030380b15440d907214606c14030580e4003060084c0c0c0382451140b040d0442070844507146070b42420555600b06520f501d547c01d9a407034006000c01180740d00144113a40c20403050701d00f500181d0010031000c43c0b044030000ca00380c01a07105a00c10030103030751010000b4039644100307100303d090180000c1d1840c41a101202d051680c0010700c2e40469000c3e8056038480f500c1150030880450342114081c0d2a410042c00162495281810106240c000d5120300e402611000000790300305480c10002d207a00d0b00d400c40005062000c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 939610845 1250 939609595 939609607
    0xf090323070f0303180c030804060210050408040e06150c1509030a0f08151f030506010504450b1c0b04020f06040816050f0d0809040506060906280305070519020102 72
    0x110f02100d200540c0708000307249e5a80e242010090030318180f0500000100d00f088140400b1560710410f40301034030074401203ca45900c0d103000203980501e843d1040540c0d5140868102240c4101040b84c481800d18100884c46684d00d813840e264032803060300c88120218810320b5928030094801c11100381d0102403d0b1600400e05a5540090030402c0ca07a042125241408010160003070b906003c5e80c2d4000710207007802c03402c10b81400201d1100011800d100c0403082c60480d001c20340c10141d08610007007003540c0c1c030713407043c0b6070034a00e1260015207444080e00d4020034044200c81c10203030303e1004115000b80c2000070600039858960030800c03150b43c1513210b00e038070040078040031442c21070500250172890341c416201c548051404040c400b66150f0100354510815103090404041020141159155001140d002807550b0700d50000420700c2c00f44105954106e42c0114034044450511080c000724107003410840e00d4030a0b0418800c6040c0c640c01c54401c000540d0a0000d80501e00740c202031089010854000541010 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 939612095 1250 939610845 939610853
    0x9010f2f0f0118050c0603010602060115090308160b061903060e011119140a050f090d15230c19030603021f11010e0d0c03030f090323070f030318 64
    0x10010f0501c08440380c240d0751440d04214042081c2003001c02c069450074150343c1341c01000f80d00c80d03505110310841d520300d070204480c00c1481100302c040a903501429154484144402000c90040c5080c01260b1445480012030703403515046000001650408440d0b140d624115030794500130341400c0e03001c00002d40d21504608000e03040d40c009804484040c0040c2410020065070081121030382c15078070070003003100304281c00322680e00c18100e4003600e10344521a9515001030300403905003c850710020700310030846504540000000e0f0010201000c107102602c00044846501e000c03491810781d600c151002c020404810100c8400c010139955000e2424002200d43d40d940101d04000c1c101d0100280d5800ca2011014145400c8440000c000f10100020041c40105c005281c0d5500c50003c080c6084c401000c122000301407107604081285c25100c0d80a0113044014074000d03101c44a490041c80041003050711b0141044201802d45044940242900606000750f0300c2c1907004124400c1d1501000118040d0364005c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 939613345 1250 939612095 939612101
    0x2030f04080f1c0c170c010f050115050c07030f020a0801050901050402040e21030a0608150703110c030301120807050a030215070c03050904050c091509010f2f0f01 72
    0x24075003a0050640b00900760308180c1019024110786401101c0e8209007441980d01c0102004005e0348294524121490001103120030700415115818039800c111b4003a0b06000c0503000303141256104000040002c0e40c151042d9400d000701c3e060160307a9444002c041012400f600480b009450000d0a140496a03c0300011030a42d01e048902c05e0301a915141070004500f49032140d5080b100c4100054414201c500c407040845001c1d03216061207000010021900b401080d9015000500d158400c403400303810001e10b065202c000480d41e804c0231030325010140103d110100200d52042a0000145245170308080c406840803442c1202501c2d242010710040340015000c2280341029130280d001400c80113101204a402500020001d50401c0401040d000000e03802100340c902002c1e00b26000f04a56031152941c1ca00c80c00f4a01c01a580149aa11880c01c1c0700048001807445000c20784c0c0b8030800303240100c0d058812a01d0b400700c448044504818000345000c4a22170710b1a50180d40c82650f500740b440001250035 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 939614595 1250 939613345 939613349
    0xa080d1b0e0f120a14010f023c04060507030905061c1514060c0f0105010621060e0601030b0a0b03100905010807260a08040303170f06030309040c02030f04 68
    0x4259400150070181c5002c1c592040b01c200c0c201c48800746840311864464441040e0f03e0000c3c907018165290380e100c04002e4010300050003c00b0390440d00d0701020309915007882041240c1d00c1b6800d4102d10209101250000c003c041c05c441003d8092410b880c141e0122820391010342c0c00d804201d40241e010800c0c0d9140402448201040c0803500d8440b00c03104100c5c400c482c0c0200002c40c075110140c504002c0c40d051102c003895110412281e0340d4a07040000405418101e0061a0081c40d506e030034004104560400008540480c28000a034140001b100b059021281c0031f019000240c1c586ca400112503600c29080341c0104100940b504004a642c0c000022603608180c0300d00301007007851141800320000034494039005007600300040c52401d00c0e0000610141c00400800b102015a0000c030381030038141080b044100541c00490190380d940d41e030071b00601c2040e44d4001c0e46183c0350894007040d1205050030816002d070300028003462074460040100001001e02098a10940c0418041001e40780d1107240a800 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 939615845 1250 939614595 939614597
    0x30702041a0405090106083f25030215070c050f011b020106030c1a0f16020103230a0c17190b0102061905060607020301021b0c0a06020a080d1b 63
    0x700c00c0c08040204016079030010168030b40c070383c03504204101c441000108801d5110215994041d04e00d2514a00942c0f09542e0402a03200c101c0c6a5603068a16a1000184074a000e001d00251000e0098904c4080d4002c51a4014005910038102c1020b140d140c01074441e0005da00f030400300c840c0c2a650389c0b00c50074016144646180c1d0b940d40c8900404002118034030025061440c030007046240d055540d07807030807161503001d0b000c09851800e071061038191440c0e04540e01c4a0000f64082e8903003070808140244200090000c07400281090b05810740b06103141b94892600680c44a11602940e6480c0300b4402055007162910402c142000d1401000d66a444d65078010303101d84515425040c0800551429186080b4080341158044010032001d0b0341000541d1543c0400244082600c0d2103403c00585940038188002c3d5165100040c9680030703c0c201b9826100190518041e035510310310b51400c1014550b0148545005a004481802c0020750100010840c0003c110f10011304210400c20700090704400041c07041c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 939617095 1250 939615845 939615881
    0x1420309061b020c010f051608070203030301181a01080a050a0b0d030504090c1806050a091508090f12250507080303070212180118030206130f050612071103070204 72
    0x1880342941445090310b51300382800c0021244401c2480102140b248200349052000607082543c1009040d904031103049800500f101e45a584941c40500100b104480210306d5901d8100c100d60f907a00c00b10016600903070140c403201086d03640c0d81e520318064035008000c1e031110350750340140d030791207589030916038010501a075202900c89003406004801c48a0021009003488105032405620034081c03043c00094822500d4540d40b42e503a508001c1d0382c01c9049400c4000820860b441c0f5402c61940408110720840c0c9503c00c071420448180c00316910786d400e9220aa2540e0403c024209008060281d481d43d03c03030040c01040300c00c0d420b1783c82e1142880d010b0341242d100c40e0030002c2030248165040082c00c21014031100c40f545000340d0160001003c6480c1c41803903042c0401c0c0c140000508150960840007150060001c6949034442d2041c1c00c1080c1e440d00038804581800c040c0030690341801d4083d0b0740e2510340340003400120744660200395014020880150b4880c4400c2100d000140c4843c040c40c10341100c005408 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 939618345 1250 939617095 939617141
    0x40b01111c1202130620060703020307030b1206181002030c122511010209040603080a1206120813031502090907020a0f1e0606030b0142030906 63
    0x420009a1101c0104010f005025500c45406a14207000441e401d6090107110710780301c00700190800a40144003c841d010344020004000d40540041d07100341c2d00d654042020400200410140d540b58135800305d00d0b40c4c0120300081300304019200761055440c0c1c42040f0380c20407800c052080700340c1c0d01c01c6401d480420000700b41d09030350500000010350030610252174100c5003280c00144900000d44005c07035101700a8030743c2000100883c00e6046600180010f4418800c050312800c00c0000340d80140082d000140758014110082d1000e0300c00d00b810307650318250840c1e1000403a115440d0075044403524010b01480064000001482404a0301d1200403130080941c4440380c04040003480c0c00010002000c0d5001030b03406500240120019124496200c0b240c2c60030f158051841d1010401040300003440b241c513140d008020f100c90380c59481e040300e44103480d4108080380a000b68803000a00c040f400480743d45e44841c846c01007204c00317501a44210350b02d4005403214103a00c401044e00c4400d0720001d154135014181d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 939619595 1250 939618345 939618347
    0x321081b041e0f0e15060901031d0d0807030b0a03080f090603010905040b1503030d0c0306051309050c0f1008040f0206072009072a050703050715021b040b01111c 71
    0x740070014a0013040c00e980c503180c0350380ca8074100c201ca0b0051501c11400004d960050740c0c000d91104204580f1008400034180d0410a201e99030482401000b0101d4007072000031303e040b44240108020104058000000e032803840d62a1500364000e07480608220700140304080c86038403903002450003041209004905d0b41800d08044c2e040c401d01a2500c01615581c4070071100741e49002040380c2a504080000042841000300c04030001c0c40c441d04078503402410300b4529080c0801c0364000855690044041c1c801401034842040ba01c20704408032160000303411104284080d01840d00c1590042c0104540c107c50782080d0700240ca41d034800c5004039943c51220022a6a901c4d0850b82d4102c2c0ea1016298100c075402c0c000300c094070380c0600d5034040703000c04c000310300f14000144a020001d5206034000c084940c0e0541703900c0c245485240601580c03402e400e100340780e001114400218600340003540d0706441600400401800041d1401c40c0c04513041c8640125116080c03c003c1000c0e08007400100b5500c8199001000c0c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 939620845 1250 939619595 939619619
    0x7020d0b07021606030c0c08090d06051806010504050702060103080307020709090f1b0506091e0d0b01171903080919150f0e070909020111010f060321081b041e 70
    0x2c000d04040c0ba0424882c5051f80014089400720b13044041c40c3c2c1c07038040203400200740c5070f480c01c0c00030142400c1c00c0600080c813030821240d2a04440b100166601c1c0d0f80c86805100450b28100d8a02c001648060010808a41030100550300002d50344144c40015440c0d850550954004000441e001d81f0200c00c0d0038240407450031143d102c2d1500d00c19509107a440d04000558a00489540b503104145036009a0318a00004002801d40480600415100140f030704005110210034800c440d82e516410080311200c00010441d03001c2042a400540b10070300c415102113a10003001004111184600c404883d40417034501641d00d50180b0409102d02100800403144007624405008820610b00340f01c150010344001250360400c0c0c0b18500c41c0003941d0102070004840700c04000350020215482c00005041c040344681024007628000e4408803036284064000c25225a0030032002c2002543d4040480c6000c0300120560180309000c2d04003900b0b0030f03110300541c942050140300400703100240c401c00b0829440381d04 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 939622095 1250 939620845 939620849
    0x1a030a03031503122001020c12090a03052d060c070303020703200d020c03030c0c10032c06160c020906060405030d0e1c051b010c060c050a02010506060901090b07020d0b070216 77
    0x2d0005c1d230421607041e84880d07450f520684a0384552001181043d00e50319620505030065400c0b004885242540218000310403026400f915010a48499190103000740000e20501a00302c0410303862030101180c50807002504114811410041008079070003800c8041ca60501c14a2082d1000d131000f614194006442d10a1000105000b078005200014426102040c0800040025181e1120a2601c410124014080c550050202a4682c9490320000ea600d2900400d0151b40d074040ba500e0751164040c14000c40c503090500c0700040d50000040340142401a0001d030004030241026090645840c002405e29140903146000101c4446c1f0006451902c031041c40581c0412083c00c2550b981d85846141e100c180300d451110358804162400c8980380d00c034081c41500c80d90040c004014a41104600070615800028054015030038500450b036146041c804540c503480d016118165100c0c600413600c0d01ca03070420b103001c2e40e01c001101146000700c0d001400c06481550181e000d451200c2c1200121038481541d0303 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 939623345 1250 939622095 939622157
    0xb04020316030c0906120f0b090408120a0605090a0b0a030b150a21080c07051008041104111605011e060f0e09030d0905010912050406031a030a0303150312 68
    0x11300108481a044030094000c0304840c031010a03884201d10500340901030016800360071810319020001803100c202c029205003903500100c1c00464981c40260006e5840e24010305078000014000f00d60f81e0301051b400382401d84006442c02d24403da41c0e848600021804403011400d03200501581c5a86240648001000d82218515050b904080ca45911500d041d0004014078003000001c1901ca826800c004170b6005202c001c1c5100007805c65054004c0075500c0c180d804035044030209410214502e86070161880b2a40d55814250603d11107400751840c801c6400c2060312555a030b0b0709580d00d68905855503403074020100c01c011411903d0711a00c2d40c0000529400050000c1c411130900c0000140031080f2603170f001e8943d001003144841428039500601c160100200003004c9600702c14a219003090141080380c00a480800c00c9590f10b42e031000d14074000b50350495054100c0e800460010340207521140308041032140f035503002c83d207031f66418100d4680c580060012903019480746003250a184900058180a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 939624595 1250 939623345 939623357
    0xd03050105032a010309170304080415050a020c0f0105040b0408010e0601060206040b1303050c0322060504211b060210050c0414010e0415060e0310090b0411040b04020316030c 77
    0x43d900024060030050b0103100e04058494041c882480030012903103642080300c1c2d00e419070342e0500e4504110a6809845402c42142050070310081c0c01e8000c0341500d62400c800d4001c0d0458030110340c100b0407988040d12446041c01800d00000c1030100c6104042c10281a00344000588050b00c03003825840c00070140d000c00110350100c0c00300400261840b250301d0308100d000d803502401030701514041c2c4942c00307503180007407691002080e11003c2c40b80505040001c500c0c16800c030700705152035902c1201c00e4840d902034180840b10640021103280c0004901c040c005000d82030707024080802004240032008a40c1c4500e0050f4013405018003a40e05507c101900300d2110061030745002d1600107580140301c0d00042c143c0c14020940441410354586400410042903032542c028520b9840750700290007581e000d03a0041c040d10800701d030034200d4603c5104494507036800401000a0baa03c0c0e544802030400c482002640054a0f101100c025444030700186025820309016060720740d40c0d0103030080445001801060070008 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 939625845 1250 939624595 939624643
    0x30d110a152d051006120504020102120703032c152a310b091909140f0106140703170c18030c0609060c031308030301051003060e0106110f0d0305010503 67
    0x2c0c00c846240c1080603806c0700403030169500d00050381072001c0c42105443c50000001c3c080304040d4980d010750035222114420b40708203a4111322515460380540c8a00783c1591090180200008010304c406501803600f11102c5201a07022160408030316640c2a228901213002c103403808080800320812500c034406001181980d501d138400c480320040c05118504107401d00040500d0b403a101c10034034a101c074aa81407079002845e0346001000007441d81050040c407200c03984021482800b031071012a8101c50725503541c2001c03501e1040c40514140d0210000700e00b804064884140740303258488215200d03000c840301481c0c440c22032146494404184950b440d100c0d420084800c01d103640d80705c0c20784a4601058450680316581d11600503d036104030400c0d0041c0190032240000c44210004c015810303220191024510912070100a80594469024070140018001c006000c1d042c4500c0032210608085801c0301c8000d03075101e280c2403c041408104000180c1c40b200144043d0408010440203c7d028800c0c45500340 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 939627095 1250 939625845 939625847
    0x12030912091f03142802073315060f0e0306040b1009020705030a110f19081c0c0e0105040509041e05031206030d110a152d051006 57
    0x301e40b40000901c19601e40601d420814400d9120552030102c0c05400412824882240702d00403800340b0144c040760007410f008801c4020b0500076503a10903072241c0480f84d065000b5644412406080050000c030000c480901004c1036844c1c0121009000740b03c201c00364107414000c00402034034880701010288110720001140948000075240c0e4041e07040320480082d40c88003e900c0000b00700c1580701000c614000704200c811320401000500c091511a125004c0480403e401c2079265203640800d501945c00001404000103c84200652070a1164480c1031030070b04040c3d0700d25040b141000c0d00d1890140e440403141c0d90507801204030249a802403c0040c141454440090130006c07000b0401442d00510f11402ca20300103040414654865000040d40e403903d00560595005041c01c5505510a100350014003113807a008030601c03841d01031400060b0ac042030450f03c1c0d00403491103010304051916510300042e1001c0c500c0d5040c80d005034038606039000003264400721500036a07001070320201c407030010740e0170410020b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 939628345 1250 939627095 939627109
    0x109030302100c0e100305011d0f0714270f03010213061b0816031d011d0f1203040305120a0203040312030e030310080105130210110f1203091209 64
    0x40c421501d008101400550801c40c2c581d900c44c400e8179000910a0085c034509901600030038103030707600203d021285402c044540403828201f52641c007508400440030400551052411311032900b143c040e07040c580516203114001c40c81c1c0282030440d54100c0c01d0840681c9140c020003086c02000120002d50030010220380207190421940710711b20902082c0c8420203030302c00b030346005030a0540e00000d038141ca43d20a02c0308900e464080c050200c2c0020340074403900c1c0883d110710015030030340038042e50754505098050110200201c3d8006000d64040d0081c0c2405003941c5d00c1c0585200141a200040d603150b83c80d625140d441c10385c22080112685009100c540030b441da0010a8801701c0350424840c603401610711405a0003003103c440110498000003003000500d0348201400300c100c039250002005555034040d1003413000b441c2000003e50100000c102e6a44d02441070190030000802e50701940c900038a00e060395840c04600500c0140c900602004000d20740405004400c60b071001865007e140020701c50001c0c0f50 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 939629595 1250 939628345 939628363
    0x605092b0e0f12030c06070306060f080a0b0d060e191a1803130f170706081504020403050a02032802130f020a030b03102304032604110109030302 64
    0x401c0441290118190750b0500391040940700506100c40400302c21203110f89a52082c00e002105104078408292054840c0c4980c5003211050354030760320a4103020300100d0395220090b2110a1454903245003120b5551201d035000d104a22400c0001440340000030312a05149a240b090541e440c07400c0074100c042841506081d0a41e08003003012107803a680c6811100410920301400785041c071011462141c41c03070761030181000343e811341411011000c5e070b281240f001d5181c00500d025042c0d00019000c014141c05800500e0b0040c1c01410840d10500c10040410120f820546c4103492a9001d04400415410b080c0b15014140d1880104148003148a0046120450059000a0040c1c2130316140e000030807240d501100081d030540c102595280c16a101c010003800740402264070a02401503204a486064814214150200520410021040250003020102c000d101340c041c0600510b8072044100003900f03107600ba074181600d40e00181840c2c10702e0f4030400351038181c0905100c1c5a401c01e01c0480c1d000221020 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 939630845 1250 939629595 939629597
    0x309142a06040509041a04030f02101a131b03150803090307120534210602070614010b0304060501050402030c0f09011e0f08060d1a070203070b040605092b 68
    0x40c0300e44644c506118806d030081c100c1c48001d0b000c0c8040c001015400000710fa03c4014a0303080789d55900300000039004613804080b07084000d0b1a1503e61103c0d901b04142c0844468400c10b40c0016004444078080741011718840d00440000e6a44540380013060030458010081c0c400000114105000403010960343e011500801d5102c00305810150304208080001caa0b0300b044052241d840e00358000c00c62110b0019141c481c440f101c99241c0c000c00c1a074210700440601b1107a9a80200b001c80300b03074403041c0c0254031035407056072070588030000a880140b00c15403941c000c1c0b0241250998a1400e41405000c58030103811140c45540100280054101c0d410f090f280c0b40740001d51001d960b1310242c0c006032561028028001108000d042044603c0c039005103441e0318a045980301c4020640d104810031041c00f005441c028015040000d41502d60910145156803244542c01100e00e0150507480340111040e0440c2d08640d127039150400c01112000602840031001c00e550302d10010010010318040f003102c1c001d94184 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 939632095 1250 939630845 939630859
    0x201050c04060e0121140402091602120702131d19050601171006090e07080c060a140408032b0b0f040507031806020334030209010309142a060405 64
    0xd038040b0700714100307440e0310660068104400c0c06c2d544020031b42007000702c0b0160320916151001400d00a00801030039841c4c01c140d40030b00310710220b482907a074094220b1841079030071510b45d094400c6003113158415814089402c20481e802140300346d0b083c0740760000d6240703c00700c081812072942c800124001071083c15100c031026800c01c90080b0f00c103080d00d800207a5103071850f03180c101400007900081d03940c0000b890565940542c0d0025480d224507580d281e50400c0c4868000c90100304861009100d040010400703c180f5400e90b24060740d03000d00b00e15640058408400d0f4100d2a40c000c03459045412a0710258501d48409110300007660000800c11034281403280d0080fa1507000040c5614825441120351902e80000c44000c4071850505030000e400c2140d0819202d61204501000c00c0910881103074907460410034100c2001c400c40d002c401940080500030b050503180c5014800084118040030240d42c100e00003802c02c0d03201800346284480703600c00098003144031000003041035102c140880d01680d0381500c0807 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 939633345 1250 939632095 939632117
    0x60a030305120c0d0912030b0a2103020c10022d0a110102030c0d08040c090e03071209030f03030e01151d0405030f0705030a170f1611010c0f0201050c04060e01 70
    0xd62814484c4603aa20802c80c502100c0c6010051003003924100c00c2500e683c1000f0700c01c491424003098801501800e101c0d0301d0180980c1c081e10307030443d0041103032912a1042d1203400a0714004034202200701440300015800080c0760615a030550354512004429000d40b03200c4503034856408a89600401c04044c1442d121722003080c00070b900800c00c0320b1162110208942ea0010614801010502c1c03e5408407101203610b000090042281e0150000c0d07028280051864501141c3d2010003282e502d0202c0024001c1002d40013000c5900740c000c54005d24066200820702d030312490103403130850310f4266200701000c0e90039000b0f1190096030100c030030308200281500c11042c5c0340e50600920b54058014130070584040000c1c900b003001300201c080e00b540d907407036291001c006480c2201c5481114044a55a040000781d00010303625602a01c0c8800d603020f114200b0b840554070340704200e42980d40d03140e0720304045501201c12203440c40d0709100d81030f84040e10000590901c2d0600400510951035524440d040020140740 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 939634595 1250 939633345 939633361
    0xb044517031b0d0204080f0303010609230303040308120604050f01051311030108030a09121104090602090306090c03070608160e030718231003080d0e0313030b060a03030512 76
    0x145200080303a0400b05500da0010781a0800030358018051082140200c0560b450417800000541c0c0c1a101151a54400503003880c0030040b5000c08151000044c803c014850385c159202440280041c42c0070b0124547e603241c007034400c00e40549015140030b0082d40b074001005601044001028155001124009185c0320784c0c8c4031000c094640800142400c0c2c000000006102000000408900c00030780c0b64000c26666a088942c404165104080c11595840c1e400052038034181c6d01450034288209001801d0017195030101b8034141b8110303400c9106c2d5005854200ca145070410440c03000380120b20b884000da1070703c600360801404442d00800148170a514507240669020300000c00509800020001480c01c03180d5403001074854a10560040c8800c140c1c900d80c2d0b02e24111900b8441c800b0034090079000b51850f6a030580d258019060500865aa00c820150388501403000b4000308031032142c055a41821803d0044c40140e018220503c07031140c203d03080000a070820305480642201040070307542c1c0e1381d64141c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 939635845 1250 939634595 939634621
    0x20a0909050603190308132a0812030a02131206140a0c05271302071e030f1409120307020a0b070b0f06180412121e0b04451703 56
    0x8d010810385800c56184a0b03034480783c04284903900301202252940c9201d02038440b00c0190601c80d101504200060950031a9001002d12542c00c4000c2101d40d40e64112000100c07220001c03c8410b10b4841f10403000c9168100003054212107444002c01102104c1400a0010701c00e0104000f40d502403070788410500c0030090407070030100d20302801403022104801550802580302200850b60580c48800c4060410107850100401c1d50345030702c0702006c00b822554103882d10302007030401481458080280c04815100c00004903880f06141c80110b48070382091041040b41e0700e1a8020883c05a003c0c410007000c14641c041194214060b190040e134592104408200c030800111504810134000905102c204070700d24000c102c94213160fa58520405040d401290182c4030242e40c103014010f607214041031107a0040e404440107250042c40003690800c041d400c07044080008131400c0c03c4800c1500b2149603d0900006401c400c095940540903001041c2d5a03401200851905140606d801100262840440e24 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 939637095 1250 939635845 939635881
    0xa05031905011506121a090402120708010c0c030323010b0307030908070f06051807090209030708151b12041212060f080c0a0f0621020a0909050603190308 68
    0x3000c06200c01381c035004060710703d00c0300307201d118000c42c9001140c0e0075080305189610345d14003004010303000648842d0200302d941441c64048031061300507081d0004000100b4460000c0403a52600c407007052032000e01b409000ca402c0c950f804403240302e00c69034850801040d807500d2030646187ca4860790b101c1e2160350040700100000d000082ca407040028034441031000201804041c00d1003014240280d035030f921000440c590040000c83c1c12a0b01042060040c10000d4001c0e004481d00a03044400c0980e6641c00c00e481c0182d220407505001c0c082006102100b0032488040e1000003100422515150002c0999407540c03400074030240a14011a652403481d034424110480302e60820102807140039240c01b004d6000a01900c6014024482c5418481003418548528811a80d800951400c01460b00a0544403070b000c280382078590b9001d240082c0101041c07071026050300c200c3c55680c0c1c00f8080c03c11659104444028080030710030790106003a540c007040b0180703c240c003032503042c9000305c07580d110700c040852004021 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 939638345 1250 939637095 939637121
    0x503070b04080d050705070f080c0c19090c0908070509070c23010509010b031011070b0c360d110a1206110a020d14040f091a0a0503190501 61
    0x1050901c8203000041c80600302e48401c0200030405501d0b81901642c083c40b0b41d010060000c1280d0640001040b0300c0000340051583c010306841840f40c5d241c1c00100307002030008103407140c00c0c1c20703507800d0000c02d11030321031807030418041e06000304030700d040200c0d507659402c02d4825240714079240350000f45880e20910000c42080d600810b907640c2c0e80352030030580840740b0020985045075860000040c5c00480705018680d0014006800741c220b00122102c258040c042481c0490b40806e020800080010380e000320300323071054040c01d24803030301c40c907081c0310046c0f801607102c1a4401c001520000440c540200b521040c071006011100c101402005140004400340301c03000c03a95114004640005600160000350b00c00e0a216400c200084031001c0c282c18428050441107100503800100303924289c80c000c0201c4001403507200700071402d260b0380e2403181c8501c0f800d6800000e41b0b50b4890f018901040300722081108103110807104614960700b807101180d5a000342102c500400344444008005100702035008400740000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 939639595 1250 939638345 939638363
    0x604150e04050c070218070c1707120203040905010e070f050a02071a0403060f06080c100509090411010809070b0f0706091b0e09010207020f01080c130f05010f02060c070f050307 78
    0x43c0960041504010401e0740100c14905c20b1400c011258881203109103556200c2c1e00c52080c3d13a44a08a88030446400b607000100708000c00f030003103181000d039107101090507401140d031282080401c506482060344038220006400040c0b202d016000030046071201d0242c54400c0e100c081c0b01904030315000c1c1a0f804035800d42c80482000031280394410090082d680500c00c24001c104182203000200e454501c1142240c0d00300e401103812614280d00300b4100c002a91400ea4184120000000c40b2000280c070101c030b003854822610070817940c210800f0756000c1c51f01005400390600d8120101d129100d884441003500310300165190402241c1c0d801440900e130007850203542198004e40d01d170200002800390440300c045840010b00c81c40c1c3e05000311200780d94041c00701000d603100070005640c418406801c1d940794400500010081141941c1107400500206000c1c00040b45000005858a10007900751b00c21904000c00700003138240c2c0300c1c045400c110303407103441c0a401040905100c4c0c21070141810003022241c1c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 939640845 1250 939639595 939639601
    0x504080a0f061e0c031125020a090513030905010807020607030b062b2409050c07080a0f1412130f0507060905030c010f17041127060406050604150e0405 67
    0x15070720510784d54480d514100040443c0400c41c1405002c0c0c100c0003241c0b03503101c04141011000c00c412000316640701800d01d00300d450302c1e8541c01040c1d0310b0441d442c0d446409203d046d041815404a0014006c04081c241301070341d070620800080d10364a006207010185a04d400801085403a85000c95806001030100340218038468443e174805410440d040183c105c1c280454001080a021486000f0850440c641c00c40780e85050344100241c03100802c004043c60003440302802040d070f4880141502001940c0e8010702e0704030f800000e0110303801d08107901c8410030180304002d84401151500340d0000c228840080189590740707040c101070307950448010180d001e44c60700000c4403a0010400000d07190124151082c1070301440044a84129032444400064809114200c14420010300c064206000d00d050008941c500320105070180c803c148150003d00181e1a00820030202e404c0980e0881400c0b01c1c01e203c1c0524100004801d401640200d05252400c00004010513015450b4500c200d1005441401585 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 939642095 1250 939640845 939640901
    0x809090903190801080f160e07020304150c0501050f01050d0201050706020708071406010605180904020d02030615090a180215280f0801050102120c010e0604210504080a0f06 76
    0xb0028070500c5558843c840070600c40c2580801c1c40e0041f20b842444000c001c5240920031144000054034071400e5001c104808100b100b000b100d5100178120641716141007203618030b0040c0c00c51340010b048a40c0120000014409660b485800d1040250240303010b07600c0d4281750501c50003e1050640043c01c80c000040d1100400042c3ea29414110101d502070f2843c40eaa6604240c415216690a8404d01708003a2840c801b00d18107039a51a80003030000d45550662140c41c1d011a00c0e20400380c1d07081a00003121144100245829083c442e44084105018080c48403400c0c0a0b0000850901c0002d1060707030200d04000007070f420303101503440802d07000d40c100407103001c080d049003140031401081100160701c01c107682018600131110103048410690041c008040c4100c400c2c980c0e500294200c040383d5480c4c94244c2000e031000c0294a00460007101c80982c40484034409440e10484c2503155404c2c00b0090004120070035001c2441c410064000c49005400315445ca0140021324081c5d0032102d1010007034008134200 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 939643345 1250 939642095 939642107
    0x1902100f03180605060306150a060f020f0a05060a180b07031e0c2102211f0806090705180408070c080a03030b010813110409210507031209080909090319 67
    0x20082030f0192a8151508c4603495468568016402c4d08040540c404201c41e501c07a61000d904103910744150b5600b8a42d1100710303070034181c00ba0380a4540e0741c0800d0602c010b4134014070805d15514002c200304844009181d60340103440d4070050546042c142c0d14006404982e44140384882040d01d01203040021101c40d400c054600400403013240413269420302c2444090260b403085031080c031601150490f4102230f00c03c00c0c40100600800305501b04048440980c05215568400000382c0844405800c0300e1034800f070030328602000c9501c102d10030740c4449042c1c0c1e58808100306254029030801d10350356452025040071080382d000741d807110202c1e205401408052540c5075000d03c448440998800349103031510150540d1800003144068200d000c142c225010501d811307400010018451680f0001034549614138141804034001c41c040400d40000e00842003562201c0f0840f585044d4110400c0059000d4860036841e01903641d01500450148002c20010281001960310300c00201741800030b0002400801840 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 939644595 1250 939643345 939643351
    0x10e071d18030c0f060708040809091f1410050703080a0e0a08212d040c050904030c0b010905011a0a0908010203010f030c0812270a03141902100f03180605 68
    0x158015a001b141c525031180c90150b014a800080f1242080031101c10080c00c4034001d440ca0703101c515541c071180740103000b240c403501c02811000003482c0400c0101040c011003d50f4084d410041000802070f6000094000e03c8642c0c00c8288140c1c00100401d465903164034100d20130038060440d43d000309031002540d10740c0ca11200004030145803ea1907480c1d080e05d01500000c2040074440c0050b4500f00b0121011801400303c3e4018020383c00340d09810354803004035203400300644040e0005500b091010041c843e60000741c038014045c51008004d55850240c518542c0350380c2100300c0b950242c00040512005116a00c01c9000e0803490f00215600d581d65441ca2190015920007200d001235100c000140340700d804180c02e0960509408030318a44031120510519081343d11030f00d00d0309620800c1c00c0c1c0d85141c60711074034980550710803e070008203e42c0d608a160300d403140b055580060903071601c00400044e10b50f0300070421411035504140406915030300066002d4800c05c14808001100007501d00203000b1950400c0340 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 939645845 1250 939644595 939644623
    0x9062502041104170a0201050f0d14040b04022106010b0306120105070201021c09020a0302011803080c0d120c021f0605060d23070503010e040204060323010e071d18030c 74
    0x7a603078000c3c251154a405d00424040c3c04204c040c0841045889448004c0c003060502d1400003480e141301144034092510144d4080e9000d6140204110071814400c9102c0800460360b4200003407150700c1490b0907900c04050040001d0040c002c004641683c40700001885000c444400034003661401c444020700035008242c010301031013070000700b0b50044181ea00c1280c442940190204144500f5030300159101c040e4801141ca01144601e00003022640201c0917001c40c1007508041d00d644107041d00d000781041c01200d80c0b1500240f03460100103440e0340014082280c0400c2802c3c3e1038101654041800040070194400c2d90440400509480c40b8070306035001c0024080b090035901c001601c000646001664126018404500100700601c03004102024080d03010384001c10114a40761660780344031015241e1001c0c4000b6030703600f82c00c88085003001e0054950113400c840080030000e140040d5140082510030811248500000208210341d00070107410306210a40011295500801c80e0f5150390303030b14020f0b0011 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 939647095 1250 939645845 939645869
    0x1210c0206070c031e0c050703030c0201080a050c0921073201020a1103010f0204060c02040e010c0e0d0215130e060d0305070b090a141005060609062502041104 70
    0xb41c0c11809603040ea40b540b03425564401408854608880090031385100383c0050141403107410340012410880761001d14401d54030f01c03001d83c00920001d8035500e4042d0500c110b43d401c0104003c411110034040d201d0306001240c0300070b02c55040c2102c50443d02c2d41a94802c50b240503c0b01301140c3c02600720b0159109186680c15555a1031500c08280e80c2110010000d07170041e04080800c00102d0403076010081a000010000650b140f80010210308aa00c158010310201c0c520b0b0400900750325141c4a880a44035152009002518080130000c000b0440203400c80d120f54030400f1080305544520741c0c000c01038001541429584c194507000307040146600e101d14032207106404009a00360501c144145d844613850b0311003606042943d40c849000c418002c0c050b50312840342c107801e03101141c0001100c14121240c040580f00403001ca400c10400c0d5400205014060082041280690b40f61a4100e951092445030007107600640381030340544082a04c60b010f5405401e20200a1600069030018000c03079507071821175 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 939648345 1250 939647095 939647101
    0x10c06050106050406180303080c0c01061e080c01030b131817090a12020d060e0c03011113050603270f10020a080105030a0b0c09120708010207050114090304060e01210c0206 76
    0x6100b5030500340c00010009035502740400c0c1d00c1c85039840644010310b031140020079410b44990780300031812410390b840c03821540e42040070041142c09100700c00102030207180c00c1c400ca14031000810315040d8a00d801c1005103944d2882c041e040e0171040d030314055495000d010300028007440e440001940e085100c803d88264682100002d07540c40032100e14214a03800742c031304c6c15aa046034403100700502e074508421000b07005e10304003004140ea082c0314445007100503040b50b0740c0310011a0540d0b4540b01441c0c200038002d4000b001400507550704c114005030310703048001c22039961042c14082a820046052101c80f01072203603001d511440c900c5178028200c0702c2c04c1da40e296902680d0303c0d0704150703540900c0c19010b000044003801080b111041c24005190050000c3c0c0b042c0441032a180185180001c25400ba141595000c038040c82001002e0042c0414010104540c0302c02d8240b001c8610f8584c4500d119007020b004e490610720000307900612062081c1c9a25500200c0102030804001002e001e1402400700140503040c00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 939649595 1250 939648345 939648377
    0x30a0e0a03240b040c080a1b0c060b03010212010303030b19050f240c0307110108011802090310060e420a03050d1701060f0815010c06050106050406 65
    0x10903080300c0d0004906071012080322042c21045028030011140c464884a400040e5100c50245448400c45070340c9024191400034100400c4a0390000d00352902256105040d00d02d50303212024210490300401d000a0a101c201c001070300910484440150300441c2c28000001d264240e40300d02498981503402006809101107040d00c500418000c0c0e640c4904680e07a1690359003401c885030f01d00c0400981c0a24940042468a0246c540211401d21240d50002884004210000c240160307800b0083c204880c00354107004244071101d04660301c0a2085501140342003581d903042042404811040e0b1003080083d440312030550f00400300300c620880c0103111207024070300d20003000c0720428114082d060484050041c041001c410700e030070003c0564011145100400854070a02505045014503150b40e042440e040e18040080001640b0440c18400f100c0b4040b50b103a40c000400580c4541008030103050103c01c800181d801181c4c0c01c4c8003826043ca04000801d0940d040300040c0141c03041c83d1940d0780c4920042032 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 939650845 1250 939649595 939649609
    0x2511031e0a0f03020918131e021c05030307080406180809121605040902040b03010203100e070903020a030611070f060605010311030c09061c0e0a0311012009010e040e030a0e 76
    0x100240c00c00d10a02c20500d00341b01c550b00d25908002e02c2c2881d07400741c0351162034041110341504041c01c0c50805d0780703041608500e802000200e131600001640c0c0441201c1d80c83d65a100c2c000200440184000700c00010b00b0491103500040072150f800d441102070b0344190901601c240c0107400071901499045144001c440310000e046100844100c001c0400e66041200b4400034155000f0220381164440d041c0344040d642c2800034611812400980500d400d1034895092041c110152110702407002c08102440940c40d040501c100762900f00102103a180b010310701d011023620640074081c051104103003904041107402d4002a0840d8000d0703030107020324032504038503404900c0300391164204403800304070101d0b071800d04d00041c09081d0100502d0725495240320521106646007141c090542d50040044002015009007922000d5070701c200c000c01c800c41450f03c0e11062003110454400512001180c5102503a1003844503010070f0001401c00c1c40760301c1d01903000310760701e400080025021034a04498003145003440c070 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 939652095 1250 939650845 939650857
    0xb090a0f1101141617070c030602090a0510171015020a14030406231308060a0c03050405030304230f06100b070b070305041e0b09062511031e0a0f0302 66
    0x1440400404a8940e1400004c40b17560b06000705000d4140b104a010800c10702a40d40254000e500142c1e40e014120104240d019135038020310f108001000c1038801280c0d010031304010001e80801000c1140d1102c281200705460142d00c603504032514a0ba5140855901251415030b1510540320704484042e21604c1c81c0c0c4030702841c0241c200082941a034224580e0400820031526449003186a191001c070071405140b0a1a07504008500d41c4104c080c4202000d4510814012540519080080341403c2e41d4983c0c4034407001c2e2006c2c00b006540810b030040b000c02c10800000c000020401c0f14a81c8008007015503d403d81150101d40b0080c0d800c10003d904c00c4040212100241d012040c1c11490f9107a07101030b001403502030000d40e04155481d510890b02880f441d030031250b281c01904040c6581c64210b044518102c401441076441300846401c642ea60100740a000aa102940c1019130a8101210129241d4003c0414081103044000d14074451035000c80001c0c10480b85644c0d07010700314410003c2c290140c0c855a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 939653345 1250 939652095 939652117
    0x806040c1413020d140f092a0907021e1207020405091c020a060e0d02070b032509051e0a060c140307030e030d08090309090603031308060a0f0e0a0b090a0f110114 71
    0x84c06e510195009000303000305085c402023213900903030700e11000880d50718002100e03881e000d0383c000841e588211850b0000c410014050740c00904104108514401c032a000e0040001e000d0750f2a080816618041402000781d00c1c0d2200c560b44103082102140299102000801650032619004070b0305075104021650710542d0b0402c4d0000c20391240b403c4010440341e03200a01c070041740e01c0140001d02a072003400450b0802c210850307541c00145402c0c4001c100416014402c460341900365400e40c89040d40703038648000b0440328507007000d0100000505041520f00030049208510b4080003568204141d0401910511100281c0481e0042c0c040c584055910540c2600c0c42451a8410301c054481882c0440480360f21100180c00d0724205400c0520214420285400150312038000c1420000510035501c141440c0010118003030200404d070110454440c40c0390070300604580210b000045190600704200603036243d000301a120444540e09202110080b12421103002500402005400c00340324000d4504604070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 939654595 1250 939653345 939653353
    0x61c080706092105071109060a0f081006051009060f03090b04150c050c06062b06052a18060c0601080601080c0f032e14060a0806040c1413020d140f09 66
    0x1240c407c00818800052129621100c203803000b10f643c4c0c082d1648040100042e01c0100030380750704000c420042e03d100b034001038022074040e0b080c514065806240202200c885041c20500c00b24080002c0340600070440c0c026120140740e4080c80f0030402e03081e110801c44003101204209002c8519130880d4941b151148000c035070ba020802003091441e11041085160a0185640a81c41d6441904081203200301509481043e0b0f50b00411024642100e2441d02d4482c00c1000c4603415285101c1d030090902030312441c11600c0d4070032944103000e6107d900c1224034055000e4122000c030341e554201150303985024020a4107134010707100000101d0504050001c0740f68002000381c1a1004d5039412010300307a0200e0081940000c681c249060480c0281c450980314034901070210341f403407500c02c0c14010480100e07803020301907a09c0b41c010440801e41e43c03965002520007102c00500034040707107000140320780000d0704144130491000410075603079191907210803019040d00094640310350382c11600204d1001c1c222068421600 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 939655845 1250 939654595 939654623
    0x3030609041b03020d030503040203010e070b0403230304150f030b060d091703070c140a0803130507050a1202091501020d030c0903050f0303040b0906061c08070609210507 75
    0xb80d0032150304120724000707004030a601d40c0c980010780c1d00c1305501820b5002c92400018041582001c1c00f583e0700c403003640401404a5032030003070116282d07c110300c00a8030034203085101d841d9010700d4545c940701c010920300880741c4454440903101c410708a41d03460080410769080a800001c2e0081c0240c51214030000c085c103003000050f8010f000a0114074400322117401c080304500400c548003c001d10300031666940c402c10811000e180c4001d2907039912401d41401d610034100b0f40c00041300390f41165448442c10141e1500c481480c40c0c200d2a010290300304961000c048040442c0c2005e0046041d89070320300841d4000074a40341d4080c444144031400042c0390060304131403810300e84035010750441407181d00c1c40c2c50003030023003542c0c2d803120360818480707a4003643c440d0400001d000038483d88006464002503404003806881c10020000f615805c00070b00441c90f000c4000c0302c1e01d400e000050058440c90b5401102c14401c04040b4070b0030042c22540058065801401d5800c1001a1440360b42500c2030a40c0c040e80b0348506007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 939657095 1250 939655845 939655853
    0x1050f090d1b030c0212160501020f07150519030234030302090f04050c09190f271d1009020901051e030703030809100903300c09080f0303060904 64
    0x2000b4605805200354440d54800680360000c010402054050140141d00b18030101c01300550510361140b411076003e80b925040c1c3c034002148401c11102d02d004503601030640440c5c00e0b54a80a4000c048034001501207003600d1040c1c240d0014102a40e801c14404115042404034441540b40c151001602c1d4060041290020b4003a500030001740100402207140800701c480080d066800480d100d101100000c645102c0d035007020384001d110841c000d01402c0041d4100b44484529907098032440d40c3d042044110140d00d884c03204442c1080310f1208506120182034a44007220701e0251807203200f01c42c443c181d4400f80c0400d0900c02d5201c0154020090401a40b9102c03c012003024200040d8400300382905030301100b55020007c0000661117900c0d40c1c0324514100300c0003800c203c021500d07020001d084c8084480000d41c803030745200032100220001005110014201550038240102c0041074620300305100034038540202d040021140c3d09402c4800c40790b4000c030056164001901c40d103400205d0324010400103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 939658345 1250 939657095 939657137
    0xb1e04110102010f1e06090908030a0f090f0f0506070201021905070204110301080601060806040b01081303020727050a11040513020c060a0902040e0c030d1d030f01050f090d 76
    0x540e052002003020b0118240540444134405049030541d44020310b5155005c0050043d6401810b01000810440ca8a529442490b100003007a401d0703056a200000314408030258088030b60079800480102c000c0c0702e6071a207041040c4070707054191098031800e00020540c91050080b61840754403280d0580d0114010541030700e8980140d02c00301c1e44a170700c0300c1241c0070900c044005103009042e400010500381d4034091000d003000030054803050080e814120655010f0340c0004110b0b03080700c0c4841d948405070300941012420071a05401040c3c80c1c40c80e54a486503c1d81c203040d12204010720101041015841d00e1003803030112101c0c031110600d10101848200f025250058803510451400070f4050718100b0308601d02800c103034040785c080700b100341c2d51044003055040034401c01101c1c10111004101c05445640020740d1096043c030854100070307410900344201460001086550003001c5c040303480d1002d40503001400f0345411900b450804100740002400414005100c80d51010680c80340080c0440d007450340902 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 939659595 1250 939658345 939658373
    0x260a0b03060f04261606060f150c080703110706120c08010e040f0c0b1c0605041a040f0f1112060306070c06021e07050703120201090b180a0213090b1e04 67
    0x61040e05009840400b90010b038445c10081c450035000516904021030b95504c50707096044040c0300c0f0007840e81031485c10b0300b090101a495030030419007900d41010346011502003442c8101d5002c1400790b22800550b050f007003a010011103481c40001c3c0803948094030f0071a0880c10904c200c01180000c0004140420150704a501515014000300d8112a03100c08800b50683d200300d2039503020948040f1107403500089881103102522044805000407440d0030020b07800d40700b411905500c11986c4005045140345103070310041c0c10035100b00d0184281298074400303200a0700104142c0514891103800911546804100c0e10701c030300b00d11b45419803602c0c060340f0b510000b504107803c1d14142c410242c092014043c5054003604d141c034821002403040b58114680340102c0483c2c2d0f1241700c1560f05254100000840c0c0140da668050000d055201d841b04901480c04d01e04400b0030001b940040d14080b030440b1064094100c4840c1c1c0b801007140a1840d02d41042070f502c80b81c03804051080041082020030b000903462110b6a40c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 939660845 1250 939659595 939659663
    0x120d0f0c0507051e030a1b050a150e0406090c02030304020a122a0e0103080316110721020604060503010f0501170a050901110301060504030b25260a0b03060f04 70
    0x1410311844d802180c50005a808103903071035152010803032940c00b8030350319070300181400380d0304802550302d040c51603040c5400d01e98240042c04800e81c80b0070030f991141c0d4407202c0184801c031420311260200031f0300a03440f42c1c0166000e0703000d0050510045401c0d850342640e05490f56104100207a90018408801113404250030052805201d0324400a200349040664501039400390700d025940381011103a5403850790070f405102007440307025280d00b0320809010078030703074121820396443c2c41035004010080b4412034015080207510100101c0c010035050b900801030340c141c070001c1000403880d548520064602081240001c114022500c0004205a9958100942000450001141d146114200c040c0c0030b4000360083e400080d40810200148425283c08540000c5400d26080740e55080c1450f43c211214030921802c24004507450140c04d0041240c040d600c140d1420351030080d40c1c00c00300442d4020b00070a00380c2e01e00c03074403076080446e800500003866140215807001c00306592111011a0100445010420700c0e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 939662095 1250 939660845 939660889
    0x12100506040b280302030f0907290f34080f090301090204060605130501030e03030103030f0513060c0c1413051b030f0412180b0d0b120d0f0c050705 65
    0x120b0f40002011000c2210540b405600c03441e10203c091292800100455426806035408000c004481480603260354402100240c4149c0d40b10000907861082240c3d4241d00302d0000780a00120050f85080b44289084207020644007002c200320120f250780b0030201800d603650400401440b08030410040203400340290000c508071295400043c02c5842e15071000c00482c0d400103080e00d104201103656000350000b428104622111448003a55900050000405200c0010342074107800380100180c8003c4c2c555494564040b9403144802011000441000c407444481c0b120081211400004010b141c000c01900241ca502c00d1056184003800014042d90490540c4158201c04c00d8403110046200c6d0b0004440d81e0317401e04041c030b0160301031808840b0030820071100c1325540d103146200d07200e07040032966440c20b555100c19140f0021002040825980c0740d201030106090300343d105000c51040140041d44e00c4070800284910401d81c0c0480b083c1c9002011508491010300840c03801302107039038008035003820703071 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 939663345 1250 939662095 939662137
    0xc0804150c0209190f0e0309060c071e1e0e160e04090308091006030201080f1b030112050706090807270509150702011404030c030c061112100506040b 66
    0x4140d00700030945000701c00400060706000d1302d5940780981d180c19500110100f0145401105041c0c590258103a203d120714400103480c070340810100701d0440032304030714181401c09410700782c000420b40b02144100c0007030700c0300c907408a889440542c19420460301d000008000079901c00ca11201e40d2003d00110106100f41c5840b0350300b803070300d42d441221191031080d2035606150a0107051680b40c980c3c20b20a9001680c00c103002800180d90003601103801030000030940425884042d021650281c2c00702e00e00791441000f01c0000b40c0005856116040d040c080d5040d40d0803036413139210444150400703004040a6a121000410030841c103441e83c1030816012011421140c40c440c91204181c80c420f4584210031b62040310b0b0441802d0502c4111504101c4078002000300119098080c0340c03100d002803014051051101014060500070000c03c2c10259118204000214041c0980203241d04001c1e0b42c0810500300100044608c0c0c4118240340c00c4d13690040510b82400d01d483c200064942c4044d60040e15502c5421407 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 939664595 1250 939663345 939663349
    0x203041d0405251d0402030a020628260103031b150608070501090e2412060c18030a2607080c010b0f04140a0b011b06050907060c0804150c02 62
    0xb40707160001440883e071195924028a2810218502a0608610300c4030418440140d80000d00111096810307518251204074003486214800c6003c184401d200e07426000503034407654440d8102c1081c1c40035468410780d602a007001e00414100900008000c91f00e01c1d00350342100889103000d1414148110441c4440d0a00036803240d0035241c450703018000350390000f14180441d6810506a80140125404a0364a450b203001e0aa80010024a0b541da0000090204c8005c035111483c52540f01600802187c03103504001c03852600070303481005d0254a100c8c50f8560325078035240204002c040d44e9000051204412401da41801100114a01040d44c0140c1002100000742c2c50001814101c1c10200001a0280040d810321100d40d9203800c401c5e01c150310f42000020190b00b400344003074008058a8000840c40081001a01c90032103d4085070790f60341e000303c100c034104181034010a00c90080c1c402510101551403a0690f020102c0300d8000340f0b6848180002d0204445040c521400500a4a041c005070708090700 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 939665845 1250 939664595 939664633
    0x80c07051b09091903030915050f04170403030c020f01020c03190501140118050a0b040e010b100302030702070905040317043e04020306040207020301020406120b010203041d0405 78
    0x581d000104820141c480480d01d04007100d968003841210203800b18800c001803503462204803910003070070b16642d280038800b400020050003000d10704030300c2d00f00301c14203080d0f0284444080440d0104c0d24a0f00d25818040d1340307402d100655046030741c1520f401400301c05607400c006050f0001c068050452042c0d80032065255810480c1c1c11b03901e07008480704800d1f21100e050850969081e59a042880030480300108100c8910048400144c920403100080c1920f40b683c1180191560b881c40f10b074400c0c10305c0c0785412401e8041d44036101c0d0180480b8541410240841c05a0503404100e40c20000350300001e104108040c03071a00001c1e803091003442c1041d01c4244150b11180c5d030080540e0b060302d0b440642d03107409561003111649029290626011202458240d51840c1001d2054880c0240a90380200214007151255010340d003402c0ea008000755117032600c55070b008005030003443c44184a54105840c1901550011003180d0540c0e044554040300c10b401c400d4402c260b204081c10407142485071f0503c0c9907400e041c1700 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 939667095 1250 939665845 939665863
    0x41d1f031209051008011e15110105061008010b0a0c050a030f0215010806010b16020307120c140a03060c0509030a061e0212060405090a0503030708100b07050607080c0705 75
    0xa07001c0101180c88050003028802580c00481c014806840c00c07444058100c030400741140c80c0c12102c4030b5030250042c480390b400355080d030002c07071714544021003c451107030032607002c02a0120600082010390f58090820a11901e407241e2140070034010801800044141c0004003a4a4410f00700304030341c000710341c0e2201e02e000ca207484160009001c00082c00d40b005d0b418001d4200c02c100d1041030300c50319418010640c2c1c0b03804041c82a4520b500380012444542300350000f1501000b9002001e0f159078030b82d07901511410401d42c0500f150404c20070400850030540b180120003d010010380581241e41c2150f5500005088616184c020303c0000e100710032103554104007242c5894031031400812960203010819801403904039403040100d00600c919264054124201c95000350112004945a11054080c80c00c1203c201400f8125020000c1000391050b00718041600034400700182402d001c3c2d07260f5410404e8060050004d102d0b410103004104040c0c410040b1030703088440109030794649070361a07035018a004401 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 939668345 1250 939667095 939667103
    0x6040603020a0513121208040201120b03120705070602060705030114130209061602010e27070c0f030207050f1507060b0f030a030306050f060c070b0f0421050111041d1f03 75
    0x26618032042121a10425007806c5031400c0804060810b640040e0a00d07403078004ca0340742c0390b5035081440d106503010020800c2400003854420355400d117030b0505680310741c020302820300540b20b10b0000c280c4591013602203d0495807800384038519040c01d5810009a00b0000c040b64030301a03003c7c072111040742e44000c02410780501c1c4118204003040d2030b2000ad8440e100e09035025100d2136400109038900541e4103112100b6511755a5900e5856403070401c155401042038401034115507040e850441019000103014064400444184242034520010404801500d00d030300c10b05003009100c4800010b55541045110340d0004100300304010090002ca1f00d01240c4080c2500041d890300410031090604150303420010100381e038810328101403c02c5080e6120024030410911210019464000001c00c074155009000c0c10030510020b02145095605111920740094030716501c0c0c070340c1036602204001c040390b0441e030055582400c41c0355505000c604000c0e00500750760103c240307101035074550002c210866019601c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 939669595 1250 939668345 939668369
    0xa02040905070e040c050f09060706020d090b1509060d14100f0f05060904020603010e0703090209130b071107090e010e01090602220b1b2e0c080606040603020a0513 72
    0x343d808100a450200c10742c5410b0260030000250071904500480c0c44204040d00c41c159201e002c1d01c0c022000703100342514036910310314040300541003041c21401c140c015020501802008140c0104015801a0607078140d42d010307101440380b00000d0250400302e1660061141928040315416002c4020f8518032013400c044582d4a4140e002d00040c1442515003059098402d5606803510f0740c04030342944418091903059030078010028058510035045244030680c0500a080301b13040807241c0040240f820700b000ca1301c95a1540010340031a115035209000c03800800000d0008034980720048008141800d041d0117a55214110625842d10074011b07200d07814410040144d441101c0440c01c0b180701e900c102000b81401c2d03080410884d4020340425500d0b40e200595a10441002103c595813511810a0520f44014002207c0300101d8001a51a000e0310034103401c24014414402011030b01c01400b1a401640400203200901095101742c0c090110300d071786ea090075403504486801c0c800c6000199804450481d00d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 939670845 1250 939669595 939669617
    0x1d310615061806090b070813090609090b010501020a0c0306180b090c10090e0f0a0207020904030e01031a031c030e0f010f0609050103080d0f0b04060905090705030609030f030a0204090507 82
    0x100d4142d60600619143c0b804000482c203180740001940314010002d01010000b1458450604120041c0002045142410000f0790754480302d0300301a2040e05000d0390f078051140000566075002141c034503107290b8090400c0c10a1802c684e038041c0104940c134082440040104c0300c070780c0051030a044090044100c8401040103481c11002c01070400385100441e000c1100b12001002b01c0c0340600b03200c03508021827040f1200a03a86a01000c0c00a01504d40e02a510200e11010b02090503000081e0700c0e40b004003039805100b440c42d42141e07200e106401614298141d4803144219481c51180000000ea91b0a02d04d0302084148140311450b180008608058526955030324100380d181c8030b03602c5103c0040c044040309020b558559203d081082c000e8101c0f403084151249141010211650700005820000520800c06180c440040d503000740703801c407030400044c401c1c41c07004541841c0001c0d1203403148000f140114501241c1c459182500e400c06428038005903003e00007c1900c01d00c03801001d01c150559640d800c2486 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 939672095 1250 939670845 939670877
    0x3030e010b0d02031f1104030812070905060f03060f0603160216140f13181403030c04030f140106170d03110301090e161d31061506 58
    0xc0c400c56482445650740b414035200503200420380c0000e0f00c810102140f2541401c0803001e0250410035017444113610009404001c0064010181031600d2203000e40e000180d48041c03040e20401d1142c0202a40004140a201680c5d62600c00450b40000041c15810902c04000c010ce140343d08141c441c15040012035602d00c06055042140c8104e42c03010070748021144e481c20f0003900d40309004600950084d0b0911010301c0345501d804013141c41030705000800f089502d007034144140c0d6000600804a50169030960a900007010020035030340607071400e4044d01e141c5455981c60060041910004862440070b440c0c5c01601520300303104d000000c00d0144400c044000200003514101260012414145440c0400415042c0ca1a0050f03d0540b21811800240f034003681101c54645141c0b4100c0311a507400340200429407001b0402200c0c0c06100e103413030802094480d4a49007402180b00510700152114641e8042c0b200b94003001d64103070281c054803000582c0c1c42d405c43c003140c5082142e00000c0c0494458201900d040f = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 939673345 1250 939672095 939672101
    0xe0106080d03111902030c0d02070501020f0c0906010c0c030503030406090b090609061501050c06011707050105030702030d09060e030a020a120c020f101b11040b010311030a09030302090d03030e01 86
    0xc1a00b40780800080ca019180c030b820501402e00c100070b0680d2508100103075203000300100c412100ba04402c442141402d000003e5844119001c0c260041c022040480d200001c00103c269014000900c45411581c441004444006443c20b06403500703422001d000000ca0002d00040d800f5901400c40802c600c0c400c1d042c075600c0302d14082c0c60b13001243d010070100007045070089055a0440380c41c2545007031900400d401201c4038040c140e5042114000c520000803124007505544101a2a40040c0d60540d5035682c01903840e4002200c100c000b40e04200316003c11404551700c18940b00d88205400260f0302200c002ca645142c2105140c42c0250740032890f05c0003400b003902c05020600c1c0483c40d141d1611421503020035a04001d060b0158000c0c040080107050721406807000c1c8841055209000c81e08801504102505206003201240124581124001d0702d510074001c00c00c54048102c590340c035584480103144018600604140c003015400e20000c4d68617510300c8041c0c10078a000f60340100d01400901c4000c0e0031 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 939674595 1250 939673345 939673363
    0x3040510081302011d060a03090b0a0c0207210803150901080105011203080405010b0306041a07090f0b0901031e0b03070e04051207030201140a1d060405120d0603060e010608 76
    0xd001c0000308000c48a10190011800c6950a00c0d0420190000a4000c1d044200c0901c0c4180d0040c03010441229040e8903034062964240111500400c5488000e1041c04941b0740084150058002c84c90502c108141e01d03001104150007010074420040d020b80b600c040c10f0300309403040c040640080d89071020b0380c9481c443c81405480c07040000c101c55450491003503240c0c400c1c218001d0034005588006000d104003944003612120000d0301f81d5035940780030b1a001c03800880c1d2880c02095404a0800b0a00261040d903801040c2c0302e080349010300d10390820803100c9013a045020490b04041e1141c0310007100002103501c00d5041025041d01041c455201c0ac20107080003003075004440c469020008200214000154101d902800d205400f030741d0b21540e040890151484000203048e4680030014880400f040d940a07d980d2019218401080c0042214541e2102c40c01c0e01c02034880e51140c13016880004440c4e00a002901d20b4200008000766203556803c19600341d6403585c038040c0d55420080220315818400e00704 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 939675845 1250 939674595 939674597
    0x11508010f0c052208100903021e060117012c011a060a051c140709061805150903060a0c0305011d011e080a060b0109051c060213050a030503040510 65
    0x441e034481c02a004080c0d02419010440a607180c5001c801600080e13628030000e0801c20083d160503a000501d10703c05009100d43c01c500622408108801c5241c030410203554464600c80a8603640c6d282c107098058078802204510b01d207540c3e44c0038a00d07103500010a0800c1c90f088d4002c803499905054011142182c00008074a005141c0f103440a8441b43c1e07400381143c5011860b070a105484111200c09000342c8800000f010301c0c085d00e8056140d052000014541e403144800384d44800f102d40c0c64070b0040b140c01e01c00020f1003a01d40c4903500305001602e0060f150840201f18402445d060241500011b8074014040d40c141030401c3d501e03c1b81310707080c642c180909405004003c0714001c6030320800030400001203051282c4c0c0010810000c0c0c00d20440b84802c0080014000b1100f1961070b42c0d4030b41001c0000b441706c1e000ca1404580055000203540c00d101c0f00411086680c0300b50b40c0039580d440d0f00d071400a540b01940c0c41e0300c800305602c070110305680c070f550504000d540110025516942442d0501c41f1003c04121994 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 939677095 1250 939675845 939675851
    0x141204030b010b0d1b05040f0b1c0903111203010503101b0c020d0611120f09191a0108070603060f1202040c0903022107120c0e100305011508010f 64
    0x10001c1000042024115041d004100303a880c104514000c0c01800b0040300e00e211020500fa1442402e07500c20060019559100194840785940b08450a61446004481010501c0000e090b082040041d4826032103e03002c1d0405051207101e14030382c14100b42e0361800f4030250050201c01400700e42000c010050394444e0031031003048142180410204e005003010706020800c48440d00c03d000710b4440760581080203174802c45c14010b06445502e03002064004200b10382c01800e07480009803035504d1809500c0d014545050203407504c1280c80084004c4060041000d850346205242c0502d420f206a0703240798001d0503541c000d03000140c00c10400a054400030340c4204160843c4410900007a4025440c48030354030b41c1120001440041000162140b296035030000e54030100300d0203403407018460701c1d5480522030540426240d110351a00c00e0041c64001c809006000074540e481d091022003030044140e90403e01c1e000802039a40da6a640382402d64110030300e02c40302c4940c00d0804200074003090146c1c40703005075004018 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 939678345 1250 939677095 939677099
    0x121808030a2a1701030f021c0605270622080403080412021905060328320c070809130e010f0b0904050607050a030f1406180c0901051b0109141204 64
    0x2481b1044c4407003001c4e00c504412007060880d010300c202000001136000c04141300c103240c040700e20008514214401030762009401d040198890000c0364007032003070f401c04855114240307074959000300521500e002216510310400010000c01e810710043c00050520f003e0789181c450b044d105002c44100e170301d900485c03c10f00840041c0440d1b610307941a01d40c0494100d0002104000c1c942c21f07150360352001c0010b60a440e07e4154404524000b403881c24521440b1042c41215680b40416442d1a0460880d24102ca084040c880840001c020800821060200500010a0031200c054450445001c0c03000c8003516035451507259074540b15406400e0780d400086880c001603180540740e598950f0002040402003000000e90801d4050184c0d010345042c9100d42010440a400351009000d00380c02524820310501d00b403000c1055441c2c2c00d074061846640c259040c05e04002c012401902d023a0003181025031001d650306c00c0303801d2550007445900034a80c000c600441d0403480e00d02c1e40f1030034482c1c1940c8411800b0810802 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 939679595 1250 939678345 939678353
    0x9031103030c18060405100e120c010801090209060906040e010f0b030f06040c09080a0b010e0a2901050d0e0a0b0105010e0f220c0906121808030a2a170103 68
    0x98800480c41d0001c2e81003001030f16400214648a2904946d6000842c84413003146281d00c10000c0b4059007050302d2039190305460400e610b0303039110b06e880040c5c00500040014440900f40750041e01c0e80e0107000c1d00503800d022840c40007881940150308180c0c5244203d400402c000e4001d859000e00400503a81454a1414100703940804c0b180300400c07090045854005032000d05202d9034103000202006425161054080d1510401180d0280304403e040080306010541d2980240b003003a103950b00f0310541d850b190040449141081c04696045410301500f40850a0300c444640512445400310700c001c1c2c076070b10f161450720780011141a040755040120746d0792480c0160b255a0300700084a6411a01d0b298076071311901e98120b408000229110301207041000f803003501500200b030403055910f80c1d100c0a000030542e1550400700c2c1d01d4100b9002c80760102d42000d10108000300300558000c001c024000c11101d502228105086641c1c082c00d4415850340e105401d0f1541c0d01036113100c0ac1c4852988180040d52458513 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 939680845 1250 939679595 939679597
    0x1409160b0a0806031005010b09010905100509091b0a030b10080c041701020d110a11190b061306150e0904051e1c180608042604080f0109031103030c 65
    0x7420014000d551010803181e03a800c1048500700e440c0749106210548c1c43e120480d48540150224a0101d01103607000b0515140043e0b103480e1180595445034100b10a0400f0815500d00142284080940750700c4426101e02d0705c40700a10403418030b9100420000e035400140000171034150148400c01c60340c2401e008450b5640d404440448108000b10184649410703801c2c2e0081c820498a075045900c4e011502da29404010301070301d0109556140d441e4946c0700034540d02d4850f582000d03150708080900c0b20100020300040800342d001180545120009100000220111002c60f00010500304941d100c2c121260b03440496122490001d84e40c03c9000c0c01c0540d50340d55200f00d01e01e207415802e5104d04c1040b50b050010440c401e8164000903144c83c001c03058442c041d005001c040c442460843d400000400c00b180103850150045078805151101c0081001001c03641310340404060080038020440018501c60400c00d020401c140840000f40220662a01a0031a1101b41c90307625030381c000f8000c1007803541005c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 939682095 1250 939680845 939680857
    0x60d09050a031115010603020c030c1b12030f07081b1911240306030c1e01020712111002031b070f06140d2a110606040b150912011409160b 61
    0x1007402358484e11310320361250a42c040c24403003504511400d1070406e20700c480d4a40703031001540305440c2a03100780c1d05840115200c1c492041068001c050421000d00060070000050240081c0aa0007003001c42c801c003201401c210342c12a282e1141007001c028001800780b8802c0720140c0040c2100c018030082e44100744142c038a17035001d0810003404000310000318580c0302071203112444940184146042019103038644940301400e0701c3c0038014428214045a40c601c0d6004070054150060340c11402d0381d18030420000c02c408506905000c40c041407280d8410074408061241c111366484000d440d280e814180f2a64540729164091070420803603982003042d0409d00c0341128800302d503410011480101600c0110904c84041e5070600103241c0d0000086131065001801c4140113503418117451103500c039076082205680c07070224055030092068454000880f6000001d0000c26000f411004030742d4400502031303085905898020388092158400c2040e00e40e403d0003000d04120350340c45c00c90b8059003041d070825580c0c0a14 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 939683345 1250 939682095 939682097
    0x30319172823040f03140405060912100e010e01110a140307020102070210080a29060a030b10320f0d0b090c04050406080a050a02040506060d09050a0311150106 70
    0x820a84032000445484806200071942d1001e11508191500c01914038840c6000e500050300b0b101e2250b090000f980458048880080c040c80c2001c40c01410040201c4428042c42c04034070400205105035041b40c045c1c81c042c0391544c4000a10505c98600c0603003581c218150b0800003103c10800c01d50001c1d0090300900200300307007001c041c1d1030366100308090340244104074000e50300001d8415a0b84600e6440b4009a00c502c007042c0c0d0920040020f1044407a400e40031402101c20002c41c4403200315141400d20261102c4408ca1070081081001d0b1408111840c0c5010520800122218000c40901a14552150100c0f076100fa08030704590229801d00c40c94020703032a070444000c00005114083c0a281c0e000b2548103000107000c4582ca081c859000a0f0742e9105204103401203090410009904502154603d01c0740e070131001800c64a0850388c20000140802414aa44914140010362014449110368081c8c1481500240300604a9080181c01c41502e400950305c180c1c8034800c490135a80000184504480e09 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 939684595 1250 939683345 939683351
    0x60d0203071b0605010f150e0909070b160b01050102061e07090306020d0615030c080f04031404030809031203010617070225030c08010902010219020303191728 70
    0x18080222a020380c0104001ca420200503204000c1c40b003c0e510035170499102c2c1c200b0040c1c10303603503500702c81002c50040000340110300445a4206a81001010294018400e0042da104240c0780d201c804940d420134205100c40c07040c800b48e190308004980300c00c40d014150900040189140641c2d41841d074940206135104500154004203920700c1c080d400c1d80c4040c6610840a40d100e04800d404440100014494025208544103a045426000303102e404041040d9554034030907a030b00c0700720400c40c03440041d00880800c0181305000600f140c250010388069486115565a98060002003500d04070302107200c042824020001003001682103c2140c901c481c40501003c65070390341c05016403c1c02e20b1100c0c3c510550350410340d00140d8159040c004000c2d6031203910100ca403291100c8000b401c9650f055030080c056441294001590103644140c404903034401001c0700e01e001c9801800c06d402005861600c000b14010640240009440300710b0b155000001418559441030f00c0800f030107205400b11506458195 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 939685845 1250 939684595 939684601
    0xc180114030a0206030c091f050706241e1d0f0414010c0e030f0d0e1c06060e04061802010f030c020f12070c0f0602060c1b012f0306060d0203 62
    0x101401a40d02ca540c0082a2580b0ba24103c1c0c891a01d0350710040381e06100e200044504082161265104a8044072076501c49040034001d540c1c510080140d5540194800a444d0350b04c5821503907251410040c03c0342d00c41c00c0d11800c5407600d5020010000d600310b41c3e040040c443d00d001440514182c90343d13105284e418204c0303803921241800150341500a8040040354240b20649403520b420261004a00e101030f0101c030319602084280d103440341d840c01c040c2c2000800c0d2401d143e51500d0b10b060141c003000040052481d0b0707040b45548443c2103079000e60000394518001c20402081c03155600c0307003001291440d15411310105103980000c0c4200002580b407824141e65a49915400e0300c200400d2135902d0b940c50454401644007105013980d50440c003400c54052041507404111640d01c5c40d10402203403030940040500c2d4a40d8448042160440081d08000d00310070341d601a1410701c00d0107141582c455445c1c100300b90780c070203e040c9125a58030903000130380c0322001c0080c0030098a031401100d2071151040c00040e00d9031 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 939687095 1250 939685845 939685849
    0x90103121107050f0103230f070f02010e06070e01050d0c0f0305060301180201080c0f28020706020a0f14100b0310020f03010e090111040b0a1e210608030a030e0c180114 74
    0x1840c20015202c01c0c07400c400c2000301c00e00400c000d060150f02749440c2d40c003030214818002c84c01d0322074000710500c1030b42102011445a41c058280540b0380c0c001418082d0138110a500d440c012948a51080c0001a01f4800c0e0132925640501c2590f8000704150000c0c00042110030710150942441c80e0000d040120082c0018402480481510000c3c6008200350303541e560420b030b10003040490b41794407100400c00d0f00e10300c010079070001038050200c420700d4003d400e00309000d88480505081241c3c0a48400c00702190300c140052003070002c5051203151000001c0d083c01d00c031062600c0c0c02400040200454410060100351201e0750040d00c1c111880c54103d001c04d5039421880c140501004030132301c0b2a2200c04503010800c5c8508034090403082081d5900d01c03407140c50621101811100d602c40800120725000016184030241e1042003401041c0c808002c42c0f44e5a55580840c619481944a9400244e0390703020158894014040024132520890700f0030f0bc0c140c2c200d4001c150081041c852407480d4107a40c0c46000c900e0b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 939688345 1250 939687095 939687131
    0x60a021c0807180e0415060f030b09100605090f070c02040c03050907150219050a080f1804021222020a1206060b181002100903090e1b09130b090103121107050f0103 72
    0x241c84400231a030b095981d40e107003c44e2210816141549940980110543e0704e0306144188011920010f2280c203181c1c170703410010f0542c0c0704090800c50800091746501c1c00581c80340e019801d10940c0729030380003500d890b00110541c00e101168025250315a052131340303898041d03030019460341c082d614101d19542022803403405900c0e00c0c3c3c0d00300c0000c2110401080c0560320700b40340b1001d09a5400c511100b809038044080c1040101c1c40b8020302418251480d40c080f449046000c48490076080355030543c50030114494000ad1240d021075400002401004d2294904100319070041ba0002c11802a0607030401180e100c0c4d80000c20100781000d40500b403e2081d0075180c6208000305000508210800c0207083d01c2d90400070124000c1c0c1c080e180d80112081c000c90014607c031803060f140000c0c03100d243c0e42042c55001c00c01082600301001221680d880d2402c151480e80c4d8ac01543d4000c501ca003680b018841c0c00090081e080c100300c20f60b040d24a40024034200416190211500f060790404d107400214080c00c101280c0390 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 939689595 1250 939688345 939688349
    0x40b0f0a0f0c03020d030c1b0b182a0d0b01082103041703090307060204230303070506010303141c02030a0c110c0108190e010f0e01020901050702060a021c0807180e041506 75
    0x38444c0900c00c40600190640040c064ac0e0710103e24031001032100c841a96598104801540550098154070301c5c65110161000341228014001000d60381d0b25100d4004d0000d0a0b00a0755080d0031104007003a200d482000c05e2041070b10030f10303c102c1c11032070300b91944074640c051091401140b504c0000003070040c01c0248211244564860000c5482c0d5440350581c24031111242c100c11000c4d8844006403003146000000d594503550300000030043ca030b0841e40d007195004040168140b00140502c1000011000c03500c0704210351050500045e01c038581304482e03a0a0f154100301c414140540d494259000d1000404c3e0310b000d110083c281000300b511b0b800e01f1010000800c181100405103031403002d90780e03c00113400004150501c001c0910040b07480070103040c200d1242ca044d0780e012410400103403005003466000f401400600d80141c5014000f4000c05600c1a005804524009440f41040190b050b420030040400c1820300000b0220b92401d1071003940d0510000b0b00040c1c4441c02000310140100000c1d000000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 939690845 1250 939689595 939689627
    0x30c0f061201080a1e120e010306050307060804170301080604030c0c2d090203010b0702040f02072a09110a0518120d030612230102040b0f0a0f0c03020d030c 69
    0x41d2540e5100101a2907040c008000c68001c1a03041c2580030f816501c1000000d582e0b0003000800003003207036507000c3da106082c410505050589401c0002a2aa4240709510041c681030300d40f8440c6e03140901e09100585a214186100d170f1304140010311a1000009840b540140c2c036040402d007829450030040000e212681c0424005207107482e41d03000445508050204144400c041c0550580d11000c0e200c05a010900803404a88028030a100151030141c000d116425035020005103068101c9d1200407540c100d94100141c8018200841e2a4254480384000c0090046d0350301045031411281740209607202d0700307890104001c0041200071302a07000700000e60302000300920070440c113a00801c0081d03c6500310401440803910f040e80010790b404031402c195201d81d034000103820111510311080c07041e000100603182c01c150344c203100c0411083c4c00100140349141a0111294488042078402080c807120348542d5410040d620040000194000400c0c6927500e006060200c0c0c052074500301140c1201044103003a03 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 939692095 1250 939690845 939690877
    0x715051309060e070206061509041103010b042112080411040603050c0a12020a260609010b0901090b010c110111030304060501060324180608011a0901060905030c0f06 73
    0x1901e0741e12544003404580e441c01003a96a9035900c0e0040ea181d0700d00700c0d00140c00c8140e0b10640d01c0080380c108024446400c2c01031000840c41581100301916420980248036010b100080c1404001580c0740c41c4181002c40e00c003030a190700080d5990910381041c00c214081481020400b11b410003d04e0882003501d41e01c007802c104050b03556810890340d100a0000b08901801c683c800c0400c01443c00803100304040e8007d0920300580d4a0140d0858801c4d641c181e01c01da4080030100714010300f0400307210a0780500303489030011801d106401d04014044d5810b134400c1d00180d00e08450341616903006403005504541050880800d00001c20050b0f810008101030075082e404000200020801d20fa444141681d80340d80d07042001c0d070b5280704038208601080c008088140711000c42008444e88542c000480c07425003d0303010800b10381e203c031650700b035401141c1910703031103495000c0342019800c140c01e04d140102900e2038004002c0340b90401294680000c0101c4078043d625012010740c098a03100103c8020284103001e107 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 939693345 1250 939692095 939692099
    0x20405041e0b04020705030f0d0204050d0506041205190c170706090519080316020a020a030605090d05040f05040522080c0105060609090105010e0a0b18150c07150513 73
    0x72951860303074400210449854070076007002a007064800c0d04e0762198010b00440c902103282c4250b000c160000c2c902c04a143ea000c100c0414651a042025400b5501c100c0042100707080a2810954602c51588500d0803c4018270031805440301040980c1303050706080c00c10401c0c601440c10904055000142c0ca02144040040e0440800c44a03034403029029004d8001da4050304800c1d82d6810411070101000762828109102044840d00b90341031400714034081d401128540041c960221308501816070043d15404e517a02e040140784e0000f845001c00c40d030410b02e040e62a02c1d04011402c030990605000e031502850395800010300340300359444c11003a151111030020003510402d14201a142d4050724002c0c1e825420031012614900f0701200341c400540d001811200c0036805c0900440e041c4400c441580d6221042480010315088000000c121034244030232003100840907142403103016a60410030030302502c01042401c90080f8040313801e1054640c0f4480b060b14480c0c11140458260080c41f15844d0b403c2403078140 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 939694595 1250 939693345 939693371
    0x902100c0309032f040b10050d0e0a11040b0307080319020c0909010606090e0118091a150a1a0717040f090b0f01111e19110108060303181302040504 65
    0x380321134114040c440e80c500c041e00c80e0305210a0383c100d1546c154120003403400c044941c5004070f01504c00088442d03000100c100844041600d4144010320584070203616029540e01400d082c0035400c035510342507000f88011440c0240503a0740780320f40c0020106074503030f00030905940c1d44240820a000f080040811003142480c000060003401d9501c110004100040c0c400524040c902002d1070480741c54013041440c10b84042001c002070a00144100d0b000001c0c843d03507500c48400070032070740d0140d1900041010000b848000f07011080602d50001014846109450940792580314201c60031190300503090a420100c1a034101968015a080903911216001000c101460076501a294500f0101d443d40c4c603000407540156000240101070b1641604100403840203d50f10340c1040941201000490300e00e940030842c0080c00c003a144000300c0d03002102c0c1c0c01e044190340c0e2060b54a90012022405545400f042e00d16245820f41061540b030b0103110400c00c0c2d83d800e80c0c00d0b641550018400074105110340c9217540d030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 939695845 1250 939694595 939694643
    0xe01150b0c240115120c0314090f120c011d101103040f0b0411041d0d110d08190e0f0f0d050d0f0e120703020d02010902100c030903 58
    0x30300c181a40b194400284401a404034464030303409141c2c034102a642d007080d4888070000401c40b03403502800503c0c070b1545a5441944280e10b210f60482c0d4000800026039010340700c401c5170150800d00242e00046011614500204101e81200e0040502c1c9641e20491a010307400341102c050070700b000305007011440854070008140349142900748501004600241e00c00c0225500040d50702400c0c211004845400240d00903008680160041c4a03030400070b00f5020001b4261510100655070036881141c0040d001081003011136000529030074070741d040c203060204c0a40d9860166004400700444800442c0e2003000c0500c0100b020180c0100c14401c152080d40300b83c5e076800214070761400510980c6049140c4080101c0d20440108966903014a0000400149009400044208000103a490b01c40740c0111a080101d10604000110510749818141c207010b814160f801103078034156410106140010381d500000941d03101c4882c180246541202d08040f01c0407030658000070600c80c1c01c54070a001d014101c078 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 939697095 1250 939695845 939695857
    0x3100807060f0e150f18040f141303050f0307030225110a08060a0b121b0306010f14100507050a03020601080c060f0306040b0d0f150e1b040e01150b 65
    0xa00d60000f41c65a0005001c10a981c582c801c00703188500344030b03070030712511300314001c024099000b080052144804800982141c40340c1e0032400200f80c0d1904c040b003400d60b10f5122117900100d43e86490000550702e40b805801e40c4220320000d040800300000281c825030096041d5a45500542c0200c0c41c5500100d40b55064000b01031400d80310018050940c03072852030402d40c140203682c2da100c05400c4689801e44101e0261161120a40d44038910000ad0b511411082101c0e16880705600d01254005100313900381410584180c10918605905410520000c6100d040ca0079920f4810b807140100f8040f908402c9803140140c4200400b6070241d240000c05040d800160241a1444038041c3d459503c5070004102c03e9204034140107141540c207000058141c6000e03072080c058802d002e401c1c0c20492881e5a03c81c442e01100c1d4404490003c90b101c8036410106191080e005103640d010002c151f100300300e686411812044250491103203848081004079424290031500302228014410b901d6552580d010781c00c560019 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 939698345 1250 939697095 939697097
    0x32d01120c0f351c0e03121201061119081606050105090106020a0c0515070213020406180302060306040b06041e030b0601170705130308030a0b0f010509030d0503100807060f 76
    0x4070742c40c0c505403a008043d2480712050070006250003500398010548024820701c0320390030b009041c4905442520140b100e0210a4a91250f6a80e00c020518940c2c030102c5045c0c01c0202009070b0384150380c100880001301c0c1c944003244d1320b00c2c3c03503150744503898400742520801031a5074004480c3c2003c48104420398210300d05a450450322001c0d281c1c0c80303807402c903078a082255014201c0c0316210707000c001c1401d000c02842c0512442140b0185042e1194000c64441c8550110f1080b030b4503400a020819107a001003c100390102252010f03000a1a680006106010183c00c041c40303a42e0310b18451840355181d004032401081d404035065034849400400b010848050701c015500310080c0d000140196124200c94140807611490807503850326001ca080340c26400040c400e654895400001201082c085806903129101121003c141040141d00788050040041c40da14103000781403104094030741e00800e040754912418a0050b48a0f507170fa50142e0710b008032907801580d00c0d00070742201141c03099021140e00000c1500d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 939699595 1250 939698345 939698399
    0x11191104200403030819110a23040306090501110c030a0905060a051c1506020109020102100608060106081b07060e19030806010507020316060e120c15030402030f060903032d01120c0f 80
    0x80112701111000c600e0401300c0170b0a00401090000030000d42c0103e52140c040c0c0c00001e001a040741a80e2116400041d42041682c00030074a0b2000079484502c1c1c0015040655001d4141803200348098050700030702c034184000811086021480071510303441950511024041d0004c01c65890201070700034100d13000164018059030048d20b894000301d01402c03040300c24400082c18540e203040380403103c111001d8540745414080c44520070710036400d0030203080841e0281c1000503500040100ea030745099011160389900c0003511a108006c40c1d001020540c1c8103c0a0034060b540346440d00c0003c0c2481254020702d410b5080103603000c100aa4003502002d16a10b0a690300c0190f1400301078800e40c0c41000d030311034680c4002c1000d9141e6420121401442d001480a81241c0001c1c103140c0030281444411a01484541d001000308015152005001c0602c096118500c1e011010034101040f4402414040c910f07940d0030030030414003084900000007004040701304040d800640c48131291214040090300c0c044040311 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 939700845 1250 939699595 939699617
    0x70b041403060105100f020304030f0b15040b0d021c05060a02030a150b0a050703090914090c18010506032e050411160311191104200403030819110a 65
    0x4000074800d050319401081103120317040803003040320410321401002d011400203010020010388221010440395100d0b2241403c0d501e808620802d009850000c80e1b446030f41410400401501c80715141c0b20a0b64058a000700071100c186d0710b0360540850000b0041403442410100404815543d02950241c44c54034028045184904001c000025003401080c0d00785004100442c5c4003400b07400280240c030710904200207140e0f9a5112003040364110a5001030307040e01c5100700a08072106108004459808854000381100d6007144114444d00501072720340034220000105030034100c1c2c401060341d071030400002582c00c0c903d015044011605184200c500803070410750100040044c7d642a5030304511502c81c80e0180a401d5201140c00c24101c0728441d0a9014100076121503a01405801424a00a0040ca110301903503805210445106000020015610340341071004941c0e65411a02100d406260110840c2c64030b00e040321011401030030b0340c04128a0032141400c025141c0c00941036540ca5505e078594540 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 939702095 1250 939700845 939700849
    0x312030a060b1e180d030c02030c010503190504230a12090b0901031e0501080d2604150204050405070c050d181a040918150b0d06020903010905070b0414 67
    0x40105180c404407144048207001c0741c5803d0801400214004020601c0070545002c0443c104108268041c0c0003e0812641030f020341c01d040010001e92007007860301514501d401004440d6a1004210702d078020368641001c41d040c070200c90303605400c0c00b07001c100d0f000300252805100c0f9035a05c050481218000e5031700110101060156000d80116114014032626140c06507004500a01d9055101011100881c0d07044511101c4c0c0c1c410f16010340504002000c403407030101005000035030508140c1d0302c40a1140380741078420399041c41842d0820b42c80001c0b0f102002c00801200081d0045da0400341d08240341c901003200c503941c00002081c5072402a03003500e2a600e07520b4422038800c900b28110000c1c0d103c1d104410455107100e0b0800104103c1c0c080e1030b46091a486030000130a584031800c122081c4100c035a95401030084a1100101c0000d1090003008481040000324400084018014000790b0b07000c20318241e1600e007074018500a1354804242c0382034944900c039502054000d405040c10900000021100c54 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 939703345 1250 939702095 939702097
    0x3020705120c120a03020c0904030c0507030b0604114e01061e080f07050408370b041b03140105151801171609140a020301030b060d03030b0312030a060b 67
    0x31781580c050010b0b80d21034802d00c1500c02c00038004900700300c2140c0a0b00c0c0403d40a00c0884c001e5441401c04104600f0440100029600010300c2020f0010040005000041c007200d81307030141012526821030340c03461401c1e81c40090600042c1d010046c200c1110051020f1741c10300505416a0082d03229042402074440720000c00110f01e51383c170340116800e00c1c04241802c000c4c880c0e181c0c3c803450f03610b403003440e2a8031582c44506003400c41c01a40c90f40d1a001c49000307605045040c21a0307010940c480c84001034119600c5011303440c00f02510141c503800b81d004011408036101d59440d000796030400d1051180407141c0358550b0080c20100c0345403d100c034031489442c009107050742044e0501d8100003030040d00c40e403e101040c0410310407140c0503026442200012241d08561100310f00040406840009600c44111207903440550010500e4040c2c1d403041005000044c2d8071103101f1f41152080e500d01403a01c030342d460140e0040501400f031940c10301c640d03044500d0400d0750100451194021180078040d0355521950030751a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 939704595 1250 939703345 939703363
    0x90605130506031906061404110d020d11070308070306090c121d0a0309060915090b0d0b0301062904081924020408010b0f060901030903020705120c12 66
    0x3202200044480341103003503410440e00144000c0c1503c6000140f5a00e024060b114404c045441d1510f0f903a08110003803280151030342c20b074003d5400744000d000008201d01a44203151050001e19801f1400c119120001d0348460090303c2840025075441055080c0545004000c07076402002900f810004035101855000307002c0d5820041c2c68008001d24292041c40c01380c072045d0746220f40e4514520303081c0240c1408204a40c2514002d440d50100b040c1081c4006000520b20b4102d00084501d40c10a007207101c2d03010f20480d08a403045050701d030300c0d85054403803880074142d45403c41c1d52540c2040c401007007100c01107440440341c44600104045000100c0642e070910700452141032007540045c001801291500082c1c403191321b00c500e201800388542841580c11002100d00342520729940070600b80002c4000344940c1703051613800c490ac0400e8030304000c005805881984442030416465060000425000f080307508090140140151040f503254448a030b0f49441140e6032500c50f8184001c005044480899500e01c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 939705845 1250 939704595 939704599
    0x50a090c050f1f05091c050616030f0525020a110d08070c0e160c0210120204080a2604063c081f06020318031e03070309090605 56
    0x44080e00c1d20781040182103840001a400a207041151034064030076a2846650390740e03076200c1c0d40c0c95503080e200788202056904134034202c0c00f4507a28091301165000820550181c400c0e001c60701400000e0742c0480103840080f6440030b00711708103028020303c10902148480e0f042602110010420707042031049a586d5040080035014401e498407510720b074103007000d005c68280e00440c141da140003040e903078005202020703511810340080b05000f400250344140250110796030f01c52030041d010250b0340d00080c0e03c3c800c00f100140d0510a241c04148202c035000e80540e0020803543d02510710300b1140381032012503041700010f41096040041001040742110700281c809682c81d50741c07140490341010301e141a948107081c0346543c140e49956144424540c00c00089203c0700304690b50324120741000030020303421101446103422035101c42d1a0038030456500009955038140d007043d400c4080045800801d0401070521048840801801c203001420a0004010010dd900c00d5030f03002c042960b5141d07160200c6070140201e036 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 939707095 1250 939705845 939705863
    0xa0915060b040e0a0b03030f04030303050117031605100606170c0406080c0706140a0213050609010c082505030a020d0f090e040302011113180e0604200303040f0801050a09 75
    0x8020b103030301800300951181c81c4c490009038500302480001e00c0c5070000b801c20110304500142c10302c01c06a05004032801003d410344d8144114016502c0c01e86c07a4001c14601d0350700b040344885e481c1c040c80410000c80c0d40e583d84d04c1000b0480d242c1c90315002030290001c0d0300c8400d1030300513000c0802d03000000340e41220101c1d0750030340d20281c0e0f035121405071300b285501404d01501d5040d00c131941010a418001000c0380a980900401652406000070b4001d10580d1640964400e690600161000d030341c1226520b101c0b075a0010017540d641c0080c40307106540340c000f07078880401d4594417440501044000402418480d00c15021035030038222414003114124550407c900010340400401c002c503044d00400907070494401d000118081c000d40d10706011640101d16100002884075008021210f0103004010710302040035024050102d40c0c4c0301d80c070754400000e000200500c0000800039240c08020f07440950b22600141501e50391340e03440c50000701000c03440c000e1803225403a0a0204000c00290b115401320300e03600c40118 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 939708345 1250 939707095 939707099
    0x608040b0406021e03060102010e060402150c0102040b1809010807081e0c31050609011e0b0a05070605150d1403130905090705090f060d020d0501050a0915060b04 71
    0x614084201030021960b0756001d110f01d51400415254443c0309029408040352039281c40d0000a0944403103441e0704015411500500000d602d5015035001c012400c0704140d0380c3c0700140802d4038024031980e03000036040600460902c4c02c03c41e0446c201d0001c000201e07500c0c0308030390301e5002e040d480c0c078080c1c4204001c940c021006641103114500b00306041d14002c0090711507a440300c0010840071a60075400210002110900f10481c0460744000d0041000c108800c103c2ca241000100e04268018042c2e11640820604107540521514207110050105920010b45a0207222005015a00408400c4440720b060400252010200f560b8102401c030000b42041365640c0070b80c0b1030741000c8a0b5065081000d02007003205c0080282d03200c04c40300080100400005540c80c007003000e9070801c0642d405c40c5205003500414803542e0241e101100b500400700712158060a00f092000640d911101c1c42d0040555081c5010400112060350011003942d004280304240c90003c440a80c00b10f41d40f602611113034901c14001 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 939709595 1250 939708345 939708353
    0x9012c06070c110d050c103b03030f0909060d020607020f0a051207090b030a080a081509090f01050601050c0a0303050603030c0a15060b0901210f05090109110a060804 73
    0x109115940c00b454240f8070400852001c1010074480d01d40642c2c00d03600924803010a401c0c0710b5502e00021217640f0385150340600d80001d4060f02c070310045070b4000104801c203031034552013110307490600090001411290f0740c3d020111605a0742d0000b1031811301c00c085a0000455a0400c413030304c0f40c1c0d0030364000d00ea5403910016a08000d040c410b00b500c0ca40e004066160041125110740d44040c0c074914600c402400128a00100384090781e502560b15070180d082928408005400c000a403103000d007050034042c81603514451800c180386011040381da40b01c44070405014400c1000300f01810151f540794003e1056907144d400540e024800ca142d0440071340e1040e448000443d00c280d003c81e070460002002d0780d141000d50300c907861601080300c5081d1050100708804100d25801c1e0703c64400103264800710030341061000c10000e0419074220b103903420300029a091034441e42c1659444452602c1381c21108202038140300c54414020420120121110f44203003e80350228600600004219242603a4034021907a0310360b1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 939710845 1250 939709595 939709607
    0x30f04140c0a170a0c091d1504020d1b0902120a050c04050f060705060a0e15010509010e060f130501090f02040b0a03022503030b0f0d0c060f110609012c0607 69
    0x10f503180e401e004001c0e03203c0018402c9aa060001e048000010603440200d4180030100300140c40001c4699001c04111040c100c0e1340040340da8400c0c0c04035401c2c2611891f601384040110301401003c00c482d1800d4030301052031034040e405049003903251070300b00100b0b994128141080314029240b402200405000400c81c1e441d1407802c044405101806042c03e00c49169106840d2400640300d48840c0703a00d5440250200d4410403261240f24002c070030300d0034603500d0b14000c9500c810060240412810b000030006207980c5072b0900400c04282c0203010420345040c1d401d0600c0c028002030142400960501086402813001802594107071150030000900d0942010802e40c001e40c054511100c4e91031a06200641c00080341c1c540c00441402920085500e0640c48200283c0420245040e84a82d20b55081030020480580d841000d440032414401448880080f0940e1201c200f80100101031040b4000c10406c01c00641003001400d040070300400183c45814400d46064014444e1010694002000a1481440f8071 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 939712095 1250 939710845 939710879
    0x7091820150a121d0111031e10120b0712020702030304092c010902030120030a0b06090d151812030c0306090c030203040201081501140304080c0102030f04140c0a 71
    0x41401c400c00c0e904140036070280d4040c031000c1d2052241302c0d004220352650078000c02581c01242000d9034514980358001a95014070b84c000c0c40080d0251600050212880f11140c1d00600501e401e40004808680303010800030408030783c000002464848007070324000050090741c4690f41d004025508003410a98120000c040b20840000703008201c2c0300c60440181c0c1070340880078203c007410010440b40c04a0050509541d2080e800c824030300004800c1000c0303101814243c9401405400020a1200185002513000d00a0940c01c0c0e070701500601ea00303410042540080f00c80c901452006210501c202c07602c1806132080001c014160640c0c2c20b545407402d500c070390f002c2c144100050400080050325100410708403881c03130040700302003680001400203668001c840b0507403005a41c20142e10042c4510002010b24030322501e101e03180c0d54080003190800c002c0200b0f80791400d130340d500215103030b250900c440981d800040d2010340d40641c440c04c0c0d120300c40d00041800d00580401a10701031741c0174600509000c0102901d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 939713345 1250 939712095 939712097
    0x2031e01080d080a0f15030b010b0301050a0306020c01110d060501080903040b0703120906141e010311100e030a0b0612010c0203040611010f0c090f05040603020906100207091820150a 80
    0x143e011020500034600c62a4a046c1c10721a44408643c21890181507404068010b1500d1488c02d000400140c1d4550303282100342e0340d10410168480003e0141140540405000c001c0885804101300c9009140c1c2c5e4040e0080310001d0340c400400c0c1c1c480c01822030310b9108030300513011840c10400a20020a0044103205013006100d8800100100306407219000c48444225202c907213501c4800f4001170755908181d0000c10510001c10407544c1d4910395601d00a4900080c556004010f02d40e00c040f0494085c0d6800958100701a040d507184122615101e26011350440e54944204039001c2c5d40c84282005201d0013945c15256002585070606005040d14043c1c140c0c00020602d42d214010403081903082c1c050018007078010780340c00d0300450030000d607503281103031541003a8000d030320300702c81040540e403149000d541146081e038148904103c849401c904004a60b00301002d0142080c600c08466140c8030034940d0214082c0490b11202108003219045036405d1002e038503030141c12010a019003050136401858a4865 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 939714595 1250 939713345 939713351
    0x7110904051c0f0e09060a0303030b15030a0b0312070308011a0903160603050714070f0c030c0b09030c0105030603060f10090e010609150803070b060a0b030a02031e01080d080a 77
    0x800303402a5070300112620b1020001c1d162045100300b90703400442c2c1c44104c0d401240d940d449464880301241d0340c0d050a01c0041e0030507441743d10118042d259000a0390703034200c840b00e03901d50b40c1c03415102610160080b405210b0092003030400030840031803ea0156410641d256035089226460404141001c011000201d000e0210802c051001650204184040740c1d500320211000030f4035140000d400c079040205500c060240700310000c50000f44100485860b6507000d045035903040361a04181c2c0c0c0701000c0d508010880c070340e000c0c004914400c0402c0035118240d4110200e40000700024011a0709000070754400740c06500c16004900c1c0340264030700b401d92001e0050100050a950303564420306844180c3c03000b4004d655100b01c00c1c000c03805140101200102c96600c04048945000742095991040300c601070701120102e03020035030035a01c1410340300c01404d81d2403540307440341400c40f180c4c0c0c02948265a800812010310061407030a801c0031800c1c9040b0b54045000c3d2207010401c3c4401e4031003c000604818001c0d039 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 939715845 1250 939714595 939714613
    0x102010f140604050c09210a1a01030507050f130c031b2102071a0406110f0d1506120f091b03020108090f06060f0303070b28020711090405 61
    0x14092099498210020150030071504101041c8011540050089201400104131428203a100c52050702600315210600a0401990500090414403100c00c010300002c3ca004040c841a001c914071541601d010354107403040d840c0c0d41c0040042401c0310140b03441d0031139011a1440c2030f21925034050b00304038065003004a40d10599880c921440c2c15210050008100ca1034018000915401140410070302c403000110303d4103003151108034440b8140402c1c5044e0485400014082100c103230441d0300e12104000307009031691204134081109800c03014000042c9032400000c400201030384030784007040707912613110f042d190100c1b001c000c4007610101d0052111142c84204071400520481c0c0c46207143c8502d0700d014102907003140300040000c20040c110919591151a03200304902d0080341258002c01c0881c0c20300c0c0e0322203079140403d041d03011700900a00068095010007420340502040c45040c6040104005901165031840034100d00038240d02600c00c0106c0100b101450032710341407080e000b0707010310304a50400c4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 939717095 1250 939715845 939715871
    0x18040b010b130e07020321191404020d0804080307052a1f090b040b091807091404060e0a0b040b04110d090f0503030c1305010306030302030d09060b0a14030d030b150702010201 77
    0x100c7c80500604182180c000c004140d40340701251315094070000000d001c02e0b11865552404007001034000f0f8410030490100c80200701c2c43c04204c80c020910802a6500c40b81e25060540d142c00d0b400a030b86200120b10507600030641a149000e40764a03070010b10a00e508c01e850b00356400c200914031180c0c42031040c0319402013020322135507010700000d004184c505682c5000030024030a1084c0c00700c5812800010560900c02202d410905a2080c0c801c4501e40b0284d5466900006010304000d51010100d42175035000d00075020181d0b0841d480e0000161414400c5d81249421700046841c556420328510302c0c107009040b0302424581200054034020300f0f0407080c01a1988a540c1168400d0b02d10742d26a5500098600405000b4124140205424202000958510b40380a91240710b42c01126828a648581d07031010840b0795070080e1148000600312544c0309807200c0a055200002061036032280c0304400c0e000104510a015038003c04030090409510b4401e00c1000d00110303003010b24224159501e0f102121004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 939718345 1250 939717095 939717127
    0xa0c24020d0e010b010c0c171903030b0a05030601081222080a0606120c05010c0327031401060b0a0f020309130f0b0406032004060518040b010b130e070203 68
    0x2040801d080050441c021045050843c4c00904840741444004440e0002290030b40710000211807180c40110381d407280142a2608040000040a00324036004400005060303140e80a040c010005964000c00b461300c2d6000c2699402c024446c208140d07110300503510354500c112000c0c1001d0341a08000c10001a2110311074400031002e42c21136500c59010780b03100014403005004400003040f0010b15607a070004152294250704840c5c0c042d00c0e05110f4801400810076120300aa4a059090027100303c1c43c007080b10942c3c00201200e40320079074485020503c500030200042c81600f0450300010b000c145010100301c01a90b11400c02e0120800354081400240f080d80c45808610380b000512260000741c606038046000c045803801003000d401240b401e80280700280c0c2d0100c08136000c0c8025841c0d08182103031003001602070800ca8100a80000c0640341e0140180146682940594864850084030703a8a8001c0c0b40c016009414a04103020780d4000200320800c0c2481d081900305410340b041da0301d0300d1a110744180c12 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 939719595 1250 939718345 939718357
    0x120d091a0403020c031911040c0e1224100621050702010c0f020d0206060909030c0a0807020a060c1707030e0418060b04061a0a030e0a060e070b0a0c2402 67
    0x1681103c0d11406217031030184003443e110754401a10f240130300e0b1b83c0e4032a00228588600680c1c000c0d0795031a540c1d0303845805400c0142000302e008280d500901c82100320305031104813040071031034048a400c401484000900511034071464800c4110a4a28030303000c01102d6038450008105503c0305264030203560b2a00d01c0c0070700381c031840103074002160300070307085500030090200001010308641040408040c910340c0410440c0c1c000ea400c964410300b42e1101804c080c194400d00d0082d0300c0602c1528001d01c00c114000001c1d0400a00032a08607485075a0307104241c41108040c50018003101c6c8003100d1a0842da81c40b030123005000d01925041c004103420760040303011141d89600c0c25090003448441c500800056009606080f4015a014032616242030014800c2401010303103c5943c641c04a001011140f09611549082810030111400144c6a080150040c01820005a018054a503001c5199130f003520031104204910f0342e416403002410780740d200104022203140d40c0d554060145102041e8074074006415 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 939720845 1250 939719595 939719597
    0x180b0406090b070f120c020718060311030c060a0305040c050d0b1b0901020c150c0109032007050904020d030201090c06020114090109020a0506031902120414120d091a0403 75
    0x580080c1c5082040b48880000d10700010044020500c2c4d0807180d000c1c0d84128200104c40010618480c0141e007039081881c03035040785120001007041240301222541150003101d01454990051108a805242c1c94010100b483c54001c5010803003052414801c0d030000b0350190040d6002d016017a10707440080c0124410050a8803810003000a21445135907484241c8928002074890a01d4040340c0d0300046e444034000a8014414104401c1c0741c00010320303507421036030100741c0c0301e000300700600b02c600e00581202c40c0c680e6a407080040300c40482076010300002d0344105560717004001c0e042c25650341d400c001c10009554421802c654884032000000341402e40c5043c040c09081d000070840c030100f041001c0c40900014800000c9a05001c10030b80585c80c0d0190325420f890064a072160f81e9522410010b200c0004208c00b00219440081c419a040d5074800101e4010340c483c0100c20062040d04842e16900d290342c6840e60350714482001640260711490b4004680140701d62504007202120703e044c0d038821401250260 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 939722095 1250 939720845 939720851
    0x5040608130807210c02030c0d06141003050d05031512010b0301050a0e0c010815010302071e0c0911180609030703050f0312010503060415020a0509030d02011a0a05060706180b0406 79
    0x40025507603400401c1e0300804c50300d01100d200005400003a614500004241d000d5070b00e98400205108080d0405c2c802c0c80b010119203c174038208a041001035210b91b10050710035000b00782011034418880c0c2c040745d002c2d40880440340c0c4108107020070419070680009070040c881d941c2d0524407041d51004e01489104d844600c0b0002802d0000c00d001a0030300b50088091410440200200700e0081d540001d14068480c003840c005844000c245442c6003400c41b80d0100350b00e0190040022400c01c6100310504041d00d054203424443c43c480091688030070f00480f10308240da50190104c1d5001400d01d0740203000c400d01d0040494400c00c6e640d40342c19080c05d41240d04e001b4150000604103140020a41076140181001d0b4020b10071340c80c01d030322600c92503004200141c01240c4c0000d100c4c64160300c500d0550703d2010f40241a55400794841d80040c1c020072a050031032502d886138035a91f00f12460b18007603800885030098a81e5180030600e030f51b8a001040b13802d000160111810250b0070105482180304c61103288156000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 939723345 1250 939722095 939722123
    0xe041a0418060e120322051b01030f020913110f040b040f06090806071b0b01090207140616030504020a0308030405070e0f04022b05060a0609060504060605040608130807 74
    0xc1c0a0f141c5484000006900004001c0244040402201c0e8403d041e03101c8441025610301c008817240b60a603002420501c205e4010700b8081c08003256400394014242c80230070810900c0ba419000303038000c80c41802c0e030000f411029101948240e420000340e054001d40c0d450314010403852443c2c02034100303070810068464049418040c007107580d90220050115418400745444c0b40608056076044014920400c020311001440d0b100075072045da1002c0070b50301800e01d011315a146e000e01002034002d018182c818203181104030319003d9000c91454042d152000600070103c1d06c1c07000c2a2301034800070b4000c0b600100d8000703000000c0b81c4403d0141d401a0700c1600a0705860340741c03a14122000d039002d850380003080d124005000c010b03581c545007400c1002601400c82005044401e07001c58070080144054004c1c00313180c08115032040340c0e41c042416100703c08010441c0984540a00c000c0b00c400380240000b10300b08100a008103130080d102150722242c07444410000c08050b81e960300361600f00d002c0890340321001c0c13008 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 939724595 1250 939723345 939723353
    0x10909290301060f030f0f170d15080601051002030c0601081e0c010c150914011b0504080a0b13050a030509090f091507020c0301020414150a0e041a0418 67
    0xc03490300510124002c0c89054200040000c45a80500c0014801001c40c1020410041c2411040d0003281c0c100b03031405c550161042492401d0f90040000e50010742c940b500d0301240036009200c0500b039440c628002c0c801a820241804070202c02d8200307a905501c0203000000200310708100c4103010303003088405040c4c01d00784150300392504251004030041e181c00003082c02c2840c0e40d0110400c00d40b6a0402c003000c1a0b80035800081c00102070490740982881310321501541038100541002440d21070303110f0f03003116500d07406104035007031301880c0220139898020484850100300c460b4819604010308520750710b0440550358074245000340001c002c9001c00c501060851262a0880d046075003c1c0d0b0490340010b0a1402c030300b182d5250170102001c80c482208900c00714803464402c0100c943c28a602400840d9030315140c00884120601c98541d56100741d40c91405144e2143c840c00c1a10a0014103031038030801c446c510803c20010b0204d03403512804407e0b15002241150351a80103598400300410b8210740058641d00b4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 939725845 1250 939724595 939724661
    0x2100e19031211030d021b0303070e0901080a1a3d15050910021213140f010906030e030712030b0102060a11040501030f06080304080f010b030604030c030806010909 72
    0x90b103041804074030543e42e02c000c1008022500100c08660006a9950072548117001d4650020000501c602c0040104000075410642180310b410040707824000c160f986011141c1d89203025903005111403c0f82400e10000120000fa594109100050f08100303220000024803c80c003403004d528103510800018010358450240689010380781c0340304682201034100e44d0160040c40b80f485040e01070040ba2000c5407000d4424492465203150901c0241c2c2d5800e155210091491641e00038800e00723211a02500005140c14445c5600d08807042c0c664a80280c9400c000390700030f008600b159000760104110410005401d64a1070200b5082a20009100a080c4000901e07155005210700c1c400ca01e401c40105e00c00025a090b01c04a880918002c68040d00c4040346070b01914842d03100703401e81d200100b00403444040204480100601d40d5000304001c40654040540d5410242e50141c007282d0010070070740109104001d400e60208042c104801c103150769071102400c56520180c5100e1a407083d200211000c2c00c018 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 939727095 1250 939725845 939725873
    0x70e091e070c032c1011070b18060a170c0d18030e0a050105030c0a0e031005041b052d10030c020f03070c0e040f0f05060f2202100e1903 60
    0x2020304583c68241031181e00506403100c1c4c0303440b40d4a0a540480058401c46541d52002c001d070090b21400d5076070311100100d035041130407000760030b4000300d00321646424508207480c2840483d0307070b681d03c20400c0c0e0303030049403820700141c181900104200944480c100c00f41c003901d1581d003990010049480e24a0078010210b280c9840c49034425030104800700020303a0700c20b003602d41014614040c0340e42d8a03032aa805640c01c0e04203031490713601401221640401c50403558005032103a4010740484001c1d5544421240c0040c0d0311340280d5500c141d0740c40048200b4908440e88440c6181c05035a490203488603080024060040c000a6000090700c03003006a11281c0d0520040d40e010142200031030038120966030b4901e5820145c0100500821110300050a0107000041e6101282c3c202d200e0010200c520f003441520f40300100c031020b00100040340401c0260808100c80212002d0b84030a002c03456900740c4c200089c1c2400041503204010b010480c8204541c5c66074040f0b010f40160f030b0921104c6916501d042c40c0040310328 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 939728345 1250 939727095 939727127
    0x15040b060117040201110f1606031d101122080c040c09140303040e04060c0f0f080a150504060803070b1003020d120203040e0a0c090806070e091e070c03 67
    0xb00000c081c050354881102a04290b0900745207a10001c4484980d150007104050703111107101c3c4a00c1100c811402c998410141e440396a0107101d0a050300d40462012419048103a0283d41f003d9109000320429502103400302d11010903052a02414045120043c42a2200b02030542c038200340c100111601004107006040c401c0d9401c0c4180b4890300c0024140003440d01c2940410b102c011907001c80c990b02802190080d100c4401086502e0410341452001005000e8198001c500f0503407412b103980d0f009a020701e845c10810799400e191039556503035000191484940840403954510f1011440d030350385000310b80107040740900440c1c841c0c9513410403500302c40c009094035414004215003840941c40c1c0d04285178034180c0203070395030700c1254810000324a5841584c0c0102004034065081c0550907400750840703e41c2200743ea6541c101c0130313190060503840307002c01c0c1e07005000f0415403000510710f401c1c0140000c0c1e0110b1564164040c69a417610442c9881004032070060001c2e1840c20134104050700165501f00c0302040c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 939729595 1250 939728345 939728357
    0xb03010506011b02061305040c02030a02010b18070f0207050604090b0f060c030f03091606080105100206100909022101140c0415110f1203010503150c0306040c1115040b0601 76
    0x1d0f20411034040c5040303400c0a4007900d000140703800e0020340380c013004000740700240c0108102c3d00702e06002902d907001414140015400c010044102c0c0c03602c84240045101c83c900c0c4441a40c5841006443d001d82ea520000f00354000c4d5180000c00d42e40f0756003e8030040c03900b410041480c0d030034a401c01c07911403055451035102e01c0d818440e120740120000103907600010810396050b0741ea1504152145003040140e0340134641110440042500717548500c02a049038070980760002e507214036003c241d8885a00319020014130740c440108010303c0c00070340c004a1030540054134140c80040200b8540c0d051090201d075105003603446010701d1a58000c401246980489036650742e606103402e10440c3c0421840d80207482040200030342c06801d222105000c00c07600300301404111141c000003040e8000c0c00340c009201c0c05101e40904081d100b40c12540540d902e1190b030740850001e1079950f649080000030100110303c001086034400043c40980700400040800a03465804041603152619201d401010000d00d09410000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 939730845 1250 939729595 939729617
    0x70b0406091e1e090603210302090d0204110d0e0303011403030703020607140405060313021c02210102130902070c09020f070f140d0c0b060301230405010b130b0301050601 75
    0x11148645000d46040c100b44400d11a101950f01c84090144e401002d80075240000020070050302e030300f085030001c102480780c00048400d40400e5049000c0c044440d500005030b0004403005180542c003402c9105620003102d4140300d8a080f50f213003111303446103403140140d00000060002d44810002c40305a41402c50040d8680080c0756002501c884000e842c40003030000c0c80516114506402d001e58019201c00350100340c40e481c100f400241007400a10301640242203100a00c401501c000c0c0f151008642c02903c01141c09281d480907035480142c024800c62255401c0c00f07c0c001c0600104080e4004040c0d841d0056214021401c01c11841d4410b9408186c00340d01c10403500c0c088040003c1620300c2150886110402c0b80701c60b04041c201c00000c13400212650180f130200484a03504600d40444c02801480072141664801d02414200c0e03400103440b030310340544012648102d0004500d2103031b105210708008101e900d6a03101045d4585a02c80400703800c292688417a9009090134403885070700101c24640050120 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 939732095 1250 939730845 939730889
    0x20a05070b130e0621061605031302060c0307050a0f05060603030421020f0405100f12020904150e070f0e160905060f1207050301030209010b030712020714070b040609 73
    0x642c410a8a15855500041e1303c56403040c00030790f0b40500d000c410a8583c010010016102c01086601003d52002ca49031310a00620860580e840341e051808070101c5d80d4025000c0248513004004203800381d00c800c0003103c0024006200307241d0154411080e5048201603450184e06140004020fa0702942c001c0c401005070312042c40e208000c02c1c0300284003002680050020895011124214640090400c024002d60301110180142100e0b009991540e2203901c034603460b0b10040380408081e42c85060030303001c41c000c1460704200b507680340c28445002500101e01b81c4030358280b004e50b900c01c0c01017074007043c820000d100d442c818046c1c0c06205140c50b5a4458000240074004446601500d2b001d403a021494008001074807044840c15826881d0345003c0e40340004000702154000d00040380500720714170000545c04812400d4902a400640321002c081d80006881c030000d40003208280c0e01c028910840c603513103101c1807001e04090a96000c0642c1c5e601d0911202901d9580a0360100e068401e4560745403401c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 939733345 1250 939732095 939732127
    0x60f021902210a0b18030f09010509010c05100c030f02030f04031112030f010f05150d0504020f090f040c1509031211030c0309030105010e04020d30020a05070b 70
    0x1560485085100031071103114250001c0d0b003020308800910411404030305010038030368182c2c4a01c06a021031800d10040e18600c46e164000d8070143c1d40c43c21000d2143c04550740c0210b000d010944d0062600c00e0694611303898840c984003035204135a41040c1d071441e404103c168035028014250000c00d50a40ca94200301a000311050303801080503003080b51003920041c82e1901800300d0048811015690fa45a003800d00d007010921900380301700010198401d40009841c10b1405000301040c15034848181002404403e40c806400300900403681700c1c0418001044a548102e0304c0e5008000481c0d10700240c1c549850070321940b420541001c200b200c503031107442d1000350b400030846003901c0d848141c100303030801080d03001d9601c0380c25201440c08038017000c202c005c0360b000008050100d080c4110000e0110fa40e8809040703041c034030240c030003a41043d8102a0100428a51168009140a1551a11003d070102160b040a100c5016642001a00102011424414100140c0d005400c104441a142c06c0c420800f002e20f03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 939734595 1250 939733345 939733393
    0x60414010b0a0e060903070f150c081209070e070e0f031204090911041113090b3033130308180303010f181e092a060f02 53
    0xc00c59140c90054464481d0070994110340f001904035103407c0d44401585410150311300500d00d03c1d807400005e01440394441c119800c1e8541d00000380610305002003020046101c40202003100a20541e02e00045180340404124428405641c4003c4411614010041c020018103d0340d4421340c000300c0c1d231a4502d0b42100854080714003088000500c00400c1c41c050780760303074030000c2d0459000b440c0142000c000380c3d081e0003d00b080104000070b4088507440351090f0b003c075a0255881d640064010201c44c001e041790311681d50030480316a6886142c2d2411b401c0d402d20300ac268400315015081e1204c0c0a203a1078842d201c4a900d0740c14038042142c241d14140c4042a40c1c540d02000140070418050081640707901030b110410000041a42942d41d02d6842d02404081d0039103070320660081e0003c010b581d10902d4031034803e011078450402480e0940c90407501a00380540b032076001c180c030204290750b010740da02100115051104580d000301030a9144c64000060700c000480d046403015504504109a600440f03407541c10070b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 939735845 1250 939734595 939734597
    0x1110706031d030f0319061203300f0f020c1b1c030305040b1f181d070510140d11040315050103050c01020c0a0b03070e0d0b060414010b0a 61
    0xa0742c00d4200008240002c03090070000007a0100190900409a140008611030001400d21428410f0811551411200c00b0301c200300759244441d0481c40000d00c9880c50881d0203420f0b01540110514105250140c0b80031000e42503000c07980e500c050220f0b10564042c012825406c1c40c0704504202c18540f499884101e40c0403880d41d10200003a1000c10769036400c210860551012180c0c181644681c600078008150030b44003541c1d458103184c000755202c1d00340d01c034810b00300e03100b4108098458607101440003040441620500426281d02001010705801411800f020191400510318180b0300400d000010503005542030411128800d4115104401d1007150b1120325440000280c1c0c00d19000814114084d9810081c40034100740520203d24016070040d0b07058078080d40c01c1d201050f02100059a48440e44180310740c0000e0328000401c014400c0401560f0700c00e1540c2000d910b803880c042c0001e41c102c800031908484880c07026045c8012410140f244400c01d010b00c0480300b40030f506103000030040703000e01c500c510 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 939737095 1250 939735845 939735851
    0xc0402090103021c0903080f01060c1b17032703030316030f09030e0a060207080d0c0614040c0612091716060204140102010f0902060909091603060e0c0111070603 71
    0x34500e64400e50403100b1507400205614040c004031004100a001e1042c419000903a244010400f074650b00700d4264100c2d1915150b0a0309000c140c1d9a1150581e00c050b1007805100466200240380f0494044502901a03450003556480c2c0040f100b00000c00411050310300d0076410f440755140142c030008201c98020384101c00001c442801d610085000d007242941e204806410140b01c0800c0582149030500c00342e000310b030195512034545000300d0742c507101d511031094140d005442e040201070082040320f9400e07002d5840407802480c1403c42e04021001510300302c8500f00342140400c01c0541c4180503030403555011700180851415521002202a4010000300003103800155000000b134881001032049a4085010364985a499154103a0a00d00c4080350340554280f00f03019650001b0b61140206244d401414103051140c2041402020900201032104038890340090325120500540355200562181001203038000300e210b01142080b48218081e4188110400707100c18170140444c1c8482510181c3c5000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 939738345 1250 939737095 939737107
    0x30806090c071707060f0b030c04090203010b030607200a02090403051b0a0501150f0f0b0f0408010e060105040e0d2a02040e070602071a07120c0b09061602010e0c0402 73
    0x292840e1241802c0144100c0144510340c40e242c003100301800a41340205801c00c50411354a004005480400c1039007507041d0010310041c212490141e1216041d24000740c00010305814500201749030103425100e01000c0740c05820ba044002040342e003640381440d1000041d00c4c1003c00c0794089001450043d1008080c000003180008241c88448142c40401c101442281c071802c41c42e05100c0d00078072500d8040400c0750340c1003a01144004045614000711014119150512898030380c00b2a55030b00f05410710300d0072101c10080054050024099014403031548406007406514000820040314651005c501c85500121440700c1c0c0765811a080c041d021400901580003404100c02c108086503c16000030740c403a1034413804902e0590002095000e4981d43c1d021a017403d615144044407085040342c1026506104010280014101044840d070a51250030007680305444c84e5180040140d04981102c081e07840384040050444101c50310711000460f5000802408043e084201e469044941499014540001d25 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 939739595 1250 939738345 939738361
    0x5151e0702130c1112040e0c0d2306130c120b0f1005042d031106041206020a0e1f080408040e01081522230d02030715050403080609 58
    0x3040210a082c2810042031401c1100038000340c1190800150307a10602c2e1001501d82a03000803101512030392090038a0541d1903101c18105544040f1a06c99259194a8062040c2809080d500e070a4515048043c85c42c3c0303050000c0c0016807121078038280c83c50f0705100c20311a01c4c42c3c0100180550a50b80c2401154207110800841c03941d585012003103801c849040c200c1043c4aa1000190080c5c46920b007840c1c80c05404010340c29465400701e0842441e403650308400b04001043c441480700b0130340007c0c00443c2080d40d910103503882c614a0b01c0d02a11855000540c1c01842e0f42c0c808800e08512804448180000b4000c480181e105000142000180108440440c05005400d003d4900404042c801641c1d2580c40398041e644510003030007601d42049071913010030258074425100903010660105541e01040bc3c544a802052405c90084011403240d00f000c031802d01401d108461840085030004c0da40e07880c4a1034201142e034a21038107142210b1605042c040003951120341c40c0c0e040b0004952114881d111074103 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 939740845 1250 939739595 939739609
    0x605040f05060a020d05011421070e10180c270803031303080705030f0703050c190e030c0108090601090209120f0d2c01050a050f0301030c05151e0702 66
    0x20010342588107403810402c00000b1600146013a0041103018005a40d950f0107112400b003900c40e41c240d000b010274496505036200503400500a1410208130703401d071540e0304142c2010780c04c16904aa41703103040c100c041c040401150440f955608078518104070702124004014241c20004007101c1c00151940401042e03106000030b5940900f1808042da035981c140f112040200c11085081100400c08200002d4100f41c091019640b0819090440441503540d112044004210003003001441030b50030311185c884000d01d8a15040100080d85444989803995420546070404034203600381000010750030800381d00300108000741114400403000d40c6803480760f0000b48401c2a0a2164a01c80c424007410300c0045400041c84400a142a240c001d14407580042c103282c41180c0d4418820b4000c4008620486075204000030000c64060b458a5400d0415146000840b68801c0c0d00c203441c001035511091007103141100f003c103480c05180000300d1030300c54046081880300d08504440c0f424107034040744a0741507407103041c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 939742095 1250 939740845 939740873
    0x241e1b08040902090f0907020a020402250308101a07021201020f120601030f0504050d27090212010503010216111f051801020706140309010f1b030c02060c07060504 72
    0x10036540301d60711100e0440007904045919072003a581c820302c1088504161800d640126016030281c0b40060749602032102941c0000d405000110580900110200c203000320190607910a540d81103140c102080c0042501011303401c60303032030040710000200c440d03400c0c5011a004d8035810b40789105201c054941070b07402405080e62000204c0c1c400544c0b510380000800d40355104050036201000201c94a00105e0301325141100c000f085988590b003d01b50407809043c10000100362072280e001d100c0c0394030340282c4035031005034803d5400c25000324113260b104000700401805458158021801c284903c0c042c00e02d40ba200308400707040413011180c052a15100ca601c1d00300f0155041c8105850000402030042065208042e4445034141d880c540580395032002c1043c030110341a580ea00d0650b80080c0060842d9644007410b82100e540da2002105c3c111035007802842c680003140740104031900704402c0c0140c11703035071401c51080454115004208561a120041d10650364005400280d10b81d21458054507034175000c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 939743345 1250 939742095 939742103
    0x9140f22110c060f070507080304150c170c07020907050a021221100f06030c02010912111c0f0e0102240613050103081b03070b01241e1b 60
    0x440102141d154040000342801c04411080310303540d54581d80070641c04c900a0301c0d0300d0001350040000001003150071001c1c1d43c006001c0c00e00341c11821800d0388205c080383c0f0b4210001000c40c81c03003081010200c6140c900351b54004000c54049103459503503400210354910003040c04007405008501403100d68820000d500c0d941090b450120b681d140c1d10300f000c0b01d8006c541d90802480680c00c0b0300186c213035822800820225030024144818003030030814160098490f850b0340c1c0003190b5030341c220031012030361076000c43d00c9026041c0c03141d206480c110824181010388503245c900b144070400126403030081e8800d0f1001c0b1018030310702d40303084040c0000d0300407800d0550b03140340c8a507012440d0a65050801186003150f0084004449d409a0b1000040301d060645d002444003501031401403141c9082004902410715002c0144001d030b03032400d400381d902d01ca1550020b030002c254040d00038010b10007070070085076003100e618018141048601d07200307100b00361b8480000c940303c2d0800502514038501c004000028000ca2a40 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 939744595 1250 939743345 939743351
    0x603070327080706060504021810020a02130902090f07020715090803120907080c0904060c09050303070309080622021012020a030f1103010f0e0402150408010c09140f22 74
    0x842c02c0c1115160400c0c1802d69096250000008082c41c0c80e10031105d0750541507410b009511900700400282c03000201041c1e080d4022821a803006a6030281d00c1c4104c071564943c0011404c51380c0c0180000044000c028140e0508400d050146143d000680d031f0003180e50325541c4200f00104503400311050156031b40160441c4c840800d004050a4001c601d46104011100031200e03010b80d11610603648012085d0000d0b0000c0d40381d00800c000c03610700e0f0495003201c0b030303c3c1c2003d41075a961140400d24580c01140c058001600c0c800c8203211202d024014136400600910050300d02c660400c00910345440703e500000e206608007119070603024004c04040503060407941d41191100840b52000d8040d01080c060b0018441c544070310003809094107001d6a05850401e904400718a0401203440c588160251059900c40d074413007a075000106030540204080c1180178008141c5031039a400191029850350043c0042d100405042861a11551503125420108607541417011081c200b4006080d000c045c045d00000c0d00b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 939745845 1250 939744595 939744671
    0x821062119140610050a030b0a06080708030711090c031909020603071716171510210606021b0d1e030f090e16210f0e0601030206030703 60
    0x102c8104208110400c200c10f072211603039000e0391041c00c00018040d41e03521400800092021900103402c499000f000c5600000b005601e48828910308041d50b40010b4513603100040c0c40040107030028140c211f00e04156804289428032207001d00c1e40d03020050908001548450084e040501c041d0016020140c001d00f0180e66400c060f40300804442000340c1140c150708100b004240f14100c0200e452480320215680e5003a060915020341d818842c001d40f05405440e0003030b504099a1740e4007080452500300903282e0710026204000d40080d01c2030025010150289840d2081010b80e401042d503142e9a09094100640382c0d0801c4000749064501318401703000303411401c0d0b00b02103401e0118070041c00a0f0094841e000302412141c400c984010755802401d024400c9032003c9240301440c0b4041c03038001e02003400c4c014407502c040c40554080380c1103120304084030361b00e4100c0c060580e482c42c452851140e0080010307004540c195004207915100c02b0b0001000c159440701810000a111000b50f40780e81c440d0704401c0e915007 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 939747095 1250 939745845 939745853
    0x807030212010e0108280609021302031905150f041104180237260702071701090b1503010b03030d0c090905091e16030821062119 57
    0xf540034054050360b07104004003405101c0c1025150702291500003003100d0350083c141c5d254005030500060880c1c0202d030a035041140164213002131482101d41d09142a50304030b9a111000c165280580b24031004180514024580c1c0c503055424182c8013020384000c070780c0464800c000c00a80c03180382d001c0664045130716010995540c080e001002da0a000184d000c021009c05142030202441d0850541008a00b0807a42150b85000e50b006079200001c1110840c00441c0c100c014081e006821141400160001c650030301611103102000d5408050050003040720b82003a948920650703101500c02183d4801404003140c096409410100f004030000d81525119008800020040c0004010640106440c0700300800c0380355891243ca8410b00c2d0f01c100a00203e8440c1c114032010145850307041d0036901030100d4010031140075419200007140301d80203079540c1d5008083c9661441c0c14981b0203501c3c101e040802d1120582c0d5400c803207000d50540c010030504400006080ca49042001254a2000000600304d18140 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 939748201 1106 939747095 939747119
    0x20604110109210609080301120203060903030714090a080f21070b0403051303020a1d010b0307020607110f1f050a060e0a1d0319090603020a0203040303080703021201 73
    0x3000c00d031b40b59042154000d8106186112042140000310f003410440954000070b4100030b5400c504140400418015041c24030318400240403c08001c03907903c0512030030046c55084d08590007483c2440e0b582d9106c1c04400180c4090244250031201c05145d482c0481e224164045411081c0381d81d01e940640d80307500a081c202540d45100d0001100685502403c0c00281030545100c54407075007810b100c81200728058100407241c100c1401032002c49a0006800d40e04136419081c2100b4003410119182d240c0b441a10380d2102030311441c00445c0542c1c4003000c40c2e10b20904441c005016903505c100303e41c001c1d5011403045008450700403000410305c91090784070101030401d1103850701c2840803501c241032440e0090301ba882c5030a100000c000300c4264010074844c000b050030b42019401c2c4044814061340342d01130340c4405018804880005503200b48640d0407109201c00311118031400756183d0a0f14402 = true := by decide +kernel

theorem cover : BRFrame.Cov 939568345 939748201 := by
  have h0 := BRFrame.cov_init 939568345
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939568345 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 939568345 ≤ n) (h2 : n < 939748201) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
