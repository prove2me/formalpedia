-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1054
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:01:56.624035+00:00
-- url     : https://prove2.me/submissions/5ee08d96-63bd-4b91-b4a8-e9ef2244673e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 189388489 ≤ n < 189568345 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 189389739 1250 189388489 189388513
    0x9120105090f250b0c10050906041106070b060f1203040308120f040c0501200607020d020d090b0412050a020607060b03010506150703032c06040203160302090c0c2d 72
    0x1280074480031100700110f401040640d40300d1009210b04640c10043d14080400180d01005451040d24004203a42c8000140810b2003501d1014205107002221113910707040c05643c0e03180000000405203841050524100700040d103401413014440701080e01625512901d03890301800c00d810400141c05100854000558000401006a40250f030400b42141c0307901d141c0001101e80a448071801c0d8100b00c14098030002d4500c0401c181801048103030040c100800c54440c000345080f01030961a000c00032294002c00404030704c501100c040c1e034009030009160b1841420f2041c03404e6041d00c0001d421000000b0100d041c001c09501900d11000210020b208030b49950003008041c4445000c00841048104121800030380a9441000c0c0342140700b406000142800c4c80302c0303d02c100324078609112900488108021840c050000020550384030396150000c0e030460b008180b080c20000d012802800b00040c205842440802255401030001804090441d1010481511003c14030517202c2403031113401004c1034 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 189390989 1250 189389739 189389773
    0x504020708071e05060c070203030d110705010c090513270308010e1005060307050309011d010c02070504022a010b1306060f0804030813020121060f0915050609120105090f 75
    0x483c3c81c0c2110061205031642400e08001c0e0740210300890741407000b00310444540b20036018041d00f10544555040e1200101d0030000d00b520700b408c10703080410401020a000c103a894011489501881040c00103280c568004040e005140356035241c0803038041e0316400010980d200718a01e05954440d00c0400301a10b90408440000c1c2c80f90180546c4210180b0010b1143c1e40b01d070340507640c49000080003180e41c084090440a04420143d104001a515040c40c2c40c00c1c290100010300090105450441c0740c045640011003502010740c401400c40914001000c0100c4c04c03d400c0300f034038040f00918811004140415550007031509116250215109210812025000302e690910858058841d080b10f56a98002e052140f05000b2040307041c0548510700031941d10a0b040500450000ba0000050381c1c0d003002140030040c601d95100c48000c9080c06140b440030310303800705100111181541c080c0d0b228176001c4001b907102d000b1402d46400b2907181c10b0030006841c40004004403800805030945100703007100002c038a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 189392239 1250 189390989 189391043
    0x20f070b0307050c0a12081f050a091d0601080c010909140408090109180203040311070315050a110c0d090504060b030f071701170d030c0806010c0c050402070807 71
    0x49080d0809200040b035090040c00280440441081503032014103541d500c891484004007050720001c0c40e44810804112041e070229440c4294008002e165039203018001200e8130340754029501c050713440e10150710302d1040328041c510300030341c4000c00d550581d0f840e139061756603886e001022140021442c0d040054a00c40c2031003a0040c00c182441e01481c2940c8036110413890b07500c24803080d410040b070540d000558091130905140c080301301e0b5101580c0c81c03e0a040c000d04105241c080d91209070001d4004000103203140e100702003400440100402e9903640e19040704010007451801ea4480e42000590101d0360801181d0b070100d0303044d50340f41c0607074041e240c00500040360614050000e40034003c00220768580c447c0d08100da4011164a40400790382050720388510111800c0c0e005d040f50a65001c03061200c00410300209058546500d4200420081007a000303204100241281c1d06101000045105011300b100f205409000301070800e55560796680b802c8900d540c030400094400c512640c0100d0003e1440313105803 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 189393489 1250 189392239 189392249
    0x40605070306080c0f0a0b0f130f0e040b0405120d09170a0507020909120c0d0206010605070b04030309150507050a120908030136020301060807172a120403020f07 71
    0x80c5000b210442c241700004603880782095000101d035200007441700c4408002c0a000301941c1d1103035100c0a1000e401c6c1e1a000366900054840200100c05111400800031060b40c420341080d08002e4540783c0d0308120341001451071909503410340c000f40358100c5036400e8110948503445003642c00c40c0220b00305500718007401440d18070000508204a10300262a200d0401c0744c00030015401c0d00d121144007115041c81340d0106455044540050701004110344d0103000090062805080c824644500fa50300c1d4191118010300050074541e0b585a40b609105441c0306500400c0f00c081c7e020890750504a0b40138140382c11064a01000030000007408049000900851014550102b01d09045034209800c2da82900701c1e10b80d10704901824510a1041d403032007246112401c01180200603680c1d41050002040800c0040c904c2043c82540c034003060701421801d0003550311040002e1584400d411640c03d4140c5a041c10b04800c10030400070501c25040c0d280ea1507107500031817080c0c00720f42c1443b01c030170502c549480e80c41c814 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 189394739 1250 189393489 189393493
    0x603070303080a0e03090303030411010807020a030c0204020a05091207081216110105070611030712050f0a0e0109020909010b01110d020312040206040302120a020f0312090402090d120804060507030608 88
    0x200d0200e0b451500140d4138542e42ca41a00c1c1031861640210b131450304110b4056840d05112003e0740c1c125600900902d4100c05184080d1000a40c10b460161160031003180080c0501c0c2e0000c0c0710095144034034141c0d014800d0041104004031400c10710030f0340d101900d00031740580e03010b00000009000316020865600c9011190200c0215155403140244c505c00b141c5032605100081000c400003440c184030b00004800d000003031940360308101e00014010480f859071402c11919260070301060303e24141840d548071000060105038041501c040074090020304030f00a410200080600c000b40c038041d00b240c802c50100380d851855016840f0052642c03482a200d4010242e0010000040b0251068400f036a010380060603043c07410780c1c2c1e503001c10500558000d047c034054010300d0b40e0004600e4030b105c0c60b28098078214028055042440b03003840c0c15200e45412b543c411903000070841c0240c0c440e0709242111580003040000005c510f1035010700b0514080300d044844600c0c00d400202298003e224540c02c0e42d85400c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 189395989 1250 189394739 189394741
    0x30406051e0904020703110721061508030d0c02070e040302190201030209060c10050c0a0507030804080423090115050a0c06060306060b0a02010c0801030b01260105090a0c0503011a1c0b01060f08060307030308 91
    0x40d182d00608035a4007180e000c0384be24901003400c03202000284101c0a000c907000810341d250040c001c1c2060b65603040002088422070501010039800950b020b0065030900d5036805800052006a009100d6028015000724020440031104100480c0c80c591040c103100c41840b0984c0d50300c0c1102ca440c42941424000f290040c0000c0300840d21940106601600c110301d181e241540b507550036421421340d03030a0300000803a001310502c91410318030740da0b0f4010a450f6000085195107520f01604602901448404100e504da1445083c0b060b95004140256082501001555102c5a40e1055035214281c40c00c050360820001d0580d80f4407803040e45040329084012140c103030742821603140c61504004503803100d0070002d5035000700b182c800b8480c4500641010307006000c105001e00d080c1e002400c05a1250b032086e4900401c0c4640c1c501200c800309407450040b1421200700c1c00e40084518056a16800984456046030003c5900c1c4d4200d00c85200b85111900c5421903036070b031207080580d6881d09020040000306040c1c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 189397239 1250 189395989 189395993
    0xf06090703050c032b0207030501020f0901021e120d0605190305070b0903060402010507060f060608070e0901030b01050405070c06111c0207030c08090f0411030106030509030406051e0904020703110721 88
    0x2c40030400085c1c0b02d00c161404250ba1340c440600b0390f0001052812187c8002031000915a0104201d84205c940d20696140110380c0f80020340d15580c83d041540010321000902d101001c16660200c400740c00000c02480c42c48068210040400c4c00078001182d840c070544401241c2030907403000b51054801c004004000396560fa600454064100050444055403070300c02001c11540c0d14000c050181000d0f0745c84041070302e400d17080100520b6858017640d0180c003c107401400410098002103065910070380b0003052070f440302c2c5011141c03040c2c40c12024001528201e141c1444c0e440480c010952512413080340c200e00c5040b941840200d01c40d001005010400e124130080008400e000509000040240f031414006910400314007074030398492001440c1203001005000140d09403103025001401400114202401c100340a01b00e4421446807011213629505505140e8000000b2070701080c20180055440301003914002c1d2035190103041d030303204c0c60240780000302d02006098443d90f4403504100320915a1400784d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 189398489 1250 189397239 189397303
    0x4210c05190614011809081b0607080121020f06210a05180c04091b081e0a0b01030b25030209040c0201020910050c0307060504030c030f0e09010608090f06090703050c03 74
    0x1b030720300b10b6a803034091100d0a000b200b48014002d0210014000e400d061901e0030000707000c0c5805801c4074222060314024035040380d02c801c1d03481c442c940d419035190703940051080000d1182d02442c0d45d0a03002480603400300400203070440d10a8058000b43d00240b02c5611071601d008869039071080302c4451980b088900c8c03290780c54180c021040f5a4041d00404c59032141c0015070134103c07091074001c0c02855001c400366860507109808a41c940c0e5001d1809007910b800d05a035a070304880410f2001800b1750002401040792880c01e070003061001c4d054540446014400540050f019400c0a0041441580303040501003690340180222010200001d00310075010390055010b07940307a080000c0c424100c1c4003c0c040e580010301d040c49018000d500a032140000241240760060030840455200410800c01088099464075004c507413a0559803d401c051400307965001c1a14603040d0300d1800c28105114020611545450100d441c109503405541580c1480c03a003141456a505d0b418081841d2038005545080310403402 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 189399739 1250 189398489 189398501
    0x30c03050315060412030917330103121206080601060c08040302040507030203040b0a060317030601050c0615030f0106050a0b07020a0b0a200604210c051906140118 72
    0x680a0302080302c2c041ea00440c4813904550001504101a901c0b20030074190001c03102c10081000346c1000050041c41002c061f110704103054151018a0500e0403c0e5230000980d80041300d01c0e5401e5031541d013030340e92802c0c040c454411800d4804041110840121403102c91402403600340c5100400070700d140d0f46003120464182038180d4050b90145d005010110040c3d07514004d140c0540319030b540142c0c80707080c20304000980a02c00342c10907403400d00e0158204006643d540744440c112081e07030303161510b0342d88007401602d40f803096500002190081004212409442040780e040c0c503002502150100114000001e007243d0031342c082c5551201c0300740d4007000900f1102005058180c405401230320741581c1c8801000d511380161135500081986a04c00341540e00d0314801080603070301904020541414907450b1a554041114210030070504062850601140101e0b24420010740c000e04442816960280d8192000403074002102d9075418108212184003800303a0980c140d500500010415040800c510f10040c10 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 189400989 1250 189399739 189399751
    0x14060f09010f200109140d1715090f0a110a300c0903120302090109030f02010302040f0e06100804121d0a0e04110405010509070f0909020408030a020c04020f07020f030f0f1c020a030c030503 83
    0x803410009d41c01c9803148014580900b12540d00c500450420310103c100f43c5203a181c850a4103403040c00070540741e03035010700c030441d04260b040454075a00c82403ca100d003414404217406010700c3e08003071104078141e80c03160300c00084a0040e004401c000c0841c0704100d00b84e203d808200e40c00034510340002e10100720380320201c0708102d01c141401840d2660f594400000149a61b04c01c2aa83d0424030821456081142080e00f0100d0f0034030304a4104d281580d1542c803018403100303000c000c11403905041811500d402034640208400200300404050761008202e60b02c500489042301d1607030351000b0501443c1010700a440c1a11001006200b0326074a075107080f03070086804070003041003143e20100054038403100d00c010409010030138060f40e51030020b00e4007e49031031700c82401310303010314810001004107464100c252a4140e50486441300b011844d980043c1c13900c81c840d03489002600034089081c0340074500040700d45500451200341d00d003d0300f490f54286c1e280c101c000809408200e000d101035000074412401158015 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 189402239 1250 189400989 189401011
    0x501140427050f010303020c090c0d02070606030c080c12060702030f0304050c1c020910060207090213082b050906070605040204090b07080114060f09010f200109140d17 74
    0x4002040c1c120140c4600b80d80c0440503400d52001801816414040f10750702d45825208040030381003064668441c4d208040700400d0303481e8046031150412010303402c042d0007140c1103400c590206840c1c03509241c49454040d00d140c81201280080c642040001c03c6103440740b401c47d00618181440d4907054041a400240200c82c02d0050003095201941c1c0c094164229821141d021350401c2020b1050040c40c0c2d20151041c45411403210040044660000e405001d40300d00b03000c0540c448001c40074110b841e058942011419003c0c94850105040c01005403054034a080c030080440c084000005507017a00c10425096003202d010000c00d004602d1f00d030002500140701a0000030702e8140d54842c0100b0135015108000050b0403900104222000c4c40408200020212005440d25005110a039068400c000369107041c0843c140b20040600e0244401a04108a281240408840f012220350080c150303580c044802e10722210080e0080d000000b9203001820840c1c540e140f40040c0c640c6084034810f0000d00440c904 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 189403489 1250 189402239 189402299
    0x301291c0b01030602090f191a07060f0213050105070c0306021c02030906060f040b090615090d150507090b09210111030604050106020609030a2f060402090105011404 73
    0xd0348903400d00c1d00a5010701c4c001030312007000108116000408105203441281000c41c0708402d40e40c038241706001c071850018800080000305007030b51101d000b0000c1c0a07003840c1c074050b14060030718070b607400419030b60b50400345001d0800c0d204d200544180c041c2450103459000b10400600c00102d2990051201c810010024055200800218000c5e0790040755240d089070800c038140001c030b05015440248001085a042c8401501035004c503100800040c5910300c8bc0500313a13100786d000180304040311130040002d030140b01c3c1a030b03803420f00d0804070841807072640d100d903d01400a503400e4803411405051341c818580380d030301e004001d20402480650056485504640c18401c100d41ea103030074411515007210780301c069510303440c0c11800c200803540168004011340d00410700b0401c0040000c022981088401d041c6000840d2144080386d415010802c2c0d07000160119440082d441c2c1130000e0814070a0f4421a2110126a259801183d4010003264649402d0006101c2404030301001c80610174900c044516078049 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 189404739 1250 189403489 189403493
    0xc05120c0703060c0c0303050901060602031206040213060807120c0815031f06030203010b030307080708030907050a09020304050f0a03020d032d0618020304030f031109100203090301291c 82
    0xc80d513458881030007150030041c18030b00705a01030107241e608c980c07040000c00c00706203070900c0a5182d1042000303518442030260300003083d0355200c0d0b05560014000070038400301d2544a58001d084060160340940200b19a41380b80300c170b140c0c1d03640510f42c0e4040041d03031390041e07548900c0e8000c0913032902d40b001303035030315010340045420850b1181c0030742511000c4611021031154594018542191064030281e80250820420400800ca03040b0807914007941c0079030308543d29568485064145101a00b2060b03100e00c0a038070000d01c014075a005140100d025009803401b480c2c5c0c0a90301542c0c0c0c0d101000c0200076800c40f060301d20109000e40d0011100484084180030310700c0341e00c000c5807038240400700c503940c9807540c40c0c0c401c1c0282540309841150b00103000d10300f14918107054070090000541000650209521400c2c4c40908240b2102580c82e440d80107004070388840d0300f48c20082c2d100d8011602d400d01945c44e0851070540104481c0304a2070520860180c000303070000c40c0e014010402ca154007507214800002400c040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 189405989 1250 189404739 189404741
    0x10e0414070305061203030919020a033e150d0204050603040c08150408160c0504020c100c0504032102030f04181d10270b06100c05120c070306 63
    0x110401c074550700001c2a10f004d004208014400540c00521544207004100070214006010044581940700380b0001d100184006a1600c540d43c00003084004909a40c00d02d0244640e0994215807000d950480898000d201c003d42e04100300007196440803444800400e02801c00000300840d0030a01805403a240d100c0b00402e00f60b074000d8070700320b03403201051000304031001040c480420551848929458036041c2a02e940905000300302003500d091000082d41d608000e0b034071195000414025000390748a81e4000d4249444601070950b07211920305003d83d10310028403401c00c50301902d42c8050691919203000d40ba00064498846074041548020070042d003050745554040e0000708500c10780030212500c80080700e801d032002042d07440d20104000b0309058507840003150394071840e080d1000000316150814030030b8805481c1d079117000090b08000c080d04002d01c1301d01a031013071103103005485901c0030003a44101103035440744011020f80340342c11044901c0310401e5800b000b00340d8461480103d078941500c0b41c46201c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 189407239 1250 189405989 189405991
    0x406080a030e030709060f03142a0f010203030601120221092a01090e060103090c33020601030f08070503130504050a060302060301060f12050f0f091902010e0414 71
    0x5400b082010190000a150402001002d40090801440000e24003100b0100140e0a03000c014234400703940a003e04011420004100010810091402c021800c04403540d4081602100035010307180e1510f003000e155000104aa009a9040c0d4407140541c80ca028004020b40042164030307007203810340100c007030003045801c0c2d000e003e044070b08007401032500e030a0b005070f12010f682a00041c940c551804902e0340c036038008161a0840350115407555040e07031080300480061212202c02030803412851070210303010084503040865050007040384100310441000440454400e01105401030340010010700c00240c945101110b110300c640015410310040e583c80d07509507041490300a1340c45c3d203a02c03070801080c502400345540140c0c81e514108107507403c60f0041501c41c403050040c1000d01180340100424144240000204210400405c1096040c084a0850740400c107851b2040ba4170707a401c0c04200025000720742c07030340061600c0342050304800d240d9006451035000c0f500d02607409a0b803000b0000717031000c5120005e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 189408489 1250 189407239 189407243
    0x6031306110703020309120c100807030212010b0406020f0c0a03060b0105120a14011d04032a120e01140a08060103020c010c020114010f08121617040e130201050a08060406080a 77
    0x14603250503948080c00b500c071000c0006401160300c204145130160303c55051827109201c291400059541d2034072001d501a1058500711f0407400c0e140400044ca00c603040c00580b080e10b482e80c8c00e86d0750400c4000105c0d40d455681d40d0702260310160340441080007e0040e4040e014480b4103041a0703003000d410a03000c0b00840d408540e10340c0400c0e1900c1151b02a0014103800c41c0c09041440a200c28401d40c0c02c01c0d0140e0008001c0000701880f6894566100d41481d00301c1c0d103081c01000607101c1244604600c2d041c21110031b0000580d01207410408800010b60094114106035250a0702c2242040140d6104441c0000c02a2105051541c00c004c80d41c00d010003802a0502559039400120b81ca80001010111614050b4030601200c1515001031050390408280c0c008601c010404450701c174010f02500b404940200c00000300b211600031480711000c120754020304100d500031001e00d103881e95107800481c03410740e210f02c0c0240000d40400040c06041c0c01849250740048003d8000030f0100d44506440f0b1500c9854441 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 189409739 1250 189408489 189408493
    0x60f0308030603101109010e12030a1101050f07050715060905040b070f0503091e070902030f19060e070302070f060e01020d1d0618011112040516050603130611070302 73
    0x10000281000c000440b121908800701708800c02d50040176a2a60103682d2100303042064820071041030381c0d10740c49840500c030900400d0341e03640d400d80003010b0b14040c0741308040c2e00c8a508103000508a0100404258440c10090300c415281c03070810303550000030b034148081040d0601e56070100414214183e11075188200d1042c40142d543d81052103026020546021440c820400200200441088042045000803001c602c045c2c0101c10390b10f607800c2c2440c0c2582c0041021510100400284400420030030f4000c0903080d86603641d09164074080415500f444c0039a0321200149008189100e1081c0c0c01881694021107028600710907565070760003900c03d60f2200c0b100503900483d00340c0c10038110b4480da88210080c144451000315510001c0d546920004200002031440f034044404002d000713410400ea0342401c4440c06654404000d4900e80300b61041c0c905031424032070702441d03e4404000d880e0714800e5400050100341540d96503021903945002241080390f1868894540c54445241c540180c29694401c0e00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 189410989 1250 189409739 189409741
    0xf0d050403020f0d020a090e0712060926120c0705010903080601030c0305090a030c051c0320072015040b03010e161b020d0212070302041b0e06070501060f030803 71
    0x10043c107952803140840c442d00c10140f40c600181c1e01c4090349403c403020a80003140010074014124140001c0780c0c000e03400b0b031228081480c204070190f44100a0b0b54400d0032214814000b140d2a00700c4e280600003440c4054208020040780c0c0c09441030056400200e1620759454060150b4a04c3c0c25641400000c401044e046000e0013090341c0c240c000d0280c12034041c507082100c0e10b46080819074030112060050144052001e241e410310000340714040c40c08080700e0064082541c94400140100529006051201600500c82081d9080c103800c685140d03130000b01200190300105480c0d020070101140155210003a00c080309030026091018000401442e48a03907200d615110000803c0b0b0f00081607218403483c2194260b002d150005101c810303140729224148425507a601c08240703015486507020354061a4107080488124000a901c02600c6c400d07281400000c00b02451000e00620017894100400c0c0320f01e1903d0351034207299010305203640c055000407070110755500e2140c1050225400c1601c1202c0000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 189412239 1250 189410989 189410993
    0x20d12080a050604090206070f030203040e04050303010609170631030306080106050102010227010c0c0909061103090c0d052803020f0a0c050105030a1b05090307050a03030801060c050f0d050403 85
    0x2c424503038010000e07a07050010388040d6000460b103101d04140140301c0210004610700b41882002614080d207486140ca920500f09400c04a589800034824180003400c02c4801242d04800070498008000822000340b515480e03806c1040700701e1080c2e40c24485c41600a514600500541d0144810b685009441c002035403030904240600795061340c0c002174150380c0100018010043c03030401900b8041414004001c0701200f0100483d040c651502c030241c002c080800012903080781c5580400c0c1024450b0204100800310384039005240e00045442c0d65041c1c008046104c02d5003072050030012005d202d403041d10800f40c10344200940596040c000c00400c009002002000c0617010440748420510510003844c3d503a0103580c40042c00403150103900e041110120124045070314a4100550540c10350132414074049001400500c1d0760003e441d0f480c880d1190344d00019243c24540c640700e00707880d0190340303d00450b828144251041e84452800700c038180310744040042105001c1c00b41118554050742c1e00c6540714914 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 189413489 1250 189412239 189412241
    0xc060d090b0f09030406050309030903011e050708090d0f030e030d0e0f0f12090d05010504060f06090614010813140c010906020f06160507150212090a0519020d12080a 73
    0x1c1c2a00c420302c5510050004000b0004242d03070444800b071504a94903910314864600310f000d0701801c035425600b13000110403031025241030700e603008401e010700700040d955200040310142c0301501c40b00030303a80000740015405880382c0490b08808549060201d0300d5a66640900e00e10740c0801108040c1c681d5907250001c8488042c01215030402c199801010030f100201a581e4a855149076070491004000822141c1601c030091691080c0d42c100c4000c0009252900344007000d40980312003907035001d1611602103600300c02c602c80e0b5400d440e01074091014010b540c00c010f44030800082c0181c10003800000072800003980401281006890030000742958015110000d864480785070031280035074200d13124404c00400005902d5510400d01d020254120220000942d40c512840714090031903030000c40b8042c0c0b00ca00c207400800c0b211101809a01300303076440c002110b4a0708010700c4020b060303800c02d691445200b08406800e084142c0010300da070111001e903a843d455071418041c501d4001c0b8440c2400c1000c0300100d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 189414739 1250 189413489 189413491
    0x1214011202030d0f020d030b0d0803091509010c0c020904030e03190203060601051603081f080a020310050403020a03140d06060f0206010602070b04030305031812130906060c02120c060d090b 83
    0x300c1c10700c82c90326240c4c0e91000c0d440d190f001258a08240e84c5544818841d41c624131000d078450740007100e5a83e2405d01c440c209413940382419280d003a40e501c40740130401c5d6440520403c45100c1e400e03500d403560444035508200012a028000394104080c2c402c4080c91070b0303001d1003050141141a01e001200d13040f40d1040c5801c01e04000c0203c2c0c1480b80074006813581404504010500c29814035040d040c569803021141407815003024440043c0302040d1001c203ea040004d2407844141c0220112804400200328035020b4950444000b401030308070b80304140000c0d004040d1082d009600c2b088003401c10350715002030740480780d0b00d51040f0006449100d29807900d607014041540076020902c05480705506002c0414424071840c40b004081060000001d003040c2e040791103504000c44400292a80d141150040814a4000304400d0742c03840400c0d40002404145480342d042181c440780c036100c0342c10344c141d020001d44154170300c02011b4501680055032030560b80c3d040107000c1a100e12000140350307030b01c50038490a1660 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 189415989 1250 189414739 189414763
    0x315050f0703021b010c030923070501180503030708040501030f11040b0f070b1003020114040515070201031824050408030c0a020f03030112030e0103020702010c03121401120203 78
    0x22a04040c400c034080d00400c41540000740d401c000da6100301800c04518400390b40a0281140c1d4a020109101951f041e00315903411401400c0a03c00c0b110661807056104204800400c1c031940081010091540a9140313007059460408401c00c1d01e541e2040401e003154007450003141c440c400010148002d40e090301c528003076902400c408004880440c42c80000920490240d000c1d40803000c01c0c00b4940320b91450860300b40550200800820742800303a5801c41415060008038085661f0207510411810040241e804850300102072860241130701d01c0c0b15441d540100000c0c0d04150300c80922a45002e00c030141200000d03c100c4111304102c0345160441c003034181ea04801b9120f1030906082c80b02217034419040d0390b00b20644042c7c0c240d566114037826450100010114244d6010200001845514035006850a1030294564180c561034600c01141240715002c00280440c40054442d170103e07100304009000c07001001d400250f010744070251030344a500240d00148101040c03284501c1103003018001610020 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 189417239 1250 189415989 189415991
    0x3090105071e0801140d06020403060b210a0206090a0305031c0c0509010804020f030a0b070206060f040e030d0c1101020c0102090301140615030a020906030717070e0315090c06040b040315 82
    0x4a00402c0104280c406100301115410050030250301950358100c00b1a01590110f41195215568984040a00380255a9902c10703000790407601800711103410600079100860003d00782c240c0c0030341d0030000c258110300c0d80aa0020300302c83c0d022000520130002054292080c0c0180d039205856a1031030070903515140342c85410808140800308490b40c0180780260080d90446030260755500c05d202003440c0c540a81d0014220480103424454042e03004940c003802010b06907030f04d1100c99100c07001d0000b80c4004101440d001d078402c1001032030000d06075100c00313034000551908201704000c9008240c01d980101300101c8540c1d600013220282c0745024401d0f81d43c2c8001100640c041441c05c4000103c1502c0401c80181000e4400400078001d0800c0d54122584100b0042003c1d032241400c5000a240519180d54444081002030104800314026001c009103008010000e003036030174072003400e42c1a0039405410b0403201d1050041c0c0c9041680c4a00182014104070402c450b00c903441c43c103040d242003840e070900d035040e1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 189418489 1250 189417239 189417287
    0x3370303090b152e121103040b0f090c0a0302040e010902150d060e06010503060d03020115030c1502151609050904030314070e060a051812100b060f04031202030705030309010507 78
    0xb1200406010018080e90405d0081d40507000303591030260603506210380c0426000000c000401c0600d07900a07001d040c400507015020782d00c007895030365200c1100500d141d0001c96181c08000614050700700d880500700200c00858080182c0d404602003904540c0e410b851910301250a140c1989184600402030072100740c446614200180041c059205c00b130200e501604038a444401814000d400042051200c480c09403100c136981d0801290382c00490040104010944179030620305480040c1c6007500301c0f00c0c0000440c694130390b8006020061400b40c5807501348007410000050350394619511911550080d2004642d46142c00403181c5c1c02030307000b44480c0034050340c040240d0703460b01c40b20181d900e035610900304503a0394188648083d0000340642c1c07126070300036504041100403440205400d81c2110803104180302d03032071141007045050b003e00641800086d02c2448100007140c00030b684003101e0429070040c1c0f807a0403102e4580704d08507402154400300c944c0d154014011000da12502030b2000380f9142c0000020 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 189419739 1250 189418489 189418549
    0x61508060105030d03140403051303080c010b040c051905090a080609030d05060d11130b130b01180509060d0809060706020c06060603270304050d0c0503370303090b15 73
    0x108806c003510113000c02802080c02c88030801d02104c144080c41e000b03030740300751960848000c040c060240ca580c000c0c082c1c3d007452402c80b2110b02450075606841081908400700e80c0301030030111890741142c8070f241e0340220f0307403280043c20b9082072168601071f0003040055a59540f240d82040c043c0c400142225019090080c16800403031112401c41c0a041002c8414885d04c0e000c52060102600c00641c00310341c443d9241c481c05c1c0c0000c50940c0400d100000030303200c0f0510b50302e4070f4243c40c201e20654401c49070002c2c00d01002480710320f4400100340c4800e200340c030091304001181020482036000201c0441d880c5070f000403c005065404c000032035015008403956403852401900b4241c03020100c9280c080c400013030008000b603042e024800c1d100034000290a901c86400c0c42e0402d5980c1041e6032007100e000340100b81c092000c004410480e10b2190682b04000e40890380191842c01c0340d81c003100416420140ea4514010000d60040002d5000d03810603450340c0d040912a400308000e000100015413804a080d91a030a4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 189420989 1250 189419739 189419771
    0x3f18141203011401090e0c07050601090e0a0204092a08060a0b010c0b06030c030321010f150807180e0621061b19050a09120519061508060105030d03 65
    0x20540b42c01040b08040c620402e00145d41950340c5401c0040302410860400c541c004c00035000d4861580240102e4200c0d903625080c0c001101c1100d41d80c04010740040c030040d809070405410100a052060f50f107044010840c2502c01c0408880103240310702200710200812030f1301c00c20801140c00142081c0d003004110190400030f44514030f032034401030092402d0030000303900d50b07001c0c05800008800a02900d50702c9070fa2500c401105130a1500003820008400d0002c158a25500c80394429580e28410f4002d0640d14690161900f0034003c10300f204006103400c9800360050003280400040248400d4124641082d80070004170302e6000e036404030140209000c62241c14000500d2a0b00014001514440d034074810629254038460b03141060361b11819011180030a5911a004001044660303413201c0070161240c03070306081c25000c034030090502d45c04181155a45040c2502c6100128458000000d0400700c0d50722100620405902c140480e4000b58010032050a086c0840400c0c080140b504201c00100b141c4032075 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 189422239 1250 189420989 189420991
    0x20c060307030b0f09070e10030501030f020603041b030312060501050307080114150c03030603010b06031003150902040e100c11061308090a0807080d3f18141203 71
    0x1c08064842c0c00c452071544401ca8900300004001d06113080c0c9103007052001d0489510040000e02540007100d551011a20a103c0c26059980c400601e180c82d0f81070341c0070000c054001500903603d03000403658410503111582c5414000b144291105038803461003a0380d00b0111201640b04905202040041004050b071000540e070550350f0f022100c114028242d40807880f038981900c00340408030400112292000030010185100e107000f14000e00412041c401807081a000c140c8070b00c88420090002400042d04140f0610781c100c00c80500012030241e0f42c0c0000d4180c842201241d02c2c20f801020014034011342c03900443e200f02809092040d900d111040e4401c0d07451100500420007203a806502d403080104950441d40e40d0540200b254030140d03210f012098840419201c2d44107940f007000c018801241c06401103221003000799113032003188081ca000c0040d00c000c0c0486002046001c0e90035401c13100300c032031044d0081200d41412000c00d500c0c4603d40110403210b03216a050a40c2c0c40004070500800c1c0d10b008132 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 189423489 1250 189422239 189422251
    0xb1e060f010f050906040b030a0e0102040303050a0309020d0f0f0c080d09030609020303040e18060112020105030f0907090213050f04060e01270c0c021e100c050307120807020706020c0603 82
    0x24442000b00c20380704032a03034011490140d9000500180029640c0541c001079800707040003e80401401a685503418200e10682c0b1000300425010301c08056004c2c040d038001d9002d180094003030042c0300701581e21307040c4032092242c0483d0608440419501440380c140309a0001e096400014114041c43d400003910107038251200030055a01c4090b21011900c00b4800d80d0000c208110784440542455040c440d404440c00b45650004d1181c48000100c0c08a880382c419039036501a15958559180c02880903200070008140c01e425105800b0f000170062071a10080043e032200302c01d0742010608003001c00c1061a15500303410710880c2000c0c014452100305041290454070001d04c0c10900e5580103041406098074480c1401b07545240c00460500e464000845003036013031007107850b6012004200e54140785080d9605010360080b029080d000d081e280162584103449000c0c1c804c030384c2000d185544202d00c1107040300420002407120300a00103001d80400001c00a8a08d60001c1c100d61480500856443c0c0801010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 189424739 1250 189423489 189423497
    0x60509010b070c12080a0813030512090307120f0e0f18091c210510090b0111060901060f08031215010e1c1401180204150e01030b1e060f01 61
    0x40102006402a0401d008213aa0310100141c001181402c00254000300f1150011480705030000303507442d44943c1091442c65044d00c560342800f291a951400b0020b00915521542c0301c10441c02c2d010503592901d541034003200c0d80d02d000a184200000408000402d001c45000d9100b410070185503550300c2c84103608070080020580070a5403648007043c0341020319008003151040d1845641502c0340d0102c000c90400b00e0302c0824020580c8603410764011a6400c0310601d0708203150303920510000500d42c000340300c41c0d01c0516200d21400b1520350031034181038007510044110380d034808081103034080c1060000b0080032070001860900c12248400c002201e002490000071000700889604140c0c007840c0802848007018001c91610200007000401c4e2048403507003552001032510000024401c140101c40b614581030701c00540f4440a6402c1c40007400201d00e0745080c0c1c01804001141610107261414000c0d40205001c4000f42800c2c100b10804105814840162030b0783c510400809498000418401503820304e4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 189425989 1250 189424739 189424747
    0x304020102010b0604240503160c030e040f09020a050904030207030605070216080c0316080a02060904020702040c02070608060a03020d020f030a0501020409020703030b03030406090b1308010c1110060509010b 91
    0x80100d004207009004a544150049004602010200000754013045100103070182e01c403001c00181c51030f000403078a0103821000d41400c0b0012600c0f810203100c4562180c240014106401350002d001c1d10ba80c7c41100710140d0f500c800c0801589084449400105000c1d6400e82c450b06250310025140e1480b40400340c1a244c031100402c030014420050901a10261640d00030465150101b041c0c441d800e001055101e4800c180104c40324103041114641141c11388002040200881c0d828442107811451005521607400c1c0440005030f1030700e014403001a130042d03025208282c08c282015100000143c42d680c000c600458052006803100860120303401e404884a088003a01040000e141c000c2e0201d009240f54000702c2d001691946a402a0088a2013520305000340c81000d01416501d020714841c040c0017419885041101c01b60103401044c10892800040c540705842d0610142980e440c001c18030002800c5603404030381c8200a024085011031009003e00042c0c1c940000100f40c0385040c0131390400900001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 189427239 1250 189425989 189425993
    0x10f060e0d08070f080c160521160807061407050a061814011d0615040b030a06022106041505040c090302090f0708010605030907151116080c0102010c080a020304 71
    0xb0302520030580e4010031280702e11406144c01c04a60b002001600b0f01485400c1e4260700c1a091103003001c081d1000504400c09401340c1d101807400d40024800c0d100418001c1c4107003004104a0304500f4006040014000d08209142c80c00c000c0110740d482a41441c207031010303c605400030300045002080d4a821200205070584040090000c61200e001c00902030032400b0b12b0400e04110640116894181030034a54141a5411003659150103040300c20480410940754905041e1800c2e91000ca901c0101804440c28512541c2d0703603c0481c2c0c410780d80c100c000046805402c0d1000ca580d18081d5001000380d4090210300a03101c3c0060040c40306014041c8103035140c40d10100c5880c4601503580003950024a810014182400d0242602c041034400100050141001192141c001d1049a01a20020000384002c0f45800c910901c041c4181c40c14504101c8402810700010000b0481140d140701032072100060319150000303051908003402405415a4101155805e0b0355411107407040d8001000c1754003590b00c0e55a4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 189428489 1250 189427239 189427253
    0xb1b07201f0f031a0d0c030c030b010509060103020f030a0b1c03170603060f0c0c120a0503190c0e01030902040204030c030302031909050a0b18030601120b010f060e0d 73
    0x4014403580101d00708210a8080500d2581c00d88000d20782c0c0c41e21040e04552250840540310f44c22502c00303000c03d507200c0d0560389042110041802500401400140c0381d10b990742c1110b64030440c2d00035140c05040000601c05031411000454000358242021840d02c2285842c2089500004000008c003560768030030225251144450402c0c02601210315585804903072070060220741481010601d100c501d500017400030b0400044003801105006003101143e9504046540f00b80d214095012a43c0540c40408002e40b10100c0a4450501f59855141d101d1501240080111442592404101c2d00384889200c20580165000700c0207082071070045078000030350012602138442d6500091448048000002c14142d001c00a040e10b00e040c6800b805e00c40c008400c00310750010131742c02500e0f8004032100003044040c040e88014410084d0110904046081d03608c00242020000d9000d07001c010b141c100c2c4842040110b8103100d000d0002c00c0741d020100c608150303000b001c03480401840c50242054401c1a0240580 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 189429739 1250 189428489 189428543
    0x71209020415080601050a1d0a0e0715080a1103070f0201021303030521010303051215030703080d11030f01030204090212030703090302040b040b01080703021b03070f0b1b07 76
    0xe007007440402e03008812944030685070301c03d0100314040c00e000406c01c3e1808a0008089408080b102d1080721500402922030140c05400ca074640d641d11090103000c5901800248000d2070400e480d0158003281c000c0161441c02d0003040e94038820718103400303061000c6004060b40e800c281a85800c0a80c80310f1884243c4c02846080c400d1141c07814030013800010980e001009010f0f8042c416040e07456610b114160800f513040070b02005011402c182f0803001000321082906521483c0c1c0440d880344d42c182480032a081100581040c2e80000c000102c5007503408050082080b404281010280740d031400b406100182c0d581070000a2080c2d456000c0b5201b0765403019051652000c001c41500d540d801a07150242940b1a10300c4202e02480c00c060748405103140c503209110080c44180c40e6019259520035045000b544100e00300d405080c0549950801c00c0700800c040e0640e40d02c146202145281d140c01c01c021400301c0240300d51690b02090740495000d20b00c002c1501d40c1107901c49005404482444172048030415 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 189430989 1250 189429739 189429743
    0x110a0c150c0c09050709060207030323070b040510180c1a0c0312060406050103020304020108180708030f09040e12070314040e091e1209150421050d020304030b071209 73
    0x30031102c04100300354254020b5015090039224400000d59807841070f600c8100a200c05000b0980400c0d03149640007400d00c0c0c803503801c8041000286810295500c48801d1103042d101552558090801d490f02c10802d44500306070070450f0081d030051882c1550b41c40594201600a068000740150702038a210701c6aa8103403261410843c06417512a170b04903200e10150342080300c48620607814540001b1b0254040e02c00c4902842e01a51035008650319000308110118925689041c58070414100085418040c0080e000d05600507102d02c0e80c0f040681c003040103440c800320889850b904003104680d5560026801c9842a540c5800c0500030400c030030a10b0031481c0141c0c2d02840c009110041003100b0060045440031903800b66805486902101c58130080e40d41d5410800c10178004020444841c1915100100c031003002c1e151903446103482c6c0c803105103104949220302410108004001000e0810000380000308409000e44002c504281c50340d01d5141160001070030381020300ca00141c3c1d00d1441200c070742104000316 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 189432239 1250 189430989 189431003
    0xd02060d180b040317010b030a02030601021f0b15040501020a20150c010e0d08060609360901090503030a0c03200c0106060c081e0d050c0a110a0c150c 66
    0x1071402d05140c0095002180e080f4005200000020005038403091742e541a1150b8450207400c554500910000035480505028150b1140700c0c4280245601741c0c7e0782c06020f0041000c08144150040c1c28000d8069042642c07901448041c00b081c0040d903400a00d01d400c050700440c40c180401c3c0d107101c40841803400d9074003117500410743c003407460380f85c0f114003000b403804c00c5162008100948001000f01e44070184054600c000130719903004607140c1c1c94a0400341c415040020216865406c1c0d08000c8108041c06241d80d800b1600040c3d80107811100c4881455804a4624028000f4031810f544e0356499100007040708504a0f40d4800b24004284694005846120000c40e01c555008201c01e0701c1d007081d0004012255250300300323040801c42038402c18603a141035500403181820030003c000d44100348514803c00e900b81407401e006c50102c8130a1030140794003820ba20300790340c0d81d107a0f000c8400501d040440d0502c41b00952240e05004006100750490400b2603800002c3c403421500e0880f405c9425544000018040d1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 189433489 1250 189432239 189432281
    0x18090c0c01150302090a0e0c010509130e0703060e19170405030d030b0a05040b01120207051504030e090601030605010c0f020105190801080f0d080a0b03030f04030501020a03050a06050d02060d 84
    0x650700c03005042c000d99008440588403903640c00e42042c04c2c3c0d9400480015150010ba000007450f50040c005400d4669000b000b40501c0540b012401044400e4103078800c620358002030080042c00410f01c074460b102d50002000d48110943c04180e016962500c1400600c2d011000400300300c80310307546040c2e50103460001c007910544a100d0800a0103404c8140c0820311542000030000f61038503044c42060611001a15282c0c01141690707091002900b0554096403d4020301c0030040300d182da8110b0b51071040388651144201d582d20281445100400107204174141441c0100a01080ea00480104802540000c0804086142d84012581c070b00851012000080079039038400b054a8004003141c0c161020141140c4031100f800c200b41355918840003410011985090104001c40c1c00703500070102c3c464001e401c130307450b1000d4550700006a170301547c02555680d50100d0441d90b1a0350600801c0c1d04029111000d0008030308220002d07103107550944000740b20349e0700051115090002c581100241105000303140e409 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 189434739 1250 189433489 189433511
    0x90403020d080906060d03080a090b090a120e06190c053922090c0e010e2419030807080310060206040503030412020a061104090c02010218090c0c01 65
    0x81c41a0380c1d44140c01003a0148000352540c0000a880c501c515001061514039070003e440030781d4074040140444584985495810001c01d41e1200070303e01807241c00740144211111400c241b01019008810142007040140140c2030303c0c0d44140a461001d05078403a100723440c05032000306486000400710020818042d4010320414920300031002041150780c0d14403c0c581d40344542c40b020b0900d46501c982c643c06100c0c1c0e0b020703401084220040301c80d40c264030f820001e400d2050b520b07008400f285aa214480ba1441180180704c08101800c9a54101e65043d1502080001140c1180d202010440303c850040800c520b80460000500190710011341e04001a40c1e95242141480d8030306130b00880e403640100e032030030400040c0c0501c000ba0580c0308541007005103007507440d281ea40115030005140190110301c21a092500402d20a204801118070284181690345241801280555a640d0764071000e5920502c00c14180d0b1f44940003920300e650007210307807103070503030310b035031148a1500802200f040d0715071030b014401d06 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 189435989 1250 189434739 189434743
    0xf0921040501021207081b100608060403090905070e060307120912020105070906050405040f0603060e0a021e0307090b0a08070e060a0515070204050a11070c181b080405070509040302 80
    0x100781c650070380c25291805508140d030301c16172085070b81c014240d032010046030040c0b505500b40349210f400c0540542d20b920200b5801c40c0242c98258200c0c030802c2d00110240003c06400c4180040180030148040c8118a841e03031015002e080c180300c1142c0160400400039600ca40308028104080010040400400030617081c255840c50280040001562a220100741c0f00d9000300c0016044410765611a442c080c00c00c0140806800c40880c2103210320344960700400054160b00603114400c21080082562400e41e00400110b4824000ca0f03000e00c42c02c09461040a07100801c84500340d500c0102c0c0411506000d001040c44051691b11110fa0b900901b100130030f09142001c401c41c00740034100c03210303400e1a40b1802004949442c80401d00b510b6a8104980801801c00341c109607407007640240001804840101d071007002d07a202d40401c4a00e50344009050200031501540e041252610f110100f00000072000d840351b14911000f51141446500d00010301007040400c11300000d81400303800f0407514105403a01075 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 189437239 1250 189435989 189435997
    0x20d2012070507080304080307150b040c0804020a060302090303070b060a0e07020a030212030709060f02250501020f06040b01050918030a0e01020c04090510020d14070c120809060f0921 81
    0xd42d140503011001030007000000c01d0340c0c2928440409075242c00c01580c0d4818844106600990b40103031150281c851580d0340e482140100502c0b6141c10040b86072034410001404443c0d00070720245407050001c100252000000e60f160386502000e41d90280e00c4100010b00021060340c407280c801c2c1c009400700007215601013044240c0d10321030303001c0f0390701980e103c9200f12450104490280c0001d070f444204100a43c410907041c0c443c15035500603201030400ad42141022581c0004e020580800014003c10455030b0400044504101000c00f500c050300b0aa40c0f295000da10610074a4400c40c03441c000b0500b005181c0003100b01440715501143d5407030501c5000540314000c04000c50740540103140c007444040c1418018604116400303c094198004010718800081d00860303131074844607684500b19840d0381340324000280518059155000700852070701d454458498201d00030030420080e90b0a002018400080054204400000b01c5140703030764200d0302038034004014041e40c0d07800200d40c1d144426019000010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 189438489 1250 189437239 189437243
    0x2c040807020a0906030b0c03040615030305040816030804140109170c01030b0130061706090d090b091c0602210c0c0c040507021f14130201020d201207 66
    0x20114075541c8030350b820b041300c201d0703c40a800b1040840000354030201e00001540c0c014031070b020004102c0302030200820201056002180842c0e4005014454404100150078400400025600240341103a481003001e000300d1240120a043c03140310f400c041c0c2c2c050f54190002c5e00d2902c9680304d005208a524950301c2c421040c080d40442d20b0f00c41003004652142c80c0d10402c840b0000180e904070300c89070201511042050300e407002400c5d0303140404075219600e820311400311072700d441c002c002e14146609a24200155940b03068140038814200700281110401552240d000841c0d66241009815203100d20b10005000010209840080c42d40402d200da80e504a2550700f00003000c030f01603507501446015a216072010343c440d40d030000300c8290242c6415001240c1c0006140306556002a002413103600500d403d40503090855115001e0480e0400d00711501d561214581d0501c030034242042e00080e441e0005800c84104001201c0084407803000d0803c1e03000c41d07542da2202114031005000d65018240d41000b601 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 189439739 1250 189438489 189438499
    0x3060708061e030c130b0a0f0e010918030503040305040909050f0606040c02031b030424030c0302070308060f0a0b030106210b092a0f071b030c2c04080702 68
    0x605081044030841c40d018250b0180080c262403041d04100607004c411002c1c03c0445e01d46916550407982c891442040080010b80110088e081c00c0120414100d08160001d5000e103141c149801d1004c15001580c540340c50b01410301d95680c3c3c4490404603030521458000700e50f15410102540c3c1040740c001a00620704501e0420b40d1201d03118901040203480c8109140310042e4020b000c4021502048c3c60f411101100f4801140d1410303541e9450400c82c0d42e984404031000165101c80c54a6143e0140070340440901c5525045241c041e255401401800c0050481401104580c11108660325500c0008001e880c101355465104d694501c002400442d0b039400c40c49111058807689040001c16001304030003444010040b0b070007651110041710807000d900d12003840d0b4140000c49400038007050ba00400701700b6880a4100e41d2411581420074030101c180750008100f8001352401c1020940403a9a002aa004004040700d60001c111081c3d001c900308c0d074012880f080403202480200000d860090080070b2003550 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 189440989 1250 189439739 189439759
    0x3030b010305071e0c05100204030b0f070906030b0d0f1506050409020906090705070813050a06110601060e03010e10050708010b0717030705120712060b2809050306070806 75
    0x440c180c5109440d040003150b2040f6041c950b4004d14103590b032012081c3c0c64a241c0ea1107142c2c40f42440e01c2c00b4040d0000c0001d07130010b014010321901c00340c071591000b000c0481d06601d00704514020310710703d414810034007010b61310714100e0150307607491100300002500300840d21411049414400005000c2c402034001c51868000006054105030040c0784102d9001000b45601b565074100b1301c80d61020080c48101000010400750f070005071008058080c2a0340c099085284e0340c1802d040c00701c0400a60800c0701031001c0812404982200095103605441c018900302103040d10080c08240036103a0100031249034001d140d09207016002c1940918071440b0306036103950007a40d072903007190360302d00c140c2801601960000244e82c40e032000650055400100c1c61514500c1d040381c481c0741014041041e24803000250030345d47c9420505401e402042c01804a0b0008a89004030b10008100c801050800c80358040344914090403655004605c4030b4014440640ae030366991809010060001070119805031003209512 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 189442239 1250 189440989 189441011
    0x20f0c1203041203090b030a0e010606140304030f021905010209090a02040303090b2b020702040b03010c0903110a08010203092803140705070906060c0b0f090307020d1a0c070303 78
    0x200c1100d80d044010010310302d41030514501143c1620150015018011480d00029a18000e980294480d2103240d00c00a41110310b0b005590a407442d9a00c88030400c0740251019440c3c8118200312600540d06081064110392081c00a030b00b0041e0b6444c0344503032004904012024400c06400500d03d003501281e4075400b41c0c1d10311031a0401c81c000c0b400041c00140c1182d00900055188070001e11826680c9a04500007000d54400e0700c101e10000487e1307842c06600030804c1011400d00d8080c04035600c50490080c00f200160f03280c014801c4149120140ca01034418410101d00c0d154604201c029100c0a0002c0d5070b01d11b4801c1065503038144101c4c41c080320024010001d401a1103d85082c80013583c15a56002e2000040249000541144a080e1802d000b03080000440e007845109800060080d0386444020b803a4a040c11503411400420000004000b00d082041c50300c4048125048a58111000f20202416041c10311001800301c084000ac002600e0500c00e00c1070040e000382c41924800c1c0c0d400e2100081071 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 189443489 1250 189442239 189442249
    0x50a020f03040b040e090f1006031b05301e0709061a030a1e0b12010203130b1e070905130213061119080403060b03030f0703120912020f0c 61
    0x14403540380c00c0d0300240014040d0000c03454406030041d550500320341407003c4000f081800c08008d5500700d080329641390010005c102c10f4804d02c0305000c8007459000a014940408241c0742d4140240c4410100c4000740324071600603201381c21407010384c0a4001c840e0140a51304c4440d5081c03c490f6640d0102d4801e00c3c0e80010084030364056101606d0028008c00b2441505101507a580d42000d071201010f80c1d21b48851404100d8210f02d00c66043d090580c0200d0721841d00000c2c400007810f40f00b032710403440c2d00403c00c0000a01e031007100d0842480e804a51540103a0340d48080700d24641100a8005006a00000f40240194000c56607000d450301140c10010100a118070b42040384034031340000507155008001004014011982d40180043c030303100707480c034500040140608603981007200301c0e4021070104060081c02414072030314010340c400780c0085141104c030384014550740c01340303440050401501c0980c1400f0403a40350492165982d019003052030b1a0f600c010003a440e5202400c40d040c00f8868100c50900300e1401c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 189444739 1250 189443489 189443497
    0x30506010515123408090a08030c09150a050301060e0f1f031e0207110a050d0b06030a0b0103120e09060d0f1703070c0506010501021609020307030f020307050a020f03 73
    0x198078910329183c0d240003500c6007981c00070303d0b071350f03036040b51145600c0e8a02c141d00e180c20744101840f150031014542c0a00250000602821030021036201089040005501004072174022241850142e15040e0600010305007d50802c0d40345080540454445944e541100c0034506980003604c8400c10704840f10706200b1148003c0000c91750119891100350203803480c01845c1411a140c074580850038401c0c1103e1141001c1118100c12044c503400254407051104072010100d030364074200c0728042041c0c50a40011401310401d40d01502c09118030010800c1075908000300c11a13546d10154a0003150303901d0070482c201110003000c45000c80d48034a2462050b140210b0803903c0f03418001d01000e02c050391030b11210807114290100f12009078600c0c020302801c000e55005980300d0521a41d0300440e0001a00c1c105090580680c0118107641c01790390540e031107140500c5120300740c3c0c4030034500503120340e41c0a03c11000b0780480529041c980340700106010107542e1040050140b161030f50201d65411340302008156076445 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 189445989 1250 189444739 189444769
    0x80a110304110312031f080703030801180902031506040f0603151d0106080d140c03030103030521190b0d02030606100c050d030204240e090901061703040305060105 72
    0x25040000400241810700b4181da81e8501404940040b4040f08204080e607000b070752421905980d00d00c0103100c010180c84424080c19140002e00032551441d90040d01c01d42060146408040312801210340c10b8603154407814003a60000d0403290524203030b5180d161078880640e51a4001c40c2801e0050012160a01510003100d42c8600640e0512808401060003010b1800600087c81030004a001040d0340c00d0041602900c00d02000e0507494020030340203081500c1c01062181c29500c2449502203155022041c0c80c1100e4042c246244c1c2e0700e191040010144072802030b001c4201a64030709000441d03e9064810010505400c410810b01c1c03100c408001c0da01c81001c01c02903041c0c4c80000042d91324100806101c510044034103004890242560791542000002c00744240003035404501007002c144807a900d242600c008065480c02542c4100740202401001080b0b14003e0007400f0110300000425403142009001c00c0c400004440e1821201d1520390780244002c1d506449814000301d000d00d00413404050442d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 189447239 1250 189445989 189446021
    0x50705070510050613060b19090614130b0c060403020c0109080c0d140708010b0406050a06051614190c05030105130b090a0b090a02030f071a0313080a02060106080a 72
    0xc2c003944546405004000c181075089158580701266004184c003a55014180960602d6102c00201026105102d80385140208002c0088020000150400c088200746208410700640e50078400b480700c002201d156118507801480012002c4040401240706405240300b942541c1c0c40b441c0da1401190312044502400c40e894101c0a1241114035000104000481c0b05000080800e00303c920dc41e400d0494541c84a14140d440706440c28151425204060141200311801c2203001d0611000401c04c2c0184000341403440301d2002c4480a102d0440d01c3d5040c1880200120f41da040c61300841d030620040c61013000ca504800868000c20a45418007400344a03525205600c2c248040e03039115101c07240f0019000d204c580c050340c2c880c403010502240580c2c0c400e06040c801002c50450910500d4546010705110132660f0300810b00c140140569551071070b408642e20f0440d103859884034007121031500d1100000411841d0006002809142c020411074126159505c4d070b00d085642e141c0710030040c3c6005908500c020 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 189448489 1250 189447239 189447253
    0x6050901212a0e0907090e0709020a080714041202062110090e12160807020907050301080c0901051c02180906070801080a020d0204050c0d060b040807090e030706051b040e0a0507050705 81
    0x1c103c50307488620709440385801c03180038590b140b040d1812072f44803a08034000144040c00b004401d3750044110f40700e0500040b1a00d191900d0100500e0360f106072018028441d4400060801156030511134952a041c0d0020f0510501d0402460211030940c4c10701c20000150708054614020400205a0700e41d281703030200180c0c0c40c10680451a141c8650182c000311051003040c0701c50005030700d900c030045210740103540b2a95501c0d410044040e141070a040c00c26845203181c40d006001075114070418a40540460604008080081c40090619440d41a480c1c00c40e08011f0100010f00c02c0000d11107002d03c0c480e40350303c0010303600c81d0071b4a0b488100300e884c00303500081c0c0703007801d0401402d060740b10942c403c0aa04a040c28003005514600982c0c2403507114402d400b4010506101c00c0c031091080034020140600d0401000d03084071b48560b140d0140031406840b1550380c600050280718401d4100c89011a458061584e0301e17201c1c40005c001c0b100a07035001d003210b46810005440940228111607815030003000800003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 189449739 1250 189448489 189448499
    0x15030f03140d02030c03062b03140d050421020708061f050306071112090904151e05072015060f060c031206010306050901212a0e0907 59
    0x1940d4007110300d0401c0303403108120040072a8070a1001d14002c04045e05c025a032820304008001d00800038000030301a10300c802e2020100c050031190003200196040c00c0050a403203c070040c0406900800c4c1c0403e180da800d0408200c01c00c481a245540310091054442840300740341d0000300d80c1c400d494040c1000366171062021600500f0711002286064181304441c80a1350303191400b00c0e090003c180d0b030900206441035295606104140502450400d00101d0f480c28103ca00c0005800140060000303050314511200700b5200000c15081408003451388208616607040904451000b0642200e084e00000c00c4001404e0302480c1c0c5414207442c900300f000042c09003034021110710741e2980001e003519900078031400b0120000c1c4c840b04007038180c000c40c41000d1a291070075920446206680208114101440c02030700740655a110346245056850070070a025070800b912540d14141118100b000d072114032180031a09500d20212407038140c415980d0050204159590f0b58138460315070a41c1c006003550491042802 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 189450989 1250 189449739 189449747
    0x9020906160501230f0106051e07080d06120b09030307120b03010b12070e0c0403030c0807080f1206030c09190b030c1f0f0c050a0b04080d0510080115030f03 69
    0x70300c240104000901c0982451003d100c1c0d021030541282d8025031641000085490114024018012030500e20b1400e1844010b12170100a544055141c2072030211f07404050214410640b4101070301c00504004a94544010f140c403028505170841702d100085000451900020041e0b901800445c2c0b05e011788404c8007610400500a00e0481581640d80c64085800b55035400b164010610040009000c40c5803c0150440020310000c00e44403420004000400000f5840255140d800303410144060703e403011803030464a1407141d62403003d10100c000c1241d2103400d0080604600400d8110f08440da08449081840b480c107004840b10100c0654624800000302c816070041558034500505071580b0010820028101100c148400150071741420407400c60a50803001d5081d00781c0341400d04820462041c0d950541c1d9080d051002818000c090000c0382c10840341c24150703030849040c10001c0c089440c010b4181c0400c8102403040d16015801c10a03044941c00c1c0c52400c400c01e0b00c1c2c10404010041e0200e0320195 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 189452239 1250 189450989 189451027
    0xc260a0c12020d0c03030f030e0105091c050d020c07090509010902130c090b0309030307030b06121b190804030201060906030506220f0605010807090212161808150109020906 76
    0x43d8102c1a089003c500003840407150030065482900d405a20340b603610002000c44001001841642e0715010078404024400250340402580001183d0314991490004907018040c0756002c004207400852040f821510100d213a8041d580342080270091550390290b42d509984004030040e4000c1340d46181c0a0100744180c20610410005c0d0030050b0300d055446a0a141540c0119807607135450304044148102c4651500840a840004031040790800341545059007405001520200c554882c00c2501e140e41030800b402e0702c2003c06080c80e0110b10910414000d410003108841c1180154a460404116282d1a22840c800e40e90000024107090f030300d103051b501101002c5542c401c0c5c3c400c15500e00c84002a20039083c6e0481610814001c00d907549854425440d06040c0d0304030314090760050061400700c1758803e6680d030344401100c800039801c00b085181070300c01b6000400e0803440e000c043e034008128054000790020b0f1040c12078404558982c4c0e141c230f43d08224020542c00c59488181045106400c0340416400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 189453489 1250 189452239 189452243
    0xa0507021504150c020301050a02030606120604060314060a06080d121113082406100e0a0b0a09081b09010312030204080d0906080a0509280c260a0c12 66
    0x103180070b4540112001c0400700000f02000900003003552421030034280035580c4c010111781010760440c1080e01c0088c46a0080700b080d141c0d80d0703500c500019660765854000400640d000385000400e00a28401c2d07a4494004030b41030042c140c00d003a00026609000180015103120940c2c400c00d401680d4903c1c280540070203500d158201c0750501c0362049800d150700d09003000b8840d12008101da0440d003940f0510011030b40c6520303810a640c01c8100300d103035142e0244c045035900d2035141c03106080703800000040b580c0b2070300d4010281001c00824502c414076001000d00c030549155034221810390040c0d01b101c140314140d05d1201c1c0e4110410a00420004151030549815049a424054103151322100028640701402c910742c800100709620070400c0a8000c00c203180c00c80220340c0d0a100c0340c90591b0b909680c2d0300d00890010070f0340b0110000306030b009980d1580103201c5503000d00c040c03d809079030b68600301c070b0080805040e00d1100b00701100d00b07202035400030325800c01692107107000d111546010f058581e91002142c1c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 189454739 1250 189453489 189453529
    0x302030706122703091a0d0908071b05010306051c03080c07080706020304020901060e1f270e060102061b0702011419030b03160e060301091403040302040c050a050702 73
    0x204141903c1e05030402000195100c050402c070721000d040c0244440300c29070207040000d0404031a01e20a846440407501004184a004a22503140c0d18185059100e0322402900c2104c20482d039003086401c10480c2e10842c2cac400d0740d06001864881080081081603441044243c44514188c200028041c480580c4d0020740200b003e030420302c841d281c00d1500e074040070040300c90315800410442189840801e0a026200703508c0d014000b068964080b0350549010110548104980d1303c0c0c8030404c5104081551110800c05c210040e2070160342c600450020590003400c010740910400618154400504103106945030686007030b11400110b80c51903140d10582c01030341000002400c071660914a00c00810b02804400030f1000c0e0040e81040c020304440d1424651403080d0046006204200599184101962900c10100410f2b84442d40000e004109001c0014010002072061503180d01020002d00300f02d034000d640a12220040300401c0319540708101198010a02c1840a1400740c240b1a1401d40c003d6071101d1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 189455989 1250 189454739 189454751
    0x109032f0a0f0f0b01180609020301140f0f04020d0603020f03010212010e040f2a0b2b06050d05030304110f011b030c0510020a02070b03010b03190b041a030c0109030203070612 77
    0x5079841d0b500c100360080da01c1c000080741b14003140d850300c0c8680402405031b081d0442c11541083c90382d41c0441903c1c010503104507040d018200b85a80d8508040c2110b0b131001f0f00840d5200f620749440b2700501050310003a44603c444001034a0507041c18022a00c240f06400d015000e56800c00c10803c413000c00181081d0f0b848010f039040c150000d07540d0b0002e100300d00e03c41c00d541000d00071100f1000041c4440c0303402c4590302800c20701c078500400c04244210405c40130081e00000700d09440040000080525a003d40da01c80c0038003012109200c1c0c01710003540264041e45249102c08002e00c140140705c0c074804a401c0c0012011408100c81c0700107000c0411085100e0b10389040125459101e003454a0600030a21107071300d0303002030240c622603010401c0000a01e1540c41c3c5504540c501040040c0902008050401c5494041250043d4000726440714110000c010403c003c1014070303c98101e0a55034040c000382c040c0c89a0b4203445030311344c003505500c0e0880c0e0340280103003503243c1440d404551503929003088480c0c05450351 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 189457239 1250 189455989 189455993
    0x30215130503010903200d09092a091a0f07080d0b0d060510091a010e011715091f03060b120109050c031c0806041a030109032f0a0f0f 59
    0x20049189141c017070341c0d4036070301c140c0704000c02045200d10f51600c80440d400204140751aa800c030b2115002c6441d001400600b611a1810b010401460300d134911100c0078502c05600360a64100120009a032015180d444401c1300e050541c4015104a4000120360602030101000247e0900000c002e540f41c03031744020828650013804111030804142d021100e145e194804c2264450410410100a1003081350030712400c1c01c164074180341c903945184141c0c10003d04003003c5009901070b103500700030205138005a1490b403404940010341c00f603451520910940c03c441c0800c290f070341c03c02402c510360b05000e08103040036450741d9504002000d90350410b54102e03a06900f00d01c1a42028880c10724054000d101800c14148180c040506024142010540e8108241010b0b440d03654460300307096000d40c05030f40000da1422542441c400c0550300d0944d40e541503081c90901c008040d801580200d150541110905c0141100380050348404003400c000c0d60340d80d20804403070001c920080008812503002d18401013050100e9 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 189458489 1250 189457239 189457241
    0x906021f0f050f06040b030a0c12140703060b040506040209090720030409140f07080412090b03010b07020102010b10050702012303090303160c020a05120c031006030303050c0403021513050301 84
    0x4036140b001a944078010044e490805004200382080102c0290040035141da44490317400829006409004594505400400c000b41e801c00c014402c0c5070b8100c1e460315582e4036021010f4011426001e02440c100408626681054005e0301d1704410020100a11562100822a42528035140f456000c491164001e1040282403000303002424112201062800402200840d06c0801601c0d480e11066030b44100000c55a205905070b40255201361143d54095002c94101c4074285280c0010200303550001c0002044441d10004040040c400c0c0c0081c0028907102040203182840390750323000c0102e00c3c01c0080d4801584103401131b0804031020500c0c02400d8a0342c21014034103810845403480c8036440001400704c08481c5845203100050070780b50190410800394003080e42d54111703100d09401004110040c1b506141d050007922001100a000c4840c031944191101010304001d01c01a00840d1070f113800300c1c1d9041544012982940d8000c0c002580c103d00d4181c03410300c590f010075010200b10306049404105139a003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 189459739 1250 189458489 189458491
    0x106050406080c240f1e0d0504050f0706050910030f0207050a020111010c0e0405040312110924160201090305030d060f060e030a02040218030708011a010906021f0f05 73
    0x18001c001e01e22064108244108211502a21625900d04600513140b05041c0021204a00180001151101c10350301e604250b2840031522940f0255020a690341c160081c0e07403000f441603004804407083e8883c2420303c1703a1600070900411000580401000c0703110304194080e070098401a28001480781c50446031601240c1040e00110f41507084544403905660340300100d14a071403031000003040110a0100040c0200f010002814059a00d40000400749070050100510080c1d4882061042803094182503032980d20045645204030f07130480d0f91801c1201109195401c1c250400388840c6400c00007500d60300c510b000d20320700303d040040c6450080700103039060011b00012040d0746004110141054030610400205030400803c00116008006183c0c0d000215001500c0c2c042e1001a61004c2c00340d40b6046100903680e400780c0610031044002204541588813901d00d003072840100c49401351000044604844910652006078840042d52881600d0030020703a06000320214000b84a0100c40c00880c2903e01c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 189460989 1250 189459739 189459749
    0x305010209150f0304020907090305010903030917070b010302090405030c1905010c030207110f03030d060303050c060a06030c0e070314010b070209060306010f0306090f02150711060a050703110106050406 89
    0x5004181e60354903050007800320310103840589805003402042c0b103a42c006800000d04c003034410760322103002c11461401601f014010b950804002e12031600c035410f014015110390782049403d0214095805088903103041600d044a03800708800d2101e0340f0350380030007048007400391059549000c2001040b1510404010841c10031500d94900c1c242c50300c980c1031641c03c45600410f202c05040c0102310010003e00901003904101c00308480c41d044c0c0048410210b46140500f0500c0c40b599450070401105144d0000c010b84801d030b68610440c1c80907543d05442d4410341d0f602e4400104800c0440d4800d1080e4451100e003168444001d2400040c8011809400100844203a101d100c800758005620340940c200485400da01107403d4006020701d5160551025609110380b2000d08407da40c0c83c98201008012000c0584041d002030030304503044520710030314800f6801024100e40c3c10f04040300303003242420014241c8601e00001c1d101d0780c1c100b480715102a640c00b4108182034009568132a40800c550b5201d20030280030789 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 189462239 1250 189460989 189460991
    0x92d06040807030b070203040f0512010f0c03090212011a0105030705070b07090302100305091e010b060703030618050403200f1e100209062d12071403130605190204030501 75
    0x9441d40c1084400380c5409011003045402c100014023a59491000c0785082b00e009070b841801210024a00328010190b40220100c1c40381800080c0014541c907402404040b40200c0b0001d007500480303201d0600f2030704545511003160400c0c0c0c04080e59580204017031940410350b8200640b610720903580d0300e41200003c50340100031a0380c0f51001d20550804440c051450102da04003003101d801c229a01d80d1343c0d50a040c0c1028000002e054601b42c034000290404120000040c09558840c03a00d0714002d005024980196004103007108490301c0400d80d0350281d2801180c02d5100d81904d01851084490400401d44000b011480784c070041008006040041c41e0b40c220403036500d05510080c0e01501800c00d0a5520100440c80c018004601e15940d80d4003140c041c0e825409051454810205901c0c00e00304100540d00004000482c84a00035142905014410540c0d60388401c104907214886280b06d00003510306c500112035003076001c00010b680f580060340140032102415001e0a520400c40c0590b80036401c00c9a0030307 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 189463489 1250 189462239 189462253
    0x8060a0f0909060c0c1a0601090801050108030912070308030f0a0b2805030d05120406060807030602041802040612050c0d020c07240804060b1c08031506092d060408 72
    0x4003502d1302c1035421440369444c1111544c245619100c03030740040e076038408a81c6100c06c0c020580e00da0050186900038207010000740103130741e074031429070713881c0c0e002946a24054814400200405000425618143c07130b807250b0f0541c01c0d0b40f180d02402c03450b042c00404100d40503070385005400d0b040c0e8030701c0c4404428500c1c1d0000e000721348843e0f00e4007828044140d4800c82c0030360b00490b01401e600340c112081d2148403411800503a529a100c0c24640d005e000640c3c01045030b400388200120600c02c10340c00401c1960014603800701e4081012507001d04034404c074801c04002503a0400f81300d03200d4049800075a00154008442030402d0341c0030070444200d071310148035007003164460a0104082032203c0101d40c041502030104000d180d40320070b40602400d100074401480c42d6650b0f5141d280a994094003802050000070529401c00494540102d031648166040801302e1018050350900345040801c86924480191040e2034580300500100c1c0798030710404503aa004e5581d03060500144e103802001e0001005810010183e17 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 189464739 1250 189463489 189463493
    0x60207291801091e0303050903192306013c170609010e1c02071d04051e0709150b030f0121021e030f010903090609050102160608060a0f0909 62
    0x40320380380d100b15400489444901c440760302c0c0031309500407640c042c1003155440c840d0303400082c01d2a41540148094401840f1404148100c603101c0054a8143c6062111408211600e0b940e403688248503e007046841c420080c59641a0150021550303414515400034052210300c005102c0c034034540100c449a40ea021080301081000c20030303940c01c000c41c24000c11414a1940c0d509454a800702420561800020441041941b08001c0c035001070210f200080318140704044810b136031501c2a1001da03242d201c1c2030100341c0c15200c100c14045052821000400d80c140c940368104015188090300e142e004081c152000484402c958001e5204050045058226605101401d05048503082c0b00d0044e500c0ca0860110050300c074041241c010a2070034000100420740c20740003d103850185c07039006145500b000320110825070466509410780703039a9210041016201c000480c0d4800d0074225100c00346442c500308000b0507008140554020f03101501d078480d26034450f440303500e00d5082940300082c483d5440c482141 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 189465989 1250 189464739 189464747
    0x9170d020c1c200a06022127060f04020909030408160e07020313030813180f38010207050d1202010506060c0a060507030b04090303050115030501060207291801 70
    0x45602d001c242682e0f101c0b40c84019550358101480f00200384950028004540c610340e5041446c0c8400c44010b99049450100f8103c20740c203420141c0c20701146103580241e4000f003c0070402a114034940061542a56144e40800c5a10800642003120320b010401020411000501c00c4000200c0c451500c003c04516201503610034400080284c002c64100703001040980118403034031b104480d00304640300d448205046180c2140703004c95120800410800f1500c2d054214035421512401030b621004000707030815428200d1412400c1902d102080500160700c4005842e0030010f040b0180041c0f0440311030702d40b02e001050f4400300000d02a98001040700301030f08200d509001b11580b046051740c0c0c260400d020034140503030300c800300e0030b00070003a603210000541102e03c240e0040128403001001481058a103041c00340c010542800340d41d50f8045c0d45152020070b14003030301400341291513036401040c6451074041d05104103031075001101c00781c020025a00300c0700d102440c0030781004031459158402c0e00c011180054 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 189467239 1250 189465989 189466007
    0x9090c0c01060f261902040209040c030f062c040c051917010b060a0c15050a0b030601120209010e0712021206040c0201110d0f02090303030c071509170d020c1c 70
    0x41071300c060180391040c01c01021604416001d040d5013501400c0005100103006406034221a5070403c0c80c0c150783d2030389158590800c848030b00240e00104400c070780703d00400c1103000800d40702c115141c1c10541010441c0b00880c00c0f05610502800f002200d241d190400507261400c6c0207098120081040814007002c42c00410784000705100070003c00403040318001058503401080c80d80c200b03000d0101c8020040c05006a03160000c45802181002146003441c6042c00426413100342901a100e00c80c00413880b2500e0301e117007040c8940c0081030426031380c0c6880a003010720b02c8000c1c95203042260001c0c0000c00702c4014009008403039507000100e00a85050360600040311f00014070401103a0510003803410189500c000c40e20000110900800d01c036004100400c068428002c059806210003c1001000030a680c043c08560b0310500c1d0000881d400c18a4110960b00780c980c010b04140c48000d42c1c10b40d01c00c0182c00800707509a85400c0941030107100c50310b81e03050138140108a03200d0310700021602c41a581c4175202e4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 189468489 1250 189467239 189467279
    0x21b06011401020a020d030201200414030a0b010504050402030a0b040b01050405131716083004080d092a140102150105040203060607020d0f0201080109060b09090c0c01060f 76
    0x607000828803080000d584801c1c00c20080d0082025078000070515200b03402c08600e0025003c020b0340d600c840f00c800000b455000e1b101c1c0f00f504125038110194549008a10200d4103a0480300b2401180d0070701c01044024040507100302d0b414030a02d07214000007040002401e10076401410074441943c907000600c01510300040800c0240445480d4450000728030661520100d03180180c00c1e519800028580e842e408400c10000d820140c0116003140d02400b0f000b1110180104041210700e0b00c0044141c41e00011001e840060800b00d0a01407119808543d40c01074aa40d8041d0003030074100c6134201e00c6010403030700310131581002c01140031092010203a14401500190f07802e10003404100100b49018140142c18059544a2030f000804078209980301d80983d2502d40e0000d2a0303a450303c0d010f10340980e0014200c1812400305074603000005400f41240304e40f200b16800c461031149816080c41c200700302c86038000d242c0841da1105101120b098002445040054200c60f13905401c0181498900b00710f1074510001c0d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 189469739 1250 189468489 189468509
    0xc01030c020a141204092c031806070206030a05040b06010f050406030506031c02030406020c01021209010c03090806090c041401050d1226060112050702070b0d020409021b0601 77
    0x15000340950024a80300001d400c566034030031840081005604041111580101407040840c010421181c1c55016a0b40301c00d501030203034190060840b00c03103041d0007000ca40d008503401c05d100d035601150400480360ba00600c0188110700d40200c6600003110f40e082543c400f00080c0e41c80d801c0008002c07000307110315040705c0c09090108654518903c020900d00c070ba4060341c4101912040411401c2d1030410400300685642102074000c0310751801c0c000c1d620740261055034014807070f88224190075400072805020710030030b000411b071074030490308015184107503040c80450800c03240b00302c0018400414030405000e110b07100b0142180790003d404220130703150520102d00038110038000411140c2e1b82c00c5400311540354070600f0780d80418115001a904000d079481d180b115000714083d2500501070f010b012034404c400981302c4004c410b000340301880490f10102d9540700541d00c2008284040310001024060f40d00c00c668016103020b40380c9182006031307004114103000d14a200ca9044160030401c0c007a05014004441d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 189470989 1250 189469739 189469751
    0xe040507031e020a050403050a0303050601181a031305012d0506030d0806060c030a020105010e0a05100611010905190b0105030a0b0c07080d1505041b1e0201020702150c0c0103 77
    0x186240c007002d481c41d40164543d40c00101d000b121030090f07068500a40c0c0084c16280680c00c4d505028001e82011039070180000c2200d43c001d03e5507030710052020240c841500107065031160340d0811104560001e0300120b060032044100d0030010b4024082c031f4a8141e050380403200c011548540c0290500d413220b42a045490034503041144a440000311401c004d452494910041c0e1686400b18010b44140d491a0300b043c000015540b544c3d40d01504594100c40c0300e84010191982c1d40c0308007208403a016102c001340901c40c0c44041246501c605494519039000200000300b2086503520705141100c0d4400000701e0038540b261980900451081c06ca006000a03005084040099640c007020550011b22207003c1081c0801c10b08140581c2c04142d52980600030b0b801c0015040f41d1560950b0080b0714850740d80b20b0703410401004641c400c0c0c0c45601c0c0c1d0340c14080c9c2340e03241d241e0400c0051031804d40702d84210307004541d8240100405603803003103211010309100f499499514101603001c1810019800401414141008 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 189472239 1250 189470989 189471011
    0x120801060201180611040e010b0a231204030212070605180c091311041107060e0316020913060212180601060801030204021c11090f030a0201020705121c0e04050703 72
    0x10025010903540300d000068060000300c1459404d0080c2d40000301e445030b0b12800400c45505d04001025101e0300380d101c0001c0d022f4007540c0c1c41c81000d0ba40101c5601c03080d0a00c10103100d01c1041c43c0b880d8006201e40161003a040784071a480400b6001140180c1e5019100e40038450440d101c82090035502500c40064124046910b000c1461031101504d42500d10900244132000d00a00000c09100084010000d100e40c0030458500e145540218005a910707074038204040d0b0280800000f15121036020040c0c500f94400c4c2d6408004402500070308601d2140322452810000403001d10080140001e10941540c050400030380703200c001c420704032582403184d106c400107100d8281c02064003030440781e04071005640c80844103101943c0880000c801803015083c01c0c00d61000d2041d0b000034085c006070903103025a00301013100405650b09510705001e1b001d60810981440035061030305c2200c0790740700c03540708032070a40415a00c040d40084c2d802c0700000005d090300d003d40c080c43c035180c02520b401240d1803400b4807001c5954 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 189473489 1250 189472239 189472271
    0x606081914160b1305032e0b03060703090201030915060f060206070504051c02041b0e03190f0309030f0c0302130203061e15030103080d0b011110020d090f120801060201 74
    0x81c054000710301d0b40801d03001c1d04003c4045a00c0c0142c417014007941d01a002d1601e9403441c6c104010216024109110740403481a00c00d481404071009000740105803a45903d841900180082041030b8101600c1c0e0a149011550500004184074100303000091103d1410041c8028020160085411500320909101402d0361001c291820780d1001c41e5942064200d03290244420782c000800203400030b0400300c911425010806d9a4441540030b51a85503001260340101900d80c1d03014080e20040607100710401c4003080881c500099654428201445510307109d40764a07082c680b07004412202c51294503010b1085007801401c00c003000350b00d00e80c29400c5051140001d070500651102c1c00a040c0784806005400b036460180c1410a9111103103982d543e5612030a2080c081c1e480391034002402414182500d2165110340c00941c80c92a80101030849200d180440300d000c0e42c8140c210141003500c1d0b00044021940c10001d0003011845003100803030802c40c0140203844914160702040c156490401c08544448403 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 189474739 1250 189473489 189473533
    0x408030106081017100b01020d0c11010c0503030901051e040f030f03061a090f06040e010e0903040306050109050601020114010605090111011803020d02160f030f0606081914 76
    0x1500b4481843d0741c440c042c0c00c151192692060341481c001a000c0004104086061401a60b0f2460284081c04d9040c005a80d0b9940b80000c83e8009044081a140800c460f1101e1070303000c840515201070039150310349410740b840c0c205940e901003c2c1d64038024065980c0750504085d1200126982406a03454540c64030194080382200160901040e07190a04056110768842406000a00300b4a554420f0b000e0049809401004940e401640e002d101e1000901d481d00c103460031201101b041081e1030707003040310700c800c5504050f0181e0103500c010320021002450307600603180239203441c5000107200c0c58140002400c1d6010b092003204002413220041c01125400021034260759000e092003600c01e040508a203005010086130401b01b90301e0740314014200355010034054182d80669003250612800c2d40b60b5049070401c54802c2d002e28078950001000060842020403034254001d503800030f0050780c0d540100c0d050100c500c81c1e48407070390300c2c0316182000c00c203c680c5010341c001c042000414192010342003031480d10071 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 189475989 1250 189474739 189474749
    0x150306020a18080f0c03010516050a090f031a06090903091005040504150f0815130201050c010501090b121f1503051203040611031003060b011205130308090604080301 73
    0x240000c1c4410410b80900d205181000c92064814900b40d07403229003c0d11030310540c1540100c1e01425561400c20714050003651b0084046081c1500c42d554680029101e640c0480b000009100841d8000a160b8400d82081c400650048101110b0002e400402000810000700410312462208007440540403000054614041c030556185100345240107080d02c03680101e90106a000b810140d0440f1081d5904425000321041001c1c0b2550803911880d0f00b40c2c0310b01c140010003a040840340009047d40703010001c440009801814240e140000c102803081c2507580c00d030003140c0d0203030701d0700070023041d504141d400045405802c0010b440200581c0001c403070400b86e4001001181d6489418981841854500c028019903004084460100146040b0707025908100c0b0142c801c94942000304008000030411240700c0d000d081d491218050855a400c00201000c400250410110307480980c82e0780c40c0c4c4d11070140511000107540b890f900741c030310b402000743c0001000d01000c1d412a605002c002051034003942e040d90 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 189477239 1250 189475989 189475991
    0x1030c0c030c06050c040b0415020c03060723190c030e06040b0d0207020301180f030f0e010806010f23070606060309080403143306010905030a1e170a0210150306 71
    0x5180c0e0743c2c03081040d00a031f8101c0d10754804000340c00240da00e0303040c1d800000002140c0940720038510404c2010303121001150282c021541481007400703044041042290850308070b607081070601c83c20840011303c00380c3e040b410703201050031042c09006140e040021030782c0c440402c5482601d0603080c1420541240200d249181c50150085582e90456034203400c40e200f410181c1003103800c1c0c2c1c0d5050030201880200690150301188450020500d41c91060142082200c03068458000903180c407401100ca48008030341820411004074820f20f1040040031680c25001c2d00c00a8079511640182000030854170682d202c00103142c60a054400010300074400c1d60203c0790054003240000c1086011035003010700c108042103140b9901000d052400001e282416925040c1041c0701001e9074075003005542d2640980911a81940982e040c2d10000340c0b01c0200b14919003800c103194248040c0c07551201c1a540000240c1011130300c0c0401c000822a504004005ca550406070f01403011444403038800002c84110f010203440b41d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 189478489 1250 189477239 189477241
    0x30e0112050c04051c05010c080117010c08040f06060f150201051509061005071a090d0305010308030a020c15040b0f100f0e04031b050f10020306030d080711011a01030c0c030c0605 79
    0xc5c0c0700720000d014042d0300900284000814258001c0501b40c0034003030400300d00c0b10342d000f4000d9210140700b9084507080e03d0702d51040d2900c0329200c1c1078610788042d100b201c0796520f64201084200c2e41c5189500102040045258014115100130b0b0a5802c01880c050300c001c001e2200c1d00c1582e640701c001c9500f040041d1030161144001040480351031141100c060416900100005110254031180b01d104a00807070030340b228000c010344c04234140d8200b03100c040c104d42c1007400800d407541010350007000c01188040840e0030103242c548a0180c1004220380907640e030070142080102d607085001d0b0300303a40414180310036092582401c03440100401580500c00c02c115500c03001070704040c0501c2740c081c541d001c1082084c1c2e40402503e06665550a41d51030110b090140c10702e864442c2140303009483c0205001000341c04494078651086840c0302c7d000300703201d0030800ca001c54554103100a01c50100c00f80d201c030300034614060b80c640014040e15401e401100400401d82e420001203a8040815800c2c149e100b5004a51 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 189479739 1250 189478489 189478519
    0x50c010c03090f060c02210607050f04120f03020105090a05030d050a1113080d210b040b0d05060402030118150f02130603051b120f06030a0609030e0112050c0405 71
    0xd88031894000f201c410707a0501d00400d070960005c982d102c98130f20032254814000560645043d1200101c01c403800702d584220007090801d40600050195000d030400654200746d96a4900110441c05850a848601c42114240c2c14180d080c06980d034009a01d40040019400340c0d51880d54920440940302409961000801d0510b011038009060320030303d42d00e450703480d100444d006407680a8a8400c4401c284142c2c03104944c058055003900032000c2445003410000219004114040c04c0c044c401325034401e44c5d46450304515943e0031071207803c1034040c000508082c82c3c1403043c507085070702030036401809141c2d107428140054500c0201240060b6000c0011400502c0c450780d220203030081811b503a00a290328000030940e20740c960300c514418840141e5aa10159811505c100b00d885401a0901d54690490004145440610407240c02c00310281c00c0340c0c810051925280e08880f40a101180003c0d101c400b042308540e4046d0022003460400401000182807400305261203203d64410b807405041c2c40700010403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 189480989 1250 189479739 189479747
    0x9040807020f15031014010207141216031101091a07050109050d0203071b030503161104110306130e07060e010903122a080d050606160507090e0307050c010c03 70
    0x44510019103c2400341c510a406049941c104983c45914207105010004024401c200c03c013080030b2041c6c02038240c20303080c8001c000382c1b04240600c0a411814a0707003079000d066001c00a10650b60f5203d070741c01c060503080d403030541004510702003424100408502d0600003911411a08100c0c00f500b4143e5958441c1c0d01e203041c0380503121031140130303000d4020b101c219281c098012000301225807003422004d50300012100f81c0d8403410101d000c00b5015034001d1050006065905008502840c0078402184408404c0000a0240c890300d40448409030070106c10f104150034650340074420b00e0821b84042c0540c540c49600e0036608c58640c81007400f00b18045100e00c0244c0d004007442e401440d000140c03108c42c0345e07002001429000000081c81ca0740070000302c1c2480b1140d2484803031124035a00c000d44515004001d601c64016120250540c0e0340070381d00b000a80c60f24010000c10405052061015204091903c614175044800014444516400130040c1000058021414030161a401d00344400c0b100d0580c20200c03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 189482239 1250 189480989 189481009
    0x170414010c05160311040b011704061e050a020a031a011706150d05040507051503040b19020a03152c090c09150f040212070804021c0b01091103060904080702 69
    0x1480f14031101e0000b009000c00c0c0d941105800c0e006450500140680a00440d03442000021103108100410041000190701c1e81201c50b2002c15447d40084d50380c040382c60441221020390740b003500d0940c0019484919070b003501522198001c0014031840c0e000c501c20029010164495140d1400801d80707001880030f41c0c4078030384404103000b42c0000648841d000711048005000503074040e51144994000019503190141109a000b0107007115107085071640d645690800c80054044038400b4803009140c0369614042c030103028800c1c0c0075034010940c1c04030800204074001c502c0d0841d00790000820f08000c1e9158550044058610950310004420b680700e180ca43d0800c0c0000c07072440d070300500c0728080c0700e801c030461181c11002c070f0300855075800e600c0100d0f02040300f240304080354000d10742000ea00280e0018010385000d40c3c840d0008e00740c50341020007002e01c0074030b4440991702203400082540041c80004614803034201200e04401005185041c0240019140840200020a507003000504042107441d0b080360f03a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 189483489 1250 189482239 189482263
    0x509040c1202070f0515060d060216150906060515040b030a06050d20040b18060a0305070b13050d0203030405092a0c0c0d120e21030304170414010c05 66
    0x210746698141c9003600d144458007209407120f00c41c520200d4a075496a01109006901c008d020074900c0409a85034400b1350000c0c980500031040200b00308000c0b80b08550b442a0024445a0004080400d40b80074002c627007443d00814000e805000a120600c0d070110122000e40722104130f40b079243ea41d0a00c0b00d5010f0500c0ea0001604030800f00c550300108821003108282c2c2803181d8540302c402641c00e0007440704807025800c409511050002c90310031003005000348260400000340603448259240d48440e032070189582e01c10b00780d15200203404089101ea041d5040302609040b40c103642958243e0300020b640340507a00405100e0780e606004035100550982c084076801c802c0168a040034204410a041a80c00c005d203807250b2801110548051441d0182204104030790102d804001c0104600cac0c211070048040c20119042004080142c02d91107001c01c16a0b031680b03465000319601c2c901407800c804d0b460700b03029001403000000d0100b80300c6080ca01c0c0000880880030b19000d00f138160356041c203518100f130104507 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 189484739 1250 189483489 189483491
    0x715121b020601060c0606091d0d1704150e0f030910020604021f0908070b0306280e090114011e0b030f0c03041514040b060d03120c05130605070302060c09010509040c12 74
    0x21040d0004809c4420740303500c142d50740c15684000d20300c1005075055011052200404d0f8031460014000828a0540054001c40144001800605a1901440e007494080303091016880807400112030302c0c00000680283d1201d1000d01558106039000c1240090f0001c03030203019848000b10101054802c1d40d80bc00200101d00860344400d540d440d00640c6039209503140c500400100c10000b48401c5a131000702c60a003140f440940d001890080c0400085000ed4035100c441e54950003c201540090281c1034041c00001e1040074412010791401c08150102d5442444110818002c016a0315141c900c01940024900c0100e07540e0364a52070725030b24050300d8005181c103a910f0710314442c00c1752503400b040600c128400c0712010100d4840100b0840461102c04000780041c0c0d0506003c03040b0061900a01031291081c00c0890500448003202950b42c691500305000145000c02c00328240b6a0402c07410b0741002c0b00c81140c84ca81804134000038441d21a00b45c41502030303174440c0c0280c1c69691056562801160000c90 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 189485989 1250 189484739 189484751
    0x405031005040303091e03080a060302010c060b01030204050a0902030609091c14090a0303050c010b030106051e04020f0a171012020f0a0e0a020a0e09070207030f050715121b020601060c060609 84
    0x41602c9114920038187c000820303510002d09202e080b0301c1000c5c00d8940584845001c00c3c02c03175032000c01802e0b2500450341016002d201c0040e160300c1d5002004054402550050389030720f400c40501c0b0041000074600b1885501040c401c0000d40581540d200203061645010100740e20040d40312000b61107040d000c207400810601d80042450790100185c9448681c0130000d00c07006074140e0030542032b07890900945903c2549401310411164411155004484020340007500f8030700d02e00517600d042d402a01908007c80c423540b5011602e0240526840c1d8446038900c80c2140d80d6080c81440e450391005104d00a02402030031101e2180c56a030940a08014113400c03100340711030310b40410640040e40013840e0500200304c020340206198942806010302c0f540440d40102450361460701d91030105c5401440680317540c0280c18021580408405860203007940c0d980750414503480302c5507144219101c3e002d06078241458420350760603540d07000c6a814115807081c9031580403100380d4100600288915400700c005075142039 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 189487239 1250 189485989 189486023
    0x3020903060c030106021c020304090e07050d030f02060106030203010e0606070206070606030309060909060e0f180703110108090604030816050904062c07050712050426060c040503100504030309 85
    0x60003541079403529400d481039602c1c0e07034455202c7c1c02d0f107481c074210240e0010300081c0a100c0580d4000012404c104080340c505a640c2c0c070204031159004d5000390001802d00c1058200c0a404200e6075004100a00c0c04501d158034002d12116540000303481c052143c0c400160b5501950f59160a80e0f41554011504106556503440c014003d46880c1c85484085101903800007a01619840380d10121070b038452400e4003564030209943e896a4001b411072032280c00900c40d241c0e00d000204002c82c040e42c4100000d50301c80a582d0009040104020824112a84030408110000354403444c1c0d641c2000084002c6418030400c50016034041c042d444103290410300c1c000c0c0010703081c07030070f40322140050000182207055a60a24a410052401142c4290100744100158000034221007203058a00245181c901c0c1050388030801180700174405c1401c0041d01007070704200391041d0811300819420030501d903107040c640b91802e0302180e196454a00030b9101b05542d20001006e06000b500711451417a40116110440c0f0717180 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 189488489 1250 189487239 189487261
    0x10f0302041d060a0603020a0c06051f06020607021204060f0e0a081f05130b0c090d08030702010c0e100e01050d180b04031d06090d060b040f02071401050106080402100302090306 78
    0x450700c80e0f204900c0180002012401b0f48202e450b614803e036203000c0c1d00c041d02d031210780181c50040c2c8a00d00c030b01c1e0000c0c0c000f514818808040f00140034140e0141c4114140104000d1420410654492074014104001c006c00c0d6000118021042c2c1c090a01e040c0c41001400050107060159000c90350380d000b2b951620383e507074402000745107060103404400c00a5440d8101504488909501c4c024407044000d004100552190390280050440003041e10031220103541d00d458941c2c00554040000d80e4450030003845494004072620301c00c1e602580c003059104a01d4000601110120b031760306040c4500000d0b1915aa6a1500003101381803565074811502407140c5046044003104071025400540c4078915442411440301d111240c81c00020290350074490310008000c2e5119000204450070360b607445a0003480d45843c082c40c90340f28240e0400603154855403c0400000a40b1911400103034907103001405802e4001e51b00130b80042d015604d00d01c01c0c40700301a05074002d1103103d07481135051103883e040244c21451 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 189489739 1250 189488489 189488491
    0x2a070b030c0409060515480105010b0c0604020108090a02030a0605010e09010519020d0e0304030f0212011a0108151527030604031103070f0f1104020a0f0e01090b03040506070818070302010f0302041d 87
    0x54402040034ae80e85031028055405441c030002c10641202012030059881000c5050b045140b51050710784000c0315a0005e03140c0a202441160801c1c0c0300c40c0104a0600c00740306c4d0f42c0d41300c00403900a204914203891401c080180d05c100100c0003560104090200d84002d600c018000d6201c501200ea546032241041c40d90030310000c0040384100204c50314442248410b000b4200901c94040080e05500031840041d070741c0d000001c0c911300100700c000c3e80b170403074580d104111000100f400c400c500da41c8040000f8080c0125680d01c18446000c0b5003014600f61075100001c0c41c6a03c0394152400904442c10740a0207800c0d8415014040d200c400c110440e40140001c5101e09000a03115060004440c40300307405100980c001c9802050102e414036102044080c0103c49801e0742c0c04051500700d840c40e4503407031301d0f0042c1d81050342c0a0b9080e6001c0400c00c8003203500020b45035000b28101121590700b85207130313000ea642c86606010003410004c202030107200660098040d50f01508480d20fa0503492074040e4031082040d04 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 189490989 1250 189489739 189489877
    0x403060504110f180103120e040f0606020d0306050d150204080d020708010614090406052716060e060a0c03020c0d060b03060105062a070b030c0409060515 68
    0x7074800290044c540040d0003140a80841003c00c0d13039a107035844142c0c08400b5001007005211001e5020b6003250344601c0386401800d4022030006441c3c2c02c20038004d10303081341c0b103140c9024145400001e1005541305050f00c400941d0203000095070700010500b40001c0d0081b80d02090080c8540c10001c001241c000c41c00380c0964199a008103c0326596042c1c1907c038141d48581079800201071008640030900903001a41e00c0340760345c40040e9000d1044d0b41781e212185c0301c1c00c400200c1c640110310f80305211091140800700600c09461304d01006405040054124400c1341c02c21414805440e6076135041500902203e40114801446191814040c0c28003602804925420620034061040082807a191441c261a0110520303442d072980c6091450f5502101c48084800034a5880382841c0042e0040108005500c42c00000c020142c031a4a40007034041540c40c50b400091150040c0b00c080074804071044199050801c141e00b0f00e40a04142281c6101e50f20300c1c091035000040080c440c0ca9691940150240c12140 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 189492239 1250 189490989 189490999
    0xf1306020c03070f0902030a0e0304140a050a06020717070329100e0606090103060806040f0c080d02030f0d0b030607031b020a020a061404120c141002061803040306050411 75
    0x10204002c02d41c480e1a1401000c2da220005002401542030682c06907901621942000691103452040ca5186d80c02550240c2c0e4070204199101e82141050309810b4010b0400f61900504a03081c90b20183d1500c856009070905821042012407000130204a204000c60700440e8802108620700c05140341d46000001c00000030b800040841d11601481c140e4904a40c0d00d0612128291680000c11a070769000440341030416841c0c100103e01c3c881c00380001d501a40c450314410f10320b000b140ca840c0030080e40c02e5011000d103402004465201710380100455a2180e180301f940d80e650701d40181c10b14024145100e0403034161003418200135001e078143d40001c00a168443c8056441c00104004a98412a59038001c0d003000b880384003040024050240c60803904c840205c82070130244c5134a2407106031034203e101a20011b8583c40c04100c0e62810700c030f8001e84182d003521100d007040701e050006941c40b00090712484040045403620301140d0700c06d0040d00c003e1503000f4003d0181c0d081c103080134940131000e250402c1c450 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 189493489 1250 189492239 189492253
    0x60507110f010c1407091803110d080103170c060403020f06130309030f05010b030d02030a030b06033601230705040f061b141b0604120204050901020f130602 69
    0x1d261aa040d055200c805944000350140703203a0703070080c3c0d0340e40c0c03943c01c2600307841801c1000c00c90002c1409040301c030001c94040c18a80351106d040040001180d000320302440d80107010218030070b5900c0701180741560f1300f080040501e6804081c6918491003424810840d40c0071345030a0004260340440c5803030003119040200c0344c0d652950000e010403d0780f402c2d03000300402c2c0302003420400a514a42284500c81c000c1000082c03941107000032a0402041c00003000041c0c10002d00150031036050303c2070314400c0c1402e503500c44c00d510f400220352001143e48421a961540c8a0201c400f2202c42940320081d0056490001d0013100c4908440207404034144c900e0144280302e01300091002c600c2581900c00722021048001e90b1640342241c155614140c1140c00d0030322151485826010550782500c00c0c601d2150000140025250070600c510500b032098085803041c03004103c1080292000c0e55502081a01224002005d0303c1d00b81c01c0a00a100d51402c0070b0318080c021490106112400e40c0c248101c070f03801d409442e49 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 189494739 1250 189493489 189493523
    0xf050d09030c110f0102100e19081201091e0905010902100c0b060409021f0311030f0108010b0109030c09020d06030b0901020702010906030e1504050309090411030c041a010e0613060507 81
    0x80000089285c01070307120135143e01c0c0b88895504880c0324410414290703820410f0101c00e940035040e4041c02078421000009070140103143d400d01e068010440c8082c1000505117808104500301009071032045401d48403d0030906001c820740c0401c04243c0d004290112122043e5400380c1044004401034915a80139400a05c1a00345070156500955004180101960030a13020700790985484034a0020540d4032056100740654407802140503a82050344960381e50301d884030305401d6440e05a001c60410000107000c00028000c010b0840c00c1c0d5040c43c8003d601c82c51802c91100041030b0366071010b02080b4000042c80702011066000340400da000b80c2c0c0345800940c407214150180d440c00300f04a83e66501c030140c13490b000c80a0b0b41846030014814010740e0b18020a00d00080c1e01d6000c02d9605840301c00c0c6c40c034001b1415103403c2003000d1280d40700303640074049542144107160940c0000d095807418003000d9441e21406a499004484c188003904414068240d201d000050040d040000202c0e1441084820045 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 189495989 1250 189494739 189494749
    0x9050a0b06070206120910020a02010203250806152703060c1611040b04140612070302010503041407030203030706090204150b2b0e160501080c0a0f050d09030c11 71
    0x30350b03250060035003460403520301600c1e4907509008006039079a0081c40c840c1c40c0905541e000610f00e00c006540096168144002c170402590700c83c800e500351754003c0d8a10b0400e810307040721009501c000c0448610091166180c6820071521401940455030b80240b84140c5841800300501d041c180ca090b01160744076a01c4d0624041c051152400300b8041d0030a12840a00155001d001c003e0152009840440e80320700c014081016a5041802c0e11001000307003080240c2801e207a00001c41406c030102c028010b4a00d0b60300060f01078440a080508440c0c00000da40d55802010071040009640c00b800b100d030b558210742426402010350210881c8110300f400d101304aa4512042101c1c1a03c0b000e1040601c0d00862030702000c0110381d00004610101420300400000c85414850b114128034400003030008944000300340b5690400c2c0d5080141030040040902c10007051042c1a25941c11032030400740b13810742040105550500403401c00035240c1c0d00305200e40b0304056100c4003941c01d2500c10007a0231244840c47c42001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 189497239 1250 189495989 189495997
    0xa0c0911030c07080a3b0306070e0603150904080304050f1c0503040f0215070204050a020a200a0609030f020606011d041d0a060203061002060708131a0109050a0b06 72
    0x10300d0310303041802100d02144d40c60008081c1e4036054100003400b070070250718003204165465403801d5551050302500d50035410140c0001e81d1030604401801c000e140c800d03030140c0107110305502a805540301000250f449000c240100714500401000524107282071b28202209034801c5900b11124003900c00401203410700029914254514810075009203020090100c5140e00010401c1c4c03801c0107048000c10260301ca42001701c0322003500d180360035690000340c01803006407000a070056090130720400070342200545c440e040c94800c06002c42e5000c174084201041c5440c0c040e0941d805025103240c01d1b805810180c000444a24114454003640c19540c0c0754001903900c80e0a07900302c000115850f80c5107551603d80342e80000041080500d84592001e10506454500038940900321400c07035001080c42401d103090700c020b00340c0a6862004019600c1c1c030110040001d900070300a98101d484600500381040b084400001d901c11046107002065a9070f006103a029003801d44002e00028549000c02459003007442c115 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 189498489 1250 189497239 189497251
    0xb07121d04050a0209190f0b040308030f07051b0a020f01080402150f070507150216080d0e0f1002060601080a110f03070e0d05070e06220f020c0a0c091103 68
    0xe1410038800d01800040e140c0200704030034440e4204403176806170b910b554030301d4413840380380c00420300ca14242221919103d00c1c640140c145540d0900c02080019240c0044a81c400381000031050151580c00c01a0b031240120480d07400403440205910281050000f281514140201c4d00d40c0407072403200b401503945041c240d401030740180002520030b68010f103041c01009402d80c1819140d03e04180c03501d85605000c1c680e0800204080c00b0300c4400300720f55040001c0002445402c0e080d440b031a1606804503074940f22180e0480c140009100d02c04595a0b4122040b005040c000e0039a08150482110094030f52400b201c90901007420000400c6040d60544146113085100217080e0349080000040c2402d0307504020007100410400503105461500c424403200c0106e03119000400380c00d42005200f41010100401c0c01e4090700c21243c1d1500511408007172260200c900010001d0002c07064200c3c030004c1c0c802c05d40380c1c010302e124900026081080b001c03105002c0705c10010042100c07102c8003c0b030081d01c0c48203590b0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 189499739 1250 189498489 189498527
    0x3020c010b0603062107050a061e02010b13150306020d0903080a0b01020705010804020307091e060b1305010503100512031b0307210c060f0902010e150d090215040b0712 74
    0x41c15100c5e040503120300d140161310000c90780020b64440010304000c0d21740c0c211000203001c1c60140d480e2180154420700215016000902020105c80007041d994008031060101e01ca44442c0c260112300580d000e018055900018259a900c0c900045400984081d5a0850000d016640000c9400ca014820080300300d4059005c2c0240c24682001110324080c0504142c2c0e15000d02d00000803401d000c1e2280d440e0407464140c6481502160310711540032074003550302c107000c07011003041101c522000701081002910400d091080d1603494034100040e054110f908401e0f0001e181900c0c9100104d00000a414008039801d00810400a2603003415100d008800c00140807181c440c80341c1c580724038181005507100b03030745c0d240c4400c1c2140c40c0d44690090700ea82c17040f019600e581c0d4660640030340d44e11807940c0c140002c0c25034000032030074400d0001d00315a200d0800581903007030740d4514540c11543d6920741320b04140e0780c030710340d2603191070700c03905400310f40d40c00300c08102c0d68017443d126003030038107070154410344580f00011031 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 189500989 1250 189499739 189499759
    0xc0d05072c06032d0f01031202030306030703080d0b030d0305060301060f0f0323011802090112151d123601030f270203010c1b1e0b01030303020c010b060306 69
    0x140c0d45031000c2c1035100d0740000411010703940030344c1580c040d240d8460180700c014890720354074500b09080b4030320030412140c0c02c6410800c2000f4035914006105411280d003c501c0036030714211960300400601c1401d00782a414018403001024880e4141c02407070060718110000c00c0500e6440300c403120011824403910218450543c8100301043c02034498a40b240c0d442c055450b044a4a44031442c2101c55074801c4101c40c0707002800c020150309044902901500802014807001441516017080c004040c06e000c540c100e49900260010310b41c203580c0038440c807240d0720071181480390601c1c50303030100d4019501c0d000d41816941e1100b405103e10b101145081c0c1c904400000110901c4c600440c0645039200304540305603140d400042d0074001c0054000c860000240c90704032503402510416017502e402281250410100403009541c0001c42000c42000990001d1080d4864110900720442420780f0500540010f403510000810b142d0141c009241ca00755100c002c0ac06022400101702442c001559450382004142c1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 189502239 1250 189500989 189501001
    0xb030a060213030c09020301090f0b210f030a02060612010606050706050606130b0306010f030c090b0706110301080f01060f03150b030c060a020109060f05010b09090c0d05072c0603 79
    0x1a0060041070010a80c6400b259180d442d003188292481d403080c0c440c84d50000c010070401d821445506000c0003040d4041c0102d0340c424000503510110103401061001414400d100e00c0b560810100030000749460950b81c890890030f00180d100d481c2181d03014000c101500410344080e6061240c071040d50543c2e11014203201c0e10ba00c5520041c140100b03001c0c0c002508011b41705007450400721040080180d010401c0d03484c603140b0001041e68030520545000d1506107a0030240d15900880001c007a210f8500005031951258204080600398000d25000c80990000010078002c8002c20f103041c80e036040100900413140e071421108104140c1d440080c00100c0c401200110310031341c0ea041000c15000c003d0445940000c4400000c0c41940000c100707030050717996014120204480c41c00340c140c1030f04c1e81072800c210761762518809508a00c9030a103040d104600324000a100406901c081d43c20561540d14104241c1c82c04005c0a40202c84c8a0100c0f0010041150750a03064044180d1852120401901c490706646a01c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 189503489 1250 189502239 189502241
    0xc03030503130f0804060f0e030c04111b0609161505030601021c020102250c090903020a0f08040f0b03090714030c0301091119060815010c0515040c090b030a06 70
    0xa001c02c80c01100302c00100c0080341040f120720303c0d56802250003951311032514002030403045400c1e0000f01070109030140e044c25a80c0104600003500b030144c402007030201400711840709612541268000c10711080b01103200b010f500040452044000c4412640c503001c800107101c03c614030502c51000c1100c14130701e0bc96070301442003010310b070040b006004039501102c1e1640c442c03103964440c1c01840b005030343c0030641700d0944c407204d207210780c0e0440c1000c2c0b07006030002c0070740f242040c0b103000307010b8101d01765140c408400802d4400c0240c2d00c10143c000c01c48a10080a1745001d06850740244941440041d41c02400b2804441c4402207a004041c00e4000300042403410040844541c000c0010540c0f50082414410003510b0a00401e40158410649051030000134410080070100006a8040310b031030a0009014454010b0065904201c4084045280f103070764400480c3c3c0080c81d0340c1d0041283c022003e21000030300c0310041715030040740319020051203962215540740454000280590703055111074204801300c1c0351 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 189504739 1250 189503489 189503491
    0x91d011a12151507060b0901061704060504020109080601120201030506090f04020d080d0f0e010c110a0305070203070504060b09090603190b1503070b0d050903030709090b0a080d050409180c03030503 87
    0x142c0035601c0e2071101005040c513a00050001e540142c3c60303004611092800c50000b41c007600e258141610107200c1caa03d4058580d8004000520841d03071382c80898150fa01494400c0005c2c200c2000700c1d0401e61311400358004442c05540e0880c0840d00313100100b102440e00700b00a500c24440d0070b141a09580e01d036002c004c00c151302c0c902c0584420340100030803401d590080c02204c1c3c030401c3d42031000ca080d0740d2050100e0f0840b40704001580c1000b040082c4280e00010128482c100d15425241540d126501d40c00083d09090741c41c1d00c100d90091408000098400401c2c014010000702104c810307541350344035400d243d140d100d00c9003d0800c01501080c1080080c20310481c4540020000000041402c0c0303030408a89090384a03000750900d44804504a403c081040c040c850b03220561034055811428107400c05484041d0074020030042c0c0e0349400c08851581c603892100750042c05900c040b10340c403420840002d031055000e4040e403124141072003130485802140f6005c09221950220700c9980c12455514200c9107508 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 189505989 1250 189504739 189504781
    0x9080709200702040e010c020109030e03010c0e0907140307030911030a080301060c03030902040510030209010b0a050a1202090d060515010201060803390d03180f030f091d011a12 78
    0x50b1756003e0319500c00c801d10a01848881c590000558440300c0d04010b44051514003e10780300c2e80c145480d4030480750b8405107203401c000c0140c8640840391242c0d082921800c400300c141ba03000c140c000c020021340590580201152602940b0544440107103031007495201c458501001d04060403c0004005592088002d0306100d40039180000e401e1a04c0c0d40024155003040d80c656402040b801024020b43c0340101232140106003284d000341c500445810050b099009100f0040f045c020510785100340c8036400d40440d8220031008000050903138841c5001344c000c00c0c054400c142d0303207002c12121504550051080e0f0003601c4041d402181001400c0107070b00e001110038201d40b0300500c01c40031511608556582c41070701400b04075014101c43c24001c02d004007110040c46a00700044100c0c110303000403940e41d12420168682602c0e2000f90025000401d517040185076124595080100d0421b00340c002da030f003000606981461021503d544802c01040d400380c000c2d0400c5862103040d04003c0340504181c8680703000c4040c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 189507239 1250 189505989 189505991
    0xf0501020319090c30050c01030b0102030403031e0521070e01020129041e02090306240114041e0503060a1515020a0204020307021c110703170c0307030908070920070204 74
    0x2000c1c0d08543c0504090710f08120341b5940005041406903805001c0c0220883d000e10095040601d1a2001801c200e56000c841c086410000340d07030307281c6c030b8450401c43e00c02038944281d8441c2d40d0111010130704100310441d01940003a400300e40f00741e2998418082c05031103043d10030400039882d803c4a003122101d4281030362103a00036a281c089009440d001c900c00231500c1c05290300187c4440115040c10304040d4010074120f03500318820050850803c0940480b8203c5100386081e01140c098203501c82d603248120f820102462204640014070040420000c509840d415010348006840f20746842007a0b5425100100740c81103000402e001411850f803204181102a2040304c50300c800c2a0003040403a48203451200040e00510300c3d1602c040004d4840030300014141c9001d0f5062104400d0154440c0700390b0000030080b50014402140c034840a0b000e680d03030701c0c05082c2926554842481c0103440c1d00354921400c07000e401055800500c000d80b07031050a0300e13411000b00e8111415204000b809581e4005001240d03c2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 189508489 1250 189507239 189507299
    0x52b140403051203040b010b0403020603040b040201090306060b040801060f080616050f0a031a0909100b01020c1008010303021209010905010e180103080c010b0f0d0f0f0f0501020319090c 82
    0x8101d04008841e25a0f40d42e0318041c1c0d0300d04282c00e101c211054140c008d80c4c2c150b0410001000161200c10803643d0040d00f00f00c20500c43d0f112071004035225203076039102a00700d9041401c00f1802c98004001802100d8180008001c5d4560300c001c954601c144903c40c3d4900c070303004000003820450360449011144a00e618141e860481c00d400e40701d0441e04605956400260f45031068100c1c0c072010381d40d62102410842d005080e5143c40404156100042d4622810458403030040d102164003c00c01a51001d40080040000869070100100001e100b484290014400c0c900d81c2c909172400d060445040d000d040c1c0d40c0240b0581803800645003104840410385d0000c8095541c1030625450b42c00060203984a01c03200d69981e01010b01040c00d5403c3c00b60200c4c0706600c5051651003d648100003086a15031149a03000300d030856041005101910580107031010710050242e40401a042d802144103141c41e162542907145181e446400711000154000c0002000ba00144607521001c82100c0d00e0342000c0c0c20032020 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 189509739 1250 189508489 189508493
    0xf030c08070b09031306021b06160f0f050712050c04020f0c01020a120e070b0415020309190602070f0503101a0406081605090c0d09020d02040216052b140403 69
    0x1e4228111410f001e25000072603460f910340030b45544d01004001e10705c000c01100a68002c0e004500303941800641c0320310070001e08581c2c0c5c0d160040390b80100c940c001d00ca02942d11680d0030071891828007060704a400d07000700034010a02540a0f80c5a100f40c136000b03401070070514035103000d001c02507001020b0701d007483e00c0078030016003800d03800d000a0841c802242d4a0950407021005000259040c1031401104ca421605050058032009001e44084400c03180314244ea841591009a017548101000305400c82c0100040200c0415003181c854101c812582c200c2d070361180e4078215520510018011a80e040d006120444501c08a940104203aa01303243e801c10001f01d0320340002011a0300540c051112034021640e16810502803045080060105503078130b400d02c1c6045400040a071184190100c0c5e11655180307042709545494800440311340e4058411951980380900310083d030745590303d089810348552011001c441c2150b00c492503098500c020004030010b1810415502c02080f0300003540135800074000040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 189510989 1250 189509739 189509753
    0x7031e0501090c060c0204050f010b0904110f12011703030f040609050715030e061006020d0c08070b040c2321030c060408040609090b030d03110c0f1b0a030f030c0807 73
    0x3c001c2103a41c43d4003860f1031407803041c04240c8400824580b10743d40303508010801c48400c41c0403180040c8040700c00140c40020380c0c2c9c0700b00080c0140310301d03455440800303e000d44d00a140c24a200e030503504081c070b171080c4600f1aa1005a40c07444200d40b0320000a500d44080340016840f034102145141c820000d070741000d80c4410007800d014031420703080d00001e80c450070410b0b2110024402541c1241210b00e00600c80b60401c2c0001c2c0d1b03203e80401030b0b90300f0042c00720104c000307200c01802527980240d40048c0300401c174201818441800c03200c46c020040b00d040c08101e400c56000700c0d503403450040d44016100c2c040c3c030000c02c0034584884110504030440ca020030410058192000d101e100e11580c8901c944544590810600900c00710198001d26a070f1490f100d422402d03564001a01da040415928020035614030200301c210b15806003c9070741030140710314069a6282d80c008912400440c8882d0751520025000004202c03641d44e803480003500100c6240d00b8132004c20303c24600c3c422228000c0207840d1510040350340d24a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 189512239 1250 189510989 189511013
    0x20304170f0f060a0e0106140d140607050702010f05030f04120908011d0601080303073e010603051011030c18130507080a05090c090403030f0207061a0307031e050109 73
    0xb2403a800100800588003140d01c9000c5210135004001c03c886030802e2000a9400f14452044d4410810483d044c0100300100c4511140c4070b1588041d030b04541012030700a0000d410509080f0f02140300b010710343e032071103116105980c89407030aa2083e0b60a504d030750301c41c2d5034000800011074040080d50071700807030b206200740522400e48a0b60901c981c005003442c052607040020607003010129800400601540c0703130b03125080940d500c1082c0200c111040708290050310500c0d40c000c400001001c8412055108001075102004481c010030656400c0002c01103420101d40140750f185114130300c1880414034204003c0c024005041e0103440c0d0321120a4084002040a100d0a161013640c0c2d85900030001960f030700204070342e003200a01405010340c2c1801a06151100304000681c1c0c001d8840d00c00180a16200e03401001d200080345600319550615400c00c0800762005084044100c001440c0d0100305040001b25581100d41013101d04a40c000c00385060b4404491508040e6401c0d901d6030482030205406075000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 189513489 1250 189512239 189512263
    0x3030b0303070c09050f011208091c240c1b020f04021902012304110d080301060f03061508061909180233070204020f0f03011d0601020304170f 63
    0xd500f0780340790040c10b5007550001055074408040400040001e0400c100c650040980d02242494480101c0c80c0490752001e211400303400c402100b22a0f19041c40900c1c0000200021300710170070011400c00628060580b0821640c400014a548568070843c514400d1040c2c030861000380250790340c1c0d104000003000d0743c001000b0b991000881c3c20030904000c0d02403040e11148440c10b030f1404c2011082c03541810340c41d08000c20240410003420700c41610750b91841342c1e295105602c44da04c551a56191013000705024616000780022910f000000300d01c042c038010040d240d102596891861f655281810700c49221110316882d40101500600426a85014010f442c03462055110b045000040c0340100403443c00a10701014450101301240e0b01030805124211050500c0320300701d943d54003090300c049030091041c102c0c2c8040081003c0362000001084c0c1e0020b504a44880032071260040154203030380003c2c102603800c03070301681c010031003080381c181e100f00010f123441109425954a000c0103500716060450078190 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 189514739 1250 189513489 189513503
    0x302211503071d0f06030a0611040518040f0321060306020307090e090606121f0e1e030306040506060702131413152a08060108161b03030b030307 64
    0x20560550804010000041103080c900c0e80380b103181c802100c045480007070a0ba482695103000005c1042e20200302c1c0203070040d4007400c20030a04240d90900d581076001030003864030600c0b0240d502946440b0200081e030080c2e82003400801d0002495409807091741d514003902811580500c010941040c1620411000f14040d0001503178a00d08484000c00c40c20464002c0152951060288209075500081895000c2c0c001e51f480c40d4102042c4040c5407520400f00080c18074030096030f000003c000c03a19002440e100e50b03604100e4004010310799003a800d03031035000da502099900501c00510a4640380d0403682e0486000741009151109035004544604e030210400541603484290411a81101c0401d03150720005042144254040559501529058000b40841010782b220300c6040b966510100d421000c140c04001c280040002010180c81000b0848080b03012070b5007180080d48106250021200e6100c5950760350b440c031701e5580c240c0d0078008004041502011798880c000100f9071020030081803d80d008480b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 189515989 1250 189514739 189514771
    0x3030f04031403090a03140d060f1a070b0714041a091e0d021912050f0f0102040e0115090b0313020f030c100c080c060403030903120903050901030221 66
    0x700a86504000750b00300300030401c108100a4964000b140040d80c80e0750500e0f001d03809030106004503855003e000d1141d5082860500300091031503580402400b290a11108030030066042105001a401882000780401059400143d10180b04004a031000c0c1210310300641859114050030743c107441c044204c0030106800085414540c40d041c80e01c400c1002c0380740d02d100010752480300030a03000c21624000a004aa8690880c00400c0c45618018060400310381030420305456802c1c0303207a8414805448000078040e160400000501c10300840b400e0720483d60381102ca90346000da02107884d0400c3c1001408003c04c0701c001041c084243c0300154000c0c01d01c01000e44410085004010300120448001c80c07103a0300400340c103442e40d107440950070b4201c440380c10f2104134a846410001610b11419408007024050f4078208420190141c0c88091268001c2da0f4181c150080b9070420000ca030b551080141c0452000d1100e50540d40c440c0e00102a8025458242d20401c0c4582e540542c203240c0a4401048000c0700344 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 189517239 1250 189515989 189515993
    0x1091a04050f0705280801090605010e07080405060105010807030b09040606080f15010b03040215031614030601140d0225030f09180906090f11030f010b13050709030503030f04 77
    0xe1108030042c01818059240c2000502c10003110320200e6030001110180004081119103c8002081c1540c003e0003850a940381060041009001703185c1001c11392404035007018031401d5070358441c0381c1c820024241a42000e0054428590040106040544840918135a51140c184440c0642d126600228405041184460030700c0c11b4101e030038055511941101c400f1614011116044601680059940751114000309200c036030760240ca4070034000d001051000780032900801c41d0307211155958241c0303070406078078601d4224402942c2240c0060700c10030348001120a084001c2c00c0a00300303800010f20b030514837260301c0701d0340708458109c480c00c1d1003008030074060503009aa01c688604c40d034600089180d080001d100d031111140440d43c10000d695513820340400100e40d1140b100e190300006010034514880c6094462000c4002480380680140110040c40728414001c900c1009001042401e007032101d5040c034070090000404040422100810001c0480c0062005500641c440c0084071074901d454 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 189518489 1250 189517239 189517243
    0x50c040b0f27010515071101050f0a02030a08010510120f02090a030b0a0b04020909041103120d05090708070b0708090d02220c020703080a1101110307180f03080f03070201091a0405 79
    0x140c1c0b1132401204100e079108000080c040448041e59405450900550805001202c050240101103140482c0000d0840340260300040070f056083c00c11b69500010f0382c0c807001404060312102405030041140c0d4600069401030f150030045800402c8040182003103620000215404040e51062715040b51040a00c4018011802016480d2405031410340c030b420b00c00004184026002403000d0072001c41601000400e80c3d00703100d0003c10060344094035403903600780740c0064000c20b010b589203482849003803030006004202041703010407a203030668600c2c28403c460720b918032141d005058580c0d011403001310381e0f00160b071044160711201080707a03140c4105e03000401101e03044507420107910f419940003540800025034124100e1f11202228500b0459080c001a160f601400403210701d14446c0001004203d44107500131498001c00c0303600000c0405582c0e44030410340341c400a500000d8000c520410401b45c810100800854001c03509100000307000626440d807410b402d1102e000300345101ca490082c00144402 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 189519739 1250 189518489 189518491
    0x1903060b040501260f0a06061401030504050309060706090816031d0609010e03010f0e0d091a0405060c030c010501140a080625020106030b042607050c040b0f27 70
    0x3094808000a50421910781103103c9081c101a00081c180c66000030a00800c0c0b04804503801c0b80400c460545503503107002c0014213840d000f595080310410040c01d0721503109015240c0a0340e0448007a41c039010310314043c070105511240084e9400da44480e060400100d44000a0029560b402c0c5d020f10311501502d002440101c82040080009400c400ea58400f950784204843c170388003003400e00c016000141d201080c0503220055031243e400340360520000d4000800b05000c525480690384050802da140d200c0c100c2040000c54a6001454091105010710704024006080c0c1c026040126400d021007403111a003510401d80047c07000002121010006042034400f02c030180101c10040d01040c5401030712001080201c0c400b040007010504540d4044500070350201000d99009841ca40c124a4981480c0e004490404417260140c0c0403032245192100e130f14015160729507030240160a141d0034840801c00500b4401070b42030b0b0f200c0000040395086507101c8500b0200c4004101c0d01440300100b1185007228804 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 189520989 1250 189519739 189519761
    0x70207050604031520071226040219030813050310060803030a0b190b090a09090b0c07060f0c030c0e0901060e0d0609120822021f020c190306 62
    0x201c10b1200380002081d215008801115410001800c403002144810440e0741e005161544040b00040040601900344a41e011140d105d44078481c09810388104908424400c07115004041030180220b00145050940d01c821504400f28600c5400e890780c80300d02c0903074010a141c5070081048582002141400d106003106040c09150400640d403070302c404952a40300c01000300328843d903102c180540d40d60300d061001445107104000e0601142d180c07001030700c0c26440402c4403841840320020000d403a450b00d000780300303007241e004c0d0044013180c50f03101c120310090300002d0040311202e0f12240420742c080103d00c1880a02d8204d9130b0f021813a540548000760500c4016142d90b03028440c1d030b50050140c0c0b42c01440a80c014801a81d42c0604000700b81440b500a005219004081d2007803010701a91442e40030744110f0160307d0000310b815241c00798840301100a464004001e40121045000031001c0c6502c5620030124100c5006480d400c04a180004001003a040c4121000c50103c4109005011041c0301e9840303029 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 189522239 1250 189520989 189520999
    0x1008070905030610060c0311070b07060e0313030803040c0e160f020705150903010221090f0303240316081605090c0f031e040b0f0901050f180a02060c0607020705 71
    0x8140711481d8100410395011700d006115003901e42c0c50806104010000c171a02c1081705658450ba154503074408268000d8005440c841e043c540c089108072404000c480d060b820b80180c25070420324640d21454160001081610510703000400003c62a0803007549501c640c48050710a0582c00404101400d000c01080b04801150b100010038042501c80f28a444503402249000316102d84404000a0182c880e009041c01d42c204545c560700540b040441c1e045005440300b0094507103100940030320f1aaa804112501c41011380d07607018070a04007219848100240d00041d050b202800e20051101003071417840c0e844401140c0c00702d01c03402145455800308501809003110b03c03950a05041c41b040b801e60064020a1980110000c00b0070b08003d00c3c4181d01c01000602091075119180600b0028003101003150003520b081201c00001716035a60610503d4030a0a00c0e032610f1000703884021100d0f41640304680800031070320075104e500d80580d840b1000741003c0360b0400010039203440c1804000741094003c0c4d10850240b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 189523489 1250 189522239 189522241
    0x7051b010e0c06030c0d020f030a06061d0618181f0e0c0a30050a02071a1009020c010207050c0117150f0a0314012007030305130210080709050306 64
    0x4920220720b00d11403003400ca4500340c40e038580940700f007010b2007403100409005200141001c400070250019511401c180b2504200043d81e801080c2c818011240030034881800c101031040061070500003600d202141009203101c164400300101d0701b4562001c440a2126007043c1c00c005000d1103690308450203403c01668240f429251100c508000c100242802001c068007140081842c3d04c00d05500c14421210200d03017030445074110700505448403031040601183d0801d000a41040264001c5901140d03020040401c020180100080d103200050802c42c00341c86c0b1079800284810b464005481030312400000141d8803102c500c2c06a14010980030014140070a000d8112144140c50b41415800600182500c0f0682d11480000b420444101c0c0d00d00c2d800904401c000c01030045441c00009582d440e40020004019003401014141d1507071000103c0001e4104100c1000030b2082e0452500700c0c0b92001400c28121043c1d002441e008030300882c00b00068901d000704801583d0081c03c510003040158041c040fa = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 189524739 1250 189523489 189523511
    0x7051b30070206030603010b0414010303120c0921050610050a08060112020607060e0a03080a050703290409020a03060507080703020721020a0c0305010b1201020412170408030307051b01 81
    0x1140103480001e0f10821000c0002206a1000c0d0001d6041c003400400c2001040920798561408106c203000580c0081d2030003428a0140010b441228520305650b12442c61492401c88040703d01d1800303440e10100404e0409400c07000410030002a80500b03840c080034072140d0b061801380842092503910042d560361208004001140303006010300c0c00b894041d40c05641e1142d42d810084068001d500120304103200301d151410070b15a210300300078001c0301511002e21050b240c51008070b085c0c030007442c0588130003840083e4030564112856280e00070300501034402b25068809800103050250546c0c4161806a22001000940c6600c0b4001d190301c65141d041c110700b4511651181e1882030f4000140c2500000030001c91408980200186071455a0088403003000c1c0341c072840d10174003810b8101c1e0003c0c02074081c120071055609060080d101a15400d96003059500c81985503030402c030401048102115808100200b107905d410320042d403080c80180c4030207503034000c1003800c40340f951030070750010382c003a40341034050f440d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 189525989 1250 189524739 189524833
    0xa0b010603020d111e0318030309011a0324220c03020a050102061308030c0904051003020a0512120d021908220809041d030408250602100507051b 64
    0xb05e001ca0407000ca80d01c0c1d6039994000d0005c0148521451001c3c4008003c00c8555141500540e400f501c4000e00b002040c0441c80c18503076100d80c88070ba01d5460485082e081003003248400f1141c1c6d03000b2905d1001c0b0f9018900e9111540030809829025103902d1134110090056042c800c1c92200103020a20013807106140080907500c8503110308000500c00b5000002062080260300150788404200134010020360601c00036005480c4d04920040340205554040050513152071480461550140e2010384200f028800c1c20f080254458038101101e0b69081c003034503401088515103000000080c0d00c40c442c2508000f00224101c41541000a0003007207050800d80000e03007450300744d50280380c0035100403d0429601c0711031640c0061a80b080d501d54880402c00190130040011000e00c50800316400d044444032100f4041c000f01c2140c000c44000d80d0080481a1038020194809580f00d24107281c0541017030500c40d03d1000c41e00000746041140d902403074880999100d01480d003070030510171412280c0c00e00302141c82c00d1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 189527239 1250 189525989 189526027
    0x40b0403060207060b0a0b070204200a03022503021e0106060c020d030909020d020901120c2a02040516031a011d12010c0215180c0d050a0b010603020d11 67
    0x41c462500810a9400c01c68560010364451070020100b041c4103032a40c0d100c580c0e0b5000b0b0101070340300c3d90402100701c204240f10803a030f1384c1180801c08054505107605000713a000c0e600c449000e680c031a050095117110007142000c50b4850304d01c07903405844202c030038014030019964441814007240c1d140c03e404201141c0c200034030a001076410780700001140d900707050a8500100340d600c8809010b0001504a801d08810341c0207114001e026214042c0c4909903100000031500380c06170321030216021098801d40b130305a118800c00c0d2240d2103030403004401c2e02036000c00d00341d13038050b00c0d03500c4040c00c0d0004420506030940143d8100314294003a401880809100003002d0300354400d030303900400e00d20407040c400036103a51140c000743c521900c009100e044001400295a55204c41c1800e0900134003074045010760308c2511010700a0042200140728804402d01008032007030b0390390400c4445110312407044000807148004540280030701e8800580702d00c003030040041a1490300c000c002052104008a002c5025801011 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 189528489 1250 189527239 189527243
    0x9010911030402091e072102040e0f042a0608060d0308010306020c010f060b03010e0f010b0409110912011509090507300528021c021314040501060b040b0403 69
    0x100c0041d185c10a91148080d000b600c3c00b0391101c201d07000c1000103a04000b840055035a05110380c4030321046080c03000224051405800c402c822034030003258060580180302c50f0098000c1e0b4220310052000d080541c0d11011400c2c980c9844d404102d010007499411900444d44507a003a038120340c8120307040c0e80040040c04140002000e056010440d0f800c05502584050210701c00e2030000c200407500c0e044503440d9900244951001402324100141c88460120141d034100c07401410040e00342800e050b00382c0c010345503079808842d44040a008400f859036030f40c4034201d0303800c1040d0000105022041c41c80c00010015400c5000450b08140810b00010750001d841c400300c5420411028120480d50a840a07060000b440c50380c09858945040d0180724001c202164030410a484100c045040c1c5400c020f42c3c402c440c03401a60040e50f4020107994081d104c0060600540300800000034a01041104000c40740e8094000c00d4545184042000b0403600748220409000c040e900300d800d003031415081c0b881c544240c0c000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 189529739 1250 189528489 189528499
    0xd050f061906061b06090303241403030c150402011b0614070e0d1407090603031205070c03050a030218060f1b0a05060105010c03030e0303010e07300216050a05010b09010911030402 79
    0x1141c01f89403013580074074001c0c0c01ca21003038a8002d0901d8a10222002540241d8040c540b1000088255144c004115a040c2810801402c0e0550810401c01e40764240100242d0510462055030202c915a000001c00c00b07610486000a0701900030450510721007005060300d00b440500f058a10b0b05650304484003150341e6104021050b00700003281c07598102007441d4040ca455a0502501008250304403c0300760f00000240790030070140e03032801800c4074503500901020300454400c12022210700c0c4039400526485021108112032000c03040b000c00c5c000e52081c0011003a0030000b1a0141040584600c00c40314650302034000c100b00191a15201d450310811b116680c103004040f60076104142c000d800c6044600316000c2501d46943c0e5480c00031042138030172108a8001444020703000c030400354445a100c0080200040c4030312034bc5104078100e009504c14015503080c0c10300b40c0102d0b80020000c05c40b032400e04d44240000b00300c0304001e00520290080c10303044803e040c0c0c10641e40081401220058030343c040c1d01154 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 189530989 1250 189529739 189529751
    0x109140f030607020309010206070806060d02090402070c030803160309051e0a080307021e0318010305070e0d062007030c060c0306081c1103180d050f061906061b06 72
    0x1680d4000c5010145800d406200200b10030030350084050603281c1c0003a0240c030030075540e80b5411552020f0480ba0143c2c403c1c024881144c0464556003d000d2035039001d007005141c580a43c4500c0a01d6007a0707801180e540c08004100325044c42c1d600d568109800c03090030288500420342d0359058407100d24900020809013140070038040d06c4c50801c0308041e403540000c2071541d02d040600e8025110682c10f880c03006aa4101c030102001d0000000c2155510099003c2c000c140c0011100118083d000c00341c07a02c0300b045582004005180e0303402100104c0d0a22a410000320710340c5a250089030009031a02420b0311102c20302c03519020a401100005030680d0048000660500c0250203900404040d001062503203e000000400520307820007049450340b480d03d52851034054180003580d82d11800015640181c00c0e080028024105615034501140c442c070250b45900540342c0500303252440856400320501c0008841d20302070710880c1710301c10181401e0b1a180b0034403a10b11041346030300703c45076800400060307a0320 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 189532239 1250 189530989 189531029
    0x314090f070f301b091b1e02101d06061014130b0a0302070b10050d080d0e0d050a0f0807080708100b0c01020c010f0b151806041d10050109 61
    0x210000c2d002980015194544013400051806684c030718041c1e0f450700b0303140600707140040001e9031152400403c3c0b541d5040b0b001d03614101ca600010408464401075120b044166a44001d903800350030b0300003044070000c8031003804518003c0e18285002d4400b90007054101f48010296502940f00681c0d900c0c089401652038280d505c0b9800c8804d00c943c011503060002042d0840f4140d8543c000b00f480714003c082100e100e4403141e442001526840c482c407039002c640d14158200040c1642c2c05005030b040d000750000340b042921000f10b8100000003521a00080740010410342b111340042c0826260142860300c07010501d0040d00c040d20540c030103040d1405101e41d21002030307154604803168401070f000750181240c55031291441d6a01130b401011008000b0350130481040040700440c85512104400105441d48000440880320030f1944012515000c2030101203807499182c407007200402c01030084400041c141710200d007181c06071003405414800c0140c079521081055a92040e001015555405201c82400400d9 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 189533489 1250 189532239 189532319
    0x314071707090306230604110a0f030f02030a0b0907020706050f0921010c030e0a0503030402091e070504050a06030c020a0201260f010801050112031e0314090f070f 72
    0xa82c4014561420300d6170b41c1c440560808251000301588259448042d101d00c42040203032458440b60114150b020700c0701c2100d4130b00c41c000f90005648035080004114044044803400d80c0d00460b0b414104940702d10032514603081522015911000a00c060f122071408d000006003030348601e07540312812150209520900e40d6403070030007026030703051070154901000420f800c80340a020680745210200340340504031514000c0c045a4016a26400b0300550b145503119420424000c1d4050900c4003400c0f04c1844280d03403282040720040c01100c0307588500e074a9510381002c100c84202c3c0c540043d01054205810300c0c1d5001d8001600050103542420888640e6142c080d0811544400d40c2c0401c8030b441c07000d81405400c00072241000d050306c12801c000d00103a03898003e1070081c0e00038000000c0008941e50141c00c0e07040241c40781402c1200040c94080b400c01c07001003145401c101c080e1004025600b04c3c400c1f0365160781d820011540280383c04a550600c4902e0001d81a2180902e4007291a0886104162400c47c080d0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 189534739 1250 189533489 189533507
    0x1a06070b072d0207050a08010204050d0813030b090f061e3c0103060b09060108010905100320030708060c0f03040503040e1006030e060c030414010b040e0a030314071707 74
    0x1280c0030300b0142e0b410a4030000c0d41c911003032064a025800c14040425640c0041c005c580580b517015106035842000c564510342d503588000300d42c0d4050200320f1808400644100d003418050003041c80103018109044264a090010261040d01c1510007545880c403c04250300b490756100000d46400019036029080c0850324038000002c018248000381540d8400840c40b00005044c1d03406441d041109503c3d41040c080c000809807202408140c14000400040c0c0468204a621481580100440c141e40355039003000005685982c842507607003016000002d0404100380e600912810004000600b00344600c00741c076218000a507980c4a400200050600004108071001001e0201541c11145403025a0000140213400b44900190525079034207001c510000d41c5501460800c003050703195071104e544451039a05c0300000c0f00e031a95250384a000865941d445000210703500324000d0f00d0300c199180340080489142110b0100b400070060288041c5a5000c1c02c010b0001d4181440c0302e049484200050742d070740417 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 189535989 1250 189534739 189534797
    0x2d0302090a0b06030a1508012007030504080102070303050103030305060904080307140408070806040b090c0306072d030203010f061b060b0d051914010c022109040e011a06070b07 78
    0x3c0c0020620040412540c00321505000c910300d040d00e2280c5a50b441802d0303030100151a0407103186c1e890800d20020601000b070100600c2400c12030b140ca03903100081400d84e0012038054000c01e640d10010024035401d030052a40c0007004541403940d519080d502d414050102130014020440e40500c1c05540103041807c850103004501d08403801c450b070f9800120b942c0d0104940490b02005010045802800002070307a400400000300907201076030f00c59804440c10504150141414862402c4000d03200c00c400741001c0c200b0b200d550303000d0394030341c100a1503950508035a4880d4080088131400d02c4030a801c000e86c0400130640c000e5000c036a075004c0c0c00000760781c050b580324050001e0241c4c6440b00c0108015807040e01707001c0d00c0303001c2008110b40007548181c2200c01c0c05440101503000104002100551034116407156400e00c1c80d80c41c18003500d6404501142c2803030110318480c0e0754074100900000b1204040035503a04046a0035883c100c0c1c6680c40d0804603c0191220b802d2081c0c07800707403442000e81e880d8000b403400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 189537239 1250 189535989 189535999
    0x102030109050106030c1701030209040206070b090a030221041a0415030c0f030c050a111213050f040203040312050405010906050f1005031614040608070303020303012d0302090a0b 79
    0x15848040920080600303114100100b0b28020146030111f00a80022150408104080190741e20315024411084030081080342d1120042040742c0004908200041c01440a003005104c008928036001e0300e004036150024102c001c4085103102c0551280b0129400e542011440d51500140312895142d00d00035508643d81d0340005080c2c00070720b40d42c598022030340200385903101013a007000800150200e4503105d00440000d00b00300100c0c2542d41c0590040314100a50b841182d2a004401d80f884440750806c0480510280f8600400c0000e031038003a1851640440c1240d003141313142056540505000184103040ca00f59403103c1c002024000c081d406440d24980115043c401483c002d4451a60305d03100301c4060004c076640500108080c140040d9444504102a0764107401c07a081c95201c0200180340c505140d4800e4030b81c1030215000f04241300b0310000314800c2d0003c50b107a50601080d005024181c0002c0300f08100c4d001440c5c11803119958202c1c007101c0c1c06036100c1d891610b42400150140989846240e040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 189538489 1250 189537239 189537241
    0x304030f0c05090708010302040903111f1401060f1b020a2411060a18020a0f0320031e0102070b040809010311181207030b09031209010e072303010203 66
    0x40480d40840d000550710aa03001c8441c0c507160010040414020f450640000700920010f20042c20300c0c1d0b0000300401c1c06401c108032180d04101c0100c0c5014408600c070030035080344240d03804040149000301e000c4d111052140c000b00390304040c4020401800c6922000411001c0c14100b20340c1d10300100f0401c43c558019003034040e59030321007410003c240c0003010900c50340082c10704101484c0c0c0c03260310700d0081b07040008060051515503680e19009084507110289903c078548060038010382c4c402600200a00003161100029884d5050000e405001e00040c101c1054980e8071214640d0340128680311103085941c1045d20700c42e41000024028080c20400810304010041844240880c0b8000703040511026a400c0c0821a0074007521a01401002000302c0d1080c007243d0078001da45031800320400c0c9420250f048800c1c42d6070326180c2020000e03095500c6074254000082c1c1c020350403d440700156000c401c000003800324100b00124245e40c1d00c110310400140c1001c20036040d01640322152500451a0024025074072 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 189539739 1250 189538489 189538493
    0x10509100e1f260603070b0d021c0b032401060311090303070606090507020a030909050c0c2a010c03081801021b03031906030b1b16060b0a0801110409020912030403 72
    0x82d0f07520031110040e0001d048000705101e40d003030740c88548140c10107405012918600710041c0d6890300811400c1500f40d17020b0100c64810220340401c040c1c10880040c0129082ca200024581000c030f18090306d029034548100000e000c2c0c1e03600039000341140c00918000946200c0b00003070303419038021255003541c180000590003040c0005070b0014010384d1210b071002c12064a4510044e69981352900009010400f6450204429000d591100d5804405224214074050410302028100314200185017811410340c40b95828100601c0001c1420701001c4c24038440b24400d81d10042d207001d00c002d04440b201105990480c03100300085d01034480c900245045585020a4500031503140e801c1143c1c1410101e500d82128400c032180c0740507c0782140c3e000b1911400d40d803241501510f9194042003a001502400c10520000300301f41c20003064014010f440004000c0019401c01c465039000d0340c072072080c5a050814142d0820f00180444d41101c040315801681c910025021464940700c046c6085414080420b002003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 189540989 1250 189539739 189539747
    0x120501080313151202090d0b071806080c0306090403020114090a031704080702010c0c0b04030f03020c03010506030303220c06020c030f0d080a0902010e040906020405030c010509100e1f 81
    0x200340481c07108880c0302c80da1203d1030030400c880c0e45035000c400214450142d807a00a00755009000b4040050070000e41550952103200e5000015900d03540004c401941070f29484017083e54242c00303443c0c5464a8902d9007844204100140000340c2a18030591030100030408050007503105001c622514191060b161500755215600c804000c54250042260107090050310084241c01b035126541c040040c50a0031001d8004407203a080a91003111441040d0300b01041c0c15a100c80640b008500c2514040d01008407468020b081100c0f030030055000b43c0c10300d070074031485a401200f5254000403c2e080907506c115529a8124501040c00c1f0240014140e400c0c0442e805501203000d8140030000c3d0b081b90080130500416907034800c80301d02d02e00000380034040402c03003185172500704400c0c1d107005241120181c0d4503203000400b12003180c40100e5007158001030800032800d00340901c4044a109003855824030002e075000c100004180101c240400945000c0e00741c403a683c1480240000135141c1404444040c1c0e458058 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 189542239 1250 189540989 189540997
    0x3180f0612041b0e040c060302070c170109060c1809020a0201060513020a081008030f030a0605100c230c090a110a020109050c0a0b0a110322030605090106080303161205010803 77
    0x207101400d90764004510240c1c4da4032650300a03903103d000102c1040c50100c1c1100290801c0030204d58a0141040005e1a01c0c00f03154100e0102014200024403407403030380742c0b01c0100c07011030000105200c100c00040044101c12200d50048551000c000360303a030908900102c1c01000942c00c00fa911001170040001f1000250340036000c842042d4507909155120708104080c446680c5c46940341d25801044001003038218000515003201110303a01180c4103031507800080130810f40b45048000201c03801148020b1044509410650104001c174407102c1c00c0800010380e03124003035030220600039003d00700410201e64050b8003a100d40300800141540345e03900c544009002e085600400e5846200e20040c6018629015981d44103d802e000c0c034880c43c00140c1442518119000c600141050000b40400d8815040d5481c0c004032051601000c2c0c0940e90842c5450411aa806011422180c0c94584148500380c40007040b42e030014560000111502407040e0120381c04403001552011503401e0500000d40034000002030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 189543489 1250 189542239 189542273
    0x3070e04140c0d0305070c051c060507091a070807081308061e06040e070f1707080a08040b13030c0e0103020f03010903020c0d05070905090c0a060203180f061204 71
    0x503403441408250620354400d0b0041c01554070080e1907900e203000a02400c0104601c61041507001580c56503000024210404d004001c01ea0000110710030701044080c2c454581d01804034140512858145990606001c0c100d14158005c1540001c00800744980310058580280c1d00c00001503840b00708203418114209540300e155118030401000c54800c14504040045816100511002950b2045d0821010708075045100386280581c510200e1041540c0342940007410b5101032452051318101e5004c0e142c1021a4000c190913049000404000340019045404a444410756141c13140d01c00c080d20210704040e948001d011007080d21002802c1945185103c0c1220300894014a0000019040c107080e60301c0c4500040040e04103480300600f07450880d01140d40d40c2d015108851003183ca40320003000b1104145d80726803099020a007007803114031b015014400a007059201540c10203a140c012032948205038a0580d105000c080c140341480e0b111a0140c5800e01c891004060140c00c1a041c2080c06c240e402ea51 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 189544739 1250 189543489 189543503
    0x1e061c0218030d21020d090605040809010e1503011a0d0c17061c12020307080d1d070305061504090b07030b04050109021201090504020613181a01020d0309020f03070e04 74
    0xc1d103d150b03005840d56007151224407103401300c9240d4040b5010003035210840c40d1078866600c06491000c07600b1071041510030f900c06d0a509580780300000000d00703030701403045105110700d05280b1600a43c0310900300b0340781100c0040c02080d00b100c0503c40200050301801c85602849407030300403104906a40300c202168102d001201800309500e03084203114005090316410039091400ba041036000900071b11040d0480e180d14810341e070900010703555031071071079000d49180c0059a484000d0200048151407142c43c14568040062203440c0c42c5a66180d1150401410501c411040340d8064a590b1140e0f0018018254031030044096132801b4003015004040e0400403a000310300e060004210300f4251f10841f100800c07513803c084440ea1070f1099540281000810490b004801803064082905440102070094104042026803d07082c0c501340d0002c882c0400d03404500101100c0721001e5a98000c901c1199240d02460042402c040754000301d910407a8a200080d0148142d2000040e40407640284500030391140700 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 189545989 1250 189544739 189544753
    0xe0708040611040b070230010915050405190c0f03081e04080304030803180d09080f010b010e01050306030715120f0e0c0d060f02070b09010b1e061c021803 68
    0x2c0300140d80c0220300072448101000c0084101526200c0403014180c0100b00049064072444d901c4214596542506200103a444000d0481085018005001c001180820811840c82c2c50b840d440d582d032800940c11404010040401018040104820400f91288840c15203180c5d41d240342048540e80b0900084020001c410003074002c001a003005c80701102d00c500011814a03041d500c901c0781c10740c0060154401d03078000004a40d0000824454a0a010101c1d101d8401140c07501c94818200790722004550502e0b4513218510025070f8205000d0183c044c400c0c6006600d0b5618800844d15113019074200c2c1030031284a40300640d019070f1185814006103070b00c580a0107152010203003082502d28070641005937400c06104204242040d0010303002075400f40b0004a8040000f0308074801b00e90202e9015100c81d0046003c01500542c00d02510541c0f0300161044888011b030030241e41c140c4070341681c00d50703c6000001602c41d10a04610091410ac00c030b0f0100131035480b0102541240166241c105442c024000e0704 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 189547239 1250 189545989 189546011
    0x10503060f09030a030b0102030d060906181e0e010b0916090e1b0702010c0c080703110303160206090a09060803070506011703030a090f060504062a020c13060e07080406 74
    0x105040c020303040c8100550604104e208154082c0c401400c02c241140700034004c881c94802c050180f68000c6c00d440b04000b8210341401503d030b28036007111360284103043c24400c04010462405030354080442d87c0d4107000900c19600154640584094440341d5031168a41061214000c1e840203454800c01d80f41d00c400c120155203d8012451001c119080f1603481100c41300c80d110103000c900200010341c0f051400c01e07070b404501d41d21481d0001c920340007014241c0c0503c00510030414000500440c0040840040d8140404501c05003003140440c1c4009003d030001007449559512101c0004018150b03084090042079120800c81d96203411040d0142c80c1407003880000a02c186500f44208070680c4040059851a80c0301ca440e803010740a4010106c40e04000e500991b03010030410722915020300d20400c408502c500309001c1482025502c62054206901140003210704a0b400280b030311004441070f61100c41304007003910407400801c1a40e1080b0041d104000070802641c0e48068640d1040703200da0400c00c40f41d4294 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 189548489 1250 189547239 189547261
    0x6170706120b0a0911040803120105090c04030f02040906061a0d1515180f0612060603020408030403110d0204020a05070303180f03120b0301020a05180312190507081201050306 77
    0x111070b00383e4014891034800d0000a160b034000100e0054003050952800faa00c1000914640c48040b042d800b1806000050141e460516862174000006082007401c25056450b100c031422604c0400904c65591840a6030800203140c0010000300a40007503001319407031400e00031580c0d034055885003c0712841c00504008600078110300000b540c0440b0041c2c800c50606843c02e0b03451b07842064010741d25140d10400001d010a81f0800306000d01400c3d80c400440c101101d601405881403a005103080c18018803042c4807000002064400b1633421040b07010080c65800007080c4020006a4065003050001803110078441c4c1100041c051030740301e503908105000350b002034101901c030038140050000910340c05a001191060401e50100f2180000019110702090000390881e40628507100101d1804500d240300d0114000b5090740c1c0751400d178054213440410b42d050f41800c3c802c10001000010f201d04032220b0003031184043d1508543d2150752030b59205551648601c88000901c40c1c40d01c03d1207500000b403d14440 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 189549739 1250 189548489 189548501
    0xc0302070b0604060b0a05030c1909050f03010e0d1407060501030c03021207060f030c051308070503100e0709020a020f060103030816020312040b0601020a020303070b04060b0105180d03030617070612 87
    0x68500f45e901304013040104849a501c0980001401401071050703400040710030007956a0001c241d12480001450070703017440080d1080040441c8a6450503d91050165002c10741070071682251604080840c00b0404480040c029a080580700d03a00d08000402009001c10240090300d000701c0f1125440e0030000301c8281d40b4001c901507d00050480384004400b0b030b010360800b41c1103181c54200f60f420142a4103040c00c5032100c990100d240c42d07116041c1003000d42410b1116180c00c070b4105800b4070440c0c5900b030400e41d072144188113900000c2d0740040c0342c1e11100c1c4240002d144040c0481c0c113444503035075070b420001d080b54015900c3c2180100250f1400031030030b0001003154081420040c401b10742c2c1e912520b071054644c4005001b9810b502940541c0300050340d0900051051502c06c5407485c542e8101428000c046401d24280706050040030400c0540391040e9502c0f00d02c102c0c4045039004200c3d061841d048002e0125a8080e44800c0710409004915440110f003000a442c0a40e84a245901180100000340c0f40 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 189550989 1250 189549739 189549749
    0x8010b060c070e060604080d0e10050703091203030e06100816141e0604030807050615310903020c01030b190e152805090103080d0e0a060c0302070b060406 68
    0xc401d0400f00101d990f011982d9a00c240000c04503405c050340c0d15041d50500c00c84c6004200050391040503001c01c1e2a1114001054092524025060102c00d5401a26501080c092480d5481c1c0101c4580d041500c20703081517411050310030944420b820503640c3d181c08040180241c070302c43c4c00390108041c0405010340d007500444020214905446008000b40100740541041c0000d2000c4954034a111a4484500400055100700c44140c0d40b0038960034410705260b8041c01e09052041480e8080c4865130726803d0100c50120541144d04400b85074851005100c00c215a0f030b4100d00d42401850800d06401141034a0805400e032420b02005d1804410000003422452540d1388441c0d02070001c1c000422070645255100700e010380042c04242c9104c0000309401c900041400c2000c161440c107000311114608444010441919400d900354115516218580100402c460700f45d0380d03481d805161380740100444c4101d2500400100211251040c0007400303540402000d4410019510100311681401e10400c81192 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 189552239 1250 189550989 189550993
    0x2060f09060c2506020a0906030b06092103090301061d070207080d140d09060b1c050a080a1701060206010602013206060d18021003020705060a0b060c1608010b060c 72
    0x107145508080984045000c03e5103640c040c000d80000186252008091000d19030322250005454860003c0603116a4440365000e2502400101c01d69201c6010f02640030400c40300f1406c0c0120300d900c0d11840c5000d0030320034551540c2040e200080740384125442545208030700c1901c10199550010590340d84590344502c0d5078a0740700038003400202d4820355004007460290001b00349041c170a01e9100b07003079030a00c100543d106039a41d890310010b4549840a24038140d90440c400480a0460311502e48450011501501c0c0d00c900058841d002c510501e03000f0100c1c190030b030050b01c07156124070000355184030901a030350240d860600b403800d13009d04c01b1540208951400001c0c00018542203036040310400094882500b165050000b85041b52141c0101b00340c01820640c0000408241c0c0108004041030b040388001341807040240d0004580c01103a8190702c03c030f05d2003020a07500727000e03c041100e40c8208140e554040c0a040c0400254041f0040001c00f21000c000c02402a5084601001403521412409880341c6d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 189553489 1250 189552239 189552247
    0xe0a0b07050906070b09010e0c150f0904020708120411030a020a0b0c150108010c020c010c08090f130c0c11060c1b010c02060f0a02070f0f1202120102070302060f09060c 74
    0x119100314002c24900342e0140a0608094a69071280c9145100391115040c0ea515984501010746041000e412080340841d4100429883c07107407403000910944410031301c40b40340018495410b444c0d9404880c1d0640d440420310795608002d46c20203c00b4141600d0803035040c109480c080354585400035200040c141c00400840301286400d5826956501201c0001498001c0c0c40c032440100a1880c0000c0c0200518800800c6001002400900300729240b9181070602c0399401c004800b150f1b419058441c032210075100c180da90030900c00007500302010300d00400c3e4250304214490140700d038400c1104c0c4880f07100340034541505600604012450141d1003c841856001a44e070b25a401c4902c4000f0b24072030018100042c0a986680104071075038081500344c0405c07040040e0125170f4a40c1000600c1c014030025a4140a19050440390804218144100c1d4291501042c6110641d601d1403d10301107c48403000031580e4050524019454400455208445510760000600307203030800300d91a8416a104c10b0340350304d4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 189554739 1250 189553489 189553501
    0x3080a05090601150c21090806100f061803021c02090a1802010c06090503030c03070f2d020111070c05090106020615100216080c0f0319030f120f0902040e0a0b 70
    0x9800307002d800c1505c200c41b078100c264040807005e04038107500508aa440304026403e204001d032500030064501005e0319455034040020100c0000305105840c024500f203030407000410310070f900044450b00065409180740190040d00c1c40020407a00c03c8520a44cc031401c1556141d141204440c9a2071b0914211070301005071400542c814500712044610401c00000c0012568441c1440c6070401c86000c600990000b0600001c1508905422210002d6190403401814440182007000e000c902d4918803500b00107041d00e042074002c5d00005208580c0d1440c40b5258203440c10060300c01d950512070503004801d581c002240042c8081450b600c55800b0b82e941000c003000d0300c0d05010b108007082c06102c0850103128500c03e0044910380c91100204080001010030210840c10807424110f00c00d41148640e1105a8047d600c0111303000d060300c2680c05041c2014030350005802500d0250349406141c005c14030f41506111052456440620300d58000e4804029101c4108107240d036400321690701400c0c5440513000208 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 189555989 1250 189554739 189554747
    0x16020109021c050708030412020406090c0210021b06090a0215070b3d0906050d030c1e0f0b010303090902091e040b06120115170703050601021903080a0509060115 71
    0x18071a00844c3c034110399505078241181c102e03070044e03103c1004070300250043d85418020355003d424900300400c00f1407010b110180d5140000f606004031103401140d040307007400d030b41085008801800c1c8190786691820800542d02d4014240c0c040348182c0000791003140070004501510807856200c4030344030241d100c5d958401c80220b4450508400c402083d020900903c1c00741500c840c0182c01145c0044800303003440400c2c020340f011600241d014062040001000c642e0040908960a80000b0880758004c0d0f020b64030200b2070901c03d4094080c4c003142a40404000f01c18100e80c0c1224007a580d520080c41e00c0381640001d92043d142000d0340241d140005203800002c1c0d43d0b4100052100500005500d1800c101088141e04079500d904c09003045040100080325070b2111200f5200c200d460003c2030004403144000c621140030f8494420140d6032780c0010301c26402004149103604403500ca906220301ca40c0341c002d11680f800c8482a11050030800030480c3d030040001c01e2070584003681d04080640c09001700c111 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 189557239 1250 189555989 189556039
    0x10c0f0e0301111c0b03030c030a051312030909050c03070905091f0b070311120406081810061e1404020706020403060204030804150f1e02030712081602010902 70
    0xd9895503070340d214000c851034810010403003074a040c84058049124116054100e1380c0c0b104440c0d001340c000b00700e4400b10140120864050000710f0510580b1514117a200380100c61242d00008050130840114009141d0032500b42e000b01c9a080d4000d000300d59507100114030700c0c0800d49140022804144e42804203103021300110364040d020f0284000d500f04503000400184041c2d50080410a10008000c0c0900d680000b001d01c0d20030000004180110f04442034441034030a81c46542c04009802012a84000a002640108806e15422600d03810a84d49484005044510401c10860b442034480c81e07600c8983c440d10b4040303422407000c40030707441c91000501003e50710040085030169400c01011000410901c003038000303503004080d119182c3d800e0602c280100840c2c000c43d03100b400369a5410000459100080b280d0f61071a860032040c0350307443c03100b090b0b01e50300400400a207c280e5101c1407010a56201c90070510804002c0810900e075401200d042c1d08035510309201039000150b03045440044d0130908044 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 189558489 1250 189557239 189557267
    0x7050d0605100314420405150102070806010308070b090f062511102004080c040b061608070206070b13110a0317030408040e010602030301030b0c0408060402090402031618050108010c0f 81
    0x1e543c40044800011b42114400c9039400c60015000d82980401c1d641000100d0241038071200500c071315411616401454050071400a100704007820024404400900507984580d9514080302d985051250f003010b60440790119410429000300ea28134001c5e885081c1d841014000e00c805400318a20060790030004c2d04036111100680900d509500d05071903641c6005000903c0484054019446101e00b004151407012000b01c1c8285801e00001114074442809084c80310341c4607590710b51fa0504ca02c04110b460007403440c05042924a00100100d46a403192424075240c82036034040000c210030010092840214000505141101030602000034001802181c201f070003014154102550f4403002c4034085400d80040e001600044010410002c0b400003458014a00e038082030309213401c2c901010755a000c0100041c0c8030355965404201551400e02ca401905942d120f10601e5080d159850449956102043c804d107075481c0034000580c0340030602c00c0e681ea40c401551691444810806c0450780501c5501d10b07 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 189559739 1250 189558489 189558601
    0x30c030f091207030201050109152105011808090312181c0503040b040f08010903082409090f0c06040620011e0c1b080307050d0605100314 61
    0x82002c1080700d030302c060040b0601c2580082010340c1040e02c908242c44c403607508070030000010b01d001c0c0180300c030f036100501000d440c01417200f0648a02d420028094502c2c2c1c2c442d00e00243e10a0094001e00c10040d0007002c02e0441913007242c02915644e10b88640520841007059040d00d161414800130345070041200c490024004824601e03150952070707041c11548154020007820a00080402c00c05d43d00341c5100d0002d003c1440200071000321518003400c5800300402e440a94100080c0040700b08003e1940c4014007440500456050320300421425542c0700400311b140054410840b40300c15070310b400812541036400d00d68800d00e591402a81d1004442015800040c036552505045426020750118814180c1800039010650b81c00000014003803c407940b000c445c400b0304003034070140030580310b000301d0386c111840d13142c21903854020304c0405d402480369420a50b800414003c0c444480c5602d81c00a091046c040415200d043d1500760700550009a5104252100000100300d2907052a002c0000c0351501661a0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 189560989 1250 189559739 189559753
    0x60601140a0c060f02120f04020907030f09050d02010c02102901020a0501090506010e0c070b060f060d020c03030f10030515250810060e010804081e0406050301090b0402030c030f09 79
    0x2a8030010f60350b94240ea01344c529804030f001441440d12200035a00080950000940d0b41816000f055212200400510034507031910b03040c418041d815808035841a4110341912165030311242c00034040c00350100114014441d0200a8546800ca4404e0003002d4054a0013008900b19982d40b2500d000c804105c0a810750180c1000c038804500e0038040d50703500da4482c1000d401c10351706280c0d280c005410003411041040d0b1341406101c0c0040d560340805900f140e02162090740301281710000503018450480340c0d5000b54008952941ca1400c000041c5014000010400c22181c0e90b07100700440c1c082141c4006001c030380c4000c003110150014181500d4001000c1c00601d8403004030600d020681810080b0f4440008203403008110754442142468800340203e03181048000040b43c00080a0800142c805407400600003042c0b107a02c86a0080c401034400d5801106440d542d581501909030380003482508103481c00c2101901040c60140f084038801c40c11040b0304c034155281d96022901e44ac000802c08503052180d60 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 189562239 1250 189560989 189560993
    0x509090903040e0106030b10141603120e0c030706030b0d0209070c0209090d021b040914070311030a0c030b0604063c05010c02010503091005040311010b03060601140a0c 74
    0x4081849444080d00465542c0d240080c0b050256205901203410917150500f00d00703080e521006485551800c610340904081c110f4265550a4130404454050200c00c02d0041c10425401002010801c0c0d11410f0410000d0b424035046500c642d07006411645c540c20108003886540d02030345c02000410703030142c40b070340e110780b116400b0a00090b82a61060041596281d01030218642102026805802c08000d0008501216406503803030140d4031010b000d2089074041c214498507035a11506416030490340344044800035040071901c81e1810700050310811803400b88100181000076190301240d40c0b025540f0745103451500d45410180c00509040c0c0d101c0e8450100045501540e10103c0c0801c100e2020800d414407503100483d0040000030b42c2a80f0041170500411050386c0000c4814810768080c20b060782d4a550700001030303090180e1003545800701d13071510050100b410740c400c04030f07800004010001c10079035070550105580c0c0d507012140603002038144220710f03603441500b4001d429020700c507003480f0500054139 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 189563489 1250 189562239 189562249
    0x403150f020f2715070f08040e100b0703090b0a0c050105040b0601030605040603080d09020109030507080c1302030f07120605040227010c05030702010309330c09060e0f010509 77
    0x6140002d2060380126140c0c40f0f20302581e20210a600740500d51018200050020901d035800f80c00165081c07400c045403c40510081d004807070800365216803034035aa69200c1180005c0d41000741c0f4204170310400c1410118010051000300da105640545a8001c414646a00448a41d0004100400f003040e20051000000c409010b0580078a05c41d0311104050f103020ba0004040b1200c603400b00e0320680c1071400c2080412050001c44026824481e00031403041c01e2800140c03a00030660b0310041151181e080002002c140210b0303902d01c25002281d9200d40c100782c08048805038007040d101c41c103200000c2000304e00014000c00e074501c40024804d40108403d41c0e100001001c0303802400c01d80c0007045852514040f81c400d0320100304001034090800003071a806035101c455684c007a600000f4141a554005282800070141400150380c0015103110840380110404030102c8241c000003508141c00d10328008184e40c060107140e010365a50f0f640302400741d111a0100b1805080600c0c8040c180141040400780302c0e151 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 189564739 1250 189563489 189563497
    0x30c02090606120709230913030c05060a0606021005060f0d0c09020a18050103050405030d050c0d1a030d09121b09021b0f0a02060f21090a0201081503030403150f02 72
    0x1181d25488115490310740c00c107400000000090383c03c00703851b21155100e036461542968000c01d00c484203183c1a0707030300c0c901a1030810700ca14014107a44103284c1041032814254000c041501c55550a55040c484103403900300079a04181c2e400b40e4404503401141c8000d09000070b541c0701442c010321003003030125078078401001264070840e43e450008010580024130803050f4400c2c07030001c09080c0b03403c0080e803916442e400e40788d0040d1000e10820a4490010441c650f00c56000d40744101d11400c0100000300e040114124030800c44540e190080c043c01011050a80c0911241c13811185800c03079410303940d003117503407800403d0001c072004442d03c3c500c10502148000d103501c0941040310b5110302240071413881020711480c1c1304154500d04407940c420381c0c08400584440301070b144071005d00c1e0103158844541d00c1800000040c80520703a00402d210f0030411483c49000544c200c8464000e80b201000742e00d40741002914410b85122040c2c266004210420001e4400c01e079000312441301003030018104500405003c00c0e680 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 189565989 1250 189564739 189564751
    0x613050a15230904080307050c0f07150305090703021f12090f0209010b0408070b2107120c03050915060316090603031209030f0e06070b0c0a0201050f04030c0209060612 74
    0x82d0340340a002240082c150900745180c08481e038400a1810f0b9880940500c402003002c020403130082107002c0c610f00100200344900c1242000d89a1264a03021050b07000e03901c03007410350006401e0070041b40c61884042010010307a0340207081e80f0522544800c40206030b00d0700340e0b9180d0400c000a10320200054082c41604282c502c603c1031129400941d00410440b0081a000210030080c10041041040c90006102040394050100f290b140c0c040141440010351348000c01d611240000e00410000070f61149540c034009140a404129103a98000110126007084680315000c2d4454560b4889456000074000d90041004044500701403d040c040711341e021859201a03c1c940d240c0d14240101500302c01b61400c5114201010446807046440007010707000090300319001d01c40107044554440e05c4440403500f44035049902154203041404180318164040e041e0400154030b0030b00800d200111544a81c7d00454050340c407840c151500341c0800078800805002d0507072242c0c04100c12075600b200c40e40c22038400c00d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 189567239 1250 189565989 189566009
    0x180305092b0524070f0302210901110403030e042712090e060603070c050111040303020a0c050405070c0602090a05040e0309010f0504080d03111b03040906050402030613050a15 77
    0x2001a2810510f000d040700307040c0b80d0303ca8215031020108100700003103039031010f40c2e45001628040918401d900920485124070303001504008041c10b0310035074001080c0170b900880c0080100c408032400112039800b80f800002c0008800b10800b00320341c40e041c0c004400f181d6101a148031b4000d5810321041402c03105200413600c054003811284042904980890003c0040503440811450404000303100c9120003040c0405000c0046000c8080c040700f54480030010950440456a0350b841e410069640c24000c1c00803545061100e8000c00e003410b260265501481941d11541e5013140541e0320000a508500c040981000d03030050b00140c6da90f00c5010305d01e440342104014540e20000000010144040207010105114080104122810002031039080703504492030700154484591840030214851501c01c45a04c128280c0c001c4400e0300301200500860350102c00030444141c2d510140b1090740411194540c0c020201c28000d603500312190032143d802151040c0c00110302030100303600d0440c5036254010040c1c40c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 189568345 1106 189567239 189567319
    0x606090902060d0207230a140d140c0102090a03061e1b03150f0b0309070602061b09031009050607021e0604060e030409141918030509 59
    0x50711b10444821000d50f2582500d41c1c40280513001e5409a0480c10001c03541310700080d44401e0750b0200d4070340c4980c40e01c401d10307000c4942d00054050030031550200900034059803080064006140b0070ba800103105c000100c0082d43e956030040c2d030ec00d0130354035009107022400c9480c042030780441c80d54600410722154906020300d00111300d0f80211880590b0034004203a5080c2c090185101c0c10078001104c2c0ca01d5602c44049a8a00c01074030200700c0085144464941180031074020001071350702034200c4070244804605003040301d101000542d4540c011400b84101182e041c05184201070200e821440b2200c04080e5180e07c0b01400f520040071280d8516085107203800600980d801443c0701d400811202e1001542410b080500711840d60045015826081d8030003007a1180d000c1003a95440c1600c0702c207101e030703a05507081d41c080d8035070340e90110040203441041c03410042c9110b9084210710020b5a4 = true := by decide +kernel

theorem cover : BRFrame.Cov 189388489 189568345 := by
  have h0 := BRFrame.cov_init 189388489
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189388489 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 189388489 ≤ n) (h2 : n < 189568345) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
