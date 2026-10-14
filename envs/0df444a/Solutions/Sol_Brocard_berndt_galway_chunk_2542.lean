-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2542
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:01:16.810978+00:00
-- url     : https://prove2.me/submissions/d73d379c-5964-4e65-a274-21a12ffbfbdd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 457014388 ≤ n < 457194244 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 457015638 1250 457014388 457014403
    0x30f0b060708134b060f09090b030303340309021f020606191505040806070c020109030305030903090d06050618040b0a0b03031b01051005100c060b0a030218010503 72
    0x110f01c2100b1301140c0d100030b0088000120080ca05440c5400201e81c13080006038003121551201e6400203055008103490750000c0e0400c05080054495139100751f607601034107051b10340d9003110a4041d082840800c0c07801241526460b2400d42201106100902c0e60240d05008104c071100140001c1d101c900240645c240038400c405040c003016140d01c0e812484220281d918400503003202e0080151310031101d0600c5c00465590094040300d0003040d0458600c49008019800c5402805198040c0c503003c60315132030055003a6103440c0da0607190606c200307140d0f44054545070001402d80700640800c01040c4525580d24240340c1c0c03aa4450040052035081800c00d10513007020451080340c0310103840d000c2c0f10100d007110b60050742c85051a48045040110340b4040ba0840c0034201442c0d40909584c4a451010742040d001144100964a6a02d240741da0320313020440b100561402e03100108016001c41d4000c50320580290b401c0d000d001d0200302856030b0300d601007080035010307121090080d03c4032401440381b0703d014401d07072 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 457016888 1250 457015638 457015649
    0x201120e0c041413030e030106050a0905070801050a0e0f1504050412020c180112050a170315060a081f080a0c0306060603090c0909170c0604030f050a0906030f0b06070813 75
    0xb41c003d441c18003038100191001880107818045201411030b1542e5094020501505019101c0d018460380c90036481c2c040e18041d03984401041003040081254208006a001250400b1b1000100c0751180740191141d4013001d0700c60514004507031a040d0300ca07152409440e01440c412108506401414800241021840d0131040d2064001c10302e6040d1254034440220305442280c0340f030008621161030424504078038200002c10408154802030490300c080c0d001b0b1032090980e0702c8000f004100c00c80401200c0d00c21703078032000045860000421550700c81110030803c21489080041240382d1910034280c6000041c0740b007143d2030015000b041c820000140140d100030700711401c05200c001102e5561181c1448217000d034010355660313004440140a4603031404d58400c6400302140355150305e841c401a4a92008403001da0100701c21000240b4000d01c168201c41c90010300e9520000e9007410b18078100c000d0007801d0f02032034446031901e07900c1c2050b903203080040c22aa40f2910455540f800032001c20030f0602600d500c034 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 457018138 1250 457016888 457016921
    0xc04050f09151603021312140d140d18211814060c03070b15120a020102031b030d02040f23062b050108011e05040203070e040201120e0c04 61
    0x41c05494000c0091070190f0088906015869507040840f2804004d100d502403580c0f5091682d0707000c1445070403800041102030b0441500c180c20061001603840c0490300c25840d170703d440100229451070800707134402d02441d010100942d44446183e19540c0803508640070a4030780720b40000c0355215180d004503500741035011145440094134501041442241c81c00fa103000d000741d50019003400300030000d20442d024954031001006450502c447d070211100c61803160350b405007002048280d0340c1304000407040b40050341640114030b8024000c241c1220b018203000d44a0062005010700e00036080c641c000751001c1c080e1102d0960060707140141400000781811020850f05046940f00512600c94404840c84000f6402d1080e508207581d01c040343d4000043c004201c4401d1900d800480d00f5041034000b0324080c0200300030f5040c020541011102110320640d8025419030200f2400c2294900c0c401820350b01900505040e18080c1004c20000191420562845803e81201d42e011a440c945032103140c124401d1380340c8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 457019388 1250 457018138 457018141
    0xc0a120509030a140f03090304090608152703071b150944010f020c0304030f0f0f0b0702070f0b1804060902040303021e0609060a0203090c04050f0915 66
    0x2101d076200c0c4a4240b44108010240104207041d0185904075090040e00c40340c010750300e16100500d55200e4101d1302501c0f504c2410300c940003460610020301281c42019051118a960301e48080d9100041d4101801074203440c2d81c00326081580106001500801c0d015080d05005441c00b01e40b00c104130412a046440034201d01c44840600c5a030000d070380c0c802d980100081c440c002d95680150398041844203000c0d0020280401c00c20f2142c082000c0038a03100c2c820000034003d050800c40090300340d002c4c0260100596006200070004500300b80d9000f903507035015440390800e0070f00315160800008174034103040d80d41d100200144602c1ea82d0410a0b00006c11400c01a14105800c1c0a00400b02d84100d040081c0c081051024182c00c50380c9a60207407000b802e200c0000c56495503070f4907003c2c0d1a000408515642c6203480300803403018074404140644550284400703001030341c0c0d8504442d00203400c05020b611044c07140c0e060343d1020351502e10449008070b4810080700c1c1240b40080740c81d850a9181c1015054900c0c4850 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 457020638 1250 457019388 457019401
    0x1110d0506042d0902031905031e0906121302151905030601050412022d1c051c0c0506010609141e060d020f30040506070c080904050c0a1205 62
    0x141203d03d4005001c3c0c000c01d0f5001e00c0d0000a181060015110400c0220422120200840000205400c41b01508140000d01e540341440d104c5010303881411b9000f07501081481445103144040039480001e004c43c1d0710010300240c007c504030340d000320f0400030000c3c1d00285082c100041da1703a1244c40d01080e483c01c58503620b0807100091241c0200d00c00c1c8400b84495840c4a411941d40121a00c8407181c1c2e400d0522015000c4046015403c2c000300a0f540a04083d0001030808010301227041c50f410303000401003031804144510240700d61001c0f510041008541c8030003030001001071006a0007484156180550366050004144151400c214024031540b4000001456a251a444180700d80011640250ac62403c0e528100180c0704e4078a500b00c441000040b5680c0c0d5402d01e03001b03d1034000d5000300307440700005102e0f211700b20603405890241c259804900001c83e054070034003030800140c3c0b00d08070300790800c8006004101590815103010321030300004600d03959403542c400b0410100f80103e44050100382000d5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 457021888 1250 457020638 457020701
    0x5070e0103030c02090c07120302040603061d0c09060705100605090705160b070216091406030607051e161112031e0a09030c0b0c0607030c020c0f0301110d050604 71
    0x42c200902907545c4400203520b450703120090b6501c80d038000a51f0441d00c07168000040c000e5109005501c0801d180180c0030884400c05943c010300249482c6038410107490b00f0b41c502400d40c201b101425401041042000c000030001d00820100c2000b00f803002c24250300b8001004820704000300b1b07120400c0b03404e00010750072542c054203058206410849005540c0c4483c0320803824000d44503858040b090102e40009030300e80c2c582c0d204040365200010011203d4891504040c1c550400f66032140010b40c1c24011a10761100c00c1c560800d030380300c045d41384600d0b10148915000050450301e10540d01c02041c11080040e506040c90081e0b034001c401d8005d9854184e82d0711441c0d40000e40d40d03019290b445404542c1844a500a410140145170850070119080740d44210104159001101000d00703030203081d003c22282030007030140c0e4031290b005401424409049100780b08500a081e03224540c15902c5190810b0ba007003103040101565078a0b0b41d00401c440c0780270300902003510211041403600101402d107202c0480520f = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 457023138 1250 457021888 457021907
    0x1a040303082410050d0e100615171312031d07050a03030c1a040f06231801060312030e071d060105181e010206070906090504111b070305070e010303 65
    0x126160b8455152243d0119124041c1c94400c58240e46448540c04078182d00181c3d441e074034080b86a080c00b02c2600d403040c01045201c805469404140c11079003440c3c0d0251108400d0381d0100240500b442c6824103500e6810148900120a0000c80e40e204c81ea1040702c0e81d10b1980380d9810b9400c1c0001c01809103480302150b4054002d01c0090100030b00640c1140070031441d404454414003a11555150034201030a040d00800d00b4428103c40461600c5004440c5214000f0003004440402c06032014503511041c943c0180c04440c62010510f55844a010000030303611150003030604501da80c00a41d03a500511018900180c07500070788681070040120700c20551000c1310031580282d080c6000f9407541720038811641071122405d0a00d500c402148000418410542c0840d5078071b0b80241e003152501d4136050401d03118403201c0d000344000074822880038491403c041c0c0080183d405605c1c0c3c6545410068104041f40d402d400f02655142d0b002a401003003803010030000c42e0041e00c06045414081d51460350050142000d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 457024388 1250 457023138 457023211
    0x203070b2e03020a17010917250507050f040209030106060e0a1719050a05030703030b0f180f150910031a0906011e0305011503021f0516020a1a04030308 67
    0x302220702910201c00b0340181741c085602035400b6800c0d0040b230b50010203e0300f008140c3c9040c20002d401d1000d4003101500c0c0306400c0e54106001e0a071890604c400d0040901c2000c51142c0c000c1e800b000092003c0d1000d00c142802042d442d0f4501c01c0c11280d04040145080191780100d0b40e10071601506a240e0001182014084080398100349a031045e910380281041c1d64842c010304580000f20b07a075001c1c5501500460306071241110b0313138110001c60008102885422100303405040c00c14070000760b001d00c5001034054002c041c000e600450300200000050304017074125003166007640700c81e00400c02c000c8074840701200c800300350243e0852413824000203903079038805200d00544125444813403030301620000c02c0352025542010007406152522107a51641400e00e100407405041d43c1d42b4824030340c0403c0302d80c04007201c080395149854140ca0040141409460000503070348254120070001310b819080400c507001d2815080036980f80c1c0d20f103090186c0740300b2001b08a081c11000680d02c0f00c44820850b24403120354803 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 457025638 1250 457024388 457024409
    0x2011a0904030908060103030906020105160804030309080903010207110306160804320303150103020f0d02130815160801050a0303030203191d01390203070b2e03020a 73
    0x5640b820121400c10060f4020421402120004400d05500191180682ea40743d002440651509100044204002031888000851000c00306000070f2007600310b144150301034200e56040900410000382264018941160f080460301c5081850307060030710001d640041801c4c6c6c2c540c05990a18000f524061000304014111181166101082c0c10814003107030402c41c140c444400c0b41c006403900345550340d00541c2c1c8040407050902d100c06103903210f0700817900100619001c4030308104003c89044080c2d000800d40d202410514a0080b42801c000c03ca04001190f8540b17000f405400e000800040015030341807035600304403c0c440103002c0ca03100c1102c0c0c0400c882d032510b80140c0d42c0c0d5030f240d04030300e181c640c0c3c0030303140f150b02c1c00c2400c0250801d119401041d0100c903000d00802146003000d490360b038101c3c00303854017040b00d144007a914460140101500d9161400b11300503680303411a95510b942034000c04443c1c0750100e8850300721907078507288051100094001100c1d20603280b141907030001915001c081c070070b100317070103 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 457026888 1250 457025638 457025641
    0xf23180634170a02100501090b09090109050316060209100801030308010e04050622020301150602010e071401050c0f030a0909050a20130f150305061012050a240501020d02011a09 78
    0x3c0f482008402c0036034103075074810002c03541c40701d5035480078202c1001d45a11035403114002c595a0348040c40341d1442130342d03c81c00031440c001a44044045038419034609403603caa080c04541099114022000384040941c1e650700401d60445c45c3c058214141038000c01e408104d07510401c000950001030b8640c1014186165044141d00c80b41b51428000c08818000d4041d401d00c840740f80c3c0400650202815111a60020b1002034603c00005a030351590348a2058210005404880306500030030080c9020454541620b1680f003804011350301e140d0080b4949400a05c401c3c0b8100510005d51041c1c03608000071900a011000a151100c03503030700c1c0d60700f2401c0c00c00308000840300041d511168400000703205500318114442d549915403440024803040d002c000c241050300160080c9441009000c6d22442c4d521601c00094440d11294000c0000603c4140240d56070424002c11140180076130504415062200c5d480c2d5040c100028103220f60b2869080540e81408a02d01c0c1c1d511013819625241581a141c5003041d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 457028138 1250 457026888 457026907
    0x60c050a03210c09061e0801140102030f16060c050705030a080901201c2315120f070509011206150510020703030f2318063417 56
    0x314440d800310490b40d07490000c003e40c100c0e401191200440300c030f544400b48014901d10300c4040282000c0f040c9000601c506006020f214030219284a903004184101ea050003120200c540c01640000c1c5100541140d02501c04104849401883d440031103074505541880c4807a5a070f969280a141011300030300c1a440d0004074032607025801609481602a54420103c656001c40e1140b6807100c0f00040c1071010906c0c440c820300000d4000c42c0c81c00004441e4452201c03031661049600c009024040c010144040c4125040d16a246000d1032440100750f40548003454001d010380749081c5041c1d01207406000c21400402000c12106031801c01c4130317003041001c00c40e2902c9006031002444d031900801d070300440c0904511001c0768002544016a403203030303d4182100d030003144162010015500c8030390202207102c2c62250002e007090301034508480b10410b500d9200240400051940d042100301e000418003240100c0000c4041a541d901813480364154054000102c0e1601d0310600c1e00c4042d86104c0c160005200c2e503e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 457029388 1250 457028138 457028177
    0x815010b1810030902011d0307030f03030b0a0b0307020d0806010918270c0806040b042a08010510051f03020c0313080c150a320309010b010207060c050a03 68
    0x30a001080742c0300c40c528035a4080e0040c0a032810990000b110a496007009140042c10500f03000d0b0300400800c00a880c607903840ca0010b046030720031070815456000c10f43c0e0523115003400c40c01410f440300015440c1d103400c810007441e007000484035604101e601010701002d0790b0003c81c007034113584018968000d5013074284030100280c01c50452160130100724007101c0c251a031000204d007650740d21500c034150140760348081d01035a4050a440203081ca152040c082000114504004d02c051081c02030b18100004c44c2126002460110f1741c0115466511403040200c00708030b000120010703000441d008002e98110a042d407424600b4801c515003419400141802c052604000740c8007107035144050a8081500d07a450300703440f2820005802d00402e0900700c048030741d0724000d0507281c2081d5907584c1d0340c3d1981c00c0e40c008400caa0b0380e4504020040450b0501103544241044003c511545880c00046401480710000911f40040c50340110200b000d1102c2110000b003000c651800c099802d80781c82c0705041d40c000c2440c2c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 457030638 1250 457029388 457029427
    0x2070b0606030901110f07060c020703050d54060c060e0f030f070b0709030f060c0504080d0801080d020307150507020309040f0f0f05010503070e0903070f030809070815010b 76
    0x201d4901006c0b404501c0081c0c80c01c010b01140380301d00341c01d014200c071040e400d80c3d680401317001c010410780002c0080f00019120381000d86564248518000e40609c065082c81030181d010101c0c00b9507100c44c01121004100c0d8146140200000d40008030300311440c007180200b101c1820400180200e80f20020b9114841303041214002d0080c000040e280c0d9010104000c181d207602c02c400844156401c400024005400399031000d0840740c011003416203001e1030741d030381d4001480c0361650a03003031080900011910384020400c040c0d0400752a141c0c90b616506203010f807440c2004926a41045600c20808580064849062840d151007a0075010a06860303c4100340d0850041040d6207030041e10700500800c403804503800a241300d042191040080c400c0410800b0241d070007d005880e05584064001c015907582050380c0c50b481a803520503039007000701c1030b80e908000c440080015000203800381c007401540503041c483c1c00000d1800c400280b021001e00b00c0191010f140510600322000c00100e81c8245402d2206c00c00b0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 457031888 1250 457030638 457030661
    0x603030a020a0b0a2406030608011806020d4d0901080403030902090712050f01150c03090b0409051605070c05120a0f060218010c020d020907110109060504110402070b0606030901 78
    0x81c5d0f1241c1104144005901ca28400c2c3c40000b070400030009468081841080c0d81101c0420060501e95190348894000e5072111502084160ba211b104510b41010b131101340d240550000c92405904071802440301d59030308050b40303104400028224010001c0c060000301c3d8004c00c02801c0440d45075656045c290020101544083d4010f182c0108100510390310104054040040e11010002916640c807003c031120b009016802c4c400700c810303120754015400f402944030390900ca403500c80003868071004414102d822a9000984c00303626001446801681c045240c0c1a03030310240351540c10044152110240c0c050603200c3c160242086040d1103110000c1801780021650f046024000c0007241e07490250000d41c0010411483c4929491f0840c0301584140180003059400828181c401100c5400b00041f4400281c180014400c4203941c82200040c06c0c00f40922550149100041a14081c100310501d00d9071109021300c180e104201c40380006400c800c0781500103000b514481c0d103d81d94041c40c2401410504a030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 457033138 1250 457031888 457031921
    0x2042315030a0c0813030906120b041509061a16060b0d120e010504031725030e04060b0415081902070c031401020415111c0c03080603030a020a0b0a 65
    0x400c002c28070703103420100d601c01542da210442c540c0d818070106401a0710480c005c00160968000f0480d0307900c12641034002100809002404140440006040702c200021644411030584000c00240c4014441c0400801e21810352101622114441e050a0301ca510751500214400700b01c008c0600c01c0f10b80c031544401d1009091441020043d0410740c91281c51000028000741d10601d1141d5954418810340e0100c1e64800e900c001402c4400100c030302e4540010104c0c0d403481030004603548580e903c80c410070003828001e40300c01045002410500055414030b4000d01c00c4070204000422641c1d90201841d607030301d5802c0c6001c0040340c4802e204480c0606c400e0100d0b10903240045042414040310004120440b80304400100c800d00f40c0240c85400e0b8011fa111f0360044080d20300689900f54016521122a42900d000380d5140042d1409c45480001c00303c014000050031401d141c00805803c11705941d004a001c50045041041000e0000d40e28065030900910501c03a00317011962800440c2c21a02030500c4c00801e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 457034388 1250 457033138 457033141
    0x303060b040b0306030d391707060f0614041808031e01080f0703140a05070e0a05060109051e0609030102030403050c060c07120e031c0e01120204231503 67
    0xb142642c0d08151040c521030300a092a101800f070091003100c41c51074400a0300101c846404041240f240d184001c024400682c841c4070320000b40202c1100705e070303052501c81c0a81c0c1b07912103030503d001115050208180703c5890114180104c07415001072a03000b00d8101d40c0130900383c0b460180301d2032900300d03580000c103a8a008024040c00c55402083c440040c0c008107044c0b400380e81d9441c0076540d20b005903460103010303811a1000748081900441d44210340c0400404407001c4100503610186000d400b0741c440040d01002070144104c0041902845402003c00d10307040314a24100360020f0a08200d05029050741c00304000c04202c0c03a151a42030355207507440203000b1916440c0604010b005e590000c1220b034076a009500000e101585640c0c180e0703070050b8000c07406101034160100245c501e01d180704200d5500d841a2021803e0b000c0303410305001402040c40e9034200030005044009010406840b60400368180140400e208464126810304410792382d440c3ca07110404001400303d03117121106142409403020020 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 457035638 1250 457034388 457034399
    0x60714070609080d050319020705071a0405091815091204030c140d0b060913050607021b040c0e060d02090306040605010501080f0601081f2601060b1608070303060b04 73
    0x140c0080456460f041a0340d2400700e003076400c940341e1008540c0c041d90502d215042552110303442d40a401000c0c450411500380c10744610380e60814000c0c0742c82035080341100013014491414903000d143d4104626045020a18500e00d110580382e403e1404150050400030b000a1032501040112040c280600003c1c903a03600c0c1c407420581e40881d55406412641d00006090340080e0504100c01c2903400d80055010090780c413000c0c10010b45401c054400305c506421003000340c01080d402c0c06010701450f0039130005c003100441d140c04c05a101c0d0300b88000302c0c815450800b0803035a079504050200c8002008032811a034401c201d01881001780140107803250140300b0b141c100403c05c1060303803016040c3c810136210450540c0d200c1c0300c0d200a0b10021114140000e41c4272020903c0c071401401d01c01c0c82c83d82542d1200600c40d841c0d5404002007003541c54142d084058400c1800f810f00801c0c89005c3c05484c801d50840d00d800c1001030320404071908900010454080001c5080c2498405d910140207050309451441e0740782d5980 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 457036888 1250 457035638 457035647
    0x9061506110d0203041d10050901080d020c0f0310051e070f021b151b060705070b100e0c07050319110f010c120b1f051207020f0601050607140706 64
    0x2845030196204461288002e5800001503a0845007610300040061001240149081e240505450101c1c40590b4000c20f46503070700051036001c0c0c42003500400030f0003984c64001385001d0700c0c1412a8092000c2c20220030140e1130101b00d400714500b05000201c0c0030f4480c2c045c04400481c0500d1704103100c0365520140003c0507070152010a100015508aa4200030032040e40e00c0031810310944260300585404100c081800d0f0000902070452110f44004010b100c45628941010f6040707030140c0000310001500ca00300304114100b40c0c0c20240e03074005107070864280000b2910303035180500066445003001c151141080800c00440d001e045080d18020402c650380c11016182e02c45180e9851124051000c4444c0d21400501c62401400a651345107030900102c807089000400c00004000e820100d00c0a00c086003501c184100307060441a0341d03c2968036560301080094032030014007918210b40103603201d0300d9004400100241500c60864040ba81c0d100945480448c2050084191a20303000343c500c00144184c01 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 457038138 1250 457036888 457036907
    0x1e0b0c010b18060303030a0c050c0a030915080c16080d14150d0b060103050c07020301050408030601030506060c07140d1406180304081c02120d050105100302190309061506 75
    0xa85125441110b01c2501005001044a02540651050001600c8031040e0b0700640c0c11010681085803030320b103400c01c8040c00d0404510003135001c0784807040104540ca640d43c9180401542602d084034290504030601440c1d4803540c040500e045416418183c2407100f11011503401c3d0b00040c0007042100100110300e45601d03c11202c0040a0038100c0c141c1c451407c040705d0402c01c507076101e22914425134580b401580100300103420301000c502c040c0140d5006031401d00c24a40100c1c00303103c110751a450201c00040c240e40008090700c1c010b82045c0f02510990400140540644440e02014030103c80010049880d2544e100c0000d0402d08400d6091103a002c00810498042c1400b441c00c01041c540300c0120170303074a100e103100d10640da51041255410020081414242c0d2540300e105036840303a80c140d00803002c03d070010080c9209841d511b0300100400d140071074100c03004480609007076040060f52145103800980010a000906480c2c0c0311284c20000c0307a038001e0114042d80a241401c1907290000185071030380 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 457039388 1250 457038138 457038161
    0x8090115140307230f0d0b0403030c1b050708010f0c05070b041502030c0d0c0f0905131d06160905060a08060a0b03011e0f030c0b0f0d020714010c03151e0b0c01 70
    0x10115081105091032060b2440c46e60308049a08415160303568201d00504144002008109148090302d034007804054508099034000d200411086040269035401c5410290303117103506070b140c507510a00c81d54000044d140c099400a01110142d40d450410798401c000c00c40b8664a00c80c0f0002c1080150380ca0711015109042891500700491403450506582010010348800003040d4184020002c80c50605604140e541c8100130104181e015034080d89442c0c2004042c1cad10b4250401801c0007903a2802003803c007085802c03441d00d4043d140c600000f04480b48600ea08510803c0382040000b810350b1940302c03e52004041c0c035050380fa900d40c0e5480d540c400c00c8000040204c2d0155484c800010075152404014080d00e82041114000c60f18165044480d58494481d88400741801e10005c4102042403001e000319601030350714113407941201e55000742120440c030f8006051503d080c6401c240004100354800a41e08030300f00d50205026400b01c11017022503d81c3c131074116194002400041d008040d040010002c6 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 457040638 1250 457039388 457039399
    0x609020d140a140c0a05070212150f2401020a140c0f15040e040515040305120f07020706030b030c060d091712060427030903030809011514030723 64
    0x4942d4000b200540e000318600720303601e00d0550007058041406200810340070903182810b918046195011901080441186107840c3d005500d0220f42410b5848409503c541d160020040c1450040507043c48409883c901e4050001a80042681ca0b4020440f240d00160020002c0780f1988100c000644e54019950315a80a05c503a821000c4060030503a500b25600710381e152040c0c0c1860305015100d004c10308003d10951340c41c81030741c0707810000c500c42102e00c0c0d000303d00030b54a0b91703550f842e01625201c500701c01a02e130f807101c1d1120780208a202680810b100c4280ca00360301d004200500c070030340003d1a045020380003640c082400228940c40307040940c02041d1041c864050011107106514400304a80a100c4e00401e500f101640002d10b01e1030704da4408072020030005900b00303102d4119035021625184c03814045022451074401482072540240791247d114015000038000d0441050042800d0400b40c440c04c0321041c0016a0314419603418400040a4030b150019030800802981143d01403c203050740450041 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 457041888 1250 457040638 457040641
    0x20a120903051b0a090c050319060b0c0c040506060a021b0406090c030203061507172511030f0609030f0c0c03030313060f020f041e03050d03090302070b030103240609020d14 76
    0x11a6004006c9044800d4860314159650300300c8610484840c210009040c681c1e520001c5001d941d05c60140202440140080280c84581420b2001b04e80d000b600e1184500010f01012442d40e50006510404441c904888400e2048100104000e09241d0b008152820304021102190991544c00f65215800845100c16810004262207855114526010f4100f6490303012010501e22108000e05503400026880d03140d940703c0d1000c0070194180c0c1c410032184001460b070002d1051500704140191302540e10090301840c2800c4001d5540e901c5029543c3c1881200451159802e5009200b030020001d00542901c0d030360700d0400800107107800200000c0341c40c2440c08411a403008964401d854100340d41840b4586890308010401041d0220000c1000b8030b200000780110024100b442114501c0310f454902103840d41440c039000e400e04005421081c131000302400100041a56075001c0d01381c1036228044075280003010841d09000d0305260f00140c040c04c0c0000340ca070394203c0340c45c0e1100c142241001c01701d80340b9 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 457043138 1250 457041888 457041899
    0xd0804020f0607021519120510051905030102070f060e060c18030c0a03030801080d0e090403030e0c0a1e05030a020609120a0803130309080c0f06090307030b04061416020a120903051b0a 81
    0x40b942c0c203a0307272103280081e2800c0a100e107091405a03c04001c010b4038520103690396130000607003603a1203444215440041d02c44101c041150030700800701c5000303088000d0612490070200d00030460042d90414107803151540001241303611b040c400690001c00c040c020301141501c2e401c018001c02c40a00c2426007d00c50410a001c0300d500c42c28104801801c020002c98140d2150b440480150801da050070380f8038001d44035140c00d03e9032107542d0000106030088200f40005209030b1102d42c2000240d21003030081d04040d17a00700069840508031008d0403800c0380c0c103420815140400500d4000d0004000304091800024065040752103090f040c03500d44aa03171815942502c85041e942c0300c030040c2d1501c6411070980c2071203012078078140000d090983e0000d0115103030309941e611400b00c5c410040d03405442c515170702e1703220b5034030010201812a446500496410304903202d0348002035540d0a00c030300241000506045040080d480340e80000c00850300102260901c6006c104072400040c44104140d00c1030280000000d01f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 457044388 1250 457043138 457043141
    0x40f120b060a0e0610050c0303070e011b050c041a0306150901050f18180d0e0405010905040206070b102303010608120d02090a080d020304080d0804020f060702151912 73
    0x750383c1d40c404402116207941007402244600141c41d217040c4602440440b0003820b0030005540318802c29518003542e400c1d100e0000d80310750005201c2c0c415442c1319190000120b0000514010320010aa5000407406040285000000002024164180551000c2c0130480d0b66442010020351011940c1075140d0f40c0e102c0c200316098402e000c159801800413801e0706d031100c0700d002506511100c0e031458000406800c1403154103050b06030035640f000c00c101d007519101d2403c0911502c1e000d010000420441703030400e03400080081c040c0180003809000d00400146054840300599402001202604a0722440c100d40707000341050f960340d00318000d40c81d002d03000501c3c0700006000f2600010801d82d03140703440281905c0c00007070742c0541c0140d13400c00019800000d500c50100a40448003103907034095911213051129040c140351085480d42c0801030040d05110149c1e450040f11212004100d4038185d8070318040c404144492828404020100700100350b8072039103519641000c9910865540740115050680346110 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 457045638 1250 457044388 457044409
    0x3041409070806010c1104060f0609150804080714011d060a050402060d020a1b03051b0102030402030d031e110306030d020a050c0d0f0c080d0801050105070b06010e0105040f120b06 79
    0x20000350b4039101040295004d400070ba11320600841008809041480124050780d42e02d90100780000303080e84041044a0f48022400701601400840001c0411114001071580c3d0002c0c0c0082e250680004040080204800c0c040000c905c0c0703c0000e0000c1c2d0340e07451020401c0c074113000d010001802400d0005094600d80d1244511035076004004e2418080c2d00350750322000350000300071102071000d155043c4d21b01d11300d4a82005c0d041c2c1c2c400e80c1d074150740c0c046444401c80103202400c0000e41a0380180300744001a07802040c589a102c1c542d150028402e941c2104028541a5501e45050390700c0c03808420400548140c001548180c0050382115000944031b1812641e940c4424000b40482d040035014a14510b400d030700c00030010f8020303400300d0101e40e029204d1070088110369205210690150f02409140364205202c18010708003400d00314200b01580c0c4810b100220028605810411982051001a805803040c1d801404d0040e0b200a906a21600c101481c03500300c440507108060b0032000075606151490010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 457046888 1250 457045638 457045651
    0xf0a11100f0e190e07021c0c03140d090510111e0c03120f09010c0908030d0b13020c01240302030a060b061207080411032d030706020a0203041409 64
    0x212071424826400320760445440d070005501c08404032041002d2040c0015900280c0300c48807441c1d6140c10709140c081d2030304c10003c80d1102c6034030700740d4400a02070b42c110101010703154150070544400385854401640b035110b801c84c9140382500e088041d505000c1c3c001038446507807c91110400009406840e29100c0c0d008048644060641504010303020141c000041d0804009100890b400c14060504041070800111080030881007140100481540240565000c3c2a045d0034258042400d00010603168441c03032002e4000a40c68005414003511850044110800d019100315203844a51401a0103895070700e0401c10840c00c40512013280744545e4400800302d80e4010000c0010740000e40d54031006e0300003019a50340c030420178064190700f040f0300e4010a100d5840365a40c0b40092811b4940560254048103800d40281d02440030003031b030b6500d1408903520702c051024088203900d0380003041a146d48500c0c90000c0409001184029500b0780000181c02901d40c91800c0c90942c4107040b00780f008039841107410 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 457048138 1250 457046888 457046897
    0x1080106050c030d0207020a03121d0901030b040b040f050d0f080a0614100504052e021606110a050f06090625030c03021204080301090b060310030813080f0a1110 71
    0x2241d41c3c0c080140c1c0101440e1f0f2000d00141211a40c98480c00b0019501461002c00f041100c840240b04c10104000d4040e60582241c0d00c09403541541c44003a204080100000c003050341e0203012070180140c0c004055103c55003d400c580000000c13402c02441700840b4080d69000c01c0c0d2520214103407041c140030b42026544c43d06c1003d102500d050042015000303112244005108080101040b151500041e0201800d80404280794880c1da06441d031700d020306100080c404540040c4c220b03100c0c54008050400481d10645000180381c00c04041680c203040da540c400810a22402900708103501f07012845038456842002502c40942c5da071115150346548500600c0407078000b0103110300c5030358000d03800408002001d2600501341341d4030b5914860040c0381614141e607103a401100410501d006070049101c1442c0030b036145815418540003026485085000040881001088006105140007608c1000700204401c4a21854000c1040e41d207507c81590b0035203001080502140305400c003880c0c3d09a078200b03240d44 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 457049388 1250 457048138 457048147
    0x90c020d080c0a0c0812070507020a051903060225050705090f100e101203080f010b0906091c1e0201090902070803060d03050c12090a090b01050f0706020409051501080106050c03 78
    0x204507050080d402c1c0848500600b030041c6c0402d091031507507052203554140c81c0c240d503420b01c40c010130806c2a91a48000c2c4545201c011a01d0658500f40c03815040360340c03046000da01d85108941d4140751022242840700324226001e400300c20b0010001d100e038125501982d0f098080c0d101d004842c0c0d50020101ca00f80b0441c0702c0280104807030011510541d84c00502008407041d0607403203030340c040403051050b0b03015000541c505007400314020408088600420340d810640e40740040e40390100b00c25004801d400c522402c2071403141d0001c0f20070f216002040d1a480245003526003c04003151090903041e40090740041c005110100740000c0714800c40d40071035080104d4504644d11901004034101c14050b0840810409100c0c091040908210784800e901100c01e0075501e502c007000a120349004554405841681454035004450b41c0040c1201c118066840e000d545e20341c003d003003c90207403140c3d610500e409480c005c10030017502d100d800728102e5000240c2c0c03814242d913615141201c2500a00f806564103810800 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 457050638 1250 457049388 457049407
    0x1713020303270d060e070e0106020d030513021815041505120f01020c01020a020105100e01030318030506010b0706140121210503190626030d0501090c020d080c 70
    0xc0c0c00580310001440d2002e018008102045410100c01d000300c40e601d07102c54465902050900004005e000c0d10501e501d0650701d8610025501d00e00390102d0001c3c190386d080842c030f40c1441030560042c5150040c2144c0380c641c5408404c2c89080034111401c00340d80350b2400d02410b241c074060180c44461041d00c20203210b154101010040041801c11420106100b03901511403050428000340c260b00c05010b00058607200e1380300d0003070f0035200020f144140025402009028801d03d003103e080c192a01031800409410102040141161070350700702800310b110341e0000040820010004013a031510800381480000c40140600c008401e00f0701408014540c050050348182e40c0384041001e01d94055035241000400c108090140172100919450004000004000c4004200c03800403009001c4075a0130001d00307160003d0648281d04159048507103807400c501070341c02c3c0d4a0402c15541088000f2000b04601e5a5030004580209202d0840c1c0c4094012840c800c9400d50186180c1440b031002c0200c0c0c41e00d40000c00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 457051888 1250 457050638 457050667
    0x10030809120a051506040e0313031e050f032718072a0b071103030c0a140307020a060501050612010b0c0307050d210203190e07080d1713020303 63
    0x210300740c068441c080c0c5510108200f04160b000f41a82c203450740b40d5504243c000e1005603240380080c5100e9901c10000d001c03462480300e06003802c4a8004504003c102991156a50030b54202c0b01c4c043c01a1203201ca000140350808001811902c10071440004488540707034050301d400c440e45519691100c20a502107104100f140c102c198089114901192441813078015001c0100d50f02c100c0d40303100d1004540060806c0b60320803a01b90410b40310300702000010700d258061a90b03032000504000444d540030440244c140d0184841c1607200780e580b0362964507131410042c002d5441d4800c20381910158200000003410303003050030481d101d441d20075000c480b80382e007019044405e5a000050324001131000300304442c0403880520118038544030584d185498000302e5003882d07041c0300624811170f01e0f00f441001841100025100740c800b81600600001c2001c004a0015500382486684514203d0080440038107034070350b018ad1f103001405489071610546480701e40d00e50312400350507138000750164010041c610465195 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 457053138 1250 457051888 457051909
    0xa0303050a210207060209030f01090c09111303080c0628092a1e0e06090403022821080105060f071208041101030504020102120d0e0607020c01020610030809 69
    0x2440020079810031421041240c1c1300c09001c0d00c1190340441c1c50001854188000002451414024040205540c555014210031741c03050146c0302d51340d4909411242206429142051014601181174030350300d007008045940110709042640c0121000580003213500059003100c10308003a4000c000340b4011100d08004d03c40c030a4241e440401c914000c0708001808403146034102c00c00300489982d6171910007040c0c0d035001265500002010380e020b081c405244032000d842c1e03100381c0844c1c14100c243c036030f41016824800c14405505e0000c0507401c900c810a08240c5c51075010300d00c100288410086980406030f194804030701c0c2000095503080c0100107625101018083c1030b00341441070780ca008001d41e0380c06002940b4100000110b0460010041800715602d0070301c803d140203090610081c41c0130340c0000e44031960b040c032603100c400e030200f90011500d41550180103001c5900044421301c2c00c045c1800395545400c0304c4418014441c0710700084054503040900e00403070317a1150701103042060380340c02c001e404040c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 457054388 1250 457053138 457053167
    0xd05060c0c1009030504030312050112020405071b0303060f05012f1006180501080606010806090c040906080c10020f070603020a050c0d1101271b05060f180a0303050a 73
    0x6200b080c0100c945a84034029002d0301c01e0b1035040d0703240d00e0f40c0390103081c003017540d284400d507036141400400048029200710911564125800603040e03036035650985142c10180400881040c04030015020075030180d0290090352003d4448081040c0d9600045030400b541c824138121969040c8655407034402e032540b0540c000e44510065480742012042140101e459a0740b084003d080e000034461070001c260f104107409418244003805091030301200181580c1c2010300b5143c090558a40040c1c0000b070450156006070a0403d428032080740d07110395003551114044e01c81446150142c00c048c03042c034000102800809030341070103040e040c1c0c6440c40a030002d4204110036401e10001b000b69020690003401a0490b40d0070580700d0000b402e440e40e91490031076448000b504000b08203500e40c1002c484c00071079002c0340107a00c41c9464180d94400f032150050989680d1100303802840c0402d104080e42c03072110141c004002200760120031090f4000070442c4006071488043c2c0442c80401405014500c5240035191920 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 457055638 1250 457054388 457054393
    0x501230a1203140a08070909090f171b0319110a1b0b0d0e0708070f0302190512030c15100302090a27031101050714031008060708090c0d05060c0c 64
    0x418400f4801603613024144010002d403088080003030841d0403241e50000762068100402c41c000380c1d503407002800d0204140140c8182807031140206800554401c688440307021007100022415144215a66070708000175450351002c44214888400380f08074542e03015082610014404102143c0303c070070f0307402c00d80600758016012040303010800c00400b00c000c00013020b40c03000018142281c0f50441d4140b200c20b41210400340c1040708108100342078a140786040e05d4044410030101c00c00d04004400d030494a0740b00e20b40000e80c180b80303003034107481c04405850040171000031f44101103010107414a101e00101ca04101150b007441c82480541880c01d611039018904660000c0d81c0720b101d089009643c0e02c502c624018100d0301180020400d0b9000d5000743d20101c40600034001400d0201c0054810030041e22030511440c40030000900485500850100030410b41040d2801401c105000510400007140d0541040c459101e00031811304100010002c1e003034200d0040d000a8030340c01180b43c0350b81e03c4603030048010b2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 457056888 1250 457055638 457055657
    0xa03080304170a0f02160e06040b03010636140703020c01020705011a030d05130504020a020307063b0a0b13022107080d0e0f0120010501230a1203 64
    0x3850808010003408590f900c030001340f20300d03c5030000c0c0380c440f41100740c558503074800c0c508003c02541508481c1e0840411203001c5001104200400d0042c02c140d400144130384445030f40090b00424403118246200c403051b0810711010034000c1d888096610032403c902800403590000b0340c1c0540b00e5806071541108540c0050314125040e20351070b007540c01c410040c000d0301440c50101e2029203400c100503040c11110703003005803e00310f0400303a10714600400d1180d40d00440e000285041ca051080c8202c41d00c060307100c0070030008282c0741304200039045800b64a444424401d41e1401000e42d03249440080b600d200e8400412101445036101c0003c0800070b00541407048a0385017800060351103500940307030025070128100c04075820182841c54004981d000c0c1c5d141d60030801d0080340007680045101100075041d01d940c0e801090000c0105c410314400c1c1c05a1081c0704032400790921920040d00720b60b048640160755820039001610b8003c200c81118161281c5c040c040d03800c2044046400c50320b05c1d600501a06118028 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 457058138 1250 457056888 457056923
    0x518040e06091b120616020114070f031d030912030d020d02030906130c0e0702030f040308120c04120f020f031204030c1d07181701140c07020a03080304 67
    0x1088819540340784150407502c1c83d049500341100c0e0a1070a039904a54541e030380203020075899100c203000740080030802e855010760180c0c04d0007500102206140c02c0100c440c540790001000303003000e03044c1d914180001d0920a010001c2e82c0300b24509452140a18040c40c0381200180420007005455008100d50307020510190380131024502c0603100c00102c5100240e901c1c41e00649403800d000c0000d00c1c3c401d000701428102c40104408080f10429a040510f0181d00c544844605130b02c0d5014401400e40c034007900090120801510001400110310034550044c1281c4070390f84200218003450154000c0e081e4501002404201c2c170302a02e0480500141401d041d8096010100b400d000d40c55074000c10000c40000d04104004508801b10300a21070444003007120442041c00030708e030344405001308040000384600d45404843d41030094000300313000c80b80c1140d00d1917404505d40c042c00c0503054042071251010005035580300380ca400c96011716402060000a2411683d030641356400c0604240c984010072400782a1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 457059388 1250 457058138 457058143
    0x10506210903040303090905010303051b10060f1517060d02060c0703060518030304050a1101030e070e0a1113350304090b120703030305070203090a0312090602030a0518040e 76
    0x80e8141c90040c5a44504504024111901a87c0079400c954944001040469032007402d4038041c0c80790071040719507080c007582e24500d407a07103181c0520070741864110001440c1104860803400c40e81d034414410884101c03003109452074100c0800c050101820000080d94500e880003004580342d20003800300c2d051a034030f01c54103071905003950400ca4440d542d9509010054549601c04513a44840000541c5903107040c0d95580c1d2246940d95000b800034000e240403c040781c4c082c0c1c10865000ca02c58040b505200d90705c0e000d250340f0810565100c4041c600e0700d0a096601440c28080312140d411003100104110300e00318001c1c11000100b40351042c94080383c0800d0100d004551000035001c1115401507482e542030180750401c40360710b20120707031043d48071011a231803005002c40e01204503074160800080d80d940d80e810a9041d80300c1c12000b5980520b00c1d050100800c1040542d8405400250b030b10328180c01c0c0c8481050340d90303224100e0030202003202030000016120b4807450101c05a0b0000c1c202144541c2e0382e0510710f1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 457060638 1250 457059388 457059391
    0x30c06010b09040e160e1017010c09141f020708071202030c0a030b04020f0604120c15090b030a0b221b08060a03081809041a0105010206010b0301050621 67
    0x407866000242d02800c601c2c20307000e0005002400409081075980c41c48141080c5040d03441020040000000010700049034000307941c006007a10390f6030030385d64940710344480e0003451512010341c0800c5d1040740c04a1020b044092407907004001600100e6200c010b4011000002c0b007141500c030451180c1a40800c154105001e4070004000c8101050440c0501e841050308010341120414046e2001003000c2000c21026154550440c1c0c06840c0316940c0325920303011401034403464100121410140040d4401c1000d0b5244840840d500002e0340d0465000001044444045501ca020285102800070944500440d0701c5200c0d00c000c001c0014801ea0401414280c0703458160030082562175a0b4040081c20002c0e0106507107540c21145040b071582d207442030018203202c1e685d0002800d8107201082e015802000840451038800c40200044040e02e45440c00a00300c3e20404400f04035100514000103a650000410a050300d1030070800341e00310307800c1800380900c40e000541d101001c210035071909482d80400d0004c06 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 457061888 1250 457060638 457060649
    0x2130e01050f01143a1103130303091b080709140601050a1b03120b09190c090b0d0504210e0f130908041406091008040f050d0302040518090c0111030c0601 68
    0x1d0004141d082600300c15217041d00241d8480b50304010356400c10b00f6005085a034041c06e491001d091011050804074001d0010784001880101000300030f405c840e07040c030a84d030101c8040c4412104492b032100421400d442c004055812590b01c410003040042d800781d0050005403e031172401c401d44641222040c625070413218000d5010468034214225000c0150146d4914036074262201113080c01c0001216214484800c6101b41180d9100002d201d02440303030501e400104145c4152a80781c0b007a400e500c1000340004d136011220458002c1001110480c0300d515200070900e582c43c4c0724001c41c401002c1c811040300311440903031302540101c50b035403195a00d4800d40440703a000d84080e0b43c0310703800c02d07200e41c00150444031058807070b40d4244602d010f5139076101e04d500341003811450010641d881b10300d0000c5081010341801003181c024409040c01459055025000703c420407100341000080202440d4500b450903503250ba810780240a0b40712855011f12341220000650204480c54004209121401c014080e00503 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 457063138 1250 457061888 457061947
    0xf060f0506100804030212031f0f050307050904031e0507020907120b1804060b03030903070e15120a14100c09080d0203030906010608041a04030302130e01050f0114 72
    0x1d014840c00e0261030001c4103092401c040d400d908242e20041d44d42d0308503241c00c4c18403005c0000040d446d4034a840074036804d20340d180c58283c10760b44c4920f003c4103491a58022103000c1c3c452904001010301e00391600313a00460b0135844402801d9242e904946032039060603500c034140102000302e9001611078034581441180c40d55204448d010001d111101514030340c000f541e12405510161164800c800030000b5001540b00034002041203000d00800e0642c0250500182c2c035000300a0005010034280041c40d2190307032030504007826580c6400070844030740a080c080d08115404640300f4000940018085020080c005046810803904600c011095611000c51b0394001010100104442c080c01c20822007441c8035400070758150b180c50a0f03000e50f112030510a0408102c0308002050a00c1500010b0303500e03400a80c031700d851080ca040c0c1400780107544003118500102c102c00c0c00020780001c060160350b040e0350009000c0404076500400444034603886200d40c070043c0d1000c210303041c3c60788a0002e58007000301c00c0050 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 457064388 1250 457063138 457063141
    0x70f030803041403180118150f0f0807051c0f060f060e0301020708250b010306050708090a11280f0810020403051f0e06010b030907060c110d0f060f05 66
    0x90000609426403680c41144d401845003443c5c210b09640b0400b483c002c00e203010a6510302c078018003a0300c8543c661001c2d02c090070b011440c6400d1a40030242d1084854591154500701c00d0f80c00c01201c841e9821101ca40014200b440102c8501031084040a01c41c0000200421000c0d810011801141c2d280e9000205186070710700100325103908a00c0111101508400131400c10301c0c00d40716100f5600c21010f100711030382900503002c4100300c1003405c6050b4036078002c0c4140c6019a11f078030305940117007015282d08000c205020001869441c0004050f690180d00454440041200205002c11400d54444000c28075041030000003039032241e085070b440108482100010143d240c15805030030a803003924010b04040c010882800805c40020b15120a1441d42000d0818000303034050040080015940120310348c0194000004c11640307000185005400c5101a551059501d43d0140d0300c401407811300510403c10340f1500c515510b0000007234044580070b18609101c060040d076804085483c140c0124030000da5400 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 457065638 1250 457064388 457064393
    0x6090f1c0203092e08040f02120a12030c0806100f0822060501030209061f0c11030604031e0f0909200f1215130b0f0312030103170426070f03080304 65
    0x114002806881d900380f0748006e060641b1405109805c841300a4002c52220282030000710040104599554010b4910030032801036460040140c80041114400182440302088062400000104080b01341382c880d045010b400310300a65085600500b00c00c0741940308018441ca003609e6103c150070072071280070001450740c154410064007000140140303024065803c1ca5a002d4400110441e4031811242000c40c552149458a40d03151803036141c000d501400b940e014041011740140004c0c518000540c800d07052400100c0088031050030410f000000164082c80c1000504a41d0703102114a4401c581c039030f24014504218070145034881b020a510100300060f08082c02401d801010342c1103410305030071b000303e01d4500000401d0030300a5840b8002d0176544982881840d924211105003903640034042d07820300c03003143c0062800340e0000d10080da03950f400e611030140300c80450303c01c0303809442100005041070141c07542e000a0422400802803594460003e01080a20081c10740b80001e5110b140045c1c1d4078581403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 457066888 1250 457065638 457065709
    0x50c100503160203090102150901060308040e15010e01020c0411040f0e070e010c03050d15091503030e0f0d0f0539040509071404020706020a020f06090f1c020309 71
    0x200002c2150400e00c00800d10b680d001c600d0b0b0407c00356481c041a296212410310a004124660009210007000500000c2d07500001c22030070301c501c03000c26111018100410040d00e030104081c0349240183c001244d102c00b40d242550111005120300c80c5030504240e05c0340704030308011941d0380010003110152010000c2071507000760b00b8000c6800030704e42211502907941d0003804500600c4840e98a15446400000c8581002d020920003171890382e40500c0303804c04207075204c3d03400101400254000350b1481e40742c00c21410110000400004007501c024040d031003944480030310740404802181c00b4010008541c0001609020703000104450f9940c4100c5030190800401504290600180c003450520307040000040c1d01060200031607028031080c40c8141700400001d4001e01c91804c0051585101062000040e070f800213006100c0303482da0341250380d070351141040256181e601d1001d610710b6900c0540024404440c60300350640c4600c0c10b0044034100f4031090300003504220b03040740481d15201a2000c1c02142e0f001f2 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 457068138 1250 457066888 457066921
    0x403120e1504081210180b0d05100c030b04020301080a11010215090714010f090504051b19030b0a0f03030f3629070305190507022d0d050c100503 64
    0x210b0b105e1110240b51141394280f164001640a100b240d450406110396240e83c052268400d5000003610280c4d0b44201420f401880003142010000c1e00e040c0011203e81424821281a06c1006004061240d41d5035650300b422861141d04604500500102c00301c2c0b8031000803500e0050005402825000c2c1c1460032114000c040602000c0c10070400b00d0180d0b01964021000b4009d8600c00e8401003004d99800c031901c5a600d82d071031741c54002c0c0d041c00a03074201c1032407240a415448500740e90b02448510101810000f44030b41307078081d55882c085424400c01c006400f64484280304103240c10180f540d070712090720b000301a0860088440e0605030b1503444120340320b0030200e000c0c00f500e0304000c149a00440302000401100b07414213421064040010640241402031061340c807623052b0158964941403071030000401d0b503041240d0480c010540d210b101aa840c000401c501800c290400550a052210004110079100c0c803190a0b02c0c140a4040d41010360385580150100300001603c4071666401d00d03103072900c10f1080 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 457069388 1250 457068138 457068151
    0x290a0c0201050708070f080709120606080106090618020d060f0303020309040c2307020a030804170f06070509040504060902090c0a080108010e0d0c1a01030609020f090403120e15040812 81
    0x211101007260317051b08a804508240e0040c07a100d2042c1c0d54000b001d40d445401504070040384d1030700d64194010040c8a412440550384808000e026090381c41010b441662403070301451045040c000800103241c1300070780c05044000c407018400705405ea61008442c044800c140c1040e80160000906018581068000d03c444030a00d4035111078080007842410800883e00f0143e03448240000800d042591340b58116140515004011103558660750b403143d809204c0f40902da40300b140624841071078100342c0402c0d07403807044c00103031149071a00c2c00480c1000007d000c0208121010369551032050050303100d1a002e01d108a070250003a65403113039501c00107000c0130016804242d20768148020481754a40108204003001c1c1d50382031441180385107181c4410103211448020b501b0507418400081400001d80000c54001d000355160b038031160b40401032000390501210041c012034500f5080c00c921620b07651184041d1305412003914051400d4401c10003020340152011f80c2c81c442c02042d0b03000442d611911140d003020 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 457070638 1250 457069388 457069397
    0xc0102120a022a03160305030301061d18090f030c031c1e2c0a060203041406070e01030f0b01022e05040f020a051e04090c0815100b0a0903290a0c02010507 68
    0x14134507580c10380e5a10050052f441000303050041060320040070010010300c80380c0188190f140d0790300000781d2440c404085030681c009204034041c44007001c10100441e60100d4002c005185081c0e868410808084000c20071006840d80e02c40790401c0c406441c50300090398803a00030f00440d40a04650030088450510040000e107c8552103100c90b2522001402c84103141c3c0c0003030701580300e80c1c41d420614104c5200c074215640500540c1c081120307072580018285010b40003620f00304089281c13892400c08540c1d045071040e01592020400400c0703403a06e4802070f500c42502d044001c410f60b40c0c00c00c002060744d0082c0c2d0110781e40d180085c0003c0440c070f8184485805400107840d940705600d010179100303010300482c61046004035a1554a40203112030000b5a001822604080b9802c1c01c03900d5100caa040d00d001c90303a480ba81e03451540042100b40c1c03000112030810315280e480341c0c0803c0c01c5465002d280c0d50300c1c0101c2c503024855041409902d0b42800002e03071041d6140c2c13400040525a995019007501c000030058810007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 457071888 1250 457070638 457070683
    0x405030f1005070207061d04320f0f04030804050708030f0306100804050601060513030b0f0702150114010302130f080f070501020d20071e080f0c0102120a022a03 71
    0x1c0c0d03011f0200c1a68480d41c1071691f03d460b03c0071021074000c00507103010000b00c1303a004030780504071141c00001e030800464183e0000c0c0c43d96110042c211101c3c100351490064a103400c0c000c10701103071048480580140c044c00075240d00d00d6984006a24540c0011650f01c0315881c04001c004d803d107000c4103126100c21181c00c010a843c503144e80e800d030312800c0502a80c01402800300340000100612542e14004e168015041c0c1c0e101c0c246583e1180d880c000846a0900600c00c0d030725003c0c644151155030904030762001c880c0e24048c0c4440c10054004c0c0d082807151030802088031900080c4202c41450250003003101c28050a1904c2005440703600386005900210f0555210410010030030f5440007003044560030700c04044014111130f281d0303282403445075480030041e4001540c1d810b5500714014034403130860f0421811990004203140c1c42c60b45500e4015070541c0507800c445944050f2100c000002c4c000c00000340b0507959400c0c45060052405060b030b0110395844903840d03c524180307040c02c204807540600c0104030320409 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 457073138 1250 457071888 457071899
    0x11e050406030506061909060e01140d0503160f0b0f04030809010608030414011b0602300a05090f0601031b0602160308090105120408072105070609080405030f1005070207 75
    0x40c4e203006060280980c0d046071400b40c1401507403031118094810058203014442d1740d03000b1651819000c1c010400c0d04000e4034242052490030850461145034014080c3d420113201003c0c0c24041c2c4840c0600740c0b420000d4100c3d00d0006002c00782a584140000480c0c401c10341480d01303000f040241c00501c0f11050307a06d0018180400803000080d101220740328090391110100d03010040320f522100c0924100340c2c007044181e0404115031600074005032180f0600f1040400c01c451016a80002554001000d506903080412130401c0c213904201c3d4010107074002c4030861040c84016524080d0260b200f13403160036541c4402a041c21811203903600501c168030044c0a50090b0802038501411b262000070076203000003a00c004564006d10660310b4030421012481a1488c280c00c00904581c411070084803c4425540040700d203581c120204108000d040e03507101d0516071555540002400046800e9a68120034040020185e808118149400b00920086c00300091201f44078426244003130150400e640148005020 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 457074388 1250 457073138 457073143
    0x60806100c1101030e42010e130f03030e060109060b0327070303050d06150c080706020d1b0905122802061306082a0304021503011e0504060305 63
    0x61041d0406000e00100b14104016401400c00040034032890040036202091115811396800c400700030103072808124060750761261801100c4084462403950305e070005201040100143c190f1000b1103014840b20814642c445086031200820120f00081d15a103c41c0300d03080e024010303240142407491060002074101160010349010040c2940070802c0300100d07860401c90a901d084000d6600c21040c0c5030310607120708004110303901c5110000f9150342000c4000401d8001000010315001c050354031305914140310342e00c3e03a60951101e001a030340181c003441140d50a482038880c224112080f0740c0c4d02e5043c1e582c56400503080c0c008540c083c83c0310b01003079610382e01c3e10722002c245803c4000d4818000a450848001c9500500c4140200a900b11030003080c04001c804696500800b0341d95991103441c915522144a40c90f0355041040c1c084448940c40400c0e00c000314080059a00144000c154000320f01c6844c1030200c00e81c0090b404000101d0b0107441810f240343c4500025400340405071403d100c0c460070760b10b0341a03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 457075638 1250 457074388 457074407
    0x807050f0d0309050a12060e0601080d050a050c010f0905060609150f01210501030b090601031205092106011502120901080907030b070305010509090a02100e01050f1306080610 77
    0x140100000030303101c410548690315080103084010301d00d81502e40c039940006440d83c0301000840b401460040741524030440014100e040700d0026005005002c040072048505401000504081c444d041c000441002d10038058030080d54400540011640d266040c600d103040000342690b03001d8084070003440960311044800f0340c1d88580a840c4800300502400040341c0611070022109600b8076038a2814040308155040641240c0c05203544444a0f207860062a072182028400104007034540074104981c5400748024103c001070040045c2c0c00f00070090813503440f21488042c00240c0d81c1107000180028034806582c094000d0480c0300501910b40c00140c0b424251203080011414055850006400084c0400061b4040d40c0d01070506406420440c902401401081c09090320034804840040c28070000001d90100c9103400400b03500d035900c50314400340d4440804012480c10803004004401274a10034000822882e406030500310180c83c9003103001410980b0250105100c0c103003591001d840280c2c0072010700f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 457076888 1250 457075638 457075669
    0x9050c0a090501030e101e02030c03100f0e0a0c050c0f010e1b010503190b150306010e01050313060b040f0612021005090306010e0c07020a0303111027080d110a09080705 74
    0x307031f140d00400c0d8010b0100078030038910300e684d4000410001c1296102018502407103c09000c2040152071f0451014141c1c140d01514210034402400118281a19040607580d00185e0030000d14100c10025400e0401540b552a5500c03a1b4481c80c440100c01c00410100b1000303500190b0051455030898002032092001601c6484036096101500e002c0307126580c803942d1680d1000f041e0b00c2180f0808200700081d034000f1200c803404201d41c1d50005905502400440b4441c01c1d8803041d54000b0a419911040240f1030b05034020380017a9945927640d500000340c401d0380041c16114582d88140200d51040040d010189121032080100034800e40040d9100001c90505444405114003e0740d911000b4000460103059406580301010740310000525800020381500103003030f8015100b01c2d00200f12601c06079001c8210700024851040b00c40310074109000030b0595968481c0201900c0c0c0080b07134103410182ca001d48880f0710f00c00c60000e0340c100c41d02e4014200c4001000c441c1e0241802601e000002240200740e0380380d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 457078138 1250 457076888 457076891
    0x20309010e0a360b061c1d15011e0e040f080711010f020a02100c05070b04030305030610141e07050615280b0a0909050c0a090501030e10 60
    0xa1a40d0390301c10060050500c0b500c50394103000c01c18036050541c1480b00d9402c3d030032001d10802c81080d40070b14043c0e000c1564001c3c02091500c4110743c071400b80606035040355210556502080ca01240210b100c2560051403c0d000f050008070304c5064601c290b00c180c2c4105407100058580342e8051500280d030204461800c41c1c292760541d501c0c1410380e080c100210000f440d43c840060b10100b000325030f400d000034190003a03aa6900c9400080c80503640c441040070013940c000e03500e51450800c0c43c81041641111441201501c0c0d8850b9a42c202c80300680003a0411030118101100b00143d60508901d81d9120300b00626051204400740208180c0b41d11410120041c1240078812031820b0401070b90480d10503e03070241c100c485514102e0000781000c806420454855104c0311a02e00c904211200600907001c3d401d02e52101ca030b481c0104510895000080d20010700000031800500c4910034460548141c0441c00c030316030f4844c0c03204001800d40005070042c50505152210041120400080c101a5448110f40 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 457079388 1250 457078138 457078157
    0x5040507050d03230a0e01020c0f120c04110307030c05160b0c0c0f0a0b01122f180f1605090d02011b06230103050312040f12050901180602030901 64
    0x6003141d404060060b184c0700c3c082c04450048003088003500070104035070341c0d0342c1e0017a10800c0c11004a07202c500f0f0b20013245c1d00c00d10b10b506107400e510b440400c603142005040304131782000d502e5102190541e41c03090300c00c1000d02d20100801c40d071380d90136005105d40036007249800b600c4c3c08140c403902845281842800341c0b034800420002040603c0da08100d0301000c9405003100c0d0204030021685c0c0d52203450380030869482040c43c000141202d071603127440d42c2260781f01400c0b1a1800c0d6400c00c00da001c0719000d400b810280070403c0d01c16407c3d192003c0890303030340071290124100b0b0f180c040c0040c401e81401030b142d003d500c4550300d00300c0c07541644041642d48011003280c42c0b408450884c00103d0701c442c2c188071503940c1c0e128480d8200d002c100c100d80c0800313480b02070740d651130440066124045007070703000910015103603070000c210b14128161020541c4e41d109115484506045031180c44960200c4080103589010480000d00c80c8001d6800c99000445541c442044580007403d01b04000c0d105e02407a000c06051145c20380 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 457080638 1250 457079388 457079393
    0x2060a050a0b09190b0a15080604090b0103050d09060503060a290d021b1c08040602070b07050c0606121e0f060903040f080105010b07150207021f09050405040507050d 73
    0x204030312240c01e0700400041a40c20b004400303c01600c4d060403620b180a141068030807542c02c0c150807440031145d05018080000b480c1100c1514001c0c0c0050050794826070302d80550f00010950050a4040e50003a4003d010300c606100002c3e00c20222508032a0500c0020b0080200da40c0d20950504295158044030b103503100190340c0f69040c0400708105601c0c075032202003054000403a01c3c1d40030307240060003031000c0e00c007413610700c99a152144280c0003001040410303d07102ca5800d5014030001d5400600c00c0f80c006181c690513844925859078140c400b64006500003d4009000c4401c004041c1c008004a9000c40028640c150455984001035080f448440d001e0070083d0345040306000718502ca0b1201c000b90354161034400020741d102e50050044481200042401241c121b41c1446900e0580702c4c02c04a840c0360005944031030002e081c10100b00d95100b0f130200a0040140c0740c122000c1082d50b18a00001c4482c400908040d05c5520280c01032401307245400704010216100084071403c03180c040e1404c207500101c90 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 457081888 1250 457080638 457080641
    0x30b060f0f1605210903070e0912071a01140904020103050c07060911030d080417090a030609050705010311070209010b090a0806070e030d0809100b0f03010606030207020406080a0302060a050a 84
    0x42c071020902c100d40d48100c4091000204454826600382001e08a001402c1101900c0600034000b51540640c0305410510094401e8801c0c507420035840400c403603030f0b810403950004542d40181c4040b5050340108120300c2d0300c2c10f0403003900c0f80074110342c0721552042c4c0d41c0c800c0130900280300104068100354179080485c5056414030b040b130b5180c940000302800484080d04292000da07196520303050291013051000144188038100341c42c0599801113120341c040001e480c0500d1150070514680d980405200000400910544240c501c9036101e1806030507013600c1c02c0000341c00c0302c50034958504030020070444440140d4680e203d050541c0e020030895600c60001c030012440910340c90308100305034840c407800d02c007e640c1c1040c4801d0380100c0481c00c45806011103001225019010356180071070b64000e110710110071203c2d030000001460050282c00001e03424400090030f50341603a000c0700c00f00768001804001c0d410203006910180c01703041c004086104050707500965608004008030340325680c42010070b0850405 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 457083138 1250 457081888 457081897
    0x50f100f05210906090105040309060f05091008060906040b030709020d1b0215060315010b090d12090f0f030b0408030c091806010216060e0103150915080d030b060f0f 73
    0x15454541a0b04603028440c1a030750780a0f01c000c80305101d800001928a07005024080c800c0c3e52590740d121100d0300d0301b07a06440b0300814600307103014090103000041c0280c03610800c038419011995200c010900b010014400240000b90103103028074108551051a9100000e40c0c0c001c031a51400e0050356040044103520042c03401e021842606000c0050b00240d040e800035071030141c000764038005117060301c880d002c2640d9000a070b200408501c0c484001008a040ca40000d08150700010300100e18002c940d40d07440108603420b442400100d00000010702069009080280107499014403d82205095480704050000c1c010b000400d00500000001d1180c803c2c1ca05542c2001c0014059003415440844815071201e02110f00500621610114803410b10048420780d048072001c4c0c0f2059811542e07680118040e103060301c0e075454a1076031500c0015086526110309000300340c61070020b121907402c0428540c141503641101204040c104400c104144d5514030442c5c01d61800044e1269076424500c80c0034a03113001d03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 457084388 1250 457083138 457083157
    0x12050c19321b03090307090501150c030203130609140303031519090504051005060f0121090515010611030a0207061d1c060b040608100506010903080318010501050f100f05 75
    0x712a1000c2c0c9400d0010103803844900c114103039483c198544281d035003152030901c02c407000c60340000140140f0034000d10760f90f24218082d205903860070400c0240d00c8000c2001740c1c00038000501450080000304001403071902c0b000c904801a40c0385080114400b0103100001c56541d10801c1c851030b1024001034078145090080c0000d0314203104510b03290070520788603882507001d900e0784e50821000907401e03e48000c0c0000303030203016140c020182c0444002009000d0351146040e842560700c4c0c030140c02080041024818103600c6206185080d130404e00c5c010000b01c01d15a243c6102d81c0240880681150007150390070540754203250400301c1c11030000082500500400c080754010405507109180c00d480112052900750180605101c840c2443c800d22017280d00912401d0300b144c116100000f4480000d0304140d81082d070500d0050581516900c420126510648034403a2100403000000a0b802c428011f650040a00300ea0b02d001c15a50f460110322980068060f0300c0400524032000c4002c03a00580580d040b044 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 457085638 1250 457084388 457084417
    0x1e0b030307020a030c05090c07020102060f0604020d0f0912020a21090f06030507090f050109030602090307050301061205100c05160c08073f080a12050c1932 69
    0x13607403810b050000e00303003900581d409585024006205450080111000300d64103034000c000d95603d2121054000a001e4280c5500580030400c0403a003002501035850769142c5094000f50088640c44d002c651800004009025504002d03801c4002c10f0034000300740e4100c1d10014011040e00311a64088400054030f03040b1a948800103103010800b2076140c0d11280c0309170742a8542d150419140c801c0c0307800e80f20052044500003513501c0401d01c00100e650b0090561140060203c613012030701d42c0c0029080d01d0680d00051050060030420720b0900c00c0400c4458a1326030040400c100f1040a424002e14a1080da0310441174103007000c40c0d1008010b14004a0b5004044920560b203d0755100e010035104003207004414100143c800c0c0240c4281c44115584d213400410303106100101c003580d0794408416411000d080c0b01480003010703482600c1482401a14421400307100074030707921544440d81280301c03040348816108201c810310030405d180b017400544059500940d41d80402c0313554030a010350030030301c0707441302c08a1501e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 457086888 1250 457085638 457085659
    0x120705011b0918060f1809080a030c080a090f06050405163f0f0201110a06020409060b27120a08041a0a051804020403061401060905041e0b03030702 65
    0x41d9802180182610301100341c88900c0d4280c502503000755019801649040244000100044c0c030b03120600705c1c801415108049a00d40560310b500c842d5400000c000000710340c580c1c1d42001e0065220408561201c01c2410400500c080c5450b913121403c0c500718020f107515952404201440703400c101d90f032180c0c05d4152040700040d4a50702d04000c0100503040d0307240444400b00b2940f84a101c00d000071442c0303498984860700720460548400752000e036080c005a06018403580607900040052190700b170302074001d20b005039480e40b0b0310f1080307022100d044d407048100c4001844083c40c0841614002034032a050400000303180222800000e0b00d070f640c0e0a0307000741e052003a44a420704100754000a04210354044a480005583d080210109840740c180400c00044081011300320044d1040340040000401400040c1410b8403640c80c2c00480e00c0c008421014100c03180010088141d0112204010304801c1c1d405104001c07800061142c02c4804003e00c06095403108a5080c145d1002c005803100113070010611100c1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 457088138 1250 457086888 457086941
    0xd0501020d090b0603010911090c0f0c010603020117041104092d0b010602010606050304080a05040b0d021209030405060403020f15030c040f06021207060e0a021e0a05090912070501 79
    0xa014240c021218000240001242c4d80b0b010701c15085400d03003003085803060b41c0051f410009030390002000080303043c5091108410000343d44000d0220f45254100001e02541140000b408a00e07004200d203901110381e00800c800140ba081120368003140950300810781c00c00d03501d02403140c1c1100780000c034032160f03210301035200181c10307403040039800c40c02105c08094a0b601c40d00100e090310348900440002c00c900f0400310300040c0070030006212900742850582e080c03d0302c4060860042c1e026a8042c5412500070550000d03090f090000035403ca0200d070003d5203400d2904021540c43d0103184030191003a41c40c400d00144070785416000103060720080c1b05440e80e0f4034101702c86484907045400384080741c04403261702103002030001411040800180a81608210b0ba556504004d492002c0b60342c800382c050244100e0040e20341c07481050f0100b00c51031440010b010480305110040000794000c501c1401004240b0007010310202d0303003103204c045120045507201c410b0304025025240114040358178060303840c2c0c0f02c1071 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 457089388 1250 457088138 457088141
    0x71113020d1d06011203050c01150503011a0915060405060a05042103050f21040c080d033e0408011b170f130204141b040e060f0d0501020d 61
    0x8165001803010429060064042840e5464007103084007030340e003c40010b000340e030800c0071040130482c882c1c6801464800003002150070740c0d56031007448208244204080c0401e103428007440d052000d54080070030030082448001000e41e500545013100c07040021560030b05989500e0204ca010b028007400711aa00c04588500071300552080c400c07a250741081900d0000d0b150b00300051113241c01e80603500c00b03040c07034801101e46005a10910281c0100001e00000c00890300b40c41c2c0328039100c1da0203803001110542c035000982e030505920070340c000c08141c901000790b0403d00c1074910051a16031314076115144101c0340e04c0000130759801a2801c2211482c040360004200a0540042350502d4042e10340011448080e1070640d070150244451880d02005007001a181e4a500c0200e80c2c0c0c400c07110510100300c801c194000c83d045900000402c4501701c00e9004000784e410b1000146000c20b000c0340780d294a090b180410f22800307a00302910240c820b01e41c9c0401c1c0c4060b6507802d0b00c50110039801500031950756403600304510 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 457090638 1250 457089388 457089397
    0x714062208190f061d0d0201090606060f121505030f0a0210210c03060506120906010e040f03050306030313060c02010801060813020904021c1a06030610050607111302 73
    0x400c2c0c450082141d160040c032403038100e6002d50008400050320550341d640e40c041c02082d90054002c01d42d04516642660041240104420302a000001d0076981703400e1003003c2e11280d4002000740f0140045c0324103100e17401868a040340b20b000d1000203d00f44118030b14840e15801d43e0007164944201181c0c000210300218010b10b5a034401c03a800b80c001b0400210a075401d00b58a5422854400c100802d6289060340c0c0d0001120201c40d03180010704251224001005a00084040e10107604030360204011100c0c1000040e0141560840b4504a4070f40760703845c0051080d5044004082000110110f041510100305440c0040320866034401e0458546000030302024803414184c0c002580b0070000500f1038014004c29000782480480b0300319982e035075000d10150300310242003240c100b4801d03401801c640303807040a0070340a18031600031201c88515820480e1a890350140107280710350401001c0c82055500c81200004861090b02c24549507c06c90500700300c17911601603c0340e000b0000c1d1051240b100311650052 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 457091888 1250 457090638 457090649
    0x30218031c030608060709050d05010902061821120703090f0e1512070504092609031e0307060902030a02090f070912050601032621060603060307140622 67
    0xc001c3e85540c1d4110507598181134840c80c01003444442c0600c0389061028041c0d0b40700313008000114800041d6400b00d00c980d0f06c18180c85c4101840c01c201251075280000800003912211045030a1290001c05d034140c41d2035941d4514071410070700203110f00c200340c084c032001002885665000642d0b5951030809189103074044859005004022412082034038284007001404001c00f00106075140c100300034440201828030045c0c810700c07034403241154081d1018404044400f42070300c0c0982c88030071000c24145040d20f0031044218019200c0c10540b1504400002ea42d08190041808694034400d400440d0070b003400d9401c083d411903001c0e01041095030143d12040d000740b40301c0e40c441c46030942d100c207181d1072a441000000c00701e801c01001000400d84001440748010002032098108000704452100507511940d9a880386440d1036581d8083c968590181550110055860350f14500d01500060f80328641c601034164a0b49402c01e0709009516580d05032251000541c07642c00402200c1d201409248403180703c0c4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 457093138 1250 457091888 457091891
    0x90605060d15020c0102130909060b0d08030408031806090f190b010b09040b0d0b1f08030910050c240603070f0905132a0f0b040501030218031c03 64
    0x1061141c01c01d4032a007809150092024000b41c00e4401030400a98042c01001407190740910240c0114180b88010038010700840381c0005048900d442d1020035940041d000501ca40200340317901d8042607160085030790096214000729a00d948518111003400c404603080f0340240719100812589090008101020980d80b0b812900c00b030703044008024100e1074900004007035075941001040f2402c005400741101d20402040403510700e541d82c02150705007460203000c2e00c1c40c228000c01d1051403245a042404032100c1c803180001502d082000700e039030300c6c0714a5000d58021269002e1441001d44190140ca24a040d0407040e0744407810200086a42801080740d144403460201001c5902c40c40c0000d24242190345518015042d54a40750920000b007000038507465811800c10030250001d50361a0301c04007400098070780c80b1400e070987c161113180d4131071039084400540e00164040c01100c0640090300c00b01e0b07109290140c0e8030f00d481d05a4280b050f00c4900e8640d01440b5403810180103126403549680f400180350f50 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 457094388 1250 457093138 457093141
    0xa090221010503190605090703020d05030414030c1507060609020c0d02060c03090d0c030203040b27010f05030c1303020303070303060e07030203070f050729100806010810021b070603090605 83
    0x3c042c0c8803140d4008200300c428032208044c00040186d044294880768200a5a843d107990341c02003918400010b40468140c1c0000405000c900958007031a00d0011042c0d004140a00011010507440d1604080c2199000008501c420800c01c1c0790700a1000381c003504100755101c181030b4501503070b40c1011802800241c0510703400210800a6181642d108221000003029104211642521805c0e4202419411404100404917400440d1001040d010302515008003010303040c90201000040480c107081e0400c40d41c00c1e640006246e014058036003100c4040399103a40e0f0004d046111804c240281c0c0002d4050001140b02018140c0543c00501160007035168000075641da01c1c4110102d2004544076404200c08c40304454415200b20050030642d441107440c5101c914042d19034400c6800d0000030345008810540c10064032a8940300360000800015004004550420704210b445601100403030748065408039070003031000074065a614201c52110142d984445d00c89070007e01500122005441d46801c080 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 457095638 1250 457094388 457094399
    0x20a2c251d010c02060d0507021908031006051204030e0d0204180203060708011217160c0f0f08190816050312250305090709150504050a0e19020a09022101 68
    0xa01c11031000e50300078031192400194401c801c0087c10041c040c20704600c05d03070030000388a600720344a4646d02c0380589505501c074584030400d8034001002d6080b40c02044818003c1c50100e1040c0c803900307030700603515041c004014190382c00800d0004c0d18094000c1c0d401401d140e80300d204050707240e038480c010b00e0003641034564555900d481a6801c900a03c100100d80244850090100b001d2544000b840803160218926000300d104d412a0101c04800381540c090b0019801006544000300b0500c00501c41595807400561030000d0071503d842c4815002d034455005442c640080041100c00c49604040703240c84042503e9a9080c225500c1d0041180030503d200c0041c0854501e1001e41040c82e42030400c00c0c440c0c00c94041c14030003100904005040480e240c8106800410b4a0059004070a400851b42c0c2007280c243d032030401004241d90010300003a84c007030f15001e0301405004c004a144004d402407c210090398038054804034105081552100403c4c0740302140c0c180d240c0c83c0c1c2c85016040f1100844480381641d0b203a6 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 457096888 1250 457095638 457095647
    0x3150a0501140135011d01091104170a0c0e0109050703060e0a02090a03230c0613052707030209011206060203030a0e0f030a0309020a2c251d01 63
    0x5101d408030306010004110a0041c1560480c0442d06003041144180c483e031198284c51402e0700311400c061049200204150990b4200d20300401000006004901000c2d0400405200d10700034140c00b10151034818103450010008104000c1d88030500c65071241c2d680304025000902801020070013414500454041403083c00381c0c10540d0102d00204030141c07540c8442d00b00a500c03001c10320f40c01a180044c008042007404007803a0500550b42e04080803801094000c0341404480101144548403e00100c4640e0011a4078482510000d5822900c40140c02120400441d144000584a10501e108000500b9415005401c3c001c000380c903007030505101e00b990310094590380d018240c0140d0051000540240c042d821040032411707200c0544031b90a0000c0500e5003960302088820000c01e446040d00802c604080500034010181c01c4200840020f4000b64288199040c40c14488101c2c11100401d8044080c034404110855541e1500110a20408005001c24212840c01c816004403207400d8003455014 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 457098138 1250 457096888 457096919
    0x90602030a0909020c0c030d020d1403010e01050405090a1b0e0c0717160602040902040501141309020a050c1b1219200d1506090612030309020f03150a0501 68
    0xd0b6180c0041d240e00785501c4500941200207040903d10940075600300546043c0800d9006100e00c1e40500924580c0d40400352110110044032200f1500420040201014540c11181075507000c840208454880c400801d19000e0710300c0c0e010f80003982e9070b603075465919901da2280781203070341c0540840e4183c0d440711640021800f403070740d001c3c06c00382d20001c80224041b00c00d0010800f080f0b11010202003c03090341c1b20b840881c2c2194100741081940010240701d65a080070030f2200f11000d0580d030512308401d8180b40120b9032628410803640d6034010916000301070003941514a00030480003260b62806841159401824021640ca80684d10310529040004408541c100c070b200d00482c00d010404c1003580d070324041c900018621014407008102c405003240d0b0780320701d105801e60062180310180403200074510129139880e80024270503032070305174100582c451b45d031050585140c00d070500180200903800070130030f20700f803144075140d1500521044031440c6000c20245401080c1c22034040149a8851140342ca00060 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 457099388 1250 457098138 457098157
    0x30706080c1902030408010e0c030712050a0b0601030f020a0e040c020f0a0b06030a050102040803071103030a0e042a0f03150e06090a0b06032d06150d02160c0609060203 74
    0x2080141002842d661198142900c0c40c62048914065a40e00d0482c21908034004000f17494004240030079036482d04200c1800a4640c2001201d040030745075940f6a9600d550100081540024a0000d1442c0c2c0c0260b008820101c00b9410035951241c035580002c050890120146100320700c5d2107080d8440c0c6100051150100e0307200c0c00288481e80311601c6850b00e403030b801000c41d54544260003d50001850170f002810003003021000668444225180c5208103190011a0320b019500610a60340c0040d804945051a164161000130f00740c211050020141c0f42c4044440c0c5d00c0441c260100c0c4402544440350603402407c40d0780c20000348590b41c02c0400303003603135600c107514008070b050010441503d81001d4058001c5a000800640303090050003007492034004441c0c0080d001300305828441c120113003030b03410b40c0c0e0084000c4d840040d5180400006821010f1107108603024080800c0081e0708407846d5044551042411013a0754889a1501d00140804014024a40000c50604000552500000c01d0f16610203 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 457100638 1250 457099388 457099411
    0xc0c11060d0222081e0c0d062307090504090b01032409050604030801061e26180f03041503050a091209030b16020309090720060603070608 61
    0x6105604020803038001d01c0e5601001a42081550450322040c0514280642c4051503010300d14605803905061501100c4040d0300c0d042012280c002c0c441001c41c0890740c2a000315007028403c52a1b04081008124a032182c40e0880c81071201d803c0d5095149140034070519459880b0841e00c0e0300c0b4014802540d60810000b00800c20840050000685000500c80c00504d42c910030243d40d80807a00c040d007521200340c001d9070303030780c000f401408149544850541c0c0501030f64102030829900b00024a804402650130b404100107a00740400300c0c0319071089858480d2001c915400002d4104540341c50f04241c0b410494a10a211313540b0b410b4411000030007501c04481071442d05000c8000400819009080010581c001c819a90400c0000180700301050864281447d601d5441890035403904150004000e05100c0c01029500701000000f030b400011030715200c4007500c0300c0a460301c541e84103480100302c9030080250300c90500c0040c90300040008071244580c0c000c0b001c803403485a40700700a5800c2d0038103589844801 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 457101888 1250 457100638 457100663
    0x3020403020d0b06060c070e060103050f01031112210309010c02190f020402091e030115080d05070809060304031d0901050a09020a02120d0614030609150712090b0a0c0c 74
    0x90f110b0140340c0d9102d070380a80860719000100b505541008410f8100a8001c40c003079080c002c080d64103200f01e03503010b5602c040200711035065880303210f14100440c02d1507108901e005007001d003911050041c0c200015005281d0582504110700f6100550002c0707900780030b158a0010703640b100500c0055201400d40d2192036041c42d01546895000c1f44a07140d48081c5d80042c0c00300150741c81900d41c8101868420005d40c0d07200000c1202074201825903425640f0503000748482e03003080c030009a010920361200a000c0c1823090f0307030348002d1415846030700a14403182c0d4460001300420080c141c00c4490810b01040f008810480030480204102e20b200e003c3c061950480c0d4500003e1203241c0340f0380d0003040284850300450b030f0b919008078000303180350b03101070004d808a82e2207020400c40c200304000302c4910000101c02914842c41c0c2450181c1e40e504159100b005880860b8011130003641c02581c10459000350036005010300f41290802c02440b00c000e035001006549040d190340e04080c441c421918900d94404400b0210 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 457103138 1250 457101888 457101893
    0x12010b0306060a26030f03040303020417010e03091207030b0c09101803121209060f0c11190c0f03080a08090604020307090b0105040504020409050103031e08160c0206032503020403020d 81
    0xd4100c0340800c20344c0d03c800c1080707401d441c020201a501c00da03c25038016a4550070080500520300c01c507140c10505a050070316a200141e0003205031100768070155009640d02ca03030360b506203203868020f0340040c160300701d0b401c284041145030600405030342d9410b4802d002c4070000b04e0001c40302c10003c00c0b41c20f013450003030100a00004000d01c404000441c02882c0080350030429280c0310003211001001100c07842d95420324cc100407900c074001d0600041c1282005c070303550f04540c0340c882c0e1a814075a010016601610554204022880307020038080c004025901c46015160b240c4000e443d4000076603480850890400540190000070303981e032140e6070250141483d18900610030300640f10710306509052040c01e200100b1586ca451000e00020102000082169403660402030200b2070601c403085214015640194403a03900000c2107a0054003030b407040d4469211592048a4500291030b0095210368000b040c0081d0b40d401100c941d00818244811060b1600e03000400c0e812803285210083d044400d0f40591800f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 457104388 1250 457103138 457103189
    0x3020f210d06150f0e060406090e180a0b060a170a0303050405010b06070f021c0f0b0901020f0a05070c0e1003030810211203060e010504020904090212010b0306060a 72
    0xe0301c62800e601090140e140c10006400004403544200068003c400145030740da44110b00c0d04030b0240c02d4505501e040c0c00c010b00240101028091401007820314030128440c0715001c146074000c004850141c0d0b503040100d261403100500d0544006201311200e070310201d03620004d100480c4c02000101c008285038405aa4141c0103810024020b80d155541c5200020494803400024096035110301030306415090a4410400204480c8041801c5190744299401c00641c07540308c0000729542081890710b543c1d80384003600b8060b108500034448034920100b04c0c450419080409401890303c21012065910f48580740e035440520111400c1440b0b4000c000c04001003400341c40c06a070000310a0300b08410854903041000070306000d9081e185002880310382d103038003441908116660220040d2400f072200518003110500d00074810b00645100396070001d28480780b944d8980c0202540e55015113802100c90800a1050081240e003044a009010300000100d1700d01c0d0054603901540c0c1181c9404800c9800c102d000c00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 457105638 1250 457104388 457104397
    0x50a060b040212190615020709150509061302130b0409050702060403050a030c02161d010902040302060711060d110406030f05040803130c090908090111010c0801060503070e09040b010303020f21 85
    0x20201a0b171a440401c0021032406001d0380c618640d001010900d2821008e031040726030760070380b03200100c0c80c0340d41c00d01c59941e403030f01c1150b0480021188800c940280320350010085c411b08180500b120307104940058084d0418000d44112840800100115600d64009030b0310340d1411600100082e01c1080070801081c02980820035001b0140b0440355046a81c40b120b20a80c252a081618445140300340d0142c0e03141074210140c094501f410095040ca45036901250180c051010b006110041e107169082e8152034000984564100701e00c804e00054000d441c9009080d4031600814001906011020b001c213810703405058040c43d44036008604c0c5544451307554103107103980101111100c00c13003003000640c04158001d41c00501d0003840035a41c1c88941400140c00483da510f20301001da418401c1d20006150400340081c115802d5007005070b6260340c0c201d4203c500c240203072041640441c148080c00140103010010f54140d0788a41c00300c078901d40030154075594030b80410007040406196050f4101441e6013410240 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 457106888 1250 457105638 457105681
    0x1b02010c020a02130f050a0e06060d0f06050a020c19030e0a031a070302040e041b051c0b0702031b070515090303160317240103060b0d1104030609050a060b040212 71
    0x40400c80e020303a08055942c11f1301e0040d24070b0b807585203603103010806010306a0000c1c001c03203121501c081d59583c1c0c80c0190038001409021141c0d45e40015403c2505501100e03c0d00e80d940065466540003100c00075007001c0500002d900150000d00202500d09000701c005054030340140d02441011160890ad400f50351004256400301502444001400d0703031222150b40c01039200d4070003c2c4059040d0082e0202c01c0c0c103d6407000c1c2c80780c00149101440c054080d500d0702103060300805d903c0d000ba03171803d50076440c500c564030b00c10400d8241c001c0b200c4041c24011038010240d074002c448043d000312580c030300382495010341e0080681c5908100103034180b080602200c108014864184001001061014000620801c48803c1c0682c030b905108061503501518140c0a0700d5401d003010016582843c0b000d80142c0140081044055a1103000040700c4005000b038400455105109220a504614007603480700c00e503d40495404c1c0c10403d04030f005107000d009480301c86603031001d00030055452078a2544131028000700c4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 457108138 1250 457106888 457106891
    0x14010c060902060f0a0c1203140a020309160612060b0a0f2303040c090b0328110901030c05090127240e061003050f0412051207031b02010c020a0213 65
    0x10280400113460190011113425103c101c01010130f0705141c00039a81001504040602d007500b07446540d10094011500b00300000e0005072a540d070514480e15203044201c01ea01d0080091384001241e030361120a401c1b41c8408a00180401541e46084030040d014209500c000329a40483d80c0034690320640c0c4440da1809080e01900b0215000a80e0314400e07841038405440000e64a10240705900e558003910801c0e100075401403d01ca0b404014404c4154a160143d0050344400c41c5080c003444450f11040380e003d00000c0400e035140d6581d10303041a0801d101c5c45000d02514100d40001244d0010058450542c0c600808ad41c0010704900f031180c0082000d44134118481c40f41c4202203038940c48072002000030b0000d403010324400e41000000c100b1020140c81749241094100020001c454401501c0d090300158004100a01248211000d54a50144003005200115468100000740341e26800c03600030341c038412803c805804400e500481c20703241c0d05656003000d82d0041c50400d005042c000240c880c01d4041007030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 457109388 1250 457108138 457108147
    0xf031b0b03040f0201030c020a2105121609080d020a080a050f1204110d020a0302040b0105071a010303090603020c03030f09031b0304090e07051f050702041d0714010c06090206 77
    0x31024140d8205540668450301c44031420411540c042c41442d08400c4070740002c284c2543c50f0303030791102e040011082110b58410b640481250320ba000c0e0041d10710261044001582524250403141c0365152407180d42c40002e0844800003d01d5400800c00b4000c043d0039038081c2600003010b0b1980c3e103159004a811008000c020022010f409000002070f05040395001501110f13400c150601c600720329612540e4510407800080040c0050340c41c01c000c0d40880358140d0303001c50019044070068400d40500d4001400810b418440b10000c10b0f03a60f10a18141e92083e290840d4254a070305049040340246800b111842d441040400d07944111160b00c154003000c0303502120300d4240031741ca1110007a8101035030081540c0c00442e0500c2541060700440d400344071804014640140347c1070004401144909880d6181d046907419444000d201c2c00c00c4903411a0003034001d0008030205150407c00e210056413861311801070031400320301461201c4001e6401d0714140d4442e01550b2440d212a0300519400000b240e10550070030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 457110638 1250 457109388 457109399
    0xc0c0a03052512080a0509070306110702040e15010b070f061503140c0310150608070c02040c0914010c051b0a030b0907080d0e0612041b18060806010f031b 68
    0x11142007140c0e100f4615440b619070705000141c4009405072000f421203081034100102e0542c0065210201da0b040300c00400d03410140b121030030561040c1ca0b000781d00142840481c4030301840c00520b494890100c000c2c011002ea0340e41060b0305103030160f40d0009100c3c400300081d120102c3d10981001c48100a00301120284d0303603507a561600c1c403460101442c440d580020151052034035090101d0107481d081040d06104000512111070f5201605000d5030041c094000b0118800c0e512481c0901c0c40c140d800382c010003c1100500c4060460303110f5101e55500a0031075101030055501c2520f410740b0392a4864020a0540a40040e1803002d20301ca0704440d8101c800d09100101150030262894007030901c24014114046c24614520b0400b00709480103010b00000c446014050b0726500700300d4111142d280b49010044d1200e04c2c110a00003484250305d98001511036020485c2241000244000c842146040102c1380e620448291282c0d402d1244007001d580c3c400003027001c03801c0d00c247d48031039403e09520318142c3c903102c6 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 457111888 1250 457110638 457110697
    0xa020c011505040b06040503030406030e12040303030504121b02010311070f0606170a050c0d030509060c010f0b0d030804060506280f0f0e0619050d0605040204050c0c0a0305 76
    0xc4403410400414070350204242d081612400030801004c1c1c032124a400c0c18a40803c1d640c0c4a548140010195107843d0110342403130500c41460302c0343c83c0c48070490342c66a82c0c0c01c0c02030280000b6181950900c2400c0320072900340303000d900001c41c5e204070f41c55400314400780c540055008000004003186650b508024190001d502904c0e12010284126800940d082c24803160b1821508508402200d5a002c42c1614001c03c0002504201144044800c1808482d02d031400719206e00400f00926000200032800c140c20b560190442c40706101906c40c10044410400b0820500c46030b602000b4022404820100d00800c030960800b40c0c0c0803501070200400d0408089042079484088071700485120b101050500840c2c1a44070300d00001c00d02c040c582c80b20315051440000710702c000505010301c80c09030101d00003640c40c1030007003c20050200605030110100c850402202616084034224812440c040000e030015000801f901d01409a420042801c15910741d401d44207540710014840303801031141c5907007240c003015 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 457113138 1250 457111888 457111901
    0x301060f1d060f07061113290408010b03120f0d090f0804080d021b09060f03010905030301081f0614060d060f121b290904021303050706030203010e0f0a020c01 70
    0x31680c0c6691350054140401103c0980e0391349000300030100f01520300f1101980e586425644001c041110822005601e007801303108049508880c004007041c00241501e0643c01524846410f4064070059103686d54410340301d1141c201d45a01c0c1040070b20106c500c0010f540d104210700e034495440c50307085160907207403014141c01541c020f4030181e02512800e09103980c103001d2100760b4002008400310701003c60000070f14584008240901a01144c00341d245076135025004115525003040a4981e2941c40300301240e22004100310010440400307989950749103141d4402c03030007250700855251507402103290030040d480d803140812041da59221100801c90481c200003640c02800720f588161050546464000790f100040003400b01d80c00c814010402005a03440b00b0603800803100d00c0891820750709003041800700d0041e01a5560424804101d030131003440e030a9060025240202d003101c0c2071550f034000c200e0aa10090003003010129200011624260150a005800c40c162860150030414041c0c0300f01d085444 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 457114388 1250 457113138 457113157
    0x213110d091b0e0f0f15090106030506011808030306040b0a0312020307020a050d0510020307020a0f0503040305061b0d1e0c0905330705010b09040b0906010b0301060f1d06 75
    0x1c0310400440d03804100100701c8020480d12a402075613243c0924644009a0010301e0098820303954070028848000403064003a085030b00410950f45542c54000050041800316107a601080c00c01e02000c06180000401c0d80450f80003c004501c2d41d0b40d83c034103100260a0b00032105e6003005100c3d0700400011500303603100c08049419802540c50346918010021000d64951090340507690740348002010440c0820080e00d01d143d441c5001da80e0382c540f01e86c12441d110042e0000390204003000034403000c1040101c0100100ca00a80131501151541c440180c981d0344a03080c40c0d456540200701a01040380e0310740005210708201945100182071414000301501c1c48542d0700170004d01ea070b610921107407511040c014510807188003e940c00010790508440c2c8240e40c9040f501d0442c1001c5048000c0000c2500a0410144041c1910007141000c0c0b0703060840d010240c50042c2c03d80180800444ca0001304000d0364120303940c1e5914803013840e80d105004d86501401d49100c540c004840544a01640c44907801003401a0703 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 457115638 1250 457114388 457114403
    0x1902211c020c060406051f06020a110a05090417130806040c060816051e0f070506070201151205070902040f03140705220e010f06080c09040213110d09 66
    0x2981092002410140d5440d440c0c031540c414003003085242c80c00100c0c10b0f44181c0c00031000500d5160386500841d8190646e0b081c5811000007100403907110b41c003096080b006403041c81c0ca0b113102c02003031041019000f00c2e80900358001e90540001000300790340c0c1b10b9154807442e00ca080d09140c400100c0d08003861300711a0704182c060358826024801007081d609003039001000680385c0080c440c140340591400c21b110420b580701c10841c021428001c0a07540800f2900200704000000c0d95031140e0301031080030b5411400050b149130240d6400140494018010b103901e40d60a801c2d1840d1050610000c030100c01c54110007035a03580b280c1d020106007403400744010009003a004907901d03082d91961506150340b5009002105050b000200c0410443c1c5803280325001e80403d0301400384030600100e890310003c1424110985c015130030500c100740041c049502101c10b41d0707240382c1902c10618009080c003004040c15074009400248140507003080b03e07141d0b401444102d0303030b4608540c03400a010050fa002c0d589120300a0340e900 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 457116888 1250 457115638 457115647
    0x50c0604060b0108072c1f08071101050105030a0f080c1203101a0a0c0f061802040b03031206040c0903151b110705060d020f3606190221 60
    0x10f43e00000303481e0344140c1600e000c2104c201580c0e080e00802d81000318211008400010341203003580d40c80c500c4514484002c1280ca0081c240680041c20940103075010710100d101c03007111050024040c0a024181e80d006401080070038600da8602d50070f03140400c0103543c82002072001c049550018400c059215200031045a00d034117115040c1250402d0540c004005100100d0a0b607008500a406031040708142d42440c00002901c0d00313101c0c0142910350802007282d481e00c4184240100ca07441800d40260090b0750800c410040c01041c155203104e464900c6e4a050300d0240050070324503251300420303200045484d0140c0f12985e41d9030788404000702585075004050303c561050000f0500b0510b5034030701801a14081d00c0f50344000e00c046484040034028035020383c1000550b0714903502e050301100d001103107554000c2e588101072082954260502c0c0c885800000c0800550a001c20800b000251502c4d4000c02c1c1c6071510603000b486251014031038131118190b004144100d011814a0a640c03c41d0184155085030746 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 457118138 1250 457116888 457116911
    0x50c120a05120403120e0c090115091701061806060503130c17060f060d02150f0f07140606040c14130306020a08010e100e0114010c0606081f0513030c03050c060406 72
    0xa8030001c820f0440b490740303c43c3c47c005480c3d4039054030b01d04403000c001c1d0400c18000c002004a4140b400c54203d12902c0101d40c3c40219442c20560ac40c504403005d442c502c2c0110301301151070400f6151503101c2d02c0002a824400b0945540c515209a81c2d06846520311074041680e51030604100343c40f01e440c03d50ba64009c0810482000b10381ea00c3c2c154403c40440302013590400c1a4001108010001c60a04285c2c00c089100b1302c0781ea81403011105041c100243d01d80e2501003d00d024041081090740782e911038002d001c080380d03c0c1c1c2054042d8100b0b01c0f08585680b0401c2211002d0b88901350054008000501010a0000041087e034401131103035040554814140d036050845a0410060142c0003600384211158100b00c0c24960100850540d01000164526606c100d40100c402c40c003243c07806008245003410008203000c0000d1064641103890044650143c00c0321025003c80c2c3d002c8940140d0300c0846541c0d440002d20031103980f1b000358400d08110303041109210840340f030540700302d500300d07806650b80205054 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 457119388 1250 457118138 457118141
    0x40f05131413032613151107060c02010515130b0a03030509091b0304030e040e0706080109060504090503120709030602161703040f140f03030412030c050c120a0512040312 75
    0x818042800c4114544d444580010b480d0460003461505c030854401c006400300b0010303124020b0a40203207441840604801c00c01310f000d40d80180d10884c0e0440c60008100f80035070040c0a02442041500c0c005241100944140290034403610155920795544600042003942c87c0c001c2d01c13000e14000c1d56000e40751040320082c0001d400b000780c9080c8140c1d00304020800100b0075001142e074010381c9803502d48012035031100400d014241110400c0e1040c0206e0001007007042c2d200341c5045c1200e000003400d210890f0703910107002c115501c03c400988103400800001221a0b411804981c1180b511303d00b1440487d900e48401089030450b03580800040e6160102d5411301484064924528a5280c2c003189141807035990030381d203060010001001c0f040120314005100c40107002041107508840f080c2d9071380e4907052070048203007050051014003203031610b641001114451403d480b64909100300805940c040701030301c00d0003078118030003504c20081c4c20040d041c0e0740012400d800303004074402c0e2a40d14a006079141ca090 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 457120638 1250 457119388 457119407
    0xd0816150e15100504020706090f1202060a0e1e07080609010c030506010302040509060409060b10020604050706020a03270f080f06010e3102060408071406040f0513141303 75
    0x1c1c03101c0031a0207000b503c181000089003154002c44c0c0041e0780e0421032070b1a0004d80031081000c0d08048090101c0820300c140c50070081505a60b0303078242c2e0801d41d43c8041010441318804001003440c3c1c00b0901903200d0180a01e515075141c640c0030125504a9540e2071030030718000c3c0c00c0380c400c94940d44620461030700a80500480b43c010100b401c0960425040c0301c0898006c04004105d80d104035222140b800c20f000d496400038550080240003e103801e04a400c010359201d600f40c50480b49446108000508035202055140580b58581d48d441045a90f100741454407466807000c2180c1006000c9002809104003207175100141204c0d80038001d909600c020513420501e050780583c41540409003040003c42035005c0142c4410b19005c10920b1450102c1d15070320181c89650070080d04034200080104000e10300280340350072500e054001210941c880010310540c1d0141e442080c0c00c4840046040c851858035640c0518146480140041c603000c803c0d00b501c000d40400e58030101429100d00c000c40034180d1000100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 457121888 1250 457120638 457120663
    0xc0504050c0d0c1e03090303090506071701050d08071209320d11010507051908030103021e0904110609041b030b030a02092a0307050a1d0d0816150e 65
    0x3020500203103960070051044e9109900b0405079109807403010940203500c114480b03901701c030468040c3e02d0019000751a03900f1211a050f540c0905400018551604030030840c6600e500540c114100011943d8240c51003d00c502e503101400000c02c3c0100d017551840e42c8840c02c11a00c1200407640d811400c1c0140c8028031200c1c8140c1c003920109942d00c010070140c4502c10f2180d00c0030302c0c000741c0c0d50a450a0190030305001070074403ea280182000d0009020041e030142d41a6402100c951b008000071401c141d01585600320f0b12900841444000f4021928400d0440500000174050900d00308035030001900310f503110781411200341d42d1001170407040d81d0b00d80301d21400d400c4294002c0c400d0b15016000900340e0391004040180e410b80c840e021511113940508040c10054442070301a40f030341008400a84950410b0608600003001140d0b1440c0341c200300702d0480400030014041c85084403031601c07000c40f0399210b044440714500600c9203040001d02d541d0740e1130413000b158041c0083d07500c0041c40d08504016a10055 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 457123138 1250 457121888 457121897
    0x602100902400c0305070e150d1512060b0109141c05010e060405010b06210601140d0e0607030b0603130203010b102d090b03040c0e0112020a0506031509040c0504050c0d0c 75
    0x4220040c3c40d1300d21900b00304030920b420389485801d2400c1c618040d040d02c08101e0441b40c2c1d004000141034003503009000360bc134456541401846000340046441c00341a1068000d2200305a082c0545400d24450108120707d082c13038421007915442d1941030940c0c0d0100300d0030380c280e440341e410007060100a100380031602900702c40b0145050301014000000e02c9000342080d41007642a800705100c1d03800364945c611000c12140c4040d480d0303104644004001c00340b60f10307000141c1c003500b000204501e1103449004402000200058210b441c0c00103448a00e00c2c59083c02c9805650721520309400b55110044c81011000c10765a0443e1030464600e41810700100c0030110802640169003048420742084000042c1c80301c1b18070b215102c0d03580d800c0140746e21801e580106904451080081004024501041d00213402601d20304070b01940c03070050100310311048420401081c1d91305510130b0149807840d9059001401740c855203241c141ca0300001070440308142c424114800b4000b030302c000412400c0c0682400c3d08000e080 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 457124388 1250 457123138 457123157
    0xc080106140618090118060e01060f0c03020a020a08010e1504030206011215091203181e083a0509060f07020102130f0602100902400c030507 62
    0x2016007184582603101c42c070800e008100c20702c1c0d2042c400c0c025500200b00078032a0542e540c3d55007607800c01c0d00c3c0d074882da0300c2140d050039400715118101e411700504903180c60303848081809031280c0454590310404d00840850084078041e102680d10250f41d00c0140c00030303c1c00041d8080d400821b845c80d140c2100d6280e26050745e0700b01000003098004ca0200e044940747c50b50b800200c0124504400100881d06401c00c109103051403250620603440c42c41c640d6040f071030700d08010a0a0000681880a030f4aa900500038039400600030258040b210450300d03035504c80e100c00d40c2401a16a04104104104062720521422209070039502d0444201038100e11000d442c01001a4181549134548404008200031191074201020800c030078400d50490306a52441c00c100d01440d9164000c0040c820f6032403181d10700500c42e4a0100b02501c9107032044070740040e40140152141100c1c030070301441e900c0780e400740c0c42d0161201d054080911150503903403024000d0303200350028080c0d403030800203401c4440142030441007000210 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 457125638 1250 457124388 457124399
    0x201090213020f160803010e01120b04030509030a0c0b0c01230103060c05070203030a020a0b060301020a0509040c020f0a030e150304050a0f3207080d050a030f0f180c080106 76
    0x20000c0e00740004006001d80d0341c10000c50080c1440c46413404500d005402c000d626030902410401071410380740e4101c1482900d0741d8a80c0e564078082c1c1000382c040c00d441401004500020f0040b4010400c0083c0036003036a20010f400d44a00c50121f0166002544803180090440b041c80c000f8032504400c10b0303540348088800d8000c0d400041103003505020007003d540e0b44003440c0c00d141d8018400d4913801c540c0141121b035a110505030003900e03182c200b01d04440c68196000822400c1c5018000d55459501c0d603079609050040842c1004042c220902d60300d010360103a0004ca00c007035241403080030015400794490b800c0000d00841800081e42000055400b288403d0045c0400034030003041e1713600302c03603003101032070705a80102d080c05040c46403107900c0c80c084103403110000d030000001100c0015405c0320070740907561550354030312003142c43e0361041c00c2590010301c04004040c50b035030190b800140b020400c904002886103074071000070111907598000100000c0304001c2041080100c0402401800d80c00b0f00900020b0300c2d01 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 457126888 1250 457125638 457125649
    0x262101060c20040f091703060607110f120f061003110d030e060a2601080d121509020c010b0406150507050f030304030f1b02030303041218031103010c02010902 70
    0x4400081101c400000300c5120321060b1482e0800300301e4010803c2204007a0003002c04000d082c1904102d41124a00c0f1032044130b4400300d81a41e100d0307640904082e2034101c60340c1c3d07060640a41140b0701940455600b4407a1401d407550b205010400c580c0400178014a031502c203826151280003031096030143c0d0442e0080c400120000034040f40f0305400c1e6100d0301e02700710314030701034a04841804a054101c140480c000c040c4a030321803103001c0007440724280d5611958001d0711703400c4458824000c400803503000c0c83c100c900a9125144003001c00c0440840000e80100e90001d039451070700150700402c60f203a004151400420400e108191402c3d4048404110191801041840c2c2c0031510050400340180403c50704184001131210601d11482c640c250703542c3e032420b858050078041c0004929800625204000340318008413000b01d601c83d940080013507080d543e80e6614040c501d090703000d0940030000400c40200e1349462800a81000d0f600c552100c0d8a000c08600605003180c1420003c442168144403151000d038546 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 457128138 1250 457126888 457126907
    0xf0108030403020d0311010f0e010621020a12050f10090c060c1a09010e0703060f1107080306060d0e1b09150a05040b0a030210030501050a091a090426210106 69
    0x1d8209666170200039243d160040c0140a0070501e449d0034140071031080003065224600f42c2d40f060400c900800b4074010500003403010b000000b5082030100c442070181c2e070b28140840054074410800c03505c2102e49941c8241c180318006403e42416922596a10b040001c00c03200300000d410a443d24800301141a150309028034681003000c44d44950010114400e00c4081d0001182500102c00311384025986c0c1c5003200041c115854410115860680305014031901a4101d03440c1a40201409086444da03104000c299403000e01c5040321550f86d00c00e105501c0340188208600c0449100800d03099640000a001c59404000c201c007002c542c0c0e80d400d136034081e6256a204816101c055900140c6121b00101040300c548407500040d60003080111640115945604264140c0d0420307101040358030307034410054064504242c00c0f001081c03510f8464000c0b03802c1042086a02ca0f00078602880000840d1103d6440e864000300411403406c1e00140915164114880900405922480c080c90644c0f501d07030002c061091 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 457129388 1250 457128138 457128143
    0x30a0605040201020313060e100203040f0e06010e09040f0303150f14120118061103070503010e10051e031903020a080307050c120a0f090f0530060f0108030403020d 72
    0x1680c9001c5000e6920800640e102d01007070f010304146207915010080c06a0600c00e4409206013010b4a6034200a031000c81a00d04884024584954050504045041400740141180c0c10000e00c2c0101e0980c0d0741e9044070b800d004070700a006446400d400760800809481c212484940300d4034401004011840c0c10000200c00c40d180580310380002c6201740001f45d942e044060000c5002d6003803d20141c0401c020244211145115039801c00820050781a40d40e1903000446e00400460420b2004000d030720700c6503110b191310108250f040c1e10f180e501e41c1c0015409810b5030107030343c0c01030101c884c6a0141d4213003044600250f52000c01400f5070860265402035450b0b42d000e400600440d00400414061402a81a1072590072590141c1d41c01000c141c48005458028845400c000381180e050645058000e044040039a05895481c03044e83d4200402e00c00d19005002c0d0448041c00d801c0803041d040c03043e150101d500320611502074200b07804c0a40c0c4980f23141e0010381000303109400401c02080140c3d030b1450100b1030681d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 457130638 1250 457129388 457129391
    0x1109010b1b010e24100305120318010603060501062c10020708070602161421070503011a04150e0f060409120c0606150207030803060f120105060a14030a06 68
    0x7401e80d00c200c1d0240029902d41d180c180701c2d107001800d5000040ca40c0405406080740f00304807179a201a10110195901d00c0003800c160010403100c9880e0104a000f50382c400d04000f58001110b140414082c00c4445d02d03801514601e945000520030554016410344fc5001134411640e1585681c8621041ca50075121000c2c2c0b00303100780313022a82114020300504004201410a0300d20107035448101179181c09208074500135030380c0d6400002c60704c0c1c81506100d204e8402e000c2d00c400131060a0032444030740f83c48050303405207113841035940001c0c255900b40506000c54100d480c2c40e2014140004c240015601140c00140308010081014000500201c61a540c0103650980d02d600e1030311100003140080c00c2c504806826510220f1003038882507085200c0c40a59803280d2410420141d5882e035071317580d2040401ca0311005070401c501c10400b00c1c0e0780c4400385801c200014a054101300f00900010000c424040201c0c1c8165100c10402006180c010072444c003d18036102d50320039420300d49001a4644007079400040145 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 457131888 1250 457130638 457130677
    0x305180a02090a0207020a030807030905030c041a091b040b19030c050a180e0f040b0a0e1e010e0f160608010b090907090b03190e030703051c0905191109010b 69
    0x550703407022248001c5030080d03404ad6445505040041912400b4018103009101c0e0740c00400d918106440b81104107007440c400109a100900c04201d846407025241d68034030358584420a0084005800800040031401c0e80e16941c1c44a01000c03c04030505038401000b45072506407660300590f00441101c0d00c0c1101d44c60320180401110b1441c46000d004c0c2d420040c4d0082d480800c001c940d00f6003e04003070185005840b00722036582c5094824081e9a05848900015003000c0c0740e00084605200611a09130b5024001288a0301c19000662500405c0440c0380860361000d595840034054240500c07000d8141481d02e049030b136040c00c15a401e24030030000d4031030040d04c20a002a840300d2013000920302405482a44a9480c240012250a81d141c08002140c26518010400e00850b400100311020250300d071302c2c2c050402180c0c82161040303124042c915541c06407120b00c2400052014004904034240621200d01c00e1807060a2009584000d09900c5d4005d80345c08006000080c1c0003007d850455440b1034505164 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 457133138 1250 457131888 457131893
    0xf08071203050f03100314280302010209040c09030b0c250206130303180e01120206070203150405010606091e05090a0207021512070c0c050108060604150305180a02090a0207 76
    0x140c483d00340945031642010041c819924481c01d40d10302245d000b4101c5500240c450400300380c44d1003181650310500c0e43c0c3e00b24900e42c2c1100c849481066035010340001410400440301240655408000b41400141240018804c0040781e440554000280c80c42181c104030214a000c145c1111031143d0145000400c406442196103420032511820042120f0703024507681d07441c028100c1d000301024801001c80c0004007250302e84951306040d040341e51202801c20103000136024001c9a510004042c0c0c0c250048801d0f03405035200d0301c0c203020f008510503800000e071145000c80c000c190381015003001200c10040c0311002488088005010159501111110295150300d080c280003071040040c001d41010b040400d1100d4800c0c04000391015403180d941000c103030794900b90111a24204205c00418080000b00140042d5116092050307200d04054025464182c46403445415045041c100b48002516581000200c0300343e40c4002220030081030080040e94040c0c1d0002e01144c0c0014645c004035035020580405 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 457134388 1250 457133138 457133147
    0x309050f060c1e010b010c02090c0f0f0a05070201030f1802041d0a05010b0f060f04120807170307030608030c030d05060d062f180d0f0b0a0b0a0f08071203 68
    0x4503030000c0210780405501a60902e003024103003d00310034552038510700c0400ca50250f5100ca03070141d03005255402569800c0340089160b004800c5d910845201400301c00b22a002c11002044030000a4541544400091000505a48201d40048240d83c1450120010114000600600c071a81101c021902024601d0401001c0c0306a40624146100300d0300000c05121040d4405461b1190540d0244130b4031480e1300620940c4d2080c90b0110f490340000704403c000e50300e020741c080903405210750410361401d00b043d01c44501607420303900281841007001041c0000030341c0500c10301d40104800c00c040c6040c450601320341a03d0340602c401000511743c4480006405030707104e0109042d420360103202001f040454060488000400390300c01c003143c0c140072090006010140c81a140a541c0209100040055000500c00144042d020440b100390050102c580016000800e2501c642c002c9400000c030410150104590902254012030a110001c0014085084041a10340a4546054001c08001d1682c5030858 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 457135638 1250 457134388 457134397
    0x2010c02040507050d0f1512052521081c14070f09170a0f061e05100e0c04030b060a030c060305010504060b09030a11130e1015030309050f06 62
    0x354002e18280c10401c010ba00200581503c489401c4204204110040309004545020780c150600203d1640d0801072603210005000400d4892403d941d10001104912580c01c041c0000349038000a10300003c0c0b0086030700700203104030f502c5038403404024803180307481d405100e205440000d00400b071440c0786000d801e81c5039085a001c4510fa00343d80b210070f10301074400038011001200144d002540820700040c590049400351444203c0e0310700a4003042c840ca5032200d20105511408450b225200c0030341c440d0189a1003840000070282042c0031505140040f22030020a01e240c03c000e110070264000e119080b200e16080c2c0d0b0980b5481040c010854480300001500d000d025403001700034511f941c00c0420080d0707040d00820b04031142a40d0500042d52070707500e5420f43d40181c01c407a03a05503001004035400700c0d0143d01c100781039182c0540320448607141c1042950540300c6403108004168040413025540900610402015808842e40c40200604603600200b001c5018441c80707210311104001d00c0e2047d0b44030300485 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 457136888 1250 457135638 457135643
    0x70e0a08070801020c0c09070503071d13061a0a0818070b030414071521060f120b1e070c02031204090c09051504090906020906040305030417240402010c 67
    0x84540a680b452007034040e5006031610012400386103c0341c403044c02c010b1081e40c0124810740340c0ba800d603a135502c0c08441220b4401104048405250b442c0300c42c649030300c0032002c0c40315103185007c0f41c0c076402d00d0201e503280b14856051002c030000401400d80d00a0b0321541c8503412480304400659102d404020b89803900c005034016081812001060000300041c56184000004410082d40c80d0240e9901e229502c084a10103c0780218100b4008801006011454003100a0140d1400150191541654601000d075508100189500c0308141c0051004d0a0400355000c01001d014205100252602c4210110060080c8040c42813a07030400c41103540c1405013046000613144810380b115aa900a04080d0200a04410108158000104103401d102c183c4000042c0c15141303052400b03250158400091031990400d84829a0a106100442e40ca2000a10056006400858941d400c0c00e0122064003005e00684501d41c2c0040601000c0a0403a5140780300c0711100c91041c02d40e580e641c00140c8d030040c0c407400c00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 457138138 1250 457136888 457136893
    0x412020a050a0e093d14090d02011802100f1b08030a0f290d0807052505010816050d0c1d060421020a0306050702070302130212070e0a08 60
    0x8196070482c0001a449060f5910403203001c901581700032100d803a171010290030201e81e40403603103100d106442c0c150200e5101c900341c00544011000c03003503041c2c20340070354520600b81c2000c0000554550709008045030754215400c0c4602500040e0f0004250b840c075004c0d10024000c60884007052207014a100a2600c440100c0044583c1c07514a06448640d000b100c13110ba115162810b00d100f84a07542c4a00307000c0e44401e07000650802c05001c000c1e00c4e1400100c205692012140d5280c1300000c841002a054241c8114010038500d10700d58803a4000f100508400c02ca26005280104a1a80d02c2030040d0341250805503080624144014200c542d03200700404c20a02c6810f00182e4905c01d40d000f40c2200c00780710088a10751854054404100700ca102c2d5100d407071501c0010718440c210080a914004030014401400c80c40280e5880d968501a64400c48881015800040e000c00950034100c01070307802021a4041145040c4143d0002a900c0001030643d004100c00e040d220545030701d030600b8644c05003010204 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 457139388 1250 457138138 457138159
    0xf09040b2a0a0807081003240f060305010c0f050f1305040e0a110613030b180601030309030b01052d0f030708060411041503030302160c0e24060412020a05 68
    0x22500a907200b80d004800103280000010f00d840d12540510f8010020030f00d80700d9016145440d081d6070340418031000c90003609056a6502c0010851003403404e4001d2409011038258a141022400c580040c617002007071000e001554160382d50701c01d00711803000c0801d084641d11041600c0c07000c84002d09540005030806e151408000301090700084403403c003445210310311002d03400304040c4075a034006c0346100140180c148409100040045031003551221055144100300803100c1030040ca07000081c0d10507030118800c150f040c018030804110007030160906996032481e40050b1404081803d0282e094112401c8441c01900c0040d640d0303200c01710032420b00600b00c0c1c0355603407508002a20ba0b042500c04550010311000f80d240d0301c4c01c00340281a5000e1800c041c03d0a0031340b658405901a502003807480d42c0d09e100a01d18000050b400200394000b800004904418a03e08409500d03898a22468400d1aa0a100c03289070f15559880d01190199040003d016a440318144003081c4e02c0d050541100307030700140d0b509 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 457140638 1250 457139388 457139461
    0x9060a09031b0506101710020d09020402040f030b1506032e1403010b180601050a030207020a0306020a0e010206040c1403070e0a09021005070b13020d02030a03080a0b0f09040b 77
    0x1503001d0245c03d000002068090743e800005130002c1d0000e0f20041d49801c0740b07101811625041c5d02402c5000c2c19000b0128041c401c0d13900080032070340503400c007850901118105100344180c074544182c3c0009000c0c41030b1500c26011001920710300000340960703c100c0002d9031b4041c001c1440340c10030114500d544100300329540c850909a0781486440741c1a80a580b07400c000102614054a641804c1d01100d50802c0d16515601c0044500e5884105114181502040a4030060700c03070b90b1504000b54000e01c40103071541288c460003801c441c594001c0c5411980543c0502010840102d5018119001103201109171048000420b003816102e41c0009401d02603602004440355298101c200701074422181c24001e01e030101000d803114024040098a0003030740d8000200300740c0c03800b4030215015000a10307540703100750990300281c900034035218114001003041080c030000c54014098030000c00001c4801c124190469004584460402080a8135030340380c1801080c00e41c1c107d0319181c0c200d20024003540303140c6114413 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 457141888 1250 457140638 457140643
    0x41103011109030d0513150c0c0e060a0522020307031e0c0f0f0e01030f1b0e01090506070302060c030c04080601030f0318051f0210150806090609060a09031b05 70
    0x1000e1003802030280c03811302c1d4460703480341003240c40700320321980f821101c0c0e07092500d0721042070300a4194109224424150402107080c1051200082441907100c1c0764034a0200284000304000b03034040e42c0219400907a814280c941a050700c052400c03002e500503140e076035410003200035080727105800341e070f80420581018041c500780d017040300024544d807515007a09040c16011200d40c8401354245001501c0710400e9003003580f20b45c0140070030223500e04001c111640704070400300c1a00000000b010200e4680400c0380d0003940c00581c83c000500702103e499061501684000e5210440100b014250300d000000194264500c0015074018101080840b41c680da120316054a10081401080c2d010803100d1110f502ea00d04030000c42c01c25600090501610f0f00c00e0014413072032648004200780c0c258040c00783d00e0000500c080c45144d2030705040d0820103aa8600d4482e0590429102030712880080d084441040240c420008010f6042030009400040035000303824216808004140e400c144182412041001d00000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 457143138 1250 457141888 457141897
    0xa0b0a1e0e060f0412110307140f0d05040f031b080703141504111324030213020909040b0a0e03280e090c07110904030c26120411030111 60
    0x5107021640c0a4a84400103140410112002810102c0302500b254a0360310900b2842c00b03000c26002240e05001c0103698056100304002640c1d14154007c00c0240d000700e508102da0041a40390b420201d2400d420041c4911040300d0300c0c00098a501080c0c0030110031a0342010b0130400614244050326990394984c64148610710031108240e18a2140000d10b880d10001710f8461170250350301045002160840000703000100c0c0c4549076008000c1c0c0d4480e20111400d41b20040e144010b560010b04400c02c40c2184100404d910f0f003500c0e40c05005d841405000225124518290b0b0050740184030002e80355100d2291502503c000c0130700f10114040400d0588203101c0b800c0c6407600c2846211078828000c131002d10201c030f90350743c00903240368400302c1c0f48049844007244000524441d0f008400300e03460840000003040c0d842005640480019203c0c0f0090401d0100303104040302080060755051403055110307850f06603103000300e94641100340d8000e400b180c10400201121410740d100513009004180312002c1d22a5107400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 457144388 1250 457143138 457143161
    0xa061b051606180b040612021c150812040b0c0f0a050106180506091b040806041b06081003061a04140a0506061c05090c030f010203010305010b0d050a0b0a1e 69
    0x310f0b441000034400101c8110099610000c0b01900f0181341c0582290342c042030021041543c4c0d030070451000304c800104030350f0016482c0300c0000b0401c4030101941081c009865440b84e03500340c1111030095a4034580f54200e03400c0700d0ba02420300d5100c41000c1481c504100c00300d6903034082445a03d00c0c41e0208001034103ca01202d007a00500112903c052030071400780c80049841c0e0b0ba0080c07500380010303401d100001c1781c80b940d068072850342c9080c60746541c490303481e2080680b03080ea10b608041c2c0e10708100030705000001d00941160f00e4111060704021b00c80c6a1511198007004005035158001c40c60000f5041c1a040701042d8020000c2c0030303208246012a1480c04140d038803120103030604001a04a060403011100f01c100b0550740c60a0040e142c0c1d001d0390040001804014480c0a05860041c02e990700700001c7c0302e44001e40d000140d49514500c1c285084a481c584514020600c140b89040412804208e05180741d410084d15080c1d03a8848420304020300c000340024030806d0100c25988440000740d0300507001401c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 457145638 1250 457144388 457144397
    0xb0f091204080c03070f080c0d11030a0b180c09010b071703010b091305071d13060b0d0b042706140106050d0e0a0b0c070804050d080702040c0801050a061b051606 71
    0x9807292040480c200450098041d1580221a0707050345089c0700000940e4180900d000c540a11003a400082c1813080c2c848050f50030404002c02d0161001c05036040070307000759455004181100840700890350b149014030460050440100f550300c1400940802d00c1045040150b26595075a1548000390183d0000c140203401a0024a9001d4039410b041c1704a6020390015160002030032084030042000010344005079802400048040b20408401d0103040040d15100030b44030344130551001120120b403072000c1110722481c24640001e140d9041401c00070544520178a0203080c07031419040c6480600040340303010068a103490000074855a00c00050400e031103400806121a0710708840c1070340c2d1624611030290180e101c0c034011503190301e51130008000080c480ca6a2508080d607400020300f0f1030095110944500b040083c41070300b117103090b1240342208481400c191207217504150100e030b840c0105000c1e44007070002c1300010080c14030b91121035041c0c07907a21000f250300b151840503405050701440d01c207400100c5c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 457146888 1250 457145638 457145653
    0x1060f02070e15030a120302040302150a0905060a0c12020c01110714010e130609023601030f110c0d20101509020c0604021c0b0f091204080c03 63
    0x10300c04100c0108403001c0c0a0024001d84408500001818010348102c0e410f00c1200c07003420020710072000c080d091030643d89005840e145107005000300103880c11101340644204010040302070380c00258107400d0300e9040e5a0140c4403483c02100381c4404d08680c1003e0008a0000c1c002e004181d4002100c6601890030303641c0c014100c18222101ea51203c2a00544202510b684143c0269501c031f00400003002c000100800030380c0000c1c200f0102140c86582102d080b55030001011188440c0c41d80c0341e00c2310540440403000c08003034228803640b15940384803030031410181c17964925548400103411041854880141c4a81ea42d01c010343d400342d940c6280503800000c00e1021604035003032080d40d140100d0341c8208001401000001c200c0b03010040c81d0884d812100e02e40003200126104003903102a00d00e0b94644402072585040c036004002c2c030001816180800088001802c40000b02005015a000444003103410205e4441400103810566403504d4034103d610007080c0090b81b0540082c2c01ca00000e030540c15140300 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 457148138 1250 457146888 457146917
    0x3030b060406080c070204110406110d050a0e240f19020109050d140f030408070c210602160b0709060f0e0603012105011b120506150c12030106080106 66
    0x1038001c80c40781c1008100003000003445480004010305010340f005000290801019504110580094003d0b100144c03051100c0b5403041e2042011040c2410141011410007490480081c0001c111501150041c552140e19403c0c0c54038416514414038400d098003521030700788000744041c542003a402c0b00760001c2003034840c2110718010f00c03034280d080350050b01a24044c1109941540e500c604188a0103190b4020080c040b4803c0c881d0000c0c0d40918415407403280d560803141012403056503680c010300580d081503400d010403069240300007140507500140c0543c8550096150248426401001a00d891107070b03410043d2441c1d1040d50700c416904282c450189120707502c40101c4030318009801c16a0030000420040c00220110440e1900640340c81c00d10810300d010030794131582901c141180301700352007800300600360800b50040b6008000c031001810401441c5000c1c07000682056014000e491030060000f1078040400d000d00c0601044120001c02c1ca650356911400100440000d104840016103801000c441 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 457149388 1250 457148138 457148149
    0x80c010c170108060610020c150918010e070309020a03020a031109090d210b13020310060309021e060d110304030f030e0c040c05040302031209010201060803192f010903030b 76
    0x103a41d00c100051139507a4894052040403000c5410100a5128031980c80829030b6502c1103104090400000d03090f11000184144040e4000540d05d00a0884900005002c43c002d00c03641c0703690181141c0740101d450082030000c40d01c040c6c4641c1010350855665580031040c000d40800303141c2c440d041910fa44503590780b04840f00d84c980340c080d681d01c00046c0c00750301d44aa26800600340010030251140000403a400580001481c001c05500c0d1041c100343c001c005c006c10109144294001001181002e00104246600250b444405000d51404d405030300c2c0294012501d4010a542030f9400c003030b00402c1080c4514942c05429041141c0840004002d83d04055460740b0034050a500012003c009203035508101081101a0106c04032250800c4014000000580e4042150012010040400b507135075448210009080d05d145d41c00c90f145940c002c00010b0340034603160348000504605454580120a031030394200b6816a0401485c0b07104031800660112004010350010031a0351190f00d08012004c0b81505202c0e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 457150638 1250 457149388 457149391
    0xf080f0304180f09050d030c1d0405090c0306010914150d15020904090303050a14100603020c19050c040b0108010803040302061c050907170102120a18080c010c17 71
    0x510940081c40308101024030402c030501c580802c075030081480f5001c0d03102030707044855620382a585035204c10244c401ca9501842403065411180ca000d481d4600d03140d0607040d14850000300726001d40d0751100010503000040c0800c58581d02e000703060364800d5950b02c41c44000350801e2801070b18a51003141c0800d6420801c4c10b021000009d0181005a0000413921803030084500c011010444507002c1128520a030340354070070920a039209443c00a00307810248400340442e451a0800c000c0f04407035100340140c2e207034071001c00d0701202c90034035016a698102900941c00c0800200740c2c000c0c03416880d8280810414045200d40d41c19805441c02c02c080c800f041300459107100f0031308c00c620b5140c01c1007100f03002500f8070800410100079510000c0310a4050014290111802124405000e0f00000420b001c0340700b41c2491255074940f0407000b0750078243c1101d555108050060030560307101da034804c2802c402040c2a440311070444e42001026440702d2038000c1c003d01030300314070515000040384a205251400361411105 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 457151888 1250 457150638 457150663
    0x90c17090d0e04090203010902150d0f050f160c0c060906030b03071415040b03040813140a091d011109102604171903180f0206090103090c0e010f08 65
    0x7001c94000c544103001c01001c0b00c2d0b1017031360103540b90030082c030140c0c030b4281d00b5140c400520b08030107951b50000d01d004002c64402234603108905040505015400e2130000c00d2980021071648000c0070034120706401d5030b05005000000384814200480040e0301a000a00303001110035036242400350944c0d0504054680c4803501962191000f009002c00a50600f1205009000182c61030985455160100b10314660000c0340c0440e02c00e000003401c540e04680e0744503502c0c02801200325520b00c081c64103000400c481e8060080c07507141075642c07220945030000888ac24071526444002000440812032540501d0340c8407088650150b904610455000d900c1101083c002c1d80b0344001a000450800d040c0c060b081d58050000d0741c180d6090301c41a00ba4060820090250b8071180c455109038181c1c1c00070140a45514590700d2a401483c0708080c80821300589440010a904540c0e403699070f584080164014041c040010f01031030b40c00400801e181c030005a165040c0d4602400702d51486036102c5049954400020700c1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 457153138 1250 457151888 457151897
    0xb131202180705130b0a09050a060c08090a320f030a1104020708120601031a030d080627061201060f0b030a0b1201020901031b05040501050d0204090c17090d 69
    0x400c041d40291407112038208450345440c6152840d114052410134209400148a20380700107030324140282c002d04480018007055606a812601d8500e0140824a250700054080301d400510f001c1c1590b02c2040d510b000d00800c8a40303400c030b0410b43d81c0e81d0031a249030740c003901c88032441c1203000840e528100d158180451320041c000c0018104584c0c400c60b0400b02c1480315500660240310341400603441c1e01c0900a16403d07034004034602d140050004040e1105400d4540c1a2040800080c009840214003c0c00d5000203040110040c0c0754070300424070701d24044030910103891400050f9400110300425841c0a200d044401046844808020a003217031510f200c1c0c0e0080c1c03426064108417052040020715805840130200080301100f0102143d10390a600306425117a950005510940e9a018462455117960241c8103030380380d20980300090304611880c0205814044046071469a40c2400e4040b00c2c00380c00c03c00c2c0140702900350240054002e008003105038075803228a0000600e003d0000a190560700c01942d81d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 457154388 1250 457153138 457153159
    0x102010203061c0c05030d080702150103030906050a12063309030b04030e04050a0c031505100c080c120a0210091e050a050706020304060f090810110d060b131202 71
    0x100041203a4000c0401c480001c81380000182c25a4240a820098109a10346a00c5850b003600000e0401c41d540000208402c0c1c14401807021a070301081c52001d892050928a5803114180302c291081e4142c0c5032909840d908040b004500740101c0140503200100417540000400d40a10b030442c2c00030f5004ea110400031300c01200800100748001c0390796800900a051074141c0c408503c0100c0c4c1a03030011242c860045444020551030654184141105c0d405911420110749092a00040300806014824420030000545950a2001035800c581207002400116840c9141e62507c00c002a00451041c1c005802100d5050f41500c0d50750040011260f4030544030b041c2e125103004111102d450b1503105480622601e01c8039070009404000d00d2003d00441e80003140c40e40d00c0e08000030003807140f1415442c01c00c84607203020860700c40e0000b0b031011180074088000c14000b862924041c4980252024030b4142414003400003a5004028000d11600500748514001103072a00540d01000e448510001c0d0800744511 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 457155638 1250 457154388 457154419
    0x801060f0f14151620030c0315150604090636090317090109050d140904091e0f022b0209040203010e0f0709061a1803190b040b06010201020306 63
    0x850a40148003503c80d410140509040380012482d041c00303c501141010b103401803c1d11a0012045000088005200701c002030b1000c20784039540d1203800ca82c80c0766450080f0740400340018001810b0200504215126944c81c607240003d07100305d12a01d40031044c02d00b10610791030051070907400c81c40d21882000c800030305028a0031004242d0071109404000c450060820000c5000040300d01688071000080340c09482400d125041489558460091148841c0902d040d024101d0031340b042c0b00e4007203030005407020701410030615881d0140c0422400018400c151410841308152090000380255500c00813140290f13043c41045044c0c41c0105150303e01c0445031401032401044590f406403002c2e0000c00c41d503440000705c610b400c03900a080030380c5030440344051140e0310207031003032800030100b01d0300780310b100034981d804090715100b012414125003010404441454a0402c0200c3c0543c0700385039900110300203810005420350741902e085541d9103044022038000c0d807050003500d000d2040209103900382ca2003039 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 457156888 1250 457155638 457155649
    0x80a151b050f0c0c09150109060e03070501030b06220f06020d090e060118080f1b0a06050f0403051506120c10051c050f04030207090905030f030a0b0a0801060f0f14 72
    0x880c00f0005440b03903120244094a5480c4c201b80640d2a040b00401c881e40c04400240c078600842c2c100008003d0080007101580e5000154003044032028240019050b43c02030100e44584074a9040348040036100c04030f4425510f403200075004803800348100740b07041600c5074000c0b0b0f2661144100400006c1c100442805a802403a4480b900040705040c1607269803103071010800f8140d1a540310210320303006402002c21002050040c1603001c07a000880e44280201030000800d00180350040004029012804010b022304c5402181c000d550004101c4440100c291048d60611104542e85400745c120060b0a500007940017a0041040e200200031914802e80355100f25003035008028102c5440307020701240041800700c0d101d6540a403076040d400b0304061900b0b05011307241042c03903440342030741601d46404200450804002d80390651030110307420359607844030304c1684060700c41740701e804d540411007100009030f01005600600c2151910b10742001d90a07524a83d404094059219210012a03045004c10107843d05 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 457158138 1250 457156888 457156897
    0x51c0801090e0f15190b1507140102070c03020f09090d050a180b0307170403080f0a020c0d080603120a0c02040b0301020705190b2518080a151b050f 65
    0x40c50200e4080e49100d640361440c00409042140b04030113002c040c4400810300f140803944452040006000801c04180400c04c8404080700c405064000440d0b40c10070401650103020003000b0060095403280c88506101c07950f5422032000300d21400810890400030f041940c040741c0700d40c43da007000d0441e00f07074043c509880769400445500100002e81140d02046800c03010040040c010001b0415141e240c001805003890b20200200c0480803920b00400c4002584881c12980c40500c201e0324440b41e40740c1c1420500680030b0622100f0f0386002d124a07500641d0740c0210241c1c4581021030484580c200c00d008a0b002c14814a01000e000032110220311015051640000d8401071014000500c0c010a60300d0349403c1c118240c800c0489201143c15483c140728403001c4e080e401a1341c59409030030030100500070700e10340c0708800340207014400c05148102201481c826284020300c03262040e6100d11056181420b006040404003070102440d08090f003a4040c800c0e240014110219222286089401d11998006801 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 457159388 1250 457158138 457158161
    0xb0901090e0a0b2214011505151303080c0c03150912030433230123120f1c0509090a0b1c021002011e0e010b03010903020a051c080109 59
    0xd200c260854500031000215041c900618000010000c8402d00c00d0944100d10080c1d81c083c47d00c4201440540d032214028a17020403106180e594800c140041041c9070720303595001410300d40e0045101c040c000000300310745200348011401e07aa411440098414410182030303403940b4095202610030a401300d551001140c00c2801503000000000f10301e6a080100310a0b030007400c5a1040c15500280384000034003c20314555924000c406d1101a0030001c0030f441c010505c510030814549212003d00018030171031900e12340c44041c2c407803041c010024141c65901c0d08602c58040440c4203124460f15a002c450294105602075940c0c1e0500c0c1c090008100103002e900640300400c0543c7e41c0103841410b961b0b801121104420b9160300d03c1100c442c0f80100304441c4207010420042d07904282c491446440580031001c070300008500002010030515a5207401820380c1815150150b02e4810183c1c107050300041d502114900c1102200c80004100c0d54041c03502c012010701c0404541840018001c0d2180340d00160084107 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 457160638 1250 457159388 457159411
    0x40e0304210204060f0314030a08060405060d0609080a090f030809210d0e0a1d0601030c03020403020411040311150702010804020d050604031101110702010215130b09010b0901090e0a0b 81
    0x80700c5400050441d14140d02c6014140c2c00036100700308002410104541e0f181d85a4050f5003071808a00005d4901036000703181c10b20417990340c0002081ca645d050001598503410a81c2048211441d01d014142640810503050208000c03040000f10214041070700810344c1e07401041142004183c80c103003c0411032000000030340034100c0a20101c0c01400704580307015414569594148070600740103000c03c140060b0004c689441414000c1c0c40403400c0380d01c1c00b9420600a00e000a4924400d5004400034050794000a603c10b040150002d0741050382c10241c0140e9008500480384001040304200c02074080741280c0c52081401d0240b4809580990b01e66170b441400601206941e54640c1d0711a41049412034080f0b02049003c98012601c00342440362100d150b000800003890700c241900007079941d068000120f49103940c1040080c2c04072502c000034804031603020200c25a20700300349c41c00501820409101500442c003403c00014145140d0240d1801c2c056680b025109071030142d1600750180c1002004502c440 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 457161888 1250 457160638 457160699
    0x40b0a0c0215040608060103020306180a1104061107090212040f0203070b0a030507080709060e280f06080903040303080a0504170c0312100e0c13090606031a040e0304 73
    0x40e2184a00c0c40b2071000c56181c02c0d952182890009026500d025210f941018810f004001881c4c4500f01c000b014120301c4a150103040d9202001000030f80009c5000380804540400c00107006600b041100600700800c0d419140b4403611074601d20101d00445410040e0000d0110100d0003042090200b00071603400901540c5074175032212450b503050303030286283d200081c0d651420841050360207145980c10019034a00030340c41c1490f200f40184465a01e40403a880b50105c43d5002240404669296034441c41c0071b94101305103135948202070084030381407045170045410000007450201001c070440c1c0c10f99906072078041e41d9440d1115020b0091400400840c2d41c400083c0035003400d101480c0143c0410015540116a41d08410800801c0043e01905000a8410b00c030001c0c4144286001c08940c808040180d030394999000ca845038071003414540c401d001541c0b4140740071480c568140c00406402454000b41108550510103003c01c40703083c60340f001c400da0401d200c00e000500f080091440c2d1070480c2c43d142c1180303 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 457163138 1250 457161888 457161893
    0xd05070f0e0f06040603021e04091403040513050f0c0c0f01060b0d2f220f06080f091b040b120a11060316180806040507060e0f06040b0a0c 61
    0x480c4468100840d400501c80401030150302030800c1a9100100355000d002851540e4007180c2c03a085c00c00007850b592103511246d030700a03840c0c0d988100d50700740d08549204070208040d0035440e100e6110340a524010000d41804030001100740c000c403805000c58007004101d80c0c0e40c50240004c3c0b0f400125000140d070180500d48980c902c02400307070b00301410340282c0b40c0b5910480c041c1e15900b12803041c0000140380d2028200c01d20b01c0d01c100c100407035010201c000c2c00c6680e000c4a11030008003407411081003101c2811031a01040c0d41a01d84684c5003603c0319078907060301e10303101c880010a101d001240c50380410f522541c200c0404910411240d005400f02174008219081201c0000f240e50308800414005980702034084014854400d0307211800000a0b13511030300c0d508000700c04110f6442c1000c40d00080c0b0600c1a403000350450900400401441488182c41d002c0c1803515200d81c070748000f407203520005114034100035614600a12121300b5803c008110078070301880c0200e4259940c0100103007000b07020103d00d50030f01 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 457164388 1250 457163138 457163159
    0x6030c050102060f1530070503071203050306060f1b0c0102010b01140706090507120305091e01051803030d180b0f10090f11160b07050310030f060b0a0801140a02030c090d0507 77
    0x4a41b012034090f00d505804c0000785854000e00343c2c0074058170b005140c52880800d4200c4122170308200c0a440c80c0d542e400070340000c0c0300741c1c0c800c2e44c49202c183c0781306c03a04840040713601254079213040000360700910070310080368011503081e0440c1c10500003494042003a000000c40960001c1d51043c803810903602030a13a01c0e050502007140410050740820000a2000308502c2e1103208213800ca86146550b00400c49000002011806160304612031910b004002c800c3c2503404000307907180700091100a10054861030ba000c003031900c5100003151002c1022000c103007844c00c0c10780d80d40d2242248040851501d860304000c0c4e40540041b03030ac0030b911140d9440340e8541e4110450010b002100f0840d40310a1000c0140c40c10703e01903000102410200f160610500c800b01461001d0f850440340c000c000020900381c10704106000702540108264089010240050301368410f410104035007440c004000d5499460703d509100380d100481c1c0780c250100040140d125545855802c550a850080f0200e41d5000c1c2c07580307004030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 457165638 1250 457164388 457164469
    0x306100f2007030303230105060d0b0d03030204050f040501151206083307020712020609220e03070c090e0f0d030f0501050102030c1203150406030c050102060f15 71
    0x606641000c1c0081c824145c150144842400c020b14401001400311000c01c050100c041c005c80e84541400218101808004c0d0803501d40707560014401d0038800c0003494054020b501500c1003030f000d80d0003085902080d1900b80b08050481700203001c841c0308030280da28100c58400075440901c040d20750701d8002040750641000135001c202100c0c401e40c6040d800c0402c1c82c060314443c0384680725064410b002002802a03010600c2e0b001c0300c1c1c50301c00301042c0e0401840006c195008001409810442426000d0030b10710480d240c81e4001000c048040103983e81c446119038880c45005070150012405c00c004002c0c00026a0210400b85030302400d6526001e0344a08a41c1401e07820040c2e00c000a445109010003014144100c60042c10240011071604401780b01503a110200461881c0c207050001c4000703240842d41440380b52070b10300000e2003045100e48a2804c2c0c0303080d61085c081d29005115aa0009084846400151307016082c102080265100f2070420007108282c03072285036100d105c1c0c0c07060418002d4551380303650 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 457166888 1250 457165638 457165697
    0x5190b13090501151a0a08070306120615051e130e06070c031707080a0e030c0d0503150a03051f020d050108010b10050421060b09070207060e060306100f 67
    0x40340098480714868094131a07900035007840c0d4134070020312104000309002c9030018240b17800e117103040d552040010b4004200395400302054112a110480c10000c00c0c0c0d011a03400300e2031423071a100613601c450500145411004d03004c801803001c00100740312032030103180301c0d004040761580200705042568042c1e820039809a80907400301c0c001807000010503411010f0402d030140c83e414040e05d40e2510b850300408005016080108041c0c1e50340b03500c00c0162050007103800c0202e800d01115040070788000001e000340c1c0300300c4030400c402022040070001e5251000f03180c0e08a80d0000700510401c28840707501c48190403614183da1450f039027004003c21f039034424022103008080713020000a20303004000510842030407070520b5404200d4104003d20015094031842c000f002c0a04204803801c212501e0000c00401002d4015940200c2e002c00700304a144d4001440c20513640207648130110045121306001c40c5000030344070164440494494202594442c00b4240b0580e852413811440c050300300b120301004041d035943c54 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 457168138 1250 457166888 457166891
    0x21207140d05070b010b0909070509010e030d09030c0503060c0403080310050a0308090f09040203280f2102010b030303040204180c090204050102160509010b070507090509070f060305190b13090501 86
    0xc4184541d281c0c0131401440400405850b2109010001c0d80d0040020071440a00001055103049079100744640100c907400601110030380f04007400050480005032004a5031651241c01c041450b080c04604d140c0600c50b0700b90040c0c2030504650302d2030402e4000404480180216082c001055915198110010b5000305091503841c4000c50a110320310f16001d18080c0585500c005000040e200092800000702040300d031001c00c00007140107a28102140080a0400c013000c1c0c0e804024402070f01030716502c1c001c0698043c6410003d281d400c2e803d0b141e4524200e135140c0c00620015015040540140310044010384507000d1811450b0380d4641b200d4041d821441109a01140600041d45c04220407100840d44c440c0000640f840c4c4000200d901c4c00501407200152004511802001000c110a0020f000c407080140303d280340010420f40e5648042c03060040c00e004115000800324041d10417280650001a0000c42c0c9030300500c41c54002c0c26181b03641c00d401030518200a081c1e6403407445205042403180c2c00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 457169388 1250 457168138 457168147
    0x50f120d0506030d0c060e0a0501020d0509060f19180203190201030f0204080703170f1b060c0a1205150319020a090b0607060c02030d0501030b0f1006021207140d05 72
    0x38802201c0d001050310b4080e80c4500000034070642c210700704e044c00692001c070104080b01c031103441c941046840400140f2540c0042081c031003940e140d0704201d1242034550200e409175514803501c0d003410803095031984140500c550b40006240302c1604424000c0508801080d080328140c0d0100f85840d81c07807540383d04480c1172020154115a8980a540f0701c0d5054064198182070400303000c00d440d02418440240755514401411064a050a083d244102d450400c00782e03e5190107001e081e06144e488440c202240150b00c00a07030106002c1082c0d0310030b520307566601c011000f00c1c590444003d140140c0b61b81f000040c032620100c000d079002c02c42082e42c420940003c07515007040d40305005082400d90800002c040c1004401451b50303e80c4004d850a65401c540c0109240d03910328402c3e8294450310403d1403400d41018008403c2c4481c9800640c0580021580708556994042021911442c81e0180c031005801640040048416080103444154000c800e840108500016034500d04400b40c6030440201d0400316 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 457170638 1250 457169388 457169407
    0x80406020f12090a172e0c020319080403020c03060901020c0c0a080a0b150607060507020f0f120a09090c080610050703050906070807140c0a060e0a050409050f12 71
    0xc5032003480c845682d462030a00100600140103002a80100c00310682441103801406108100c9500520040410b44101d0707581a0380c4d61514040420074031446a003405200d03400d083c400421513140a000d401301500c0071058a6040740c035403d0141058046104018958400d940c0c284090390003408040e000690316030905000c1c82c102900051040d208038001c1d101008610340110305000d036182d11945900e1165140d03900400c0da00744003a4001c0e000400818a0030800603581d03c034502510941d02100c144100680e58180c0d104115508042d0070303008040038001c00c00c080000b506a140240c1400c4001c00c0e01c500c01001191400d00c0d00c600094040e4080c0542c80c142071480b00050051450490324080080c2c07001740003032040c405103e004650010b4123005015070103066072600350f4096501c007580d2010201c85903840c4040d02980c0d101d81102200050403030700134200000b569402500d841070389454841048010b102820064646010304161003018200c00d0040f1045520801c01058a80c140b04 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 457171888 1250 457170638 457170643
    0x100504050f030708060417070609030215060d021806060c0102070516080303040308340306062a0618020907081609080309040f02040b070f11030a0f080d09080406020f 73
    0xc5010a010ba0051402848130010119100b0ba00c40d4001940d00840868000c0c00c02aa100d40030001e88414030308020724081540c0400c800940d0303d56681c6918098490004010080300c42c140c00070760189090010104e00b621001025920000050030582804001511103003640e0041100700e8964201c080444506441014420040c202020045086281c07d640c0584080030140035072122454640104000c3d0202600903018070032039100c0302ca0702c03041c1c012014000e0009401001d010510b400c0601d8407a80fa07141586c03150414017841d039005007034551038030301c0184540d140a00c41e010307181c84a08003503140d00030b9440c042e510b07507607400600b4904036000300316907001c00c0342d10710170072411010821502070004199130f070701801202d0000b903134101c0d04200c40085c841e0b540f1003894010003055840c244555292103c1c090790280d02c014441022010405844039070103480282944e80c0c2503403034800300305c0000251280700c580751400110341c6861344600300d1682256000d480168400004103840c030702c05 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 457173138 1250 457171888 457171909
    0x219090f0f090302031e0d020a02060702060c13120c1a030106142818060f090803040b07080c010618050a0f0911060705100c0e0306100b091201020910050405 69
    0xc0c41000c006821156070001d440c6d00c0b40070b104030446c0c0000c1980302000c030480707011204490110802196036250140d0040c0d280c4204071070340405805501e000500306009581110003030394091440d841c1c0707242025010000c004100c1c40a6629096100d07011654011408444000c00f0f02820013039120741c90f0000003404c151007071030110780034003050100b540014a409041032038020100014010000f020303008a038102e003485820350702da1044440004005030070405035902d1020700d070b40e103110345034035070050340c0d07403886188078001d04142c0130802100030a005c00702a0500344507040011941d550350350f5014000c8003070549040445075440d410700038211454030880d172442c02d90701e00901104403240c03110180d041012a41d07030300840001a007501009405e04c8034000445242d5002c11103408984001411642100102c0b4024421180402c0c0f09507a068286411151a8104282f9048160060080f694401900541d0540d024860f000a039601d42c000780320400003960f40e03980c41e10310300b400b006141510f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 457174388 1250 457173138 457173161
    0x7020f1c05070f03030605100e090601050f0904060609080c010c080406080601090306020307080709080d090b0c010b1c0b1021020427060606030b01080604270503190f0e0108040219090f 81
    0x7a012255120f6480b500c806543c840c2f4242803994903501080c058400d0303485001010b41e403145ca400d002145850b0007900c800240e81100042f03441440b41140103440003030803600042c00224050108105451007a80707020350000041c90100e0b02d40e82c1d0b0340d80300340c16600140c5030380001c03a81d580c04122003581c0c4602d401e002095804001d108a44806d1b8019189584034021b94000300000960652104000d400040000340c014004401810412079980403082052404991440c182c80c045502144410f0145058416440008003280410b09001801c5100501d0498000b500c4005030040301516030b065044004c205d110460a036032070b074580281100d03090741080041c1442c110003004581d9101141c107034404003e8800041724150315450413000c6510500d05440080d0a900113410072801001524101c1030240c4452808800d80d201900e05410400d0b501001a5038048d40c1c000540c868040140c1050025140101403000440e140e4050130045d00001c1600e501da201a030f00501c2c0a100b854113030403 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 457175638 1250 457174388 457174397
    0x5060f060a0c3f02030a02070b070302150f040606080105100506030405030f04060518010201061815050411040303020c030102030408040b0d1410090507020f1c05070f0303060510 78
    0x80110002034440c0203150344101001854001c41c0104010079000d03001071180c00440b821032516103200d02000751495501090014154240e1501e07450002007510700850140e00039080042c1403403c20242904030250580c1180325405101c00080500003015000d01110426042146002d040000603a8a5540003d415070b15210400684254100301141520000c50740c4540c2c2c1e840354206546140640305100b44001c000040020320740e9040f1006000c1c55405100000207028050010b82c00c9880c03602c240002039141c510740b440403139182e0f44085443c820380301c950742d43c240d103810104003164903040d894500e04800240500601d50100900e2425100840080d86140b0b01030b501c42d1258025803041e2920380001140e02040f4194a0304039201b1042d0140c10802c1310328142c038103130031101203501c101c071505882c4c00d010942462000c13440300401d43c0c1410041500031014411462000c5a8905000400c241071182200040b80c54801e40c903968001c1e80c011910034180004c00010116110700c040c03d10 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 457176888 1250 457175638 457175659
    0xf01050108310510020c0706080901020705030d18060509061b03060618010c15020d0e150c16240b061e0906040b0d0507020f01021c05040f0b04060c030506 68
    0x1440440b0009554110b0380c200381c800b00340b0b8980586483c540c0f102034a000c9001194150010000180302000c40740d442d03031102c00540f101100da038202d10071100003070800c3d0404c01c40240c42c4261901300c4040d410625400c100104c2c1d680d12a107003215001e95100b4519004442440052030140c1c0204541c10000a103441c5103007801800150781e03102d80c03c4010f00d41d880400d05105940e004e0b06010400d0b43d00040302d800f80203c2814840003c0d4040c041c00d1020034544140640404e800041407084a110400c3e40959500e41164920450704010a1910480c0c824090b880000d070900c40c0c000a021415250390140e175010240d42010344601c1e03075610f401084140071004005910142d11120700c0044180c0c9941d85c0079460100e60503104540107031101c00d900080c0c07500d4a290a030b105920941d003d07800e68011343c83d4080120b00307034807940e154480e008483d81040803404036941e01c6541c000b8030179900c034040c0210507640d4000c10350b41105c0949a065440c20b100080c1900342c003440342e0020f812515140303074 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 457178138 1250 457176888 457176931
    0x8010320011e020a0c2c060d060f3201050906090a05071404140102010509012003090132010b130e100302041503030e040203091515090f01050108 64
    0x1d1040c00702c0403414020039400c0030a04140207000f19895290058503803615191298000750450003403000c444030345601001410b111644100b9043e00881c0000c01c1601001c0f00358403540c004c0c020001886480564407803d46010001c00001e801005170005001c0d00c4500c448003a0007031015050344081d01601002e001c01030a561842142644020300c120001001d4a912000301c6000f01566031604109500243c0414902018420400000000d038004c2c02241c1e20710040c10300b40d0300c201c900d804c00c1916084101c07095004020203507900c122100300001d15041e020481c0034058618581600c10b18011841c2040300c10550568240581203035400a4034000e00b1040c0b598850100b03229200c080d00147c00850081c00c04019074000a50300100f082c03000c80710031440030220303103030911045000c110455039211090515000b500e10a0694070080c0624004203242e40b00c60a0000308008210714440c400500103030f998503001c50082e121002c03840305660401c40094800798024110302c85071846920001c03039 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 457179388 1250 457178138 457178147
    0xb011403060f09090102040e0c070501150b04181410080706170a090201031b0f111603020d030c0f080301050f1c0212030405040f0f151a090d0204020a0801032001 71
    0xb000c002d42e040301c050b54070760007100d0080c0110307009441c091322010140070014400502522040d4010402000078860451030041406460304c5054220701090000f0130500e100014842140000690b020401c071000900101030034804407001c04210020b0001440b8a6a0030002ca030050300071760604285200c105490001e81712002062001c445860301a50402c6900c40c0d00002001091034000c0091303500b24000c01350000c00d1401e00c1c13000181c046e130a0034986880000c2e0b038019804d0010703003d8290600316001e011405d001c1590950500c05d03520380f0b11001440c80c001e00b0308002d005400c0180c0300d504000c100100910f9503808070348904020030101d800d81d60b6007041e0100d090360444044c3c000c0e140c080304990075030190f40d1040d40d1051505090340c5642e101900032450300c4843d82010050b03408803000000042c8111b024460f000c903000202207000045e644010a18614000d0003640720b001c481e4005000d0f80d02c400311410010b44903400400801800c24001c0d11041e00c0c0300208121480d00000081 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 457180638 1250 457179388 457179409
    0x30604090f0204021b010c09060c08070c0b0c33130302010b22050907060518010c06020d020c070f150c020d080a020d0f0f170402220b01140306 63
    0x144200e680380d48420800003015202625030794058415500c0d02040a160600c1c205088a6545e0650a2590419080384110b20070070540d071540d19194103070301150300d43e0101500552803c48464110000108207040068050311082100b100101900c490042041d00380310a81c00c101850036210003a2540d0303d10102c454660300003641c004070700d0b0246040c00c08034050010b034031841e60400c0080c0c031503034400416481c101d204079201407818440c0c1e40b541407400380d84450502c20400080c109010703038840d00c0241c00c06d059a000b01450030000120240e11000100e90144002080341c0354009541c81c05007909010040c002c0c032058815031011481c0c21703120300c907140c0501032103010004211702400456594040d802c043c1c5ea00000c141c0d40b1501c94400c080e43d191000c98591003c2003c1140c8164240c1c0304081c0c2400840e001c0c0e07a0ba9800c1c0f40c01008200302c662015008980c8032030b90b03a46003aa140c40305102c2c60030124410202096611041d030026046080f070030008030b45030b0030410800030103845005100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 457181888 1250 457180638 457180651
    0x170c0708070507030b070e03010b0a260f070e1812041a0d2d0b010207051e13020417010e070605070c0b03070c0605090307031409040e010f020304030f020604030503 72
    0x141e0710689890304038202a095080208410645028000203507449001d04085010580003000598800800c103c50080e030f6100d10048103e103101c100143d06d8010920742d48800403141140c20341c8841c0b0b1072007410110660018486455514100503608003400740a801d80320a0700090161110810480b9045100c2d0740102044520000c00107240340040e40d040f900843c421750403c11456039495070302d00c1e06191240754940f600c01e20000b40510003840d0703c2a050107100507001403601030f00e083d01380461000c0520150040e4440340c40100c41310b40340d07851070421441c24030b0340060b070700ca0503c441014036600d03a00074219607030b240c000030850403440018042e040e61075900b4410b40395030b01803920303080c2c20529402080e0041400700a100c00c00b90000e80340d030040d9100300414401139070350300c00d0a076490041e59005000140c05000c0310b44603407520300c007c01404501a00119044443c86003031401d40d03441e2989041580d50000c00c110500d43e120a0b00d41400c42c503840903141500307207030b10010301601014280 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 457183138 1250 457181888 457181903
    0xc0a061704120203091905040e15060f0406030b070c12020708072303030d06030507050603090c040b040e1905061b0307030c090f090c0806030303090d050c07081507170c07 75
    0x21407001030f00800a40b405410000e10303415504444074040580054548541d03401541490200000507a021a81c0d40e4110b0700281d41e042d04d41d4525080201c4000003185030b43c2c00654480d004804900d03400e509500c260410344a03107203000c54515003180c2c4500900240310031900b0410702489039101c0412802d04544262400402c03072011254800074030750482c659030368148000101024403442c1508a84200e902901c1581e03e034a030349400b8050306100499500c843e1784c0140000d0110351901d40d01802501401620007c5c001032515145468200c40d12207025035116050742c0d180412000701f0400d60f015030401c902010703890b0a51541001d034000981003509040d141d0620100851088071070750024407580c040d00c1c84060f0780d68100c8000f00409074000d40010181800030701079007000030131030b4024030310700f4000d007940b10038004c0c01c03180f5070045140001e1a02490400203032501c2c080240c200c080b620f5003070040c040d01700248041c020840f180c0358080c001070424104a49580007000751501640c10212 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 457184388 1250 457183138 457183163
    0x4170c1917031906060224070e09090f0708010207030e10020312010306050613060e06040b040608030c0d020f0106060206040308040203030d0c030c14070507060c0f050307050c0a061704 81
    0x40800c5154050400a4074800c004410003112001014a450600300720f8034080020b0380d242c2c0422030701c4450003503004840c481110101181c84440d01d5216511040c0380c90415403001c500e1001880801080c0c403043e07010f40c0411074451a500051200200502c0307030900840c070700b0740d143e5409040034078000500c2c0e215003040218048954020b000b01c440400c843d20b0302c403c0710740c3c50f0314001d401450250390b014080c3c14184034660349003203d0b102d800f042d609101c0f06c2040d250b903401c04000c060300810b2589034103c0e4483c000003035041401c0001d0000c0d9256840030713051507166040003d02d4161202d40d164503da051500400103a50003240850304a40c151a203d40c07030760b0b11800440d155210300c00c1000042464144207060865141c0e00083d000c0c921780d51001080d00040e401409107001d0b89002034070a0304005000c00086020344030440c01107102d204101e481c40140d480d80f9003142c012001c00e035140d0300080801c80403450400c0b200005001c141c20076240120060806031500b200041c002000080c1049 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 457185638 1250 457184388 457184393
    0x90702030d0504031e170a051506040e0912040e010311011e08010f0503070303090e0403020f030f030a140403050706240602210309190f0b070804170c19 67
    0x403140100124034051000381424500240703009504120002c031100d04004219510313118844502c6c8a242c504001595500c8820400d0700401001c4c00016a0b003091540e680c0190710380e00003500c0101508100340c421850b1049440e41030280007035058821340000c2005004008003824400e065a802000540181d0600c03001030b2440001d001060a220451200703114070031342c0c0f000c011816100c1c0c0c5461142400c1c0d982c3c05155039125540030003070125103116030502a12281108199000d8003038812608070141c092180d50840c0d10807129003552410010070400c55815034018007800102c50102203003a490f080d04d00405601481c7e038020301c903d85941c0a9000440c0c0e081118800c1c60030508640001c0ea900c0c14080d50302c26425401484c02204e008007102c4c50f2540509491203082c109020380b0700c91700c000744002d0114040c8002111080c0d00b400320300020030551000148038940c0c5403a0b100550405003080c01240015055102c0c00c03441c100031082d40040049031400f02c001c404c1c19030803403801203031 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 457186888 1250 457185638 457185643
    0x2130506060f2701030c231218070503190209070e04020324100f0809070801020301170c030a2d0b04060b130516111c0e030c040515090702 61
    0x128410a482008034520350150b411400145910400100c0500007120203030064056402607503400380401c980f0512a031540208500c7c0101c10403010b0b190318030b04402c0000204020b441a141128a0300d004101158004020019030000d400c04400500803138656106040c4011001a0001d0103008c04002003544a8000e49440c0406a4020010b40d128a468800d81d8821214042050a151101c02d40742e00b81d42003490f00d1809110b15031f900c02c541c0540c414010740e55071201401d90311b01d900c41c031070001034550703000c1c80510b01914040310f0030030dc140ba07440d10191601e032607010050300c00e4105040c510000340301a208101084000002a8060580e10245803640b007502d000107810340c20501d04000c104001c40c0c0c800c4031103143c22240b00c00d110150100001c11644104c500c1e0110000403081041c2040c00b82a214038450784200c120f80900c0c04521080081c1c00745401d1170004104070308600c104034078050003142c00d440400c1c6c6080005203420300355405003800a051460007294030201044040384203 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 457188138 1250 457186888 457186897
    0x20a0609120207050402070209010909020d050f1605221508060408220308070605040f1b051017010b0f07170304060f020304021e03010b030f1c09030213050606 70
    0x45401040015400d051005001c0300001c44940103025020000c141481c091095440765a000350451007242c0c01c0c01c0d0b0920007000d80302d80680c5c1c0822841030702000160100101e070210f0307010401529071144107900e406015845504070510610f507070030310381010540a20180c5942e0b0b80c60000030401140072001e403886005c41d604041c4a0b402010100001d0264002c000d168003081e101107040308920400643e4082d0321580001801002c00304290030126040b074000307681050003042080413403285a42c44400c06907840c4080c000e1905030180030440b0f0b00d421404e5021908242c101040910403421205242442c14044c45c6100d56002c0b9413108140b045030141c40c0303110380c04a55203100302400003e4071040d0300300300d604862060401c0d40d050141c07038541c001d40e4000c9a0240920444120318040404601e442e525860f4240d036070341c0c9201d002c6580070030042d00002d00c01d40240001c08003459029943d45d0301c01c11b031281801190b100401c010b03112400c07001d0740c502104000140b1502c40100041c8079104 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 457189388 1250 457188138 457188143
    0x50c0f07170d2d020a09090b0604050a0e1501080108120f1e04140303070f0212160902091201050708130309090518010c090f1505040305060f061c0b070f020a 69
    0x6450000c3e08810355544050940100c80c0032807807100003140b602c0c03101381e01c9030000c8103000030101002000f440e2400c0e00301000c100700050140d030070070b5200c01c0411402555036000d081815076103030030712014841001c0c2070000c050302841c19880a6041c1141603a8507408200d161454500005540300701078000d07010f03100d0518144003003400004d206207400f512a04680103000d450329542031a20420302c0c00001b114417071940300070302c40c00c81b829540030083e9802e580c9510940c2801030ba54140401e40c0c0c208070700f001030251540b0040c2c075200384c10184444050205120580780e031400d410b00c03001d079410917070103503120350b4071203041c0003040c02c034903040f0384100303031540f042c0b0156007400248000000804002401c0c80300a40080000b040c1000c02110030701d00703500c21455010101d6000380300d42c01103409030450000c0d4504080d40b80030740d6503a0345c074604101282c80d420000d6004040c0041842c00610080d07407107848581030381000c612178948002212004c3d080324207004898904d05150b60003070041418654 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 457190638 1250 457189388 457189391
    0x2030102090d0501091e0c06030e0a05010509100b060301050616031e0903063c0207021302090a0f2301032310121709060f0408070603050c0f07170d 65
    0x202d2514003503002e84144403007125040c1c1030140c0660f007240f04a05491a07150070005d001d640c5803404605074001c0454a91f05c074040e0040a140c3e8001c02e000f405060700415000000389200d800d0b0060050803143d1818501d4400c560400041100b65a50803c1c0c624820007031211844414603840c1c161080c00060410340c100050803420b527006541c0028460085038041c520034003410101305d210782c0c2c850101c2100110004c000ea40e101e1003130300224803420020030013082c00515104544c0c00080300744804c907822101c20b0303400041500107402c01c80349010017010345021103562581085d14648007442d5040320068800903c03038000065a119405c40240c7c04011804110b0000202085031000001160b1260040c90024400505104001c0100c100e40d074009802c1130400c0c44001c03181d075559000c00c030341ca54022020300c510650000000300520081a44e0340041650030f01d40003004d8161400207118003140f150a00c1540e01c01200c80c01150401940242404ca204400f07039009600c0e0b005034907100781801d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 457191888 1250 457190638 457190659
    0x6060d060815160302030402011b022b050c010201050609010e0c25140706050f0714070803070605010e060f090901060306020f070b0f070527041503030318050606010c0203010209 78
    0x102c044046640201c180251896030098410001d50591205840003800211444640c10b490640c40d100900c659200406d004003080400044010314101c0750301e450740d8800141408802c1000030002c04003100e1085c0024092485c0000004030341090522440c2c4c071030412500000c02403085001190110803810708289050801d40d544455901203d03941100e140000c500c42c0c072601000000c403c41162072a43d102e41c64500904070302003664100344401c961504030f00802000307440e030034001000540010345c01180c840c9501e05041054540c181d0101039a000788600348012030301c0708089241d0070b400035150054561101c0b480036004040ca82d0014011034070104084c04080c2c060002003442d9802040002155120901810030a80b0300f9103400020070700400800b4020324140e082e01d41d00036051418092110f0602f0040340654607500d4042d8888071081d40f09004054140c030032480381c00ca40e40e81d407005081040e0394241c0c0d200c0000e490a4140159888020115030302501101c000000c003504005a0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 457193138 1250 457191888 457191913
    0x1707110402040f062303070309032607120507050d02090f03060c04080d020105060d030e0d0c12120e03071404061d010e01080a12030c090510021c0302040e06060d0608 73
    0x400c03181380241c400250208003065000400e083e45180c03c0c40988403c103240d500c1c1c0003c1500142a000710407000d00441d00940b401e010010040030581d81800c2c0300d24403882c42d014000420f0780d035144031100000d91a007414403c0740ca61040c280c40c210340d03129600596904000000500c02e141011a40354103214120410006c0b0100390050030846500104440090b803040310141d09031041150455007141650690b003002c684100d4102410801c0a03066928070351464840101c094101d4120717050314250500c68100b0012049176041c213a0300e4524100d42884050000aa160001c034465400c500d082c00002d1202a42e81d60b0141c0000c00c5108910310484100c0b030f15805a001c0244980a122440750000161401c0082210010340e0350016902083d2182c81071300750020030300324084074100842c1550111346a209e03045540c080b8401031b0000c02c44070341c95290031010704140b10420000c1500522007040402000c2946a4200b8001c82e01541c8942040c1181401040144d022980e0f5106207100c1c59103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 457194244 1106 457193138 457193159
    0x3030a090f120305040b100b0912030c0102040f050f0102070b030112050a021806030d050c070e0c0706090803160c020a09020307030e250f03170711040204 68
    0x250022941c4079418103110301c040351000b081d0740c4c0040c4030901072509000c55022082e80f560003080c6041c11065180c60143d41100e50089001c2100d144090703c003842500d003407202c03000c003c5403103540d07440024185c0515881560b014118041d00c0060a5101240b040706895418902501d0740c0d11b005040c00c007074010031030300307644034000c1c80b92000041e55507510910301036180300d00d980000d04015042600b0022020502001d01004001d103120b61400031a0a01c1140c1103a80d050314569204403550159100700400201070900e0400c03400308000307041000d140155200d002043c07445201e502c05403001082680042d51107040014200700c0610703260021079012a0900e400300303528400c034020310b20b0301c0e6846030f0303c01840303000140702d800711003000b90300700c00500d084140b41c100340c0e1450b210011160201030039000c5905002a4041c240850340303001c1e25400001604c00c555455841610300c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 457014388 457194244 := by
  have h0 := BRFrame.cov_init 457014388
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457014388 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 457014388 ≤ n) (h2 : n < 457194244) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
