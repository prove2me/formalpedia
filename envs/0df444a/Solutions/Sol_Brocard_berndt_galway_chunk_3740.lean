-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3740
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:32:29.945552+00:00
-- url     : https://prove2.me/submissions/11874834-0dec-46e4-bdfb-cb387a6873dc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 672482014 ≤ n < 672661870 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 672483264 1250 672482014 672482017
    0x30b090d5f030f010f0308030601200303070c050106050409020a061d1c060f0507092c0906011502161a16080309010c26100803030a050a11130b030a0f02 67
    0x440d000c1c19050350b43d25100841900c040c00680281c42800305082e01480041d82c080100c0760000c1003420100c1c815007030810302c100142c42209044855000202c1408591030300041028402ca1240009100303943c1c2ba00c040c0000c80d421801c000e58414003140b4108445406150751404907400c201e08030f46a070910b4804500c000008051804a8540d5811040140511441080321a0010716001c0c081810012070090507800c060003098002820100c202150303406500c1401c98a10510812420300d24285092580f212002d10039907446d004c00310003000b6224408110b0012040392041820841820300146018034844007094903da001c0402244100401000c0d9801040d0301c2000101d80d2468240040350a507104442ea00d010705c504461024016242c9058600c2c942c0c048902c07082c06661071442c1150001a95488805036020000a203d09101c55400c00d901c6a51210000c0c403c0d641d1084180d1030b1446130452020f098405850b040c481424002c2c0190b070003001d45500407a1344c0c580e020728a000c9 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 672484514 1250 672483264 672483437
    0x90f07080a020f09060d021e040509030306030d02070605042105010e1609020c19022803023a0c0f080304050f030102250c030b090d 58
    0x140d80c4400300d0002185000e80d1012103e420950310000700342010804155068035180c0700a10401c01105107000005105400031002c410003401800780742407070000c0c03d40fa0703402680e009020740210b203062a41d083c00024140704030b51a9690340c0740341c5480d2911804243c0100b4002c585c07005000850080440e400740100c09039981c84002402d14520004011001d030356403607100e03030120f90041c8207055914801140c203203021180244902044c048610000d0f403100c204000e190305456500c000703101203c004a100e082607a03c281c588400304400b00021041000a0608401250300905850078002c88400f907a180c19500c9510841d9486483e61503010705c0c020f290b081035240783c2c8003217410000344c0b806c07141141d0090016402145402c030322030a07100d1011a11940303511400c60440b00d04c802c000c41001c0c10401035800c1034404050342400c050541e101d00c5220381034400142c1c01071300708280804d9407030100c00026400b164503410b42210103905003a0380c400104118580c6500c07860a070800140c5030000c88 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 672485764 1250 672484514 672484529
    0x80706020d060b120a2d020c030d02040e01060909020304080417100c21020708030403050a0e040504060905010e0c0307050f060f0c0115060306060206060114160b15030f0c0603090f07 80
    0x1001d1038103104450131608000700102d8480c002c030680c00044040c002c286c0c1c00d580720401004d41c0d41c45806032481c0c80e512035000301c20340d40313880003900055170f01d40c900740a810f0b0303a5144d0b82c0b640c0e8035503505403c1090f40800d6402400c203003805c110070884916004c203500d02d02c030040700c1613a0b14524802c69070340441d2140d0321210b0104000c2d1403030200240ba010402140703041400421428100561154600b6000042c80101440720009000c81c13001c0c01050b60610600e0014814840d51520389030082c0904210a0112640c3d070a05001a82041c07020840600081c006001010640e103058108a0340c6241d031504603403c07070010044002003010040042102c041d4036000881c5c40342c0701c0c1d07100501840b4154000002c1510f000360601c01305901240e8030790803102c01d28050130340c0b2888021a951610928030b10f00720303062000111400704400c88800354410b80d1241c0110841c48400c0040c0f68807103200012944080e002901071a180d8506440919000800601240c2d000450144402e10745052034200a0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 672487014 1250 672485764 672485797
    0x1231815060415030507030303021b0f0106092a0f0e0d0605010f080f030d0f060b070609110301140115020106031a0a05011d0402010c02121906050702010603080706020d060b 76
    0xc1c941024090b040c80da80001451810b980d145444030768981d4504c4c00000c04058002860300920050080201840d112040076104a00f1501d00c141d8000c040d540f090b1844282060080b409030a0984200c00c562240400c4403100c0000d0207004854034080402c0e01d1090021603040401903449910748041e090307204038000659075041008e003000e421595880b003111940f05d010419010034020040e1911404801c00200741613078030b24106005403100f41c0204007040c0000c1980000d1101c0ca810a0b0200c03405405402c040351655400d0600707807000107800d11030894400004001d1003d4113192014000041c6c80001850364403992041c0003c240038003c17098200300d0b0418800f00d56411701c030f11801070210600410900810f5995141010001840030703040c44440003119095403281105200d50740e104105461118451820007900c88400b03001c1a140305280c240050041e0303005104107c01d40b50008040f44c1005480c1e61448087e600081d4068007242d100c45002880c8041000034101d080010f00b0b882 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 672488264 1250 672487014 672487021
    0x90602030603071205030409090f02040e010b130b03070501081902070b011a0310260709020a11010e060103021e1305090f1b120c0909070303080901231815 68
    0x2d0b150490a4000002c0600d2020300100001da0000131a01128036400c1c0104a050700c0d030400c5502c240348040c020b508541031440442088106502c01b001805040b104401c441c54488440404c840c080f001305500755020890070310141d030060b44401e82c06070380c440c40c100403803901e0b040300400c3c3d0700641001c40362100c41100500c000075804c85188004081142c000382107150041044500c04224419240c3c0101e807a61100d12209404040c008510800301c1124030341c0d43d0b507440850080d4001c418000c0081d12946600e400404107006a8051a6410300207064590030b40d000c1106070504005062160303113100800800316210703160b0a000007080e001000419244c034800d0039091200003611401540c002846005051503103000603064000151022604d1486140f203003031414120b1400290700080351010440c2d135820019580c82035900ca07594540154648842c081d007039070480e1b0556100c1540180e0a030b15900700560210740d1002041c00d14030402c01d00103100500f0062041c00403c1c002c82d010080 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 672489514 1250 672488264 672488269
    0x6060509150705071401050c06040b1e090601060e06160302010515090609160e030f0c01030c020f0c0f0a0e040b160504140402071a07020303190902010f11030d0906020306 75
    0x100d40900941108052400e5029500c940c1c0b40c40b4103005e5980b5400081c0d0911402d070340f059056880e15004502110705504040c1060840428112424820000e0103201400c10110b4010900e0040920200601180c0d00b000016a001d22200b00c8041c1c0180c02484034851110b226200c56a00c28001c2d000000e1a05000c400cc40070303582125001406040a1410300c03085444016840b9406540c1d10340011201045003011680d116011140c5a414460322028041215010810546610098804102c42e41044400b640c441d61252248030781a0001c40b41c00e802420700c203000c07120050000303098070a62521084d0885185209480680780c218402d000c020440d141c440000e90b840710b0908005080510300180c1e00040751030200c2d11360103941c02141890412030501c55410465404000070201d030b103450170f8000e43e650811903080c0307031030340d000350309580343d0741c1030f4400d81d811241c06075960021200c0c2c44071300b5100494803100d0900c03035110400c0b01d42c18402d424414028404d1141d0805650380c01e05004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 672490764 1250 672489514 672489529
    0x521090c040b030a03030506040b03030d0204090c080601020601031415071e020f0307030c0203071a03071803080307200105010b070b0c03060604030b040c0815071106100b090d0606060509 82
    0x2034180a00c0c607103810482030307640000d60f40c15403650600c1c0210f40381e44d90001181c0a000742e6a5000e8061001240b4000c0400c0e0070f401034010b407400b8a00411000e4000a01103601a106884075805a01301d480180085404925405040e0054034111680207008551000c0c020381d0844891000512240031010428225000071140c42c4480c1b00074142204800c040381d40f80c2c401d00400a00748190207880317004544091181c00000c1c08103201da840e038041078825800d5244d00803102c0d2000a403039210081890b046076058401070760742001d4220b0941c2e8038520166051a01070f2402070701012044102c0c0d02c40e0409000e070b180a064090300b0f840d11404546007014200c00c01510003400c8080c20f00420600ba00e50030240c070226038108440078107584887c180054880c0c0326030400c01c454020740a045190701d0003011458050340316680d0fa00442c41e500070090381c81d1003080e20741d036110b00500e04e070400840d59164003424030f418005181d041542010b81c0e034101103030b045078810b1001c51004141d0600c50311b085c95 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 672492014 1250 672490764 672490783
    0x143a1d13060e1b0d0b0d0615030c150c0803130b0106020705040c0816030b1203180a1d04021306180c0807022806060b16110628052109 59
    0x114440000c0703a440e044000b24090314404a01c0151764000001c0c4076950214a510001c3d046841005216001c030792000d000566408191000f8400c0403000594801d01c4049580e03800f802c0e40d03441ca40303c0d0140e80e01c02d1958009071282203a070400702d00c40c0b070200783d0717880c07061b40201802d0b0000c01b0454035002c180300c1030314000f081c02402c0c051040208000d514141200c0311f010601460000303001051600042c100f20305202c5100058880400c01c2001d4850040f01949583d108480d2030f082c076903482d03c0c009444550703292500206566503010400500f003000ea040c4071400c94400208229447e03609209103610490b41b903208c11601c94095000c519040700d00643c1015807440a42400c2040c141e000310240d8402c0c1240c100070000b0903014042c420030f54464000307060260b02071541d805c1c86600700e140c0700e09100c006490480c51040d80815134540081111001c1d04900d10202c00c180344013550fa401c000c1d15094a909000c0d04010141000d01100b0f64000086000038030b03403606040c41d002c020718002a10 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 672493264 1250 672492014 672492031
    0xe0a08060a06080622110a08070b0702040b0603070f03090213020c1c230703050f16030824040905030706320f0a051003143a1d13060e 59
    0x110b171001380100b0062051348420741060340b0005840103c008141c05854035404614540960040403c401d0381d0a00180191402290203002030400c080c10010640300c02c0d118007003c50311903941014500d0181e048000d0b010300080443e10f40503e465001b01c1030303030b0001c40301000c56080722101c502c01800c58003080c40000c103280b0f001440c0702074521425200246040349403200c41c6000c1b40c1082094424000c0741c003a13640804016844483d0310a401f550345024603400c0f0042001c6000141689041c0036000d0514076000300340e550082a0312003030100910758100151980c1c00308214a00c00f2500a001c0c00720074a0f1035464a1800690000300704e6100003114034682c041b06104c00038400e600c5018400c0b00d800071022840000c0c03607201d0201160352070809038070081005003040d48030810904081404004021102d4002c084d4100c2040b59881440502c051001c0040419000d460f0040c070441e08580d150300e030300342c1d074404401000d000070b07001802d58160582082d44a06045c440219021a210b4009104 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 672494514 1250 672493264 672493291
    0x40f0f140603011701060f03031e1409010509030106090207080405100801050d020f120706110c030303010308070605100308181e100815090a0c1416030e0a08060a060806 74
    0x30900240240c44103118500410343e02184185090000394800e00c000c0007074007000c0710590b95900d005456000008151103641407154211f08926002e03c501084205090a02c1490600f203138006551642006180681543da81c000c041100030340c2d44000c21034940660880c58a072450501040041b0240408840804c0f110000400031038550110000100790b0441e0505018800b64000c01c4e540003015074036401c03e1081440014106070030040004030034920009a0f0f907168031407810705650b4407081c40007d011450421070b001c003040f030f540d02564000e560310a07003808540d560744400009402040000480c0c0004000a90352032612100c003c1d0a41e46032501a0403600c01c40300080c071a8003604120400784215580018210500f1000c085034041c0000c1c6448000d003000d45640000f4802c1e614002e0210b04805d921204851400c025120b86011400c0b03036801e41c5a19503800c5030107081c3da603042608440c3c86200480c0c010000d000d03051040c40000000a007013032600700ca441c0b4103d8058124042d5400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 672495764 1250 672494514 672494549
    0x909021207030b0402010305040602190c061a09010b0a050c0d0e0a0f060e0f031f06030c05010c0c03080c010f0614090106031506050c0c06070308090f01021c0f060b040f0f 75
    0x20f85a0000303a1240e024280001c44e0780d103904080c8080d100700c1c91400384209840841d00d6905401c101c038020b03030501840e000c000c1032143c0c8020710400c00110900c16446490400100f24450b00c040c0200651049464402c2c00c0880300349600e4a00444c07080c054011640394400c820440c108a101c0e170005000540d04408610710b0446c2c0034010b400c2015505001d000c0d0352114000d582c50801c4989080c014030856017115030a504590740c001c00440c00103c400e41140f110018466118240100400d604428980100791469945401303587c03204031103034215520740c82c21000e00f8006100b81c0000f410100081070300c3da5401c00c1000308001c01600400181803800c695204162800d0040506982580c03d00b00d07503604000801070310f01014450504d0f48420001844d02c20141e000150302d01074264202100da2046a03094030b5820b134040e140c110b0903c0514608580e4840c041504404aa40100600018080e450380400625540103400c2414161200c1d2410404030307004451140003011424500707500e105 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 672497014 1250 672495764 672495773
    0xa0212070911040e09010b220902030d1709030315061308060f0103030201150303090612060e04110a0e072312010803030105030f0102040f050d1401091a091b010f021501090902120703 80
    0x1562049180c10151010b804120720041527218a070b542c3e400a04444010b900402c000340329204152140c0c00d0401b404012604001d40041907a01404003414041c0c03849004000340011600140100c5244c912140000034608100780800d50148114014a04040d070560801a0a441d84491403110081c6094010804a80d0205505098411f0b03072428000d409850324000000c1c001c117401130500d10f903000080c401041580040e00304d01c210207542100909980385c0e1a5003422400b00e50080103c0c000230a410700d020060036403c9020b081d410542401c08000071244421194260803000303046d0310005c01489180f50811108588041220081d483c2030300300300f4014a0320301e8521490740103089450350182000b11001c0f611a00c0b6000c40f00805c100c440c0c508110504608807000d03441c9480c2110003140080038007060128a5404294250101d62600401180c00c600d081c000c0c2d004501402c02c0c00000100c80208450080c8990b60001c01c00c9107071401044081402180021030551001c6401c20014 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 672498264 1250 672497014 672497029
    0x918060a0504021b01050a0204080c0d08040b0a1707020f1204240c020612060901050108090a020d0203120d060305102a050904020705011d0303090a0212070911040e09010b 75
    0x1c075000da0700540c49a0039605403440b8541800b42c48081c65080c0420803803d2001c41d8054401c03258200708442440e9180d5040c0004917008003005003c8007170801c000c0c020350740b812008101c0508640381041202311103031401c59021805450f1040140c00c04242040154010031244910704403000e015440d2510305485008804680c55200300030600ca0301103042c42c240115105001d240d00030b464941d03101c4503581084080f840c11030742c0d94800c202d41c500200e49940714880d210300c10007410340105a580c02076001c00c01c10aaa94004a90500c50144001c18614011001e0a1503100c13040e00401c1d041e00790b2520904101100070b0f065101803815040710314445000d05d4200c18409001e10004000b04900f00c07c079401d204040231640c000340001901003c0180552000b202c03000390195140540034010041500c1e0702c000d4a100d8500d074403906030300d8050b14014210300840c00380b40301250f5506a0368520001070319141018042010004201000080300001200791700c001e102000304140501000011400e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 672499514 1250 672498264 672498269
    0xf090303090d08040c17100c0201110a1b1b05041b0207030b09031e190207031709010c05151b07031d190b1e03090d08130c0602030918060a 61
    0x104500e03400480c01740304410840b400030740080c0252040001c2081c0c03809a9840d10507640d402c03442c0c54001100710fa00c5c41031260342140c1074210810f5140c417490001c122104500780f5031181c0345c20711000d848030000b5995801c0c0c8040d82048a42e006419140c50204412070b00855112900c809800e0700c2120718a5011a030a426690f1011140e40b058a82003541c501c5c5000701d00f070301c02c200340d45da880741032106444001510002400e080b40b1440d8800d2a0320032611103150b440024424104084110710b6840c2500290120038810302d00300c18181e99640750246032603412003401100c00404018041110000e0180c1030041c8001d5003c985440e00e1580d005142e40740c00032a40030003504450355a02c141d502d4142006051034048140072000761141f200340441c0d403219810592100d01021100200c20000058030f1003940c041001c0c3c551445504010340305418014510344d66241580c4860000a03000442c4001604203940190f80b030300c15490500075145504c90320341030b0702c4c80000200221996142c009109 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 672500764 1250 672499514 672499517
    0x10209060d02030414032805090109170a020a1701230708040807050a1a13080d05100509010605040e010f03050c0f012006060901150c1202030f07030302030f090303090d 74
    0x283c80e59541040d041c2066101414030b1940000190b107032455802a02c17095041136213140720b0507180d03e0a0010350b000e10171891141e01040a2042c00c1103405c4241d1000205c2c5403c501c01d80b1003a000d1540011981000e580140317401186104000d80145004d1003006110381c0301c10f044034230800c51741d00107a4181d10014001401c01407040001020440d60005607021075038044c00321800d81902c1d00c4c040c0c001d98050f55010300398505010019000304044481c0d4005182c214404a150148116030840070b49001041d0700354500c0304000006c1c158899601c454002d060035903405881d103082c80c040305402d58069000004641d111007050001c40e00c042540b1200107030454034060380e03000940041c1c840401442080034a004e41e0101144142030100f091881004216030403030366a82c8540c0c0070406c401c50302d142c2400003210356422000081110103400400702c000c1c01241d00b032424880a00510b0760280380100d00098000c01031142407003200c40309a07040389903040650308500e41050101c2e0b940d04403071510700 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 672502014 1250 672500764 672500767
    0x30503120618010311040c080601121508030a0525020a0e1506031017030a0c0305030705220611011116020402090306090a0309140105090108042a05040e010209060d02 73
    0xd0060742c881c491540d5000381c040d28900c5669582c1445207903014402c07460390150382041a0030070441d200d000194818a01610341002460251010000510013203c0c0700018050440011603031a400300040c100840007591065628052040090180c1c5030b051252600204210310795001070fa81d0702c40e85001c2e034004c40051502955403c280d1881d440e079800c20a42c01075400020b002034103481540c40300c19100c0040c2d691060759003021005070b0740d20440c02d1a4000500308404100000d200b0340085400c00498940703503062074540a044075a8100b200c0c448810020a042d0808c865900700014000c1c2c10580e200811a1040d11000d15069102c0d00c090005841c66040015007103503102d50540310542c0001d400c0380d440380751500046980f0705504400780c010400c030f92030000714028140140f00354044183d40301c50500700c9910055418040c094000c40303600c0220640c05280c038402008081a200c4002115030b20907251500744001c946460722841a0350340100510070950b26134204940003c5018a13006 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 672503264 1250 672502014 672502021
    0x70201180b0d020d0219112505090627150904030e06130e0420240d1b021617030f0a0c020612011503051e0403110a081e0403050312 58
    0x9070300904c5151b500781c00421841b2030920710b00d03500001c0500f810480c87c0451300580401001d00d0041245c02da00c060480010250601c55400d2850013540c00c0480601500c120b51080c190441c520512081509103450b86d05080000c2c1038480035050180150954544e0501d091644000b48543e00c200b6400d802108001044148400c003003060750002c0000c0190030303c4500741842e1400303010b218044002c00200700c002d0f0800740c51804425900d05d40a0070045007050b00602d00d01e01d40d60707810101251181c550384103541d034000b20304001c5180024600340d000d490365a400c6502e045125040350072202424503241c5802c444030710000100d0b21268611051140c0340c5100240c00c880075894040025080341012030304d42013800511352410b050319041e80000c6101e038070780708003281154000c480c407840c20701781d00e0040800e901604e030788281c04c14040e01c0c0850f0788041c041c0c042440c10380e0714182119040700028010000a18010901000d404d51000643c60a4550f440b51a03503401000d5110000c00c20f0074010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 672504514 1250 672503264 672503287
    0x905010f0206071d101206050a1d13062a030e0a08090d081b19030806040504050c0405011508061002031215090106030c020f07031e02040f020c0102070201180b0d02 72
    0x442e03036000c0f0040981000d80b03200000145102e0380040900751032807c055000c505c920304102904190380d0282d040004c444120f8000501040c40640014500c1e85003d01541c0400c4490107031400c0745034060010f51030030040c440e043e103080d0030003521075080605d48400c860502c41c0103da0f5200c0c05420035103440d00c4a08240000e202c0000214006024150000301c0b44000703001c10341c204118244240a80b03800040401d15006102c0401800400080ac0900000c01610302030340210b80241c0034070201c840070302d01100030070100c400030380040303510340310941e407100c00280c0c0418244e40c04642550703078003007401c402d28000c0e41d03170300910b280c80720f803c0901c0c40025402c8950202000300808002c1c40c440d0156914800500104a105d84100040c003d545202da10340d0340c0024480114bc0d032002078a140104410014400324100d0881242e0007030f01c404884c40c005400b0b0000d000380c0001b0b07500050780e4064038400034080c107001450241c41c030400c011040101d1b901e0001941e1b1108101c00015a070740401940 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 672505764 1250 672504514 672504557
    0xf05040c031b0905011707020d0f020c030a03080a0b0f0a0e040f050a0b04020111012c0f1f0c020a0503030c030a0e0a060609050c0f090f03030913020a0905010f020607 73
    0x3000304810b4502e4007090301c590340c4207030810121042a21b65218648000460705400c80c8100d4041e40035030311a0409140c014803600c58030301c200d000c5106031a014a03484001a0905102c500f09a0020b9861380900240ca0010700c1101c00380c890481c0c2120700c40c0900d40100d0800b61882c0700e42da20121100c8002804c0c00700c50f0100b03c1c21940d0060644100203060314010001d6101902c0c180e0000e11100c40003400d89a0510031840c241900c040c040e81d903e1040350109450500d051000020750041c41035201c03011404120100288100d59255104100c150111104641d00080341c0030455120142d1000030490200c11070350070901c900240d41e60f03503482e030fa48400540f2446d40c0c0c0402501c184002c0c0d00600c101c80d8412130a44001000034411511070443d034025a006101e010340c400c503000c110503205482c042c1d500e4821400040c05603400d10b004900020428062a43c03d0498160006040350140b40e0190030040504000d0912880c41428620000e55810000300f00354140000c0c0090b0a1480b8070010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 672507014 1250 672505764 672505781
    0x1902010c0c0303030e0c0925050d0e0c030c010903030504090902060412030c0b07091a0d2703030605010201020a0e060a12020a05120f010302150a09091104140103060f05040c03 77
    0x120740790061a03481c90f000380203200704410f01c0c3e0203014812140f0850310f0000c40d0607004d20460540f00048000c910008072000720604441e1050080030880c0140c2d0980a028010465820902400001c40321400b0f05040549020f13400e410030031441c20920019421805490035103486182c0043c0c00055880452018461070304130115040700c00e00700d0001c05511003910754140d4440c450084107621030138416500420741c2d0182054000051160110b9188020007501040e083d030000818011180d200d10090322600d05c1070400e40301750a81901085c1034050040700e005000c00c1c4001c6142c1501848001c010741080e1240c0d03842000b001480e900c159208040100c580c291003c0110340d5000c040302c000d040342d0312070490711031601400030000d80c66080e07044c2d10030b04803038001d4010704521040b40c0911145500c805402002e100742c000022510580500c40d00c00c158501c0000c00d60ba03203040040700c0ca804e55802c0202410182080b909201099003001c010003212001d480100c3c4850803102c00ba0003810344003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 672508264 1250 672507014 672507023
    0x15011202031018090c09091509080405010e130e2a090402040b0d0b0106090906090506061605160303020601060e09040f0b070525031b050d0806010504180b19081902010c 74
    0x2500085403806c03075035024a01d01882550385186022144104c40240c030b03c8640043c0207120248000c0040d0350203260020350701d5000071308108040114024050450790f40d140c58140982c46400765a48802d11028011802600b41401c4194119100300150304d5080041c0000e014540360218840262662480c0412056101c5054825581c550300300400d40300c824403441403424200100042c1c43c050a10a44d80100301c083c1c00d803032410400c0204400c42003519003040300c1300d2003a0300c2d01c0301301c41e0b1020481201075486940038011a52410350010000882d91120a01c00e0b48500140000034041081c00c405050f441903002c45c3e41c4d500e0302d82c19220b50140030140c0c440c83d43c035401c4501c6500c20203260441002e1180e101d000c1200c14040702240c0b00f140078a402800350780501a82a0014020b20942d0740c406c2c2c0514105103010f443e4615083c1000490003803000c0241c5801018003145810743c11070300300b20070f0102c00c90412890a03054030b0707403a440040200107036600304110310150f902c21406140d100303400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 672509514 1250 672508264 672508283
    0x3071728062105100b030307080306180a020a0206100803030711010e030406110f010b06070605041e0501151410120204030f0f120c150203130501051501120203101809 73
    0x7080b114603041401c805084a0f02d00410782d680b1020029403140400402d4040c00443c00c0c40c1c855510701c0340c03d502c0030b080b082d80104044010140001402403040c440e2044420140e00d500405501a10380400a0b122a01c81140d411042c44246000016a0340c014060f10348070000f6040342c1e800c1801030402242202c1c8030b0000140100e50550041d01308139480d00d03140112103181460016803401ca0b203a00c4140d6900c0141000070001007002600502d4000d0b004031610804400000d0000c1d10041d19408212a40d035100e0b01801d81440b03d25404a00400c0d4002c1100741004510b00042c50b1480b010307100a041c0030f010102d112003600d056040e51301450b0720032014801015182000300050802440031202d0444290084070380030721841a03241800e03072046214400c80005030f13a46029400091040488400701d01c0324002190090040902806010680c000c800644600040c044203e40c3d41e00056207004006000e900c00030146c1100c100c41c0341c521060031803190040042e000d0303c40e00c240581000712 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 672510764 1250 672509514 672509549
    0xd020f1807020a0b15011e050904150915060e01030c0201150305030403050d050c0c09070210051005040b040509030901030b030319020318030a03021506060f0f0307172806 75
    0x70001031aa102c680107818507080342d510301d00341c60050b80c6000e0304180004e821f80c440a003007440a41d045020b40c14503003810707400e1009400100741210b2507103500c1c00780d41c0c004120801844000e071094400501603034120b000d2181c1005070150000d803400c1e003081d041503614a03030307580c02d00c4c400e62118205c04030b4220204040c0c4d949080403652900301c1e0101f0340d018050302e00511940f030301070130840380841e10010140030142000740412051540080030740e000d50080b440d192208030030900c1500d00c42d1044014101c040d5050405000c111804000400e0195140c5020b01050003000030a4452140003403902141100509021030308600402c100b01d00015204d00840010075008009010358a46040c80c0b021265102c1d0101560340340d0010024000d42c000f81c00207500d0844202803250300820283c800c510f04050f0001a2585a000240c09001c1d64804001d102ca41a8800185055400c0b00c0c43c500405003400c80e840c445080340f901040d02a00e9281e01021040c0300580c00100c01008407400700e5a0951 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 672512014 1250 672510764 672510767
    0xe040f020f1c050a03031407020c01030c1202030702011a0f0f040e010e031306170408071506080304121101080f0f040218041a0106021617030408030403030c1707020d020f1807 77
    0x13021501100468105000d015551a044442604c2040250f0090410004240055008180001101040110301418403008060034002980181c2240e0700002d40851100d0100c0a8141c01d000303428803072005000c0c0702026543e45420701c160444101d600007201c0d400e00405070700400c000c000040c0c080c000440c0703c41c8410b9024034001c0888000d074a035010013940030b02c2040741c0504203c40050900a06120000216444000701303200c0c280c0b170103800502962221621407075a0803540c05409214081c0b1425000c124847e40c2650540d482800d00c0c41c45420042102e404042d00141030b0351a086c4154005001c0d90fa403070f80c000c0c44c0d0010152030b0841d2420a81002c1048040354144900c904034100d00009440b8400500031031201c00b900c0842e040c1e10b040083e001c03201c8281300203440f110710041c0404282c0020610082c07000354401d4135022945203040c5803502c40a161082680e038008002e201000144c3c0321006620310103a4102e40e102180c8000f00006481c045070443c191445000c494200095503 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 672513264 1250 672512014 672512023
    0x22060f051c1d0601050a051023040b0c0705060313020603070509091006030507020a0804260303090f0709060e0105060715060602061f0f05060307050d0212100e040f020f1c05 76
    0x80020350940c3d200e42c0e00d42c002d2001045c180c0c800d080c0c0061600040d0302c500740c85000c03c000d51030040d48080705003100314111402c06030000d4005000700710002907003a625032820084d0000412087e524641145004080e11030700f818181d03000382c00f03124000000340c0440d2040c400c403401224028601046803c2080c40300c2820440c40c003c100200b841c0c140810445400000d407a080554486035261803d07003410712010302c6100a600380380b00f05412103100214954180099445034070a42c00410404000c59410f80ca0181c061303100b40c01c10341c5400001e000800114010a040d2441a200c56560ba000380c6007102d8162003402456100500d045404a8115404502e05000d00031b130824443d601d600991413450324480d24801c180840c40314601c100114105600034591001007400d0290809040004a8099900006000d050751a94104100c2030440c071600b43ca020300b0000c444c01c1558034041c0c1d40c0314000c1d007802c40044c1c403030090038241000340c1c0e540c6440c4117200d117040080c0c040502e80e6407410340e5a8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 672514514 1250 672513264 672513311
    0xd0312020a050403030f1b02121509030c011409070b160f030e13060b090d140a0c0515040602100e07090f230702060a0504062022060f051c 61
    0x1000c0c4948098140c0c411f0040400c112003000401c902210b40f5800c00400a0594151400c0d1303024036030b0001c143c11210074130348ac0b007104a40055641c40c9680411103003100c0711086001c6008520300f050222802c00015100141e4030000342941d41d401000d1241040d9034043c00c4001c1c00e181421200d107003056400401030805540c2500c4044c2c40090105540f420b0b10503034003d20f64909400d1028202c2842c000811640c1c26014a02c4601d042c3d03800c0a03128240503921005684002e0b10410401240c100f1004896900b00685080e500b0182009002525000d954020305007860b1541c00a440690702440000f0040904610800a204101940f0006400442d8001071409032a101d501880010408a148104d4103a4003400b5035668a80456005000c042e006451030b40e5108208206001c440e51a00c042841c110180360725200d0454840c0b1003490140340040040003580810005990000039800130f07003620341452034075030440c2942d0504150141c49042c803114106180280d1130b48401000006 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 672515764 1250 672514514 672514517
    0x31e130807051b010905060d180c0305030a09080c0a090e1203100e061e1323011503150b070303110f090a080c0307060e0f131a010c0507050d0312020a05040303 70
    0x41c144000d001507031045e0840c80380603002070040201a00d014059030003980d41c00940d80a041039180641c985001aa01581040b901c0c2d03440041c4200403150040c41a4001f0407040c4005c2040c075600310041600312440c1d101e810081501c03902002001c480034041010744101d00368146450b443d001140c030b0a96a4107100b0140c0301036001700402c8160600c583c0314003181c03d00b41c0345c0444071500042401800c0c035103d13012603920365070f51500300d00c05881d085400c285803010340740318940e6504061640c07400e40380303d1403021f06040c6024080c04100c580015410100e0b12154070303c0d40c1750032032400c06402805001c8005c07801c646c1c0c00102900b84540b1724014040e00705059170600c0342c8903258158642c2d2a0041c44801d5495440300300308001c8c2611400c020300780c161001c3c010081c460140c6001ca403660201410358691035842d07050f2004a52f81080c1079002ca10000d183c00b4408500c1d07a1102903c500303203805114090812201d030003082c14000c1d08102c0c001c03040b5143c00c5550703541c070700c034000d1054106020460 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 672517014 1250 672515764 672515803
    0x80405120307020901290c0109120e1f030b030304030b0405060c0a1b03030b0409121404030305190201060f030807030f0807080604091b0303050408070605031e13080705 74
    0x40340420000150380400d58058002c1d52141d080000841070f00c0003091a2100307615922000d0301074002040040c01a143c9010004036024400e0314005000300c000d0325401c81001011f0004240a80c0c03a14500809880a5007580203d841680c0d0220060a00004210780601c07000a000003005040c1941d14030442c0200140e07111512442104980f6100f28519880061940348000120041c0e00c946000394903c241000107049c04a1404142a101c0c104230543d10900c894129000a42c0c01035140c0000d0500310841f146000d0456401034503074011000051800405040500c44081c000d501c13480162410001e10790940d5941e24050100d98032040d030440014000345a90010540a540c0321400f8118980300c51515680b80000c1c040104403110381910714400e11040d60003071800440418015500030782c1d0b650358441c01c0c4404185803100590085040107c100b0411aa060184010043c5a040c400907061207071142a00704031134006105001d800d00c0f00c0000d01d0b034208000016020708908041d00b281 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 672518264 1250 672517014 672517039
    0x30c020304050d11030f010e06180a060507030e010506010f050d09021206090304080f03130509090a080a0207080705090403140d0603150c0e0102011e020f0415260709090207021309080405 82
    0x9400c8e142c40701646c5103241d000101007000b240483c0003000209080100b2a0b17044001ca4454101382c030001c0c1d8000b808299640059038104d20203004080d8080020300f401c1140000c0c15400400710f100f114079641c0c10903502c3c1c2c08501156661050300f204041004120b13041c0d41046841d01d5101d5100380310310700b544c1c815807681c800480d03808015180b0340011042c9902000d4070b41428452030100013841c2e19124000e402c04040010b0504018048043c1c1a07401001001e00b0040007900e0320b00e01e9040350b8801c4050341c0030400003c6c2c0c004c5825409946d9907c030b00f034840e05c03065640c7d0040c0515410042911007041000c80c030261030b50b803040084411940d170b44200e64038030034010380c00c03a100c000d6000e800c49840300782c00102c904290000e00c15244110b8143e0b00c0c00d81d94000040d00e1411100c101d80000303005614a0503001206580c40805640e0032504000a0820601c082c15401c500d00c01d5000301600811f00c0030640d6200304001807100000541402403a00c00c0c40c0c00c60940e440f03030040700e10503000305004 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 672519514 1250 672518264 672518293
    0x6050d0f200c1b09010501030f09020a060e030c0a08060601110312160305180c10050c01060b0d0c1e1d100e040c020304050904140c030f0a03030501060f050703030c020304050d1103 79
    0x3c1c403505800946080000e9080500440142164210300182c07030380c8410365180107844a4203003000410702585d40203030f0458040c00701820080d100d03024520412001000b84022a004100e4640250090030917004d034000706620315056010b00f440b1030340c01c460b4190420195042c9048003185003109513508000c0b941c0c442510810128031070300f550400c0d9204042840c41b90500102c00c4000ea522400c0890a01c5030b201c4506095603078582008000741c00100d41020801c070380b4001c0c1a115401420541ca0030410300141c48408244480303003070200611900c1014102c5c000440e8800194009030150300b0081000c400601000d804082c0f6600031460704442d41c078442c0c0b0100645d000ea031070091802d541500c075500c1c3c85902808030b5442c0c110034050316580c81040d680c00c018030092030764140040d0140e00b1450a024040741c80591040c800e02407591a240c4400e94007104607840759a041c140010380c1004030700102d1540c001c581215801c01d1000c81030006004a812505090300b0040b0220750f00010010348 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 672520764 1250 672519514 672519553
    0x6050405150f090910170c1003020c120a05070b01080a030905040c090302060d0e010c020609150c0a0309060f0e030409060f0620120f0307081006050d0f200c 69
    0x12003040c009000d20b8143c1d00e030031003aa035041508480d80748003035602c50031950400340c5104c3d8000101d51111a481c48281404841514070303400340c0c2011420800400c00d030780e481e00351012000400e91000141551518094810380340882d0300880a0242981c44e000015a1801c4003a4140c0200d44600c90018540c135045c00b922034201d0440d80c1d01405245154248a00d80e0040c00015407007076115405c0d2607205409108000145507664002d00040c00c0c0352403100d04200802c4008814481c9070820080358088007000c80e04002c2c03191a000503a603006013082d10090900b070a103000c40d642481c211322140c1d00000041e100341c46989804200003552820f440348030616900c41e080c0400c0e10704250125500f00c25a00d100b121541c0300907514a0403e40f405d4a450fa44036600995207604084107001d2510703440103c00d42e000d0036800c802d60b0b5031030504101510078065000c030301d03c805485100200755100103070081c49801450303030101380c0040c4460043c000190401441c0d0700e02c5200f407a900c0c1c0c00c03207c2c0c04413 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 672522014 1250 672520764 672520777
    0x16051005070f030b011e0f080f060f0d03020a1a010503010f0b030705010302130e010e18150406051314100b030a030e061806070507030506070c1a150306010605040515 73
    0x102c80c8035107056600300c2900039108054005040c09014400c8032002c80100921502d4104182d0700d541c070807414850080c00340c11020300f2809514a64104001c0c1c0d9450302d1840000c4450200c60703e040040b81d42c0f804030716143c50f00394020300d43d003141c921010101080c0d82016041c1c540c114000c0c4403844601111100301c820202003640c5c5940b101d103042091354000d0380140510b506980c1c040d290f1a440301040c03084044282c3c8003080030303980c080c20040317042c00030b150101010403c01d01600300c0c00041c1035040c0500d4409440501000da5580200c1ca1080c051802c038501c540d4440000b40d10358201c0b0040a888151a41c1d001038290f003800002c08982ca17010546041c05603064554001056032030052110b1504650441c0f92240c40e014002111a90750300c0242404610841c018000b45085241c001d05010010b0f100e1028404041c121000080c0e40c07040c4583e80820100c1d00c038603550b0383c0c1c0304000a40603035542d21a0301409050004980c10360300034001c1068810075611090400f12020001400c1d12814 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 672523264 1250 672522014 672522017
    0x4020c0d02240c090117071e03054809040b09090a03140f0c1b0613120501090b0c0c01051b1b010f0c030204030203100b100507060906021605100507 65
    0xe80020b12003c62003405001c000d003040c506a038104c0d5061600142c2188203440010100703c100e080060407110320418680d1400441c41d003480103041544026500004510032410074a44460f0311682808481c20321540b600d060b40e441c00c02c488408a842d107450340c01420340c540207900b4068076040134100b08140c10301079440c031030040100c907100e40c600f2140c034407003561400c00f0b07100200114940c0d0710184000d8440101c0d400c001c0c00c0098019642c0f400425904480c45009103414040c074041ca07a507041010b422a41d1070180100464418070302240100304001c4002c05000900d000d00010002001c00b500c284071900000b081346444281c40810080c5003543ca006043d4000c10000c4585d0803035640c0010103d03401d60000c50409440d00c10f035001c0d00c28041c02e140009a0118042055180400c10701011401003c004c2158ce014035000c03420100d822a1300c07400303002001500c8010081c07564084200d481d0000011510b0381c2c0b42c00144030700c5224050302a5554070680c282d03a00d030700d201d501c00d06005107610b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 672524514 1250 672523264 672523333
    0x30e0604060f0c0f020d080a120501060e04150b0706050f150d1401090507090c0e01030e03090d0312110910030513030809160315050907140603060f04020c0d02 70
    0x20b054007200c440e52858070450301c1c038000c0b0300e02c400140c5a01204200c110b21500565440c0d00c2507010040c041d001210072190264248001006259000381c1d0982d414002694041040441d4825426960721164000306ca20040000d00005000c000d80c403003030081180c015038000c01e8594400700d07ca803058414425030b0060840c011701c1d00049541124035000c1c0503400001c100c4218070313261641421880ea00c00c440454462141c204410360001c04562121801d0a080001060240280d9682e000c0c40141f507004031908240e01040c103000c0c01151002100f503402c240310821048030342c100c0c203810400c80c480c05004110340282d41b01c0c3c000c0c091a481040d6541154003c2c00003038038103d94558000c0d0411320700e4001c0e1602120881800e0a20304050b50095101e246c805a9521100c0110794009200f0072194007c0301c0180204405070034040c40d40e000403200036450340c507201c0000f54a451401c9203d503100c0d10001301c400802c40d011031402e148403119001e42e100c04000034032042c019150b003092a0810b200 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 672525764 1250 672524514 672524537
    0xa08030105040f1d1b0a180c020f0604031110050f1324060305150c070303020a021c03091a090c04050a09020307030f1502040b0a08060d081303030e060406 68
    0x18164080fa5003003000300c4000c2080d031142c818030203103444c00b02d0240030340c0d420401440d113490b050008040310080c0240e422003121031414107815150441041010300703094480e480603840901c20404900907101200c140d03003060038289009440292011008161401051011364000030280305452040d01c04110343c041c1030b40e82441d1248a01c44100d001c6404008190000710040101c0d04010074101c5034903c00619075003541441464404500c810942e82c402000400c6011001d0700140d8100d654141000b41e00c85051480684c03c03c640c04110810440c3d00803040401c4035403603040fa8851502803101d000304400c40394040100c4070012100300400c3d80c441720101d07405040c5075108652121030a400010600c101d03a00207420034405070b01c00d8030186803078000d48042c811450034040b82003044e4803086250030b28288d5100c0b040d000c0d58050000384100340d00009c840b5160707010040403076030748940d5496031852000e543c0b040c2020b460200340c0001d03400c0840403c15003070060490381a21480c2d11003c90019 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 672527014 1250 672525764 672525769
    0x1503060f0b031302010315060e030f07120209150628030e0d050d090807290603060703090503070f0605150f0a0504201306080a0203070801171e030310080a08030105 72
    0x1181d000f00324101075a4a8000b10352440001031400600708075a80c0e80410a9100304051a0080c1d2862403212908052001c209240c005031211a00e141d05490310116a034172040075840b8080d0640c034480d00322000265403456020a14626032a268610700d1050b011240c0b800d080b022078030082900402903120401818005003c4c00240410710202035000c55150002c0d41c1e04020783d009207804075a9856a00113a1741c1a2120034405070000504441010540c03a250002a54405025101c1001d065079031100c0070520100b80304444c0340030340151034514503501d00d15018004000c11200d24400301c0c44036080000034076003090101d03080b460081060385940c0c00e040410000f00442d071809907018030921071000340003801c0b10282892068079800514068a4050080c3c6190001011550014070401c104100c1907040030189064510249420f80080c0c1c2940801d441c0200c1640d9001010640100403504c4040000c01544541011100041859030301c0405558030b00201100500d0a9410b000500250 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 672528264 1250 672527014 672527041
    0x12020904060f0e01060909110d1a0408090301150509091f0b0402090a0801151a0712030e0f0f07061106010b03070306030602040e06040510211a011503060f0b03 70
    0x10b0035000014100042e400b00340d08450a941c048036005480303c001c003091000e14034014030508010340c0d1034088000d0b5039440d40324012202d00c44024680e0880003080078040c5100c10b075607080da0094001c0007034810101868005c1a8503200b60b9110b10713604800a00310704008500840c1240c8008000c034078200400a151000c2c00c0b6400c50550460303401e214035001a55038070b02a02c02441c1c0c400000410b543c5070818540e4070002c03034215000d941890b0b48948030352950b41e000c803641d00350011035004181841c1141140503001e0142400340701e124011203150341240c0490174803d620141c0048079401a610b04013036503070600702c48540c602078118000400091a840c0c0045074400d40e1131a0000c2e05503241e0340d86804076081764200800321030102c1c007041480e00342486503170781140c14005001c0100307150111a4030001c00c808601030091b50351551040070804049024a0307002810402814a984c4030f00c0c0445103440050220000281405000604020301e0170044090b202240206450365a40c4210040072 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 672529514 1250 672528264 672528281
    0x2c09030a0e13090b040f0515010b0a05090102072303060609091e0c1807030507030902030601060e01050408011a012d080c310512061b070f1a011202090406 68
    0xc1c0398980303d03c000015205105a4441c40c40b403205110014441d00304540b80840b41c8062103480140980140242c511071410b444c00900c051803d190741d1000307000100c2c10000e980d8462400300003c80440400c0c0e40d100b0350a4010440c0690440e030555407450100010300f002611000400d8001071490381c48440070b581000d080381d0700002290f808411140c01301c4c01d410812603901540b000c1c080c051059541c1c0c1800b87d503030003211524040c040701906400080c0c03a02d40c10b110b408184603201c042124141d01900a490040a402000300042c00c0034039003040481041d003c14500084a4500540550a4081c0800c0701188155154407500880c0070094440c0040035007100e03c0030038180001110a0b5404410307c0d00b00f1107900810151070b50b040d402c1d00e50006107400c134600c10000c240e203443c003034400000c407103601c655580c424040c0342c500300001207458072030841b01a1130a8110340c8004280840c03141c81c503100f00000b03800c0c5000c1d40c0e65107078a140c1c8a600020001c3d441540c0d0710100d0b0220301d064010741e05 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 672530764 1250 672529514 672529549
    0x40b01030b060904111207030501090e0606100810080a29130803060424030c0902181009080f060601140a1b0204020d0626070509041b2c09030a0e 64
    0x2800e071b80451101c82c0c44000312003810000b5202ca00610a030b20507405603440500d040741c010310381c1d420814001407600c2c04408441042007100e000260740c000d0f44214880c010044141501d05405250601c0d03501002ca00303030060340000103002d000811746c0a03010b03030f91300c01c28484041d00401540d175950b401040d84043c09441c0d0064442c2c0c92500f8121101c0201c10900c0d1300c0910361443d86280d4a040c0564905c180d000c14401403050050505890908102d4907803070008840030703822001280415038036071400d600810020310990101011820001030b955010f41401d0701c0b00f0810f6042541c2e420220f00c41d85e150200010041e01d0034107101c10200801c4580144005d202500b002c464104d004101e6615034003142a2200030303008441c08208145682509803014805404044c1c00d00e0041013101c84054001009040302c407100c10010ba03031480c0d200000c3d15540074000c1c1003801c44c90401000100c000202c1d0403100e1a64040342c180709000088031070407020364641c8940401408200b01c1e0082c030305101c1300b1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 672532014 1250 672530764 672530767
    0xc06050f070c0b0d0b0609060a080402270a06050d03120c0e0306070905090a0e06061306090204170c0d05120d091403031009090b0f04050c0301050403030b040b01030b06090411 77
    0x70005100109500042e100311010750f922500004403802c2a44c14441446000d90130400400c1034580390541110815a4181050145502c4510214200411101c80000c484003500e03a6020380407112214207000701d1070f0b10001d1190715254030030000050726280000b070203c3c210054010450903107070041006440c0d1810180e0712008842d001c02d04110381120141c0014420040510a03498010181900018420010040070340f804c103ca40e6500c0300540603130721403040d0401c0d0039403018040d0041401f07040c0c00b42c0e007503445603662080035401c101100c4400306280140440c2c1401d5080c84200d105a0540010080c8495244041c5088159010701ca039441c0d940d80341c2c0801008503015801c0c038159107907600c0045540b0329044c80c40f50352007003054111241c40383c03e05001c58080740448402030380104078143d8400741902c543c580309203424503000c220b40c0c040d4209002c2000303050701503101e9080d41c0381c1500c09000c40e03000c0f01e004401b01c40c3d82078000c2d54890818004103805090a0f4030000c1050071118229 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 672533264 1250 672532014 672532027
    0x1306081509150f030d0503240306060103091e03020c0f04021c0f111920061b1b0d032d0b03190609020307050f0f01080403140a03050f010e01030c06050f 67
    0x341002170000c4070f000030980010a0103100001202654640452213000021406005001139240d000c003601440c1050303120b0036403a003070150345068881121001d20701241894203a10b0041d4603080d041e0718445c8104c00718103140c103481c14140211840304040036941c00c5c5800d144c82255005118848441c92007650310541462014010030080c00940c922420310f8854154a03200100f856000302ca190845078114031410901c914001109900907201e00401c0030364040741c4203114424010300c50f040465030030140845141100228249500c0c640a95080c00840e01c010780224601e0103541020440a401e003c100c0c0200c8a20341c4000c559400050a9512030340c94160070070000d019422050f00c0465480c1591811480d0801803d0020301d4181c410a02050411001403646540c04d01c8580c10302c86910005010140f140211404000c03c40e080207407140003c0030001c000707100444001050211000000c00c160920401c0181281c0d80b0210000506047c00c030300311803582000d2800c424094050048 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 672534514 1250 672533264 672533269
    0x31e180c04111603091a0f07030c020d080a030b010f03150303110114091b0405060108011e241d03071e08010c0e13060e0c09030f031306081509150f 65
    0x107580f4403900035660182d07041d0815034140082d5000350300840090104100b5284154801002e80300c0180e0103051032a401c0c5d0240c00856004401c2041c01001010005105882c0c81c0d010341c401c044088085c2c1e2070b200c3c3c810000c0e0056045800a401c884c00e80b100500080002a1192070a03e1204484600100f20502d61041c01030400c2e1064400384910340103480710003501c07502041c09143c0e6040888090280781000000a401030006000c0c812130b1505138680d47c1b603160380c0c0505101c001d0120311401c910403c1e294400c40030008180340c409000940c0c0c0030802c0c00700700c1d5181151020b01c100402400c221450b00b014224600d88940c482454180c4010000a021000703200340c2d0480c459507103400720500c514a00300440040101d602c1081d180c6401001d002c40e400d0400000d0303000410741d0056640f0b100c00c1000910301040c9015100c1c4500c400920f4034031900315171241c0000c41c0c00035152a41c01351501002c41d0240111550001d4110401600040725140861a10628100c0c0500341d1104010880702 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 672535764 1250 672534514 672534547
    0xc040b01021e060f0709061b11130b0114090a12050703050d08010306060905090a060b03071a04030b13051906110a110607050412080d11031e180c0411 66
    0x60b400158200740c04104c200c0d103812100d90390207181840e080c544107080c0400540f0180210305038021a55001503a641084201c041c102c0380203034000d0201103e8605410707614003030503020050500181e10a40c0c0081840314600c183d41102134000d11803070b80c0381d0a040040003009405142952306e4411604000042807050004820058282c0d90703602c400d44c19400d0005c2583d116030b03c480c24280c80c0030300b004624140860640c9400f039000c2d60108041000c01c00007894070030a40c00079a8241d075040700080d0b810140d04020300c04ca92041c0314800b419900d103102d07682031240c40351015001360400f90483c1c0115607454455070881d84210000900c00003100d4000c1c45903000502000c001c40c80700803014141a60800415500c0341003450030714a814104079010040034100d5070000c2140702d021a0304203400040b5000103240105483c1200c0c1c403843d102c040d200c0d4412400d00034007425038440303021070806402034041c2c500005002c0024110301161000f80801402c5007800124004410f00259041d5642d041 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 672537014 1250 672535764 672535813
    0x1090b030901022a06071202040807080604140102040b031f090207080304060528050a0f110711010305060d140708060a0603050c12120c070504020d061e080c040b0102 73
    0x10700060710b64101134030340c1c4e0409289215154845000414900e1402c00004900b544803d480c94031042852004090760064010790300100003030701070020302090310701c000170395a48102d002c1d00b94242031000061800e4200e21031400340c00300c50401000000c04a1020355031a801c0d110201d2101c181141d604e41024040380c000000443d140d202c00010b200500c1042d0107070745e0300051403c1c00c0700c42011040300c07064030f9075084e0b110185100707459500050310411700d0740c40f2003101540c401080c0500d2010b40c143c00c2d070702d9102d4101141d020070440c1e140030f040e5100384200340c402c00000e0800e00300c14184d80c8508030360292421104e1401c0c03254400100792540e0070300c20780f8010164404041141c90031480c29600b07050310040c015005507840014200d0000c00050020585e11142c804e040d038540080e0446400c01d002c42d0080c03074210740000f8482480140f2948244101e03548a21000e11420349594a0902044944201503281d03009042d151310302d240641c003076405210305004582c60703805840c050020425804 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 672538264 1250 672537014 672537031
    0x8010606030218100203042705070206010810020903030406030e011b05130605030f04121e1205010503030c0a11010e0d140c013605031501050a080d051801090b03 71
    0x10400070381d00301c82c0800041c01c00d0801c50f00502c82c84e074446002962030003144646001e0000741c02c101170031102045005811080e406c0341c140001d15003034401070340c0d82e2403c1c80388030224071440c038030001c101c4154402e440303c10f4401805140741515000084002c3c001003042c800c195540d610340c9620380f1241420740000302d0050f03142c0b241c03200d000c0361807008400c54590045041c05400c000300700b2507520309020641e0040d0321001901000b0910740045552a5070704034591041c401c030143c0c00b113180350044001140b8054450003880140c5e01c840c1419120f015903e65903690b940162100070005509070901030380a881890f14280101081e40012080300841c0000d481c1d8029682503255014400d0000c600524400c0c01e100700142002007104201c00899074222824040d210f6030f042941004a400c54003c100c028101d51710403c511843c0b00c0319180a02c502c0e80300c0e10345840001aa0180401c1d42c4414a0540d2600c0d07003008a011818410403008a4080d41008011f440204141c403907080658000c4200 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 672539514 1250 672538264 672538267
    0xd03050c030a081012020a03060e070e09030903070609140d11060d02070209061903080a0c121706030f030711060c0f07080c0619050c010902040507171003080a050f04080106060302 79
    0x42c0c0c2c40465848103401041d041c4225417032a001584544941070116584080e0004100079034410881c00e100c900e8000c5100d00c4c1a410030700100700c00001c060181d1076811025200ca41ea03030b408050710481050f01c41c00c203803881d00c0165000980752280c034034010305010340001044410140c00142c030302c2d440f0529031200558007181b44429030034030307061040d840002500e20801d442418401000344940e14071000b031040000164108426102d481d048440b158401e005641a010750034000d024194211400030008006400040442c41c000880e800f000b0000006940b03420101d0312084a900c0002c016103401c010100140c40e003140007002140250828030300600a01c81c10b001105040c18420783d00103102c1d200500040383e441e90700c218000040c0e0918103100381e0310381070514121b0241c40714200c040d510a20340810490907a400118003200c8106071840d40441d5a1800c811f40b0031401c1c54003026005050601c00307189400d001d00d00400381840c0341e09801d8182541e0b002c0690a64045400500001c0e40 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 672540764 1250 672539514 672539521
    0x90106031a1207080f060c1b010f020708040e0603010b090a15050a0909030807080c0415030f0e06011401180504050405070b0414040e0d020d030b011107030f110d110d03050c030a08 79
    0x13020b025644104101034040c0c078a41c00c26010241242c0194100b207050f9201001e50f946440d00c095001c8801e05120070001d5485440e6810090070300c4c0c01500c6004144005840001ca90b4038040c491440341c40c400410002d800c3e241c2c101640010714160541011010410b0000305060342c4e034490790b40041c44412000b180142040c5801085018003401e07000038840010244000050018259016200c484e80f000c4c440d030b20b40314022005003142c0164020802d10b80500c1800c03820300400d0f03d506a403100c1c520f140c01d0040100c01111117249142a01008680703000b420f000301d00c1e240d00010340150068049544050320303041141c4003640319230301c00030784200e100d0088900c42c03c103400380d1040300d058800540402014904040e40303c084041c01882003560362081e642250b8051001c03540d4001c20041150005500d07880d184142e503800b0f1030103075001404010600460310f410b155016465a00c80e486003000e018241c00c0c04000320960104605111301403000f140920307410406005101c416503680140b904 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 672542014 1250 672540764 672540779
    0xa080d0516090608010b0a17100f060f0c08070c03080c0f06070e010f140c07090b03100b0d0305090310090501051b041a09210d090e0402090106031a1207 67
    0x1000303801e2640901581c0034081003000e0f004041141100c2050403855540c08031a117040300c000b013100302d07102c07403a400b00c4080c0031018007810b41c10701c140e54032610440240c07078540d032007901c2d20f1000102220001c3d080380c2864000442d50005810118401c8805c104400e480741d0700d20b02e164001c0f041003041175106007010807040c88104869a080306060420088800b07004000900750f215080e50380d008d00c810320480d10220f804440c120f034a5500c00c1020381d840b0313036100c902240c0030b42000c2c0d503c24443d100d0301060030705003c028800c00b90b0b559001000d40300c0070582550256110781003043e4190b81401451042c58121603603001e03052b00343d03104100000d485d20340816950300054029180b445a80002d0000f07210400d041c005c50380c0c4d54850040f034180c072203500c0c000055000c001800e5072005545042007a0b0790030800020f400600001e2034480410380c0c0e450b9800d0411400d003c850181d8888004401004014001d910103000d010801b1407514080710f00c103000c07070401d203110703000340e9040d40c0211001c110b1391 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 672543264 1250 672542014 672542041
    0x5032a100b06030402010507031718010609060f1710060b190e0a26030a0f110114010324090b070f09081b01021f1d0f07030b06030a080d05 61
    0x4408044204007900500300410001d002c000e0009040c40340015859080c540581c800040d4075414200840084c5410341d264010643c2c082d45c851410760070300e480070406001d03a0280b2000d440c1e8107c1715208840c03420303810700740f400a510f42d0812580075800012a0400c5140118000fa150244540c2c0da10181040c100740c4201c1120099010822051a11900b55803600300c148100c50109448000c0c016200c05e1282031008102c128155503c400120111903c0c2c0045014100150301d49401d0407820001d2071003800d0740c000c0280009114047c2005000080c42d1000c1c0b40000080c044071030354119038560f0110b040740c04a06040d90641d40d817030104082954011606c0c1c1b20305069191400e4041e01d4101001d5031600755060590307110b40e802e096242c07642d00c2008801300750000141c010100c4001040783e000100f40e40499410048000518140743d041c00003160b4901001c10b40040c0b45041c550b1322040f410042c058050b55150082e0001040462417060141c01401e82d0440b000070309042c02031a90074030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 672544514 1250 672543264 672543283
    0xc0c1b100215190e01140402040b032418030d140604020702150c0102070506250323040201020c03010207060f0b0d0b010e130f030c050d0201051b0705032a 68
    0x21035010300410051640d00600c156000301100400e04018400018020080c001e01000c2c0c8240303620b0f12441b42c000014030803460380164000d03201040110504402c0c1500d41c0d410044021080150540fa000c1e18101101000ea0201c240d40340f40d00c801c07807940801400e6511189090041c80e85a0340c1c0060708104a074451358121030116400c620b000750380c1d40400c207010340c010540d92a401000c01c006420840a4044482969000040d160340345807164000000310b040b840044600790700308100b030105601a1041c0e50080008051580c082c0c06c0980c03d4500e000e20040003241103000341c500f2440c054400b4005008411b100c5d40c0c0200d0704070510100541281e10901110340f00e03040001d400d1010a801480260546103028000702055940c008a854a500e04000091204000407101001c1c180d208009000b4644035000361444000b240c10304a081c2d0388207581c0780f070314200c22008560341c1c5000e000040181a03c901c0070380f4101101082c02144055400007210382d4500701d080134210300c2d0390600c4001c52 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 672545764 1250 672544514 672544517
    0x50313051e031218070909050703020604080312010923060307081b030f0a0b04030807050c0615131a010e01020708010c02071508090601050105091c062f030402090c0c1b10 75
    0x81c0520100c28503545d522510078414034035030303035002c00040c01010b105903c00755030040c050396521a42c4d101420707601d40c03058407419003100404001003020506806130a052041002080f1502134a001c0c55000c80d201c09007202d50300d031040d101c0004001c02c06001c01240000316200030102642d00c2e50078142041841c02d40741503130360064007800c00000c42c0b004010b60080c0e010316003652160740e010010f03603191040042010842c840c04080000d04d8160301d28101c1b60103c117441c041c90416454001c50240e800c1c84000215020382e04c1d50802c0194400c48843c600f80f03205204450b2420750324443e040c21180d000000c0030060700401002d0007100c41a0460001c151114a07040300c940c500490f8a503224501070092504000b40020f401ca0f0507903c40c1011801c0c4c40800410441008151a0013801441010104105212203441c0b501c04e000980400b0031000075551410f502d1552603a0800c001c100005250070314041d030034040c0e428100c0342040040c0c14481e00b0140c0c80d201b001d44404100d881e0741107500300c00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 672547014 1250 672545764 672545791
    0x309040c170103030f020304590a0212011409060a150311040e0f01030b09031602040f2a02150105060d090212100f0f0903050313051e0312 61
    0x40c1c64424008181101d41601d800c2e440c122000390100d04521495109001b00d0b81404c0b682c514000010800500340e124545a011741c810301d01c48a808120700828a00305d0b2520a8184010001000c11880e5405440d49400610b0641c1d4007400511800d400c2c1c00c031814102c5c404d02000c1c401c0c107044c0020303038102808884c0440c1c0b10b0f29110100c030380e03222000c0d005000c040d00c0714056130100e04020260f4028080d8030041103424038280c8600c0700380c01c80902c810f4555002080101f10340c844048220b944960a4006c0800c040503e5000e010280400c0c0e80100c1e4520b81c1c4824032200f0500120301c9031940f503281300005420b40d44500700207180640006501c8241d1400a0040215030381c1c107002c480002070001e0b4042200c2c240e5000080481d0758803440710b1001d000c0d0b4100c1074039494607544a55039981c8a818108441c01f000c0803d081220b0b51410010007040c030800103d1503500e035400c18044140d1007442103402c0701349003250400401441d088004190f51000c14495100e580c5480c00c0ca501c20086c1e003e44 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 672548264 1250 672547014 672547037
    0x40506041503240204060201020a09150e0108041406010f14040501060c02092a0702040f0905030a05071b0e15090c1e0f0a05040f0f032402090d050309040c 68
    0x1d9441004a200081c50b466240940e242c0c81c0701000700c0c0e03064034030701c41d04115140c80d40c886020707020358030440503d0f0010381408400714a0813000d800100303800e000c030354550304d402c0c0304500152101c45002e0416204402109030640319235031f080003018040e01032034110300901e500d400000c0070701070752001d50b19204a040c40010300c01240d02ca01e00c1c0e0259501112501c40d191070351039441c01d140a00701c0203241d50240940c204d100c80004000100803c520a51701001042d10304003c1c5011100c0c0358000400d03c1d007081082c27240e0584950090122580560702e12000245800c8482031040401e0b40700002c0100707494104040c0c20f80d802d60040c140300041d0340700e030000cac5042c00403100144a8014000f00c1c22509242c02240007580c2c40035550885030108105945400114002e040782e0440e12504407481c44110000c04e203a072034207502c042100d030b1048201200b03141ca0f000c92501c0ba2122031803029201d5007800b1940c820ba68210882d07100c24003c0e400303140e0b10a102c4050005480e00b240712070080c00400c4408 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 672549514 1250 672548264 672548291
    0xc08010f030f0201051c1b020c01020102210907170a02040513110631170f03090f13090303050610030608300706050106120e15150a09050604050604 65
    0xb07080c21950900c0d00c0ea035520030740c2240140411484e4040401d66281c1405c107100c8a00720440081458019005c9600d03420180c00124207070310034100c00100b01061040c41d400c44016040000350800c1001d8182c4080310344541480090184102800055601c1000f003c000d50809114007604080c40c40050242003002c0d84402e48185040040b480c0100c4001a41e101030342d46286d48041d07001182e110262985191001411203000540184101ca81210281030102e000028052050005203030255040404140070880c2c14114050860741144400c0301d0303d000303000c1c680326601c1d20038404e480029107401c049003401980c0340c150071840c4c1454982001400710400010300b809881001c01500c00311104404103048020602c0fa0321003143c0e4402003800b4003080010707005181a9131417542e800203030030300800910040d10a848401170b51a0000390003904d00041c07140c51164040380d624a5031000ca170605000c5406803155611445c07103d0b40d20300030300100c0e207000d000d5142c0000c000c48050200144403090b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 672550764 1250 672549514 672549533
    0x19140a21030227062b0c05120f04021908010903021c0c060207080c0303010303050d0f0605150a020c100c03020129060304140303041208060a06080c0f040b07060c08010f03 75
    0x140d40e000c050103010600b43c16074a040480300d80d0480e0756070041c4400c0b01d450186440a545021844480e8142200d0004491090043e84c400100c44038401a140d191311841400c480c2d0003900030b030781090102e078442d6006400381440d40b0040c0309400000680410301c0c24024101a4a2444102e4a40a05440e842c8950b48a05240d4005400803001a5186110b145c402543c2c030034100c1d80100c2d400084000001d054005029011458100d041840359140b50706554049410070700884d540204021403020000540d58068a40d0100900482d40e0542000e80010703c003600540184001a0a41c50340e1810103034207024100f1402500c1000165450102002d11144111070001c80e00624000c030010781401400352000000709000c5050b47e60700c0c14142440d50310680c070040c0304400315000c04081081c502b42090308404692084d44c8054041d1241080c0418561001c4844400d1540510011860b100c0c02d0009040e02440f40c0d00001d09600d22400c0508400e505901840074854400420404508040d5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 672552014 1250 672550764 672550807
    0xf010f0506090a05030a060b13020702010512040602090d05100e03120601030c090b03070815060313030f09051c110d11102d030e0d0219140a210302 65
    0x151210745941d01080480e10000aa81c0105c2e814400c1440800a01405500c80c1c2154042503c1c110642c441610440707040c1d2190440007800100c080084982c5e50000100d501d4115100b180e0251a0000b02c2c000034440104007402a500d0b03401c014000b0090300304074810b0311049822103024608041d0007031104450280c0003410320381410380755115150f82c5032140c0c042c400500444a40152213041111004004010855074402e261400c01191043c83c9001b00c2568403980c81d1110111284c260340e030382180ea015003480560180541c1c1040800d881c0c0c0c0e5020004027080718000c50448200a0781046110a421000c0c0e8071b001d44030b00100a004a20303541803220710410155500003c10b80c28401c21100840114040c0401008074070007060134946010138074685285a6606102e41c101c2c031307a07040782c6404098100c8405684002419038440484070a00b6400301e0241e20200742040060403035508009052408482803049004500400401e804101e58039142ca45011030600d0840302d044001800e550 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 672553264 1250 672552014 672552019
    0xb0d08360a1202150a020307060b06030c03060f0604081515010309120302031512100507020c06070b0c0403060e0f0d0f17270a020901050f0604052b1103060f010f05 72
    0x9981d00c105544613108480e0800c1903c20038a55260880c81c002034580d00244021240141404081640780c507040c025280038080b80c03c1844d00c2c5881d05000c011010031034000c00b642040c0700744400030303110200b8403020072109440c03216500e8916001100e05e00c0d494030400b00d54181803400c1510800700b400c5003064a10b036003080c00c0060b070303d03264100e80e0300000120b445400c2e03200050005002d141b41e030101e1400d07a043e06500052013151aa00030a0307803508203e4043c682c11080a02800000c5020325100d1500400008505c0b451305031030303854081c281c1d0400c211a03a01e91380818007019404904200b403c02020300c0e0300d4241c01d03044001a00508281d82e005080508082410119038911000250010400d0078103240694400e9440f00c040e8448402200c1a4450107020340001034031300708032020f0302c0c0009000b02a6032505003030038104080b1010440c403c50f01c040420f40c00c2c4c2c48440740003881c451003900510140400c5854103003014a4240010079410035a9110310041010040161041044d44c104 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 672554514 1250 672553264 672553289
    0x150402090301113c0913090512071a1902090a15031b020c0d030f031812030b010c11010315120807020a06261909060b010207081f0b0d08360a 62
    0x8000c808003400c032803000030300a801011225907812000f10014030ac458800d0803a540c0760a0030302c9191040300c1c012107001041d41c000002858680c1d40c5507000700a9100b0040030800c0c055114000035030b0403c101c03520900441e83e5509040121080f144403030b0315075122440205000d00301302021408502c090300004041c80501c0d080b11010034043d400404401101108480c4007a2031801d01e00000820120740b200030924200d1400e50f503521500e030307842610350071100c489030030b20a90004500030400341c0107101c440c845003103001c1001000c8400e0443c400380a003c200e500d43c8194010040842c40c0c1d0351003482032000c08030b40741c2c0d41a4054601e049864484420f40c02d59641ea0002030500003d0303071091143d10510301000a0100a44d0368000f41d0810400c1c2d00f1620f0b00e41d1290151580c4c0c1404002031411404401145d49505c02d5a03081003600805c0131b0941d10781c5908650380d132030003070300280562036000b8003200322000d0000108a5083c4214004404081180205004289018241c4c01030b41c0d4004038 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 672555764 1250 672554514 672554539
    0x10207060e0106450b040c2708060105060705070b160209070801180f06151d121509030403120e040b011418030a020a0e01150503150402090301113c09 66
    0x30aa02414208102400030320804c145500300800d40c2040301c98044610501043c012000b4203408c540c0c00c1600d01842c010110780c0d003801c081040d540c00c441e00495062280700e001040d160410701c0a130403010a500c50404500601e07104001602e80010700000c100310000c40100850110884d205090200c0700320009843c1d464404540050036541e001021040c4860380b2540395254003450000c0400000304401900440311703001c00c00d4103010707000120015440450340c03e08a100c40f401403170300f2418400032a0b103441d50703d0b40d4480b1040118011107010856000c18580030303003094011084401c0c800d00e007104d0044085007040040d8095a12002000000401c40000c1074408100391002281c00918500c402da84d119090a00f0303641c00d000310083c062010500200107805401600d0107841c0115600b043c00720070f9410300000350804ca062950640d201c21035181c0030040c01d001403603081036081d00b840414075410085065a2461070a0a40302c0d080c441289a800300c14105507018003004407241000e514 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 672557014 1250 672555764 672555899
    0x610050d0b0301061403010609020a0503073f0e060c16020a170703140309010203120411090c030702010b15070303020a20060103020f030d02061503010207060e0106 72
    0x301601d0429007640c07a1080108442212448900000004800a101450700c90f40f080c1c00380d0040903210004a0410700c003250105001d0007512482c41101140c4000000413540c02110a040c511041182031f00340141180354807116010b00c0c030001d23000c1070082600e41802d000d813100c984a0a290389148401442c1603408554426500300001c1403200b80c05000d40024641240e26036107280b00c111800441c116100340340010100c15901c4030b04058001c0c4d801d040b0385080007250b94600800454002140404840c660750307407865407500818032040704035224a803056010b03084961080c003282c4206881000950780100d52030840b01c555501d440c1c09625062896002d8030518070185030600700b8688000500310842c4001001d504a90085810024074403600040c181c0760307100c9426150050f0440300c0022480240300e1039000420700082d00040c641182034a030300049070200c1d034121803243d4407500104440141c041c01c09a05144204e00120781d40066411345034900b200b681c54811210b64681080c0c05070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 672558264 1250 672557014 672557021
    0x11101020f0301080f01230112240608010c110a0809010516120905010912113f030307080a0b040207060908030a060906080307030e1314011d0610050d 66
    0x2400700051107900c82d41c5500000e5181c0300440c3e107034141d66181140c0426041c04e00c000d0003d2042000712030b04116401c01c8136134005518082001e640560b4849c0061122151409410071214804000000d003581000b2049080d03030301905881d400c01148d140030314030140e0045030803d02c4545c440c00381c0b41e4503001003006a48500a00f9207025442c413103205a0b030b00340194038114084405d0150380311040680c40b0b00041d120040540030389095040c106030b071a0001000c1c800302c0071070148010480b00f08125110106e490040303030b61000840c0c201404034541c596030380b500050382e18460500c000d54154500488020040301c00100610181c54651122034803545890b41180d10310781c1c008d00144182511410703d1040e55100b03840d075030b26082c030701000090303041c1142c41180305444007000510325012490b1030446040302d0040605500401e544040c002051380c91060814031345845240301030940c504686c040c0c00b442103007980c1004c0d6990070300708049a50b900d034860880c064607003400c9803101c03096000103005 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 672559514 1250 672558264 672558277
    0x4020c07030b040f17070f0209071206300302030306010c03120f020309060603070b030610120501121a0402101b0b09460f0f08070c060f090501110102 66
    0x1000e4a82c01408140000709243c142e031503016069520102480c0c0180b40c003144500b1002900700e4103000e00040051614244103500814140b0b0703c400e4066841d4200c030200c80e259070054481d105a40d180202c80c145411400384a041604007003000c049041d10082e40b0380c4801009941044110907031041018007400300070090505150381000b49e2015118a5002544280e601904c02d208070400100c40d03280015040317091f542c61001c441d0854907808117001000768413100c2d01c014006002c003c40c0c03030340b0010b2141c18000c1c044070501810b40f510311304007000c1c031140613000100400b90035801c0002603104c520107212100300394917040019842d024410010207520080c001d202c40c89030401c0c401c600340c0000b00e84a1180603003d4042e5008116030004a80306400311200d010079400b43c19651203c40704200c0c0c0c2d100240600084811021a6a20015140c159030307002c036622440490f409090001c11503040001c1c1c07407207003018607100f6840c0c04041c100c0d4110780314140c100b008a895030b03403030342b0029015540c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 672560764 1250 672559514 672559523
    0x7082208010e0c0901140d06110702151e070c0e04060e0a03030c12150909050a1205070b0a0b060d2408100c140d0b040207080a0804020a050906060904020c0703 70
    0x90b2804400c01e626182c58040140c4112004c03000850440460f1460480f03480340109104c24080c1207a0300c0300007a101e10b18034004501c13414070450003d600d03014041e030350041d04e00b0f4503282e1303503900f00084403013008a81104081408003030103102c001408494108060329220305d4140526507c62030700d00090040e100d00b00b50380d400b84940e143e040607010b03040207808034665102c00c10b20104503c41c10040f122451a200d0400c085030000700704090b819031142246a0044041d0b0709484141e848145d80302d0001130a0340c0001d500043c010040c4401174201c81d0700020389100600580c011003000600c00e00503841d480c0c0300540c3c0d0f003d104c80404050b08403182884a01d120030036840e42e6032401280c80d0101006403040700e50400d01e0036030b940c03403042d00016208805401c2442c00c000300c3e152034900804130210700c0c0da0420b07403c1005602042d0a20083c191000d034640e81c80846140c2032060000c5402264403c034096407810301406034a64500003906c4481d441550f0050b103544000011034507144080d8005803 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 672562014 1250 672560764 672560771
    0x82d0a15080a1b152a21090905060a05010c080d05090d020f0115180e0f0c01020c040203040b0c0703020304030501020313140115090e1204060c1e0302070303050a0210060f1a0708220801 81
    0x310002c6c1d102c3c50101003006034450300c0c0000c3c1d88003c59170503244220362140c2c0c81200c0c40002d11941d80200307070380e103404d50040c0500c4c3d08040c0c01c00d549400300c41054a4040e4154010402950349560401c0b0540e00c01d1800c50080c801c1a101303001d2028228407a01075a0f610184199040414009a0748002080320f202c40481e2149508000403640701c040e4150603c0c0180107428504101e410140222030040d98025500f06071655541c013030070b101d9003100c401101140410000000070070001d0028600a003070305500303003030701c0035940c90900300300d030410222400d40b641003420070b00c0d002400e603400700c0c200c8981c1000407505441550404d8100214040042040400032602184250303008880010a9110b4040160212070982c42a640081c10308001001a881202d0074070029105401508032030619004850045101c40c80d00002d03a403a540204680c0041003004125a0301414500a40c04c0c032480880c900d8481e89489002c858030070315101750721000d00401103142142d80c0345841001815088000c1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 672563264 1250 672562014 672562043
    0xb070320010c0504060f0c050d0c080d060305160905040512030a02070f05010203012603190c0204091103010f02040810020f0415082d0a15080a1b152a 66
    0xb0f0056042070160038000380312000c58107011409211301311501508030008004814030128100d440409040c000c0340d803104144440527203c0082d01030a0040e5202c0c0c0c000e8119508a250b4000c000e000c10b61140000c5070411040c4004504082200c4a601203200c100966903502c0c625101c000e40301d06403009203110a088a00418000107601550680e40c101488044112511507040307400701c1c4110130028190003c11150325180c0e060342c06200107000c98101400c04d4100c540001d0221210400180d4106e1240052801c130362a007841503d2809110704000c5040c01e05010801c0e50f40e0700c1c8000104800b980c0080d0070100d0141c140240c3c1c00903d40d40445601c002c502c4130005150a5044e20300d48590032070b420155468038508440829a64144130080c10259540030788000a4244117914240c070616100001c20511230510250f020301c4e00031501c900100001611202081d9455131100244202071071651030544e43c4410080c01c50f25400080c100c40c020b003000041404525500010b00080c40f00150 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 672564514 1250 672563264 672563267
    0x90f0d05160e010e090309130f0618020c060919240e21090d06051801181109040503070201110c190303320705010612060501080609070b070320010c 65
    0x2c090681e40442040502074584007041e175924003404003050b511803074040c050309040c202540201c000e0f2907210408030344240e40c0d848201d25500c50200e82c1c00f42c0c039000a0b00c8824108200501a00501e10900406c859503006602040010398141c3c000c0138200e120a400b00300d100c41c0343c2402c10101031500701b000880340382c890f2503036100200001d02213100c3c2034080804040c40504107880070450050903820385810695610340080c100105001e8802600c0c0d80c42111802091044480030b45a4103a4900061154200440d01100d400c1c0054400d0346200c0800000400c0403041e10207a550a0800744001d40c071700c40c1500d0419041002d945e4000b0070390319407004181000071480c000c0324000d4075521a40840740d445000d0950442000f0908008219a0f02041500701c2005154183c0101c2c000a00d03580c80c3d004040d4500680d910680d0b00c03c0e1650b0050003200c03000e11070315401c08004d00040000b14900390154a89000c0c5150190600c08021036100c2d00350f000300313480d004a0814900030040c10801140 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 672565764 1250 672564514 672564539
    0xc0323010806180c101b05030315060301050f06130e10090c18060e18040606080705060304170d0b060d06080c010f050f0a0c0c03060b010212090f0d0516 67
    0xe00095071040030007041d411a068241c507400780b80302501802c8004d0090082c040c803082c405128104202c0100030300030340e86001004004003030740308901841e40c0c0d00f046100d040b4542c000103219441410f0800040095554040021051300720079a6003a1b00d40301a160080100825035114801d112025030411041c000b10401c9041a5030803000208150f0240300d200b1658131010004101c400009a40140708050040c180d44c180120020f100d12081515400002c000d008103880844034243c50b900103222400080c07044401410003680e00034114a0651184103000c0e081880d10050348000080c00b54000402d600009500007018041c1ca980c0e10240f442400140640d10603010580244d1b01c010a00b036115034015049000c003940c2e99818024000f5030f020041d40304010340703400d100340c031710880c0005111103403003a0045000310700005042e1800c90000e41082c07031490309507060b49810051240140d441c5000c1e2581242c094503404885803c1d0b10308285003840032407414000111840000030242094074 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 672567014 1250 672565764 672565769
    0xc040b030117060c1204110402041d01050a080c0a0e06030313060c060c080105060a180905071e08010302060403120c02090a0b0f0a080322090c0306090b011409040c032301 75
    0x2421a40307541d44c0c2c0000c5038914003543e889013403804c5106001c18082425820043c029490080c001403400f0f40c1c400020030708414007080a110950040010041868407000140003080f29070003030112070090030005548030526024071141c440000000c100607450401c00d0325614010360311a8100da68031080041d1140442400484419043c0984c0c81800e51040b194103040703640103032000d42020b1200c04181c51044245902c2c1c41c3d460340080001503071807854048d00340501480d81301d450094207600f094000030002d1078511402e01401c84010001600c0300d8003128200c0e40c111180c03041d121400c0784120b9a10a503c4c1c03010751702001042c03c0c0010802c840e400381d1000322007100d540c031101d44540c00380400015544030324030141d04244007035500f2550348180c26603603a0b01203100203580c9480d0200c6500b1107a0101d40034000960b40c0c1c1040c01505804e1003154030841c401d080c201c0320104a060449414131552032560b000e1615101c00000c01b5000e60000f503861014a40c10b03249440e85d400c882d6900c1d03207092 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 672568264 1250 672567014 672567059
    0xb01140c0303161b061e0c0807200604120801061b0807020f090403090816080c1011060403030c090b090a0303030f150b0a03060b13091107061a0f01020718050c040b0301 74
    0x1105c01508100013442482040000b0b511600700070b81d140c03082982c0d68000f07110010040302c10040c4ac1c42d1401400d0210601c101d108a000412001e200c2400800001051f0411420f000ca6695680409404916040400e41c1d0114809a44010074400724041005c0c01c0350f40ca4100120318140820550044000740503124814100c3e01c40c00f0148402c41451030700e07031003800c810741c00c000341c554405c1c141511852201c0200d820705040700440d019116283c6a0100c4d800e800090755000d9a65501d81e000c0d01c1c001c01080074504640c1815281e10015014170250300c00242815a0340380f03202c207070032004d81200b640c071141941c9a0100070b40c0c60b2a070308480e6103c8611180000d2402c1008a12882c01000b82d401c88070503180300e000e41500b010003804c014641c11014144106041c000b003400a24140140c0c115a101d10080b6040000306600f4480541c000902003410b5421440062200078680c080221042c90181c0300400c3d0780d12196106402441584c000d40301c020f40001c00882d95800b44a080340825400 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 672569514 1250 672568264 672568301
    0x7170c07090b01091404021e0a08150f030d210f0603020f0402040b04180605090c0c070605030628120c18020f0d0903030b06030a0b01140c0303161b06 66
    0xb00030045908580034010000c000c010906000c4150500d64090840078103081c81b000b41440103800641c210380c010607511400549040304000000401804c3d200308100103031540c51018584000082d1600102151402001540f000444088105124410f48180100760412002d80c1d48a80d4201074802e6000a9000e030751507900000c11030801b4804c81c0c04a4a0f0000d03e03030b04060a0080c1c1d00a0460400d4040308101d84030400402e00d41d881c010000d02403180c401500c0c0d0b48a039843e11050411b00705501100502c0020300410159032104251044001c4440060850307080340305420585c9a14150800e090b0b030168840b001d0308000c1d000c5845c100342c640c8102120b2900580c0c040d90000da00c5040680b4410030014807944241402c43c0d04880030240c82800d0100c0c402c143d06001c155150422183c2030b140540700c44030b460b09540c00500013085520b940d03a1740c03403520100c05c14583c1e517032101a08071200b00000310000c0035018417a24071488244503440e0344000c005820305101d000341401c0e04a10702031458 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 672570764 1250 672569514 672569531
    0x81c18170301080c0121050133080a02090103090b090307050601080c010c06050702010209120705101106040b06031e0c0a0603150506090a080303011205010c0804031407170c0709 78
    0x592001d4074125143c050080c4119600c020044500d650000d80403c0109884061849000070074010940648581d0343c5c1e410307101206d582d219201c00300c01000c610780744030a01540c0301c40755404401254031555814026030b541160400480050651910250051038090144428020701200804181c1d006608480450340c0395200e080d2100b442400d081d020503004d0040078002401500050740c0103501d4000103050141c020046030350b050b19501000c0d40c3e90800c2c1d03030501807803402c029040c0340c409043c40c0049400d02406622540c820002c0c2c0302034850700c0c031400000c04541e010407031400304200d400c180f003030102da8910794a6030315030910994a1040c2c94909010908c54401d02ca1602450b603122030395842c442c5440144070b0954010036101d40c02406081c00480e44800820040d40217050321028050702c0003039030520314215103006c0610402c0211220034000441e600402030701c0030191114141da500d01080c500200c04e00c2d842110410032040102c0e01d0307101c89902007000011908444001e118052 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 672572014 1250 672570764 672570803
    0x204090b010f0206090607180b070c06030c0212070609050c030a0821071205090316050304031b05090103060507030f0e0105070e0301061a130306112212081c18 70
    0x300843e0626400e0384070000087d00c40d4440d41001c0d15152a44030103451aa44400035440507510181041c0c41020701c407002000b03416418454040000d6040c070140c5600d010701050101c407031140308000303011144c8401c0d06500307129090100101500b00102182c07500107203490007051940280524150ba2086a000c65040d200850700c458441c859550701c5d10f018007628656a0002c000160441402d44818014050021105002402d907a40034100070343d00c6514519201c4286648202401d100c131001007402c1010351581d40760107064940c0725101007074039680d407001140140090042d08209070b0811ba03a080c900c00041d840103018000e1503880c4d200001d00c0c001814241c480070f00c2203000c000c0c1c041660b055070801400143c4a01032101d0350b07001c0e00340c0d82c0340c450406541181124035144580050014080e0754800101710300317440c3c40c1000600c014031f060808000c1f040d501002900c1070500140c10145540d010703218003111801e0038410400c8080124940202c0344104200b12000d003031303d114002548 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 672573264 1250 672572014 672572023
    0x10201110d09030c0b10031407030201021e12032805091c090b030108010506091308070611070203060a0c020c030705031902011e08060f090f060603060d0203010204090b010f02 77
    0x10140ea991078a0704100610200c01420b140e4016010080c07145912000100d440d582036001e403030b00400c2030a0042c00e5081c40c0c24031032041c2c5a501607951281e402080142d0f00031800a0175501c81c51001b00c9a0314201c1c0302c55042405161504003000000010404d02422a8203e80a01842000a0320090038100b2030141101c1040d54490714551103101805050310704d10902101980b001d1400301182952001d9900f11030300281c0003140d441e510380040080c5801d001d074050741d06c65007030346000d51520355a88903d6014400d00d100a40003e40b289421240780e1040c2003113400e4242d001c0c048540c280303002209139000b440c902e5500c0005003d01c10824071710b8500000c42d14160703903004001d000010140640741038110000360040b07061103400010051040f01d03805d0b001c00c10940302d0b103400070f00f850a9410803060040280740c0a1040d40900148000c14408036111588480c05480161b07481e203032140011800c041550f0f009615600008000c0382e00011500000081002030300c0d034404030228a41d060f07898 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 672574514 1250 672573264 672573281
    0xa0914010c0c050f0a0305060412030c0504060903200d06060906050618100c15050402010210060e07030e07120f0b011a1210091d0f030a0e0d0219170606010201 70
    0x1108402d14082c800e41c50800e41144080000410900c00c07146e503030f600d43e42030010449003a01d5960810130409100b42c1c0501901a0958061030510700d01400c00001030300324140d6000141c401400000600080a4101809050b07285c0c020100d0301e4804841c80c0c020b0241010703004030740c0700c58100940041d603800d000302900e00d4a00412000c10184258000f4030080c0103008441c0360801103030746c01010200b0003102504c20940c8021b54041642d01c0c0038000a8900074000700032024952904404000441342c8400c0507800005510300402c191aa03803400c20b00c0d09503590001044070110940140402c802d0712641c4034041c0c402c010035075180c0c1e0f80c0e14050100c98401c101460103618100b00e800c180781041091581c0c08030100034200c1140d5103c0c0c03603e504a954801503803180043e5030410768010b8000b0445450302201c504011840d080021400508410391030800c54058407200041100715030319a4220401011050008410326944546402d015440300c4102496801500007082c669441800b45004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 672575764 1250 672574514 672574523
    0xd030c0e10030504060b0a0b120c1c0c020a150b0906032107170409060306050901090201140702011e0201060510050712080402040209222403170f0a0914010c 69
    0x1076031108900603000b418006208071112a0b0721000b02c1c0d00e55580da54104040d041c2c140c403183c6c07940403003e43d14045460141500c669060180441c20f0707010311101150041c40f0483c400070440e01c0c081c4005a240004611008003181d82c1001c00341c00d401451b6008a011360421a003982458680c8401c1c9a01c0f118aa9800e10401400d072140118402409000b081c00c1403003003010b88882e24000d501040b50350869044040f505440e04410401d0111501440f6001807804000301f018100c00c3c1d0000e0104160181c802800010100784c0b82e007503a004803801c0980c1c602210031002c3c010615a80240200958052a48526101d00e104a6001d11800503590071507440b680d43c00d81e400e00600b003540c00c00b10041003260711030b8003080501001e489102000412003151710401960070103002007442601d0034040310400190b425035111642401d02c1141c00d044a4001c0318501500c02074250212541c4a548000c41000c13000140e60703001d240c0d00c10008001c849180024001c0f10050000454840c1c501000280 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 672577014 1250 672575764 672575779
    0x90d150e190f2a03030513050603060a0e06010e19080d0f12110c1605010809150a020307090f080a0c06090506030703150510050322050a06050a1d0d030c0e 68
    0x8001520942c0d0207500e100c0080c003c10100380c0514000c03091803003e40045000a4001c60203041441011181e500900300c1180c41c28207510345080410b20114862240c511400303042c0c804038000b640208104050f40001414505451600c20706035004081035118005152185001205025101e4544010304403190340e164000005107880c100041c003121034080400e2081000030b044001d100700301004400034041030f80b204c950b16010015000c0c140040a003051504581141c80807400c10300c0341c4c3e80d40480b4201e00103850351100c100440d4440d1098100e403418a01c041404940e02c90009105c1020a2080a241d044e098482404172944d6500e481440d800c03600a001141d1920300a03000314030007980302c0301a0491255a94005003500859021400210340f00000344034031350700383e0508510220082c00c81403000401650703a699581c11101400b411850f40c42000c82c07103184858001c3c044c44510f8460141600f42d90300082c0d80c0300d07044040000040ba00d80000214030500400103080c07420001072084 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 672578264 1250 672577014 672577043
    0x81b030a1d190e060406060504060e041a120f010b01030b090103030e03160b070203010b0d0201140f160b0f07080f0604020f09030d0c0b0c040f030602090d150e19 71
    0x40c40001d60740a400d0b64410074a02048068020349400e400007003443c40741c540380c02c1c02c11070144003c444160b003107801040300401050000c145c0001d06800002d405490028040300a00551315401d00110b101c190301007458005039148010006039035141848040c001c0048504840064044910708820710b174102000c81c004201284c010114101000b0003d0203480c9819022184d0303d080b446640c11958549102058840640c1001d102e5000c03500801c1e140c01d11924295000602401501d0501c412403140014005c0d000d8070000041c1d0b01007461340d100741d008104072407400c1944841d007240c48518070760000d00041c064a100d1046c90b4007803443d031040780610b44c40b00c0044c0000780d44080754864620104028045454900300300ca001100404c4c0c2d0f4440c200503291a2003078450748040c00c00c13803d0040c1400144000c604a0031581c0884c1c1c0d00c8000113940300c0020001c2400d03480c0140000e81005121305184c2e0b060466604010482183c0707405988a4a108586942000c2990760000d0062940030480 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 672579514 1250 672578264 672578297
    0xa03122309010e1c09090203190b1206070f110607080c0f04170705090c0c070b1b0a0b06041d030702040e01110307031a0a14040f18081b030a 62
    0x50381d086a03a8600100b5040d40302855180f500320207500004204100f1911400c5a6600003664006458200800d51440c100a4001e40e0501d40c941c2035405440c1d520000e0001c03071f58940740358090040b030070015240d0030b1411940281c0303c0e01c0242907900110310074402910310b02201050291107241141c0312840c440d01c1c0c15018401d980c01183d991508448200700228000c614000003103115240b20b4000c04c015030410041c0030805402510750840001c1c140021500150041035000940303c4441d00940c60b09603c291058062158480c100300a004c1c80c48140c0522900700411403180400361130510021096003000d2511142d61080080b16820a0000c0c00c01482c00c4d8000b04106c0c12120004206c1505481c19041660f00c265400c0000c00c0da21003440001040851070710011480840d402031100d4a060141500f03144048180d900c641c1e80d81c04807004a04080c2d12040441014803050145502d6900c0d00c140c07154818400d0820340c030003810b000201e406001086980e81e0707d43da507035000c550324000c52 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 672580764 1250 672579514 672579581
    0xb07030f060803340b1302131d010b01020708070509133201090c050904060f0e0705120c0d0b04140604210e010f0e1906020a0312 57
    0x6454411070307160701d800100103008001030f0555442d03840c2d080d5000e001071003036880003840c0c40c0c040c0042103841c00103800c00b20310002c484952044036910b43c0c4402020070700c009140294503405d0055041d19082c0258024080201c030540110b003050300070003800004c6001a65600c5007441070444c2c6030703c0703c2e400340628240b010a071504014049414901d1282550f102410113244210b80000044102c25546508014400da0b4182001010007000102e10315260109041182e0003001d000e4440c03140400c00b005000e5015020100000c07404000d0098840601d42c1c45007031520034640b042070401d2160b1054480840c44404002000b0702c5861b40d800d05540b4100c03007090042007030b60b800f1500145051642c00c01c0c00303011302c101c0c41095100038201302d2071001c0038800440d0f0100750420603000c11125184c3d8021514140301409803d000d040b1030403907c00641007052039607409040403103825002890320340000309044840c3c40791f04d900803540d481518100c1140c2092021004000410b418510750401040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 672582014 1250 672580764 672580781
    0xc0306091b010215070c1a0106080a0506012006060a06030e0c1507290f16081b280203070f06050c0409050f06090a09032c0a0f05090a02070b0703 64
    0x184c8104c00d038820a00d80c250401183d104002ca00340704e031018100001014201801d0410b01d00340b000070f50500c200145001c0c00101014006556003011494981c05a4103422210b0030030007104082508600300c064440030240d800f64041c144801004c24610300074054001070011580c0100003180c0c84600700501003d0b4550420700002c4104444000700d680f001001d00d0300f4a05e40785800039044a00c0700e4400d49240207001048100c80f9a0601030f010141944a0320700e084a03142c00039050302c0340504c14000c1c0107500d0740c000c0943c8000a1004a007803031900e14040701401142c00c8141d1690030726007644c5034403403410000c000c070400080d01000910550f1199803c4450400d0140c1420748a0308a5012601c00382ca60201441580d002c021203850f02d2120aa03203e140080c0a2000c41d840e40c0d0060850b2641007034507a0032481001050700040801b00d02ca01e03c18000400c0c8081d12680c3d200031003000d2005000d00381c0501c800600044d424220340c000c44000503440040d441d8140d43d107100c06c0b0010300018 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 672583264 1250 672582014 672582017
    0x2070806061003021c060815090307030c020a090f0f0501080604080a0f20010e07050307050607170906031003050d081e060102010e0d03020a0201060509010b09010c05032a0c0306091b01 81
    0x21700080415001400e504001c1c44164080028000e007010107152030201d580b055400309000359400c109403500d01200b941c040c5c640c913041c1034000c518a4400160010400d401030b10f6444d00d40b0030302a15074800c3d0f410046292022510412840c0d0b01c4d280b20307a40384c60080790701a081031410090307140b02c20b02c01c1c0960599543d8600d005800100d01c0c8584400202c0c0c00c0c100d510306603451f5001e050300304c28107010300720081000300d009002552030480480d449008407007000d401c0f000c0400d02004032640b400e00321440100020551540c900d81b41c1c0e84602095040d0106551622401810300800c6001d906618003c403441100050360344a214080149110010090340c11952940030820082808200084d0101c0741c070f44016032a0020003000908491440d44514070030281caa00422007004440110b40004a003840d01c0c0c03141403445c0c18034529512508040f07150381003149170382e223080d003100d10110600b00c1d101c00c1c1502e450200070f80070503071f590405403604400d6400c030442d00070382442272040b13035014100706 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 672584514 1250 672583264 672583267
    0xd02010f02031e07121e0c140105040b180d0525050601060816030b0a121a0a020403022815020a2103201204030e09040f0b06010207080606100302 64
    0x2120702450318080407004400910f4000c11044100106500100da0194540c501501e103405008440c0000da002103401c1c10500070103c10b0001881590034000160084040080c841c50034203240014205104417080314240c41c5100d0300342d81d004004542c011320928566605404c1c4a411403500300f001c0b490400c4a00c5900304000000002a41480041c0c000c0803561142c02051803c9414680303c028424008030406103480e41c04001940e40003510810360740c08818442c0031840600d4403146010780305200102e2500b443c07080044202c41e64000b00b055900c00d448154040d0954280351019502e07048004140c2d4218a006000841e89201e652070504001e204a4840030460344440000e4081480c840f00302e6080900380c5c0700302a801d4090030110310800301441000301030f1900351000314000c90b0210b1204081c901d0104040c135209000c4540b032850024440011802d143c64501c0c0c60f080403010032038180840c1000522590700100d10300f8211810040600070300c0e030312001004541c5011500780310a1560 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 672585764 1250 672584514 672584527
    0x1b08370312110c1902010e01020705031c03020f07060606020c041e15050411090f030304030305071205071401021e030108031e12010e15030a03052a030a020a0b0a05060d02010f0203 79
    0x40012440004d0310344002d54200c20340d03000040581034503074170082c155403000e2020481c548000440b0120351403c43c078010080010b4000840192050302c0001000d504085070720024020103504c42c1045030b540c1c0e002c41d041280500b0911013035600b04020a17036840549510092046507a03000702542ea80341d54080821070b0b0302d4400080880706000c0006802c903a01040c1001207080c801b15003840c80074110f00440c1041e02d582e900815500c68000010300c1c4d100c2040030040354600a105036004541c0c0000c0c0303a10440707151241c1c1c42c000d401c0344404442c07070302d0340d404140c028520038011603040c0d0300e100014515044840380111180310707000545400c1010100403010003c4440c5117101d010344102c1b610783d2224200b1034002211640201ca4192107908090510400282c02034102c448004108903584c505d20b0603400300701d1062010a680f4005808002490b95102c1c2e03001c03400c085418841d0f000d6402e96243d6100910031204201c5440d90041c4a0740702ca00099030103200c5500c0c00780003500c102d82c5084c4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 672587014 1250 672585764 672585787
    0xb01140f1b06090a0f030918050a0b0405071218020d0b0108280b06031608100c09150c081b010b10020303131b0837031211 54
    0x2401544911140000400e04000e5100d00c400c00704440c1890740c0c0100b4060406040c215110384200c0701c01484081c0100c110400c140c0588420402040d6a250099030060300a9501001e008201c0b01400610b1900030203c040d4a89481440d010b42c5050f9030740c2025140101e00c19004201c003c0744a0002c1c82c0032902113006035038240384101c4407481616146102d52410f42091b02e0300800d003203502010b00030421019400c0c1248a03580c038800b0f0b0400d10301207060b02c0e8034000c41c2c1404448000c0361030035650a1070100e40040d000407070005000554508115044000c4012030b0302c901ca03801100414614002245100b502c60480042840e0250101600d0845031114403400080000843e18069454608486080c80e0540f41da204200460001d50f19603d0000840c3c10383e04c0090f1030013024011301c22404a0024882d030400300c06420900202d1b244c5556054192122030300c090004280d084071040c40191402040b205101c17001da2541f14401075826006501c00603001c8500f0300c28050702c7c2480700d0207040b0b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 672588264 1250 672587014 672587017
    0x15090e010207021c0312020a0905040920060a020307200604080f01050106030e030304030809010b2806050a0516030c120c11041b03110d0c020d02100c0807030b0114 72
    0x80241400140d98441501c1401100c00c038000310301d591802c0f82c01c414000b10760031a800c01c2c5d586213800310050341e03030092190980303a80b07200d07400490b0081c0c030b001608030800200c031700d804518031402702c4000b4850889a003000858480d002420f001600144414000503d05a1000800b00d002e00c0c440c509042580740419100d40180c5d103c01d00c1c1c0d80c000705030080340c2e403828420306001d000725142c144030b80d100802007981d81e40300190001b01001455400184800000c1d4041405400300400c0c154080d09040d043c050f0704e011400d108902e100700030000291b0309014604990b000b8000e900c0d17050074401c0a03c500f00c080038486001381c040c8a030741c1c200c00001a41003180c4990034002c82e21141c09450131420007002c810030f0340d2042c0c0d0180703107428441d0100784124450340c403040c9424500455141c42400c0c500780c0d6802101075002a00b4146400c0c151411307000321360311b001913419038200c400c1c0300c0110302e602081c4d902c01c18622010981036404a03c1d42882900402218001810200340d125138001d0150080d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 672589514 1250 672588264 672588281
    0x1203060f1f0905030a0c0e090c1306060e09130f03110a06020d360206090a0e19021303030c0f0b01080d021005060303040b0903070902030405010b09010602011e1509 72
    0x441c210805101c10340c0e0060101c80180c9000d50081c0740000e80c90ba51802c0c0850b690280c0a15a440b582c00905016001c00481031000009000100e03804105652030300036040c6405a480828941581c20f07416003003085560340300f42000541c5075100719075500c50302d8034000000c000b6410030104509144601d1410818440382ca4420000140d0700c0654500c1001106c046064601c0c100900550150200f2000081140755208201c0681c400c00e215100040403449084601030304414058400545022581c68580c810b1252040e004c515009401103582244524040b0101c6003416810134404a440f03614000345c0c0c03a1060440703409485040e2219500050709a0207030303155500c89081c072081b081d4103205c80403c040444006000600b000e50000c0e81f203000b9401038414405000c1200c00300c40c1d8080000400038230b5420021903403410302d130400c1d6010380b0421300028045d04081d400010254070510800c0e01c120704201c081400f2480d00101c0300050040d001c074000070040103401c04100d20009200c0c40e200b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 672590764 1250 672589514 672589549
    0x9030f12010f050108072115091407110601120206120f0103030f0f020705040509030405090f271e0106170a0501060e07090314162c091203060f 63
    0xe10750b01d041245500e1804580105040002c014280600b894001140940309000700141600540d000322003000107202c142d04580c5010300e882d500180380c07800c0c1c4d8825010314591030341c1003589a450060644244c0019644684541e202c078004100004401c1c0d400c45915100500c43d503d08816415903141c8600161b0f4041c1800b858507004000705a08038a210b9400441420540300d44911400007030b440340c031240318050103241c4038000100d510b1010f0040320302401e402089065541000d000740c02012404581e800e40b80014141030821082c050b1900105404405004054003507980404d00345000e0101c10b25445592215804076401e0850400d100c2c1d403601751002040c41e0030a5061240c01c0d15400e41c4890849540e1109200c00e02e0751022110080c1d03078101b64504001c80b040d0103182e1030706131054100245000d6280e400f04d14103109003a0003001d1140250116040710b0523542095240506072228001daa00080040f25510a904069544030034001c00174001c1e002e124005c03071820402039a4070031 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 672592014 1250 672590764 672590797
    0x1208070f061a0901081204031704030807030215060d020a03110d060203010605210103020102120703020a05030417010f0b031b0d1e0b07030605130504080d06090b031908090909030f 79
    0x6450034400c01c0c46004250005c020008005140405440c511590001410a810a1445050031840b49040301d0041d0b91041710a680c9440c00c0c24000e480c2d6058140742c030b210864050104400b440c1c050020f41095400a00c804859451580ea04011085070607201e50008222080d02c00030603114805140280b06c079131240f1390f40c0e09079201c0c54142402d03900c81d503030b5510140200500150342e000544403080e41021400f01d941d20310701d043c16464a0920000100f043c400042c002c529200b904080c1141810341c04024003481c030106038a6420b40d1a05005542c142d480501e05180c0c02070b0078105000004409403101510001d6512079500000c1c3e40307203000004a950300c03604010440c1c20200a42d00665a03e800c100c414101400190502462401088440d0304c640118040c0f0202c0c00480d1040c0c41c0201042106556966020025000d1040082d109003d0411310152540303005d41140c3d81a035100034010300c0d04d100b0500b0891a2a0081c090704000c0c0300030700c81c0f615903d02a0000b044084001d00150 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 672593264 1250 672592014 672592061
    0x31f0e070303030f0f11070320030a1701092a0e130b09060306070903020607081b06040201140f040b0d0b0a0314010f0c0203310b1b0105011208070f06 66
    0x2031050b0780d8184185d58040e0b1804400c5180c5030780c10410380b80c00c10b034140381c40002c800b90303003060b6503402109017942e000718000043c0706220107801800e61890a448642000144d0313070380303041c85030440340c03502030b1031780e0048043c14450810026400c0140e41c5464a042c000d80392305400c004981601c459a0101e415140c2d03c1010140e80c0c5045080c00f5030140e000c6008040700d1404002c000d120b0203223444004e01603c4082808020048c5d280c0035503039800d9070410141684090000c40e1541c1c1c2005407000c0e800310b0314855221942c407214000301c41100c800341e036400f4030382854404c141280750f00a54400e03000c50341c0ca0918084d680d850b070b0400401540141d080e2251a09015031700c46c01c444408010f000c5031841e100c1415061074000c0207a550742448111087d1014810904030004422698181c81d201241c02e00040b80307112034000545103024503180610248100707004114200ea00c01e020f0400200112022407002070215002440644c1c401d85a1200010240d554407041c0c843c98100d20b040741d107501071403 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 672594514 1250 672593264 672593291
    0x20609010b041112070905180412020f0a03080a0f02030108060a0b0603061c0204060506030a0e1005100312021c050d05150a0b0c1c0504060807020c031f0e07030303 72
    0x191661034004660400101403ca03c00b01c5141c0b04080d501c035072010080780000d25240c003502140c0002d10015040280c003c2c0e210343d4001174040c080f10300b00d03502480381d014400c11074070028041c0d0040c03507205e0040c146010541c405403400c2d003009045c8802039071507007139900b240e05890020b2b40c020704d00d007001407000b420540c894206580b440e00c0c0060091000f48100a4203079101212901d15040a182d03080c1c11138498004640070304455000070350404400414084a40c5880e031251810b09500025151071418900150083d198180c0c0c4aa2080030300c4901030000c6170600b556140107070014011a07102c0d01061460361b158104c0b0001a03070220740c01203080c0441c040640901a03101c4641e002d42030102940c000000c0a01d0502c1c043c0ea08a0345000c6440e0b856410304000119030860400c00c0701400c641000c900a01031360081c003603040003e24200200f019a400020070020740a402009005441d0500102c800b40c01d1002b20b600200301e866400c2006414002d00190010714002c0c0d402042e560f603070390b0030b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 672595764 1250 672594514 672594521
    0x30d09212414010602070f090b0609040213030f12120e0d05090a180603060b12031c09020612090601120c0b071a130b0705071115040803070302060901 66
    0x203a01550311410003142001400401003851070040c1d015022203010307406210440141040d0351900d903410308960001c910fa54000565104881a1030f00030310a2586402c641d10a90351544510f81d00064280b1101d1014945500076010410803a00000410760762a101c00040040f170741800d54084424000a05206130301500321481c07002055014028101c04120403581c44880c00c5002c0200503000c280e401d166920500c046d0020704d446484014118a0880880c005094030304c402c0b101e0b58908420440c05051090540c005141d141c0c1c0918101900c48228100d8165008190240d1513614002c0400603900c0c0c00c090301030640000c1d131640030382c038114100e28038010041c1c00c800900416941c8003400504402429001da80024445540321b050701c2c6000030024912250344100c030650b60301000610303000d4440384000640907016410564865540a41d654450080090140d021210700c41110b820540c0c1c00e80c101d1407080603254549a80d656149042d90030503142103006070404070501000742400d00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 672597014 1250 672595764 672595799
    0x30302060a06290f0406080108011406011202030408090d030309060e060613020c01110f07120e011e171305014505070b07150614011d030d09 62
    0x402c209090800b40d08400d006118018900200310b180e60240b0307060f050760140d074100141d1883c10f0361581d0b11807001401010090150824542c6042802224118201714160007583d0685925803094410342e284406544018010345400c4801c10103003010362101002c2101550007550300085154452405800f9a0146200c5402c1d9038800b10510000f5600c0700d811058030720b8408001641c403441940850301510000000043c0d8220101d50070300590031100040055130f10401d0f4116508024010540b8018500e182c0c0d5030000b4612580001c0251515180026104690074114120120600c1c00e00c9a0a02180d6102c01c1100400c01001006401d019403400e611180e08800c07822502c034407260314001010058840810340184842c0120741006403480b1700503800c0426542980d4948443e000c0680c0010340443c0e844081c5110060f07800390f90302c200801d541c4c801d9804100701e0a048011a101c82010684171175140f45403c54810315501040580098031481e2504d090503440c184000c0e03040d22885 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 672598264 1250 672597014 672597031
    0x405070b1918030b010b130312110708010509030a03020a020109021e0a090207020f0f0a1220030c0d110102070b0d0606090b160204180b040303060e01090e03120414030301090603030206 81
    0x140c0d02400040c152001045c150303804402d002c0d4076070035a0080505440040d030300142180c0400030880007013640c02003000e202107610808403055036945040340c5080300e0046580180d2a04244030120140f4425001002d004c0b41d075100209414001e500081c0060032041c00012094043c560440b80300d04061241c2401000d929400b14208170b61600841c2942001c080c038a8440e503102d022911103075441207800000341150341b100f61002d40040c901041c1044106004a00d08034800c0600e01e442d00d0005040e4110410240500c1e0f00b007043d80c0e0b00c86440103041000d050650045101c0130924404103005080d01c4440180c3c04030750280b074050b000d40201e4440d000b20340700c0103041020b03620f04400d04540c0752405a040ea40003901030011040d4901d00881074100928500410050206155044c3c1015080e504541040b00d400c1e40e8401210b01100d800c083c2403501900103200803203e09000c1802c10f91f12500840710794200c0100b00c036646046a209030030103c150b6503131348420f0040c035604003c001ea110040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 672599514 1250 672598264 672598307
    0x10c0c021302040b03040f080705150f06040e0d0c080d0213090b030c0d080c01060e1608010f12080f0c030a081e0c04170a0c09230705040501080405070b19 68
    0x42c01982c4d811480020809030071049402a640c0c20000c540d8102e900340e40d00039081d00d40c6c1c1c0c4d44000d20030f6141c0d48144c4140f040e50b0071150125034a40b42034412540d144060f04000c1c070640010560540c1c41002c20b11048d51912000d0104076108500d40c0010452440d0304180540c0090400c1c000d0340c2140d40741e00c48140651f00c01d001111482d00d80340c00d407a400503041079181b9211490f2200c101e0152403d85c0000000c1c1c089a802d0081c41240c0944040c1e01c40506d4403448600d03070b04d814200c40480c18512968451501c2c4126030004a0b00c4040146049107203a0300c1c00c0d25100741942c021703203946e105001020014440c0703c20400c0159880742030088103040516504001c2c140902004528060f0740141011205000c90122001c02d04000b850200b5174440c1e98040c11650314045a0300420007005814452040031100c0482529054000d91140e55162115400c007070900340111580707100100100d81c2482090710200f130500700c110162035403e4002c40341001e0041901e8008040351180d0702d41403500202c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 672600764 1250 672599514 672599519
    0xd030e090c0702151e1b030a0306030b070e010203270d0b1909030f0503152128060b010216080c150c0c01030f1d0c09060d03080105010804080c010c0c02130204 70
    0x5a685d0100980025a18002d03190380642000e404005109106002180b02c00907180b0001c54051704180300701c0b03006540042d010340d42d105041c1c031401c115003042401a00200a07014510ba01200b02e0654a50101c1184030741071611404540311003981d4605543d0411250104201001c0448126140e16295841170203406003645c1e0183c601c100c450210000e000c0003200003440c442800138013100341c0900034413008a013101021104001c1103d0120602079000e5500083e1001034003101d88402090001c0c00c14007540180e03200c0000419030056818110701610f07122207000c0d444510040050140400900b403040802800c00042d1180006600007111040c050060720420207c0e00310003928007030030080f80615209030507000601c1e000d030000c003403105121a600d1f0b200c5c10026145010b0b000a4a03034810b15110602002241c42c80781c5001000140300f80018011948120002c031b401510070782401e41803021040d4003130f0070340b40728110f204000b0b00c103038100c4400d600d40302d20b00004106040b407045242c03e0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 672602014 1250 672600764 672600787
    0x4061b020f0606130e03180a06031404060c0915020d031a090f0a060506040b03010e010b030f07030f0b0402070b0f011707140a03020301020c0a11041a0d030e090c070215 74
    0x800040c400f078400c0b220480b1901002140da0000c903055401d102c1034981d41c49400c0307030b85144510112015405492001c00c0401e40a000f4415103da40040c03103208481650f6541c1e03403902a000d0324030800d041003070156001500c900760105140030074420b034015120b40b0003a500d005049034000101a954a40514042e0700241c684010960b04010900000340302c5540303120120000d4030309584404d40240300064002400800702015506a81c9620318420490340e80b02c4060b40980810fa400c0c004c0c10151034081100740c1e009074419100d08440036400f080800e4018001012604501c60589120900d0010403003102044600c3c94007400030201440c1441c1d40c10114190f442d41c2c0c600414100c040f2203980581c043d511980148001c4d0350080003595181440ba41243e190483c0c2c1d00100e0703607450340264000c0589801c0c001e105e03c0b4070440440348962140c14040041199804105506000401c9507083c02307501d960040c184181c00202d441d40d0341d50020310601c10b5003818a00c41c000e000005214100a41 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 672603264 1250 672602014 672602023
    0xb090609070b030606030a060312020f0c03010501151d091302010e090c04051905060c011e020901050706020f070b01030b0711160e0402061b10060e0601080601031109040504061b020f 80
    0x95001d5680e06e49a0b542e64004000801d415040030b80250030f031035a10740d401540021410107481d0f40e2402d4480c103600382410305003611130a004014802512055100d000c1c0d11541043c0c0c143c0311691540c2d1200490100854900324059610560316509910001c065503000781002e0f203583c201f50b860902074500000121201d0050b40200d40c0710b0700078a06186c003d8001418400051b00c40148120303510040d100c1c2660003007000c2030142200b02d454107841c0600340050310940c0c1c0526010385036540f0704400d0b591544000d5000e10794001c44140b0a0000001080f9803141c030754083e501c81d0700c50300c5090070f01d600b002d07220b005843d4041d00c4940c071a04107003440030021070f000c04c1120300782420b2070215129031000450a008210403c0c00185601d10303804a06940042c0318115070901803800c00107940c036a6110108a48100c490601048560000c81c41c20351003503000c283d0b54030303078191a035003481c0c41100000d0603200190780036590035894680d00d046030a03d0012188490b00180000c0204400c8181140c1d141d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 672604514 1250 672603264 672603271
    0x111912050c030f010510170f04050105060111061906080d020109030e270402030a02060307030c08010504020c0c0f030102041802040311030721080d090308040c081603060f0e0a0b090609070b03 84
    0x1c00c0341c0340c05a11a60b00801c047c119050186910015500e0141403da6041004981c199829828080440c00c00c1d40201040410380c2c4e05140689083d03552011001c82400c15a1440904240d4800c2c000a01729000d004184222032035a0000c1a0080c40c0d050081840c032401c00006d220322040b0400882c410041c511700d896070b10646410320020755550001a040104084010750028000820030500903416408855400000e0700e89503500c0c2d8132041840100d00a000c99104580e200500610f00342c0360942860303464540c010009031400b600d84000c08004101091244000c580205060040201060ba550a00311046d0000c100790b501c0c05106408004810006000e40404040f0300002d016005046035150f40740302c00c1c14000c0000c0c903e802000400c04550035070714069144404283d444000c02c0404112111141928109003140c89050040c01101c140c0d945a6944168a0316080024808205018041c81400d01e05180548160381401c00007040002d942d0071046051051007051070030341c0e42 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 672605764 1250 672604514 672604519
    0x1303060506031509030c0106060c0201051206220209090901020909220b010308041815061815020708160501050d1e0e01020a0e0108040b0109111912050c030f0105 71
    0x1000e07101c12021904000c43c840d80000c070403c1e09010000340020010040200f22111070082110302d0360b40324110740550400000900141041101c540010460040140c000500070140340300d00360b41d429140e00c66210208860300480e00811840b41c5444d0240513240e20051540003540303400c0e50b0b10000381c81800700600c0c1d000e22043c40c0300031245004401e10401896984088440742c20350f124100400e04d9040b5103d003450070304401c401c801c40071a41c0d000703a142090403804030034841401c001099a11034261410a641d4400c104c10008005401811241c4c00380010b40140110505140d801c504000c060032001c040084000d800f04010790b40802240c1085090000c0050301100c0c80d02c8e8480d054504c40b030340c1c07075030503041c40e40540340c0c0760042d4000c3c25031a42c07540ba04414001204015150943c040301c01409002132940104020b50207030f00a2006ca4414800701c600d0005072400c0b0f0300d403001d40500035200240760420310460304c8200f0320802d03401c0780382280203d086140040b0b0120160005004290 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 672607014 1250 672605764 672605771
    0x4290c07020904050337080124120905100f140402090703150f0807080a0309090b0607060f05010608130302030301090f15030804150e030604170409090f050706210e070e07050c06060105130306 84
    0x569114000220351038ae8410030921441d0324508040e9a0ba10070502002c003043d150101800c25901c5a01c1229035100162012546603520394013000b0721403100600b42401d00d510380c1d4000310365030701010006029110894066049038248a0341518204594002651550000a250010941050000c41294103440d804a0700d0071040c4046450b6009120004000508001ca90780302c00700306401842c185c5800f03940d1301026a80c0ca0503103400d0a545001c02a0158008000500402c8590f401007440440360071008121003025003603462180d292035009584001d800b00d8107100301d11101e8440d01490000d442c24201c2700150f440003d8450b04040c100038141700e150300c54088200700081c152001454640b0382000038410a003810f000d4030301d01910407940ca025032000070403894091203606a04400601090081c0e5000c020028018000d84079602032900c1070950018014980700c909a02c140d130503a841503295820300070041e2800d44046c1810341800020700c12050083c90300c2050034200c0e80c104c0c5011 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 672608264 1250 672607014 672607079
    0xd06030f0c151e2d0e0402160308060f060a0c030807030912110f0607030c030e0106080703031d061801030e120d0908090904290c070209040503370801 66
    0x16159440540ba8018005084000c0201141e02c8640200f058007050344420104d945c015041008134412160400c014080e0f03103640c600030903c0f9000340da50103000a000c0180400c0200001101d54011341e900400250304281300c0d2040551200c0341a03040f820500b81440440d0300c07556003130400503103d104d150402103000c540b007585002c1002204c240e170318003505958503800c1240005000c2c08840c010f65021078209401c80b000c501051003480200e030560b1025000c03160440d907007100c481d00494000c284040104070900550b5480e87d0013464001211648c12424042800002d010781b0b1100d200d030f08035a0840c42c207040812101c1c8045960000085a00286490705440c040700f1314084c042c100c0d90040c0c814010031041106104100a4a05002c91503082000d94956400d100301b4007140c0142c14a2000c1c00b007100141031020242e508944110196800c000341d41c3d40c2034841780c2e5003840119040710f41290140d103004054a00341c41c148454940340301550f0409001c058880412000c0720007031000e00264 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 672609514 1250 672608264 672608267
    0x70f0f1a090f030a063308060f0403090801020a1709010e120c0a051203060108010e010b040b28030f1b14180d080a021203040210030902060d06030f0c151e 68
    0x9820b0203901440c200120744c0161008026039000f0286c003108110f544500128100203000064211405000144115034598907100a110f501034011028071040e5000402e10480030700144c6594485030b40d541119400039400e0b51480c2c14060220611070f407610400144e41c007804079481d0743c1c000480000d00d903106070800505180403443c19010b0b005004400f400c800c0001c440c40250f0180c81e0907030361094641d0b00c41d42084480704080c402d444c580da0381004100540303800c0070701510010121210b000c10303911013100e41c101080c1180c240000025910341c4401e13101083c61041c0081900800d940305440141040c010f44990b0300e203c1c52420280001c9205810314140380706520260710050000b0403650094640240641c200c8001d000150064011101c40c501d0001c0075a4800c6800030074400610300e541030309400400c1d864006071f82003e801c20512211a2040c020200114403e40340620b44c2100d03800d01c4646c500b81508506221005a040b0701e841513481210100301d800c03840c00c405511035803034a0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 672610764 1250 672609514 672609523
    0xe1005120714040e0f09030405030a12030f020a0e01141606050a0612050f01061211040e0f06090d020c040b0904080c0106090c0e0f0f031b12070f0f1a090f03 69
    0x4800c5080070010380807070843c03000c11806000d121178400c980300503240c10603044d450b4059805019051f0303104610805c045a20b00d400c0b000010080c0c10001403a103e0082800f00340d074030441391000400e0022480c103155592000b41c101c0c0a0050044041c20860b42001c00080400c03810300c00342c4140d4907103003c903000602d00d42c8440d004106007413080c06000b5662500302d807a0141088444407552070030400188081d00c851200100c564400388000c80b0880d04c1c4100002030030240004c200710300c84c5510921105c0010030605005e03800f889e005154112034810000e02d844a8104814056802c15011446540715814a9500264054401d03500d40b0b00b4202440c1c0141000e0340040c0c000f83c213201e000c142c00c94110780c0d05451023901356040c1c0624020f940500c45e048a8820145400d82d010603217407415a240c0c0c03261410100c2c0000c01b101c0e035100405644c14503115003504003a4840103900003c100c440400301c00c40c40105602003500b418401c0700030150b003c501880700311a0103074101104800d00c65a0611 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 672612014 1250 672610764 672610787
    0x230f040803190b0910030201120207080304021c0b1f1d060f013c0206090c130605031002040806060a18050a06030b180106050102010b030c24030a0c0e10051207 70
    0xc00c00300041c42d0050036006000c0343c506c4181c0c0441c0c042081e1641030507a900888d01003980102101e491615141d081c8511107c011b0084c40340c00103901a454005000003254034042c24499860f4a0400300b0505240551034031a4010034a020642e00505200d05080507038030344c000022234048015504050058480307003c10582e0a10644948508013006090303003803002d00a400b04035802c01040c030012030030f81e51b484c000d4842400c0d41d8054140c281c0f56242c24001c00d00104100c050110f5140c1d6100042450040740440660040d03401003005d000d503007410490030b5401002203910103851403502071000c081c0c09050008078112600c500003c0c2c800744480e0405c40066038004120405860500fa112a40e000401031100b143c1d402d00100090640c8140510321461500a010b0840814a241001a80d00e45103040c10070f20210f00046110030501900514818080300002260f0000c5a8000801d0641d0804016105082d42d64002c1c05844e8441e05aa088e4802240601144c1c1c41e0031a040d1801d09841 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 672613264 1250 672612014 672612019
    0x31d0105070507060f0f080c03040b0903040504060b070501050a06030b070c030306270c030c17180f0d1403012301030b0406090609110c0c0112020c01230f040803190b 73
    0x39800000d01c543d02543c106141d6895591300b1000c0d90b00b88601f26000758041d203605281940510114000c1280f8030307222600b0402107000c0341e00d41039442010070140c0d003503540031580088000c030b0038406219007800b4103079104141c3c40041000c0d905503a1001004a406420002001050b154800400d07001c3e500c00405400618010f640083c01001d642c041006c160098410460800c0c02c1d06080b140607010724101e601e00c0b900c0c0d0f6a4460500e030f50341c2e1045030005142203000314910766507400b49107052041c0d2465500c520060040c0500c0060081c0c13820348540c04040041e107081004211003a4207500d42074040500514440702a071718000103c002d06101c03511980c0c00740c6403240001c1e80350b000c0e030300c005c00701e0301c2e0b10f0024400c42110b0440d06405004000400b0501d400180d51074200e588580000002c0000940c00181004510789615007112a4501c01d0030161883c010720980c21402040443d611803994a8903400383c2c5055610b81d00d66010160695889150307140c00c3c1501100581c00201402c0b002 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 672614514 1250 672613264 672613273
    0x2031f060905040b04050f010e071202040b10090806070219020607111504061715060309190510112713051e06011b02060f04090212070f0507031d01050705 68
    0x2c2e042c04202e800c804e5904a0b02c500c2030000d1162405010f0254884000c1a08098207074145448404bd4450361140c00480c1e01c2642e50160000710703900c191110380e0304d0395165a480c0f030b49802c0c51101460705c040545810155030051104100c10022507003000c41081c0e0689a55455002c50300c0c0ca441c0d0b843d02440da17541d1044980c0704100036180014050822900c0c40c0c0e80e106190200310000001703441e01920280c000101c41344441901e401c00e28011038000b43d103141103903500740c07030101480e510403801e4004982507080748950b0103101c400d501603260040c030b0080542c0e1414079201003c5c0040c0113006000251415541d030800b43d180e650742c2400700c071601c0016040c1720b01e05d441d01c81114000c02d0904e08000c03003810707040450890752082600b040100548085040c41c0003045d020041c3c9034002c090f003d0608541000080b40300c40031030000c0c05001902d498980200e0400300809046680208590000c0000601c06040400d601500f409048051550000320103449240101c2d200c0c0b240701c1c0050002d108 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 672615764 1250 672614514 672614521
    0x8030732190507052b1a0a0603060507080f0412052203120207030c090f02040312030f06051203090105070501020909101a040608190e160504140402031f060905 70
    0xd9001020507903501c41e80603124016110002c00913200000d42802c14030f103580e048661150600780d1003410180e4004c2007203504602980800050380e401c00c4900301003140c0c41c0d11082042003154010b50303402c02d03100d003462080c5280100103808c0382c120042000d4031001107407c80c41c000a0051040300c0f0107001e40342c290619004c40c0d080e080303c1c0113190b00c0201c4011601506070000729202282803010350782e00040204010303182c521014050400940840481c99003000000002013410000340001c21040e1400700342e0320302090070541200e2140c6d011902a080c4a04124202d407030110407617185c01e00c02d0800301d458444d1400c2c07090080c0141441c1640008200092200300c1600c2e00c55082100c00c1350b040c1b14004039503c4080e91690146225820100381c1103008102030070380c00c0150340c440000c03820b00003a201d98a291801d1500c0c1c41004052911440044148a6030030031f40244855800030105d10407950401394007180c1e541c41e10614081070100380d54084050500c498004500400c0001c1c803d112509 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 672617014 1250 672615764 672615793
    0x7210309051b010804080d23090606030604050319030603020409080408070603020c0c1018180c05041d060d0611030f06040b01090e071709010203090708030732 70
    0x15000e8819903152159501e8003100144888140c841c112060750b0700c005a0b1259544c10800d508030540d20001e1a0300c03000141a0905000c560b402e007000092801c1403503050005480c0d05112018141500030340050041101284000044418425191400110901070318400b10000e180c40d800c003c1d8081c2c1040551001d101c1d5001c09002a20820000c0d900e078280d9400d42542244074280712941d81360843d841c20665880d054020b00000c422604040c0300a51950030fa60320100e000e40c0080b4454a008c076540b002c04203a034850000504103e04049260a0070140180b80c1f450300c105141c0030101140c4005242500c1d4030104210003a80300c58103000c2300303440e414030310741a4004a811900c2404440002002c138075142c00f900501800c103848070080981802c178001c070441c200600b0b0b4014411105030150109108942130b91283c0d05c20000103880707080085201e03080200035130001c45903510610852010a50964800c14802030409444100c00b420080c0040251014506580f25004980780d00c000324 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 672618264 1250 672617014 672617021
    0x613080307050903030426030304031b03050c011404060c02070503070b0d0b060c0a06050618060103050405190c05120114010e070c0c140f0603010602100203061801030309090e1908072103 82
    0x5400c90541000c1f500d6100d405981c07800304850107800150355404920b042011443e203081d2240c02440c00c80c3c40d1481c017101d07007400c2d03501c1103840c807102107006410482070100c075200d41c140300c06c400e00c0549406485d00303000960b0348220b401030360303046000054242602c0d00b1075800480a10805407000382ca8540110120303403184081d541c241c800f075040600003002854488040401c0d503441c00602c10f1582ca840c0300440c001c1800a00480e5203208409002d481e0b94044403404100c1391056450342146410312060013020100c041d1074400f1380e8100303608641c00d0012008054151100708003411401d0f5074442c82210703c0e0a2850300604041d50300d02010888512a00921b45039800596030803002030054000c0c0251807109103e02c80042c0c1247c2004802c9007166001182c00010080250107941c04d0f0f540b41000482081c2c0c022804102200700400c403041d583e01030441e0307070407014002d82036034800040890480420349100810043c8001465000c10a0714042140e008004407040e500e49003003658044c004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 672619514 1250 672618264 672618299
    0x1c050f0607140406120e120c16080a0f02010f050d11042301020c0f01090510020102120901051e040201030906111309180305130b030405011b0206130803070509030304 73
    0x100e500300102035200c80c1104442c1140c5503030f0340e0400081c2c85c2d00d4148001344100015442e941c080e40c1407500301000c0c402c010b0407140c0074040142444036916424601d003d00d080d8400d4582e070f00401070090200e517282c00380c0d2251640a00f859240040090b100300c400c4c1c4600307102030b4149850a420716010303202000141c002c0c2d60034a1481100045030741c221544000600522500580c444903002c13a0714103048040000c800011b041c40103100d6100d10000f500410140d5444005030744c0424000e018484248046400c210b03000002c0003141811003000c0304c880350902d02008110101000b080859200390b210241c06600a081000211480d20851005074082074420f418035541240104800602d403082041c45981540201420480c60743e0642c3c80350010001c10081c1150b10900141354607070803004500c00c40c030035400042c0b4285018a68041d0707244d0454103000b1135205504109200b1040791030341d9542508101e5458590f56510012155403140540c03098050201040006401d61400b040071031 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 672620764 1250 672619514 672619517
    0x70e0a05040201030c0e1003022a0a230c0120060411010908160e060a08070b072904020d051e0f060c130b18060301140a0504020f07021c050f0607 64
    0x5401080c601160020900c10f000347e0300c0b00c1c079044000400d07406a40209008203420030041d007a07110700851800c24240448030040301d60410502c0800704034001d0b11106601480b260010410f8001801c625a50a08000c07900d05114042182d00040300e54254400ca1400400302111440e00d042c1c41c1c11401c0b01b10594025000c510302e41c1d80441c00072008034032000c1c04500c17503480e94102450440300d10304464024244a41065126101145000b000d024140140c00407c10f1103595001518010341c14200500c00d00c2c054003918040300c40902d10411240d41c00680403214176010004908010b402c00c2452030440c04208c4c0c0100030320721200d2011131000c10950f803c00035508103030340c1d0340d408000740d12802d4845650005480400e00480200c2000742810701d5540780351003001d0310b004003c00c040d540207800c610392030201c2841b0000c01d031410340d400c00c02078103003501d00354102107410140d04c01c83e01a81000900c504008080e003e00111901c54640b19260030000300e80a5800102900e51200000e8800c0c40 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 672622014 1250 672620764 672620771
    0xe01050f03191b051210121b060c0804050f040609050106201b150f1308010e0d09091a0a06030203061201050403140a0e0a0306060609091103010b070203070e0a0504020103 75
    0x1104010b481410f15049040c40c0ca07914980303002e5100104103103e000340340d400960403081c00072500207426401c41d00c01610449008040c869a906003c921401c030750b01c80e00810800d009101d00003007502059070120781080c0c0d841c0c5242d84490000401424458100345603140c540303c00003c0d9140e002880d00f051501c032840c516115402c507801580c0b07401452094901035210510000064141003942c4005080d8006e560780c00c0a20b032840a25041e84900bd903442503501035442401030240c28852400a0031143c3c0040102c400c0180000e04108164400c0103605952060185415005034115080b4001c004007a0660580c441801800940065800d24014620300e505a010300405120f8580556016121403110100d03564602840d5401040040100728000c02d81200e00d441e6048103074080d612600340403400b1820f0940041040700c0a41c4899259828149201c40044d02c00040324155000d01501a54035092400400d1802d4030700d5001d040c8200051080001034804c6d6070082d80154805d13070341030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 672623264 1250 672622014 672622031
    0x40e1510120804061d03100c09090b0306060d030c08031006120912030203070e04020301030b1803040e040b1005091003120e1521130b060109050105090f03010b10020a1e0507060e01050f0319 83
    0x4ac0704449102c00041c0d01540f0400100741e1a15290310710080c0948645850b80066056540311640c580040e60800c08204002d00d00b4040d05402ca89400101c50310041c2c100070554050b00d5444040c00c8180108080c90380c00000308001a125866009044001410956480d60341b40703840b0008420407240400490300760303061800348000104c21038003241c844c900d4040c4903885070b0b01c47c81214100502a0901101c08031000a41034031500c840d644070340f110150302d5041500e181403030300d1200f081c2104541005442550300e05a541c0b16140300c0030100340c05817070313903141e040006004940d0711480e4040c41c0290019403c000001310030a09940c102445011002c0306900e8400c0150b03080704450090901003501801420b1480c1844601000003510080c000314641c0c44d40d1002c51507480340303818000c0c0143c100e10309007418030001594001c080e180796690b0400078581502d80c0c0b034842d44a40280000c00c80c10840d2207629038401e0f0141e40e101002082410fa4034184207654880d07001600402407006814a40e00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 672624514 1250 672623264 672623279
    0xf130606120e0d050d0507051b0c030c060c1509150c130909020a030201050313150e1603030e1504051c02040c080103150902040e1510120804061d03100c09 68
    0x254810f4554654604003240d19540c40050400245420208030040c800d41415014510a8240090030507000c1c200e007815000505007030444000c10b05028880400c40d608075581d000030b003d2007240790340300042d0480d110510345070308100d90028801714420212084c40541040380c1c000303000c400c040554034410555251089c5040c2e4880c40e402a50050190300d0130405940200021940049460711131038802c1600d41c1e580c032070005100c0468001c160343c3e0409252008080003224070084400d40e550b040c4502d10b59004003580810006603000b11512440c91808019141c10340307010b03000050414442c580756807a0402c0c85082194140d121f42d0614003824941405480b0b002d050700e40180c1010a00c2c800d044415001c0c1174804012030300700b0364400140388030f00003d01c0384601c40c140200d0316111508180c1c81130400e5a45507040348a00c230001014100005441c00211030459116060003200751401408558010400640058240c09480e00031480c06206034841d0302c130520340303840c1ca01402d030700c5890 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 672625764 1250 672624514 672624523
    0x100f120221010909050d03180f031d0603061c08040305070e0709060305070c0602160204060b040e011a0a030506180901050703060b091c050c150304030311070f020f130606120e 77
    0xd002c4c116070401c110301b540d518401c2c0c001c24441006841c0000b43c4014580d00e05402c40103020003a000203103000e02100e4034400700c4c0b02c0d0329500320702110198250704100c07000400042d40b820304411501e81c10019001000800310699000355080010b403885d0308c0da940c40ba4030001c03004448000c00a105004c001c1020f174080e10445001e03d43e96a00d00c044016a17580c0c140095000040f103010115804103950010b940e4ad00a8034068032051003040e0711940b07400c5402d6080350060300000702c0c621a070894200f0000d910320603181e042c9001e26022849032a503c0c0420781c5030101e06a00e01d030002402e0208180040c05420182c0142219076042001c0baa0b03540741004140100300b030541d80700b908440000e20f10780b0b40741a00c0d12101d004d48282d8a00680b1200010390ba43d69280002c0ca06000100400c4107040c0c043c454003158820094909143c2015030740d0f00402044d012800a100d003513440b6400c1100e071a1704c807482004034600c0b1800c0203a03541368203000d0300d40300c0680b101101c043c0c1483c01041c0c03075040208 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 672627014 1250 672625764 672625781
    0xf01080a02011107090608030d15081b040f020304060b0f04051b0c03040909030207140303090d0605091e030d0515010917010e070f1404050105100f1202210109 70
    0x1006401001001d900449540b407200074802101e02c14101d000c40e02c0c454610a440080c44e40c40000c51b41c411208208400b44c900c2e545484090741c1c146481008140c40c04150441010b407881e03030b008032030001c0b00c000a000b403420603041c201c2d852000c420003040102a40c42480001ea0440b98480e12551724030402043d1034044030010f9103080452003032100c01401c1070180c00c280f03824509070703401c1030303116849102114a00a01900180d0069900700540e070201d104180d038000b401d4015600c0c080e148004a032403000c04d07800080409036104009504030000307000a24080682c002e2031581c105521500640d0381d0401d40400038524500703400b01d84884440c0901000051040c0c5824102e54a4070b42840d912616500036510f02d9503e45000c400d82e100d00b0300c40a409022004014030680f030500c2880880e00f1483c0c1d01d9180140e01d42001403080755508000b02d40e40e04914640030115111a0a0884560000c100040c0c2c103940040707039516040c01c2da107003001c05480b5090314070201603903103816100c19500701a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 672628264 1250 672627014 672627029
    0x604090c0b09040e010c05071a0705030c1c0504030503191404080c1203010f0f150e0f030307080c0a1101020d0c200306040b01052701090902150d06050103050f01 71
    0x2010070424095a90080e0450100c01000003c03904c110b1426a402d40f148104e00e070000a2001525008100120100c2e1444111203040d80b40540f80000380900184005040050380410201d154030902d0148041106011381c819028495401e2600d000740441c0c00689004456000b20304c4070f16180780c5540305844c1142e0b500c03a4501d070180c640340c88a01241d4002e034420140740c0541102501c941c4c064000541c020310140c1e8414012500d0400b0220202c1c0141c1c00400e02103814020300f0140c1640146601a045c00448882c01060844400241713140b10b00c0200505817080400c0864841c0c3d00844d1f040d02c0301d402179011b62401001c4600480c0c03a035000310075000100340300910781c0010941701d0701c0d0103800d42c80342e08070a0800341e00d4400003803506800316811995940703200014015800c20f041d1030003200500701181180c1c01d00d1700351a031b00304150500941040580e0388158405650b035008004c03590108034050310343d40b02e00c2d031032400300685158055540401e00f4000400e6030314080d007190b039040350f011 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 672629514 1250 672628264 672628283
    0x3060b0d08070f052d07060e2409030a030507060e0601050603011502070302091f0b0a050406050c07050402040f06030b0105090a060f1101050907031a0106090e090f0a1505060409 78
    0x129594155503001021068a0902ca0170a418842210180a2410b500d00101c0310a860501c03100b601c0b40f8000254200c0c004000070111000030075180c0b545030550190721036824410910302c59104100d43d006203806c1561500c6840950014540c0000c024020705000304010312000800300745140d0307101c41c00c0c440c0607000002080100b202c202c000713407104001d1042d071044e0340c2c220b5602d40000700072010581c1c80003036050071000c1840740c000321a11468001d0986141d1a42404100c8001a203140103d1240809010b0001400078000070300b48050300103464020000c40d119070720f82c403040c0203403180b600840707020a15126500880b90300a40c2600d2001000401001182c1d0520904441e42050441c0e0742c402e200c028188400e01040a01901d8420200040280a1285103051405001202c03908203045554204018400760741d2000c0031000382d944c10310b4581030301e84409429a18000c8100003145170390054140d01800c1000c02e01c0c41504c0c1d0180840280010349547c0b0811085030410100104507020 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 672630764 1250 672629514 672629527
    0x203030403120e030d0b09090607211d06040515040c090903051c020309010b0105070b0601030519090302070f060203120a1a030a0b040b160906050d0603050d0903060b0d08 75
    0x1c51401c24088206000b8040b4090f10802d20a6181da08001d06201d00c0c0340c0c903030520500c141402071405074003150500003081d80d400c04401c007404643c41c0242c1501c1c0c80c2449560208242103e4001d00a140348a00c1802014070502c10842e0f2511000c0c1c2d4215658003c0300580390302d00b66690072990196402407000321300c01c0d1801e400d0f8401040d9140f0101c0a0080a0000d41d024040075407400804d2070701c4110241c0c1c0c030f1034010406401c4404540c41d039414000f0074001040400d100d01e043c1c5074000e1007800c00241c40d896120368240318540e00d0b0040e03241ca6092022180405034041401021a40c12081c0880001c0d155142680c590091140d01d07102c41324000001054081e482d00081c04000ca004030b11000004d404000c80d04041590409946490310001440200690410707942c2c3e214488000040e55140c444100904c0040503102d098201f18002c0307100c800c2030390181d110000440e0300c042100c80d45e095510000d00748050a1006942c0a86090000a42414040940c032401d65110007240c1c82c040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 672632014 1250 672630764 672630767
    0x11b090504050711190308010503030a050f0c0a02130212060a03050307060506010e030f010203160c0c09050c090d0f03091a120a2310050f010f0e04090c060c060f020a0203030403 78
    0x800200f1400030400c950707502481400c003d106000c1040c1d9032446044c02c0c1039060034064000c84045c0e004600a0340104030744201035a001083e18044403048030901c0d560700301c0500403481d102507000e000e548489082400c1c1781500969008108800304849400456901e200030081200b88611000c0d04070b800030068400003ca55501c65a0702100506000f0501384020012920700284114180c081e603600000340102e035840140c0040112105141180740300e04a559924480c4c01325104070226242c842020502c00c1c4050070650b0b0315410b0250038800002c4e0182890709010913812001e5001c5090702501060689400020103c0d03141d07078044141c41c0c50115040070850030001000c00924546d00c8445c00026010b61400c50001003116184000d01d007002d41c0440030548030359210364490b1841c220a1400c90f40c00c0f100703062050002d0f080203118004e80ec0c02180141546242c002c140c02e2080c4400703da611f400030410450b030b9001340402c2040c05440300c0410101d1040081d100e001d81c1c014800a00006d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 672633264 1250 672632014 672632021
    0x61503020904061e0e0109020405030d0c051005100e1b0306010c0305040503010e1f020903280f0308011d040b01030f080724290906040b12030c011b090504 68
    0x40300070b880081d2440d6200c100c1441611038a05007048030403003240410004610809032800760030212411403405240c0f80010741e48920581800382404004542902440401d100840590614610500c0289442c49040b8a10303542e6001e14080e00420742d000c184024103e0107148101c0b11090402e80ca10f40741e00005484940c00c98804038100001044049080e4500303001d0150504130303d00040080200b000c4003081013070080324041d80c00510510065006a138000f4a07017100160204480310f070003034010344c81d102c18449850702812141a040340070082581c0502e0043c1240c0c1c0807401031408a0b411a606c6c03c20309010341d809444400d982e80103001291207030260400581c4038828a528040d1a9551440e00d0381d105089004003583c0c1418400f0b2044e501d001c0d200d0b050602c500b4184403881c0744a460010503080c0c1e45a640200c44070b10005e0406c0d11103500665810000429088948283d0780007260741e6806001880c2855082c80c1c41000400e82034400c3d40c1203040d564407100a07050600341031000a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 672634514 1250 672633264 672633277
    0x8060402150d181a0c0a02060118090f1208010b090303030f0601021f1b090e131e0803060f0f0102030301060302070602120711011d0a0215041e0f05030106150302 71
    0x50694407070301d0070311a41035856450403051040180d0000c13840c00d144003000d0031900924100041e84101700442c44161301058440c15248060f019042c036640010141006000c4402c0c000c0000c3e1840ca0340c1c50602103031601d0084481420b80e1000031580e2030b03520b00380741c0340a84604a0340652041c40440c06140d0140302c01e0364401ca040c412520300c00440c0300300c45901024107450310303c1d2550b81c002c1070b400c4c20044203078118144c0e02070801c200c8052801c42030000b258002000741c500e40801c0d034020404c01c010070281080c41c0ca100852600070001d641403800e4164415a8001d03ca80c000e03001d18000c03410642070809510005030003441c11a0b107400000d4000c0e520540085034a29802c001240c41c2c4800075841c0c90140d0801c0d0b8903050b035003030584441421603040e074a80ca6102141c1d55010102e4940c001580404554180e600305036107400c11011241501881d04134070440181d0b411003007a40f40310040340d4422603922404886000d0f1b130790424103080700c1050040c10819100c22880b540801d00a0f001000c8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 672635764 1250 672634514 672634537
    0x4050f120a030b0427140303040c06081b0c030a080a060608040f0305070210050a020c040608060c070507080f0129010804021203070b1f06030e061605040801020a0203090a0806040215 80
    0x400300441881c1031021802a01161400e01c1714070502c0e4144044280340f0841c5281c410015441c0d42010348540c4001110742c40360004002190002030641c1d1941c455030818041190b40d502d4544036043d500c039840390820740078100020704c00000210110b0f40390243c6400c13031b40c843d29000010b85079500c0740b6400d01c003065002c0d41404010131023680142c403280b4071b601c180c8210350b0300c19407580302510b0000d05002140d40036610483c248041400306540118243e50040303040126140d0301d8260b40381140c01c0c91000e40c040c01950050348020100d4020641010850701d1020300031000003008207070040044000100d610740007903050310001d00182400840441c0301d1090504803410321607961360300420780c80704803000f8428803002140c194100f900b0901c40e00262005060a0029400f1280f0703055940000038000419000135040450720380c0c0c014800c031070207000b09070005e550350708806034043d549074044c140090241607240c80010301000701142c0035001390350042801c001802481100611a00300c00420007 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 672637014 1250 672635764 672635771
    0x1d0c0a24020a140601031e11040e0c03070e040308010b180409030c02030a0c1806120f08040e0117060114030607030e0127151b030213120b04050f120a030b04 69
    0x1c04103c0340010320194500c0c040040401d90704521b80f4040360390346240d5450050845004500010380300c0c070341e1107140d00c40541c0c0c0000e108126800b0207144c00c040078030440e058010f400010039100c40c80300c02144142c2c060b0311000341d40d0340d07655a03002c49031140b2030818410081d100c039120414501758111140c00c500a02c0c02d855000056000a400c000c81d5040c00c1b2410100f24104005100380c828441500c0ea424400410a280c81d01d10f01850851050070700400300d07042c40c1912000c1108001c19034014010325485240a0368540100489400203c0c0034110380344101000010a1102d00c3e44400d502c00e0007902410250300c6030300703094002d421081280340301e554031520342a0103001c0c0b0703401c071007e007800e400c1c42c10b102c201c0d550034a19080d080400309807806505064105c418035065900c2d60070700711a18600165a8815601083c03803809041c2c020103614001000b95500f40003150043d00d000c0c81c0034100ba40c4d800b00004600c0c40d03540021002540a0400a01840007260b0107070f8002140d02c007001d403020 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 672638264 1250 672637014 672637033
    0x10050703050d0c050f0d140709080307020112090503040608091002210a06080607210209061b12030403080601020f0a0c0504150906150f05090901170c03011d0c0a2402 73
    0x5d01540e00900c101c4004240d4560242039189500420f0640180d09400c00c203046da070604c0125030f1213100c1c448020303060055180314618074071078680c014101c013a000010707a920350703032501c0b0014000802554081428492150b03002c180011318400c032804500701103500c6206454084111b001d039140103111a110a035500400501d0140900c511031061807541c0d1120381e20f150101180034004a51b04040484520500c182200d50311103c00f25014810f2820161103d00c0d41501800d00e0000d0b08410f00720680300100c140400c168000c46a140140d200f44c00b50740014005a118030385c0c80c10603503000382c0412a040420485030801e42c0c440100f8038450301c40000f1840d10381c04e000081d00c1459122854209000c03e242c403a2990201150000010a103466480e2880780400946960010b015a061016000280004410081041c00c451020140007409140c4c2e51880c0d0610081003000351101d1400343e2910010306140c51b4401e0740540f0810300c41c2c03c0d102919030b10b05813070011048140c1d2066100f1080d00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 672639514 1250 672638264 672638287
    0x203310506011410030504050c190f08030406032708090d24141501030f0912080a05010801020a0c0816050a0b0103060f0528151410050703050d0c05 65
    0x464040c003035201040a805404034280201c2941c540b2161301090f15100074440090000b090501c84542c00b01c40030003540013940500318138010399078000540050b00d01d600207211400440504110384141d2020808011798001250800c2c41c0500588110f180399020440000d80500181040100c040c2010311810b8490796519405030080010613120b003900314404028503414000d25040d41c00805448401f410701d0745250b08d10445c024803d9040c55141c6c100d42103058100e038041d010080e0000000c5060201010000e003003807400f91f42d0968124184030011803100c00500031500c1c01d90300c1e5aa58060080300780c4a04d4916009041d012804480050612021071010403142d04a03500171011171005501d585010011220355881142c0d29a0500ac1080b03241c003961301650210803c03524445070922078110241000301507229402245202600e1b0105100705004868980b41c041a07810400c039000d0705030f050740d0300d0040b60340080000b00b04200309041c00d000c035017011031b60020606140e82403a00c0002c6 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 672640764 1250 672639514 672639523
    0x303060512060103060f0b01020a0b0c0f03010e10090b0105071506080106080313080a02130c110607050c0c031b130612060c0f0f1d210a030f0302033105 67
    0x30903041e29030200c030051060015034482c184550380503540c10010400201b0021f500c550b406900a401c0840e0f01c40025094100f07401114200c0c1c0070441440d40da5030311900a03080701e107000d9502800701d2401100200701e9811310311603910301e980141c540a0801510ba56240c1d188401c90604d128915259480018451360900440300039101703480285898101401c0e5130500700c0715545c0013904581c8103903450b40140e00e500c0e0360a00e07100d032100004681c0c440c02c07034015626181c103070b0b10300c100e80c2c07051404020791158000060450310103400d06540f603000711002015640c200d070180d01c44280c03000c407503204824602141c0740045610900c0d004144599101d002a940a40d80f120661303c1c50307102c000c1c5961140d803103019000400d10500385290054500c0c0801044002c90000303500301e405115165001958445d0410030b18003040800404c11100c01c85003181d207030159440e045000c01c0008046080e0b841c040d0081e41e01c00c00f080100740c0380c0940920b45400302e40800c0318404102542c50050171010034420722 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 672642014 1250 672640764 672640789
    0x2090d170a1112040302090618070e19181d01150e011211100c05030d0606020f07060c031818090c05060901051611060705070807090204150c03030605 66
    0x600a40d11035901401c00781818201c40c0509065030803880452803000310480540d01603d4050307810701d03103990b5440017150001c0c0d54007500702098a000010404c0e801d600200542285a05544005001c14596104e62034041030f0300860700140c40c0c4880b0b82d101180e00e035018134180300805400c10942c528400a4600711541c040302d500300384400d10400e10000c0c14281c0400e0040c01003240e100d900f1552501e5042c2c1d0003880c2c22015110b0503a8000360740d20640300381d608900964000f03066039607075141d400d03610008103464880e20340540603404500d0085000804c911044030380701e4444a0074000386075003c80307642c2c03254007100116900420003c01c001c108a92480a4090880780011356110742c0e00b044500b010140e40402d100d400304100079103859a200090314000307500c09d042d01801510506d45490351040c454a01d540084d4081004070a201000605404a40c051025619180e0303d500e00c000c140c1c40307180100c0b002054140c040b511117a200e101041010740c003e24001035000d44400004a2003002507 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 672643264 1250 672642014 672642053
    0x10221010f0b0c0a0b09010b03071806090b01050706090312050c0d150f05120a08030f04061404230109060606030b030105180a021c061b0f09060503060402090d 70
    0x5401405000c50314001c24000d44501c1d05020b003070850803000f890b0758025002d4003c1070480310b03d02203241041e00b50484007003450020161516680c0300c4152014602150003140d0240307091203000960b841030340c46410f0350307010103960300c0b4900405600c0d2400a02a0034600301d041004417004c603925401c0c1ca115450242448280843d6034000c103100940a440c0c02441c90311701d80020710820840051b65180150031a401581c0a010400300c1c011340508018441c1d4025000202c0042085444a00c54101c24416031240d901082440004ad1501d0000c0c45c080310003c00a40030303803201e60400c02846007105051465500041024560707580d440083c1c0300e030f0360300150209844100e40440d0b0b25080c010164860714802e5043e284c1e000403082e281d42d5006902c4083e02171000202500c1ca00340c540d1307945040c2c2e03503048035061082c5500412880100508240003c00085a2900004445118190f44012180560703038035821034841300100030096100d510705603400704c2d401e03800d040081c1d03198490420034402d9 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 672644514 1250 672643264 672643327
    0x10303050c100501060818070902040b07120c0b060112150e07030606140f0f040b0f0a0815010207140607060f060608060303070c090906110315040c021504080703020102 74
    0x75841c8040c5408400100103800074108801809120f0340400050b03070003804058403500300d40c0040c2d0818204403141e000401c102e8000640481d4100c1076038000d0224500c5095038240c0c4100320038007194154501c2100804003100880802c485621600d0b003014903002d901c1002480402c000000c070004806640300d6101078481504000a1a816124200090141d41080b000520040c01518600c0c230400d440d21114240115565181080c0d50081d075001d480d0381103134203550324550107801d071040d01300781c00c0c41c0c4c0050070502c002139400a45540c4820901e006800501d849802c100840040700030b541c000302c3d0040010300a40001c03400500990203682c141c03040000e121414940002d0021000414050181e8401c100304400907006030350400813141602c000050313213281407501360003400005030050560076020007030168078642c04c50714440e02042158200444c201c001426612210440d40020042050900240101c0c02c804010691755210b4400145096003034a046554aa840100784241501 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 672645764 1250 672644514 672644527
    0xc021c032c0105090904081b1501060c03080a11190e0f0a031a0c040911030907060e060d1109060403050d08011208090f01020f0601060309150b150a0e040501030305 72
    0x2802940588424018141840740c555210010b0014807488074042e01405455001600b40041c04082d6084400d80f0810b62044000c050b240607650480020010f42190b05600005929070003000312103074040e41034659001a9aa070360101d80100310110b4420071550f000c00150001164001c006540c08a41e902c60804544210042c000c0d0144004c034118040e54002c80107102107404a8800300303000ca20f00d03d01b49020360340d074260f9602c0c6c0d0085911014510782880081d40b0320708070b200d018601c5121010b00f21605550355000849107034200d4014990000c40400c42045e40d24103c0e001100b98580081c0f90501e440c100c3d1010485651180e401694180c01001201031801d51001c2606c1c01840110072002c4080f1040c4c440040d240300302003045100c2c40312407802040c183d00900161071013a448509540541da5034050103005003003444000c952000100c0003c500791516840f5035807900320040c04010a860030520442984da110a03c5d40c8e0034030520746d82c540040d44e120b01501d4080c5201e90b48050f00c605c1d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 672647014 1250 672645764 672645797
    0x13021c020901061d0909060c03040606030804171504030e010e0d0b15101404050906010e0a0e07030c0215040609170715050c090108061302040317092e0c021c03 70
    0x2c0412030280d104460700821b2081031200080c1c1290000d9800175241e68984880c9001c100a2002e9480100020404940011101c03a17004c0c614084034180400c0c2c5403144845082c550209004035001004550403608000555100700303503d511400c1c010340080002c00642d298009040c0c000c0320300302a03c400b4004400c903241000c141c040c3e210300382801c0004421400c5003141c00580500d00a40c0d000c0d140040004000d82c1c4200d0f4805002c280c043c00b00118030f501d130461b82c0307003201007282d04802103400c010030b14004520000d00c10450000304d40a0b40c1d0a0340f200d42d1180c014220013002a00d0070300f5901200f950270a81d000c001c0542038030521549040303d1030540d400007503600051070341d0440030b000d01500398281d03000054590b200c0c03401c403400022085180185002406542c0024100300c040206480340300020400800b502e01045a007002410059410440c2c007481156091090790f24441c0c101e110b190040d1540c40c40d40744014841101920145241c91400c820200285e0010f10110f0802c020300 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 672648264 1250 672647014 672647057
    0xb030c0d0c0e07050909091e0a03080c03070e0303040605030702060f0c1b01020d09050c150f2d1917060a0302090a0e15010305070e13021c02090106 65
    0x100280c822102014031900c5241407219244154240101c80c1c00c000ba04182c410b10440c0c200020041110070182450b5a1155850604845c590340151038910302001c0325800140d141651a0316a07a0261503540700d400812176a003002c5d102d1310520540c104615030940e0140301a0016000756515a500d91514001c02460500c0142100340c030481001c1c2800b8000c4884011106041d11034034100d0380c00107070220410b0092251541c0b50707070102d1415483d1000c00801240c40c10404108407100c00d0344d0f071110515007042e40701d50401524866800c00086103142818110540c40a1485203042001185124440500d900403090101503880c074401071217910b60004da070301c0c0000b941c09a0b140070914280d004900f8020440c00302034841e26035900001c2c000b00b140c0d00003c1000b81c014058480301c242252020014180c20b00040761203005407a4040342c80c401c4001c0c00381c441e0030250b03101d54a00c070b215001c3c031005005008160540c0ea855252200240e1a00020300740284000e030f950f80403400b03030045c911581 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 672649514 1250 672648264 672648283
    0x17010f12140a1a09010c2c0120011a060909011e050a030b0a0c140301092a092d060f050c010507020303010f050d050703110a08010e010507080115142a010b03 69
    0xa20070300c0302422186c1f41404000c40034041000d1000c07000001c1800050b070f240545000c2404403c03c40403600d008080042d007200d480d11002c601e081c0010401d070010407119004004800b50002c1d8178900402c6010080d051030a11102071078107412803141c4400115204809680082c3c3c1d41c65100740500c91034040340d00c40c1400807481d42c90062844024182104540c4c8010b103e4101c00e20f8a8684091000020344081070b0f0b6400924807084e0703800c601000260440c0301901c0380c6100a800a4110482d44c3c40a200682c0c0c00700142035040c031070034244841aa024001001c0324010031401b84516415000c09104441c061201c83c4c0085803a903140c4040d1260011141d00068025100000706070000340002980c0d109496020001c01403242d180d04c0864200c61140c4d00182c595801c04e280145500c0041d031045000d2401952041c400385e07200d0742401e2900078140000000120346404281403c2c0d501d00241c040700002483d00e000008000e41c1246210b01c0000889029940d1549507408500c0e082011030030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 672650764 1250 672649514 672649517
    0x9232e020105040c0501110d05030712020c0a05060105060f0f2a01062d0504051317130b0c0a060509101d01060f05010815010e090717010f12140a1a09010c 68
    0x24004266071075aa00c030300d0188c1c0c0e043d082c0440132011401040c000c1c4240b075070104204d58210b450300004c602e1540c2e101e414080070380300d900408001040a041c0f21080350340c05c250440e98a85040c0c50141ca81c0d040f80c0c0030070004170a1300884018440202c5d030100c4e0068010800c10700100b01c850418191a4840780c0c1600c0461307200301ca40c014002810105d211039821100200c4001510b540c43e038480080311003150707c00a000380000c8c4400c11081107030700098000700300d05510030f400241e01d8041200d006d00c02c0240f4984140e00888001c00021f0300da4200690004074203050b50101d60001d40400c083d140859000d0301c01c0b5005a4800340d4a4009210307071001064841903d0400c10702e40350000e4500c4101030220102500c1c0741004800c1a400740c010112495000f600d15411480c040c4002424010326208511420701204c0c000208110030700f40300816140c9082c5014102031b015900c151908410306281c280038059001c0400103d030440d0441c0f00102e035058000b21961801c55080c03400c48000f91900d00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 672652014 1250 672650764 672650777
    0x230d0f1b030c0f08070308150d150216050613020f0d0209061c0b13060f11090409060915091218180e060a060609232e020105040c0501 59
    0x3900c510a818205000540604021401c03100b02e0524500c0420001d201418018000990340100342d803100c81c0a2041c0717041c0304070380c8000300d514041000601c10120003034a401a99958944000030700d41c001d2590080c03007003440503540708072798900d42410002c441d03005030040000c40c143d0541c00d19641c068014002240c1101c10340c01e40360700103001e045002d0655405440102d459030b0388034912a40100c51141c101080f807140e480d00700c0413040c0c00c054103802100c5c100c1c00c2c0904400848d4140c0500e002d00c8260700601c508011912080c040104403d0800b40c804544990820003ca0200c03599841c035901540004101c80c0d40508119205030078540c120310070808090141d01440e143ca004400503202c00d0090f0a21070046e1001050107090034140402c4940034003003e0201001d6198000400c031061500c4203032a10f9981c0480310207205040c00701d040e40c100c040c031404045e8906646481d020001101c4216000d001d00c90701d110060048000c42c501507992002840180310704c0708210001802c0900c0e00b035 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 672653264 1250 672652014 672652037
    0x50603060901030f020303071e020111210a17010b0405120a12051c1d011d0601030210050f0d090b0112031d0a05220b040c140304230d0f 60
    0x20310030280503c400390548400c0050320003150307418401c94020742d03041021605901c4003803003112074007801108101d01084a2051802c1004008142c01416035414480300c1d032a001920a007414552140e060b040800c0042c4d01c981051111415070b45002e04925281c0d50f803110b0409040c00a50700350922000d1141d1f00400320f0303030002245001307070704058110742c0383c49034403039180c481e14802c1212740d1440304002a007001801c3c844101e100c10100354052100000380450120b00c050140040490411072145400c100010b00150824070507107040c8107900e02c0c107185424074515001c0d1260300f12414580c0a203440e00c1e031a10030300c510b044025006d0100700d0240039100c0107559015045940301010101e9051003241c003803a00f40d41d1070030076400400d8043c059000d100381c031000368170035581c0305402c07104504d251940884207418a07205100d8244440d45401c0c56401c0c0d02009000346e904000e10444006992401c0d9134890080b4800d44130290921784028221f1601804010303003030380201c0450704104004c0f190340 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 672654514 1250 672653264 672653269
    0xf04061e09051e0f0907020c040b0109050d03050c030403050601120309050a061b0f02120c01030e01050c03040b091c0504140409150209010201020d020c0703120801030308010e0604090f050f0705060306 88
    0xf1081d100090520483ca150194804589103444008040358800301c00c804018070305402094154080e2000c84040080f42d400300e0040d107000c1c0c0c0c02d000c0c0303507017050700c1810710710000c0d00a4004044201200040b02d040075034039603a580c03624500b60011030b004411310f4080b4003055008078100018200403298814403c0c1080c84c000e20a528a1051000030b1104100000c1400000c41494030202d40140010340891210b0a256581c0c0d0000f040b0140001e2a00d90503903990001842698021115241d4003483e41d21941c4520001c194080e01c005801c1c0110100d0402061489041c0340c140d6045488498589141000c0f20386160000c41105024034100101e0100003003240e6190038242d5800000142c03124281d40040b0300a000d500039040045100090803c9200300005594045a00c900ca01c511140c103018411251028288002008220f590b0b0051103065240440702e41c0c841d10244c80025004401e80741c0c1e84810004850036503454000b00103024000038144902030140c4016240c203031650914201 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 672655764 1250 672654514 672654529
    0x905060a14070e040b0316260d270e04020a060f08042003120315061207080403031116051b030c0d030203070c09020414010f08040f02060f04061e0905 66
    0x140420080d9400748001356505d50010300305002c058220b0740603c000c50001d144105190140828246000324140d040403101241c0c011120a0000501000b4402040a64211099401118155007401e02d01c3c6400d503105c0c01c100c0b006000c803404203000d03414903006101e42076059800003001c124640300c0458000c0c0d000a101c6800542c06841041c000908000710640000c41c0000240c6c140a819140c62415480d440594090f01700c1c0300402143c900500201309030b912400b0351100e0703507220900026000302c1c0140092540580603007408a10304426403041d01c0d042e0310402221464503c1509840b00b170040030840070b4a2010480c42c400b103041041d1000a03590b110442c00d00d44500440000c9c1010180300384199803407140d0020710f1000c01901d4bd001c5801035042405844ad1948090415200c2903104481504e0750401e66222820161100c4d00c41c45010800c0980c00d0340c011900300140101008100028001800c069a450842c81c0d038444038a02e0311a00f802056040100440050226030784030741 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 672657014 1250 672655764 672655771
    0x111f0804030e0112150810020301050109170106170d02010501051c020423010308190306050a3804140a03030f0f02281203090c120201020f030a030905060a14 69
    0x41901800c6800b8004882c2d0114003500c01d8595810081c40300301040f011140e0106660040059460001d52a03400c7c0c0101c2c002481440d002803103040081129150000f50f00d80741032104800491026155800032603044100c184810342039000d5002034400030307820320406014107011921a5880d0840000c8072802d04400507001e4841d0390b4643e6410036026007640302c01c0701d40304220760740c00712981d517070400300d06030703005088a0710580c03200040340e2054602c41e02c039400036504001c0420407007c3c00c00c90b140010304071459645941124404d28680c06042d460008206041c00e81c0d541e996460074082001e00c0142c0071881d290043e54401824000640c000c1c0c6548081b000c140382c1101c0030112404c0c224544040306051303040d0114821048800a455074510302913581c007820041040c2d0441403422821a00c80c04000b41c02c6400c2d540701400701d100941c0341001c40d140144125000a410b402419081d513006285000c04a60b0712803c01d4108007050242c035034403880c529800c2040d46140d0303001c02d002c0d21004 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 672658264 1250 672657014 672657017
    0x60601050904020901030609050f090d050301081c11011a0312041a030601140f18010806030a06020306010504030b1515131217070c0e0c18040507031107111f080403 72
    0x1003502d0401780d02c40d80c0410001c204242e81400039042c00d40c91050f003a041660080034a0240104080d5130790300a4048904030b0300030314000e2607043e03900080440c0b07500800306010b04100c1c07402d1403659206070034017455854259105040c0211414041098a04501c8100b42c411940c010f100030001507140809405580404500103596552800d0040383c160040800703954681001051110001d200e4030090204040c07800c5c58818607407500c00042d01d005030101c44565041e8403c40c56000065019009140c00c52010f040c030600701a100c4c1c0d92041862402ca502154410b14145020454070704140021511049401039900e0001c00c0c0e41c1400b030700c0039a402103007014403001e0380c440d0030040c0d07421000c00b074800c007802069140c211740d10b02341080c0d0030070344107100d03259420070041204511020112410070454100c1018200d40a030188009410018000410b26503182c803008500285c0c00010010a40700e007054410101c107020800520707030310000065459070003052400b00410341180d04c40b03801c290503 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 672659514 1250 672658264 672658267
    0x10804020f0414091b04060806071409100509240403120207090c0c05010b030706230f0c0a06060b0f03010e04050115060e13020c150903071a04060b0306060105090402 73
    0x107520205010b46811242c0e6030a81d00e026080151180700410141c049044580b404002c0d040322100b0403098076500e0003540165045040800d02c0e2601070b404529210710344840003810804030000241d0f035000c04080d0100815400110945186000040301400e01404e2005003d05540000d41100c24025401700514101c45158243e0b42e0718000c00201c0010182031005010740c1500f42001814900140402c841135801d04040301258a0702092040030f407450360359558414034010305507500802554103031258442040141031f0600301d055005000740780c1540020913591300145000d8080760443c0d4007225628006104036038024050004a0741150006d6108003401d4803242131007401000d140000c40300086141100060786600a082c2240c2e0410490b00142038843c00c07421070091788122141002c0582100d6500070a40c001010b2003508030084000703c0f41052142c0c1e40b0040b00800d4010107410404101d010041002018000c182c8a29415406000d260030b00030000f0380117004030407826118540 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 672660764 1250 672659514 672659539
    0x108070b0a050715020f0910080603100b01031b09080f0303010f03020d0302160305060a0b181b070b040515090102091525060c110d020706051612031a0406030201080402 74
    0x750b4005140c545903200b08559604900c886c000c0030303510000303000c1d0281d6003050000035038034000c9200ba4812000a00078102002c01807440a000700030504c92103060580c2e428201d5104581c1c10b1200d94280c503d51038801c12107007000b60b0740b440c2ca0b01c030964aa4036a801003005200e0700d0403400800e012203905807001c048055851405904220701010394800f04040e13010004180840000d01ca80150326940d0100031074507441c0184006aa401c4950242c901001800724481980b10454900d480071240d91141c1007105d944d1f207000c1d8031130040d201030b145c0707900c84110040c144010b80b030469004072600001b145046c00c0000420204011200c981600c00360125200482d02440b07401051500383c0c3c602c50450b800018079003440103241d194210f000203888120044007800c80082d0b415036908443c0c00030074041d0300c0c08078201d905078003110845000d640c0680c0b840700000c1070000d02c3c0d87c84100390b840c0440d0f0322a1441f01c820f00200c42c2c0310030a20071424044200003503604000c40581080c1c060342c1001e034090 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 672661870 1106 672660764 672660773
    0x1215010f020c01210605150d180308190e012a05250807080a0e09060102070f060e040e062d25020f01110904050108070b0a0507 56
    0x802c500700ca804c40c214800141c56442403c10b030003052140d220004038100d00b580400d038001407140841c0400e4050b4203402464a400020381a84082d2811520020f01c80c04024280301040341e03282100040c02070003508040d0616050300b00a1000400298000c42d081240304890305040d880c1c03a0051042c0c4d0f106004513104a5000c0b4001d600310220b40041c0c2070b101c00384010480e0540c03010041c444c005030003200a40301501030b5884003404a280c42c03083c400010720041049045400410041c0007800815041c41e055503010b01d042c106041414011500a00c050022a039951240b0f0040100071045008606841030740d03500c2c0c1007a503240d4441d045048400964a4a00489815003128810b041006482000c440b86104507003545100c215542d00715a141846001d08007400038400c0341508040c001c4600403c44100100503441c80c080300402d6074020f4020440800c00001401300600 = true := by decide +kernel

theorem cover : BRFrame.Cov 672482014 672661870 := by
  have h0 := BRFrame.cov_init 672482014
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 672482014 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 672482014 ≤ n) (h2 : n < 672661870) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
