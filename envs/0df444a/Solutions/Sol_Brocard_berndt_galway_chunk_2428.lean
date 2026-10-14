-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2428
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:40:57.002557+00:00
-- url     : https://prove2.me/submissions/5d2be4ae-7100-4a10-86b8-89882b2e3921

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 436510791 ≤ n < 436690647 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 436512041 1250 436510791 436510891
    0x8060903070c0b090118060f03060906030c030206130e070e09060a06090b0f0910030c140a05040515073c0b0403030e07030c09060e1e04080906090603 66
    0x1001502d400c0b140d45505480d11900488010385005c219245180c9090000e0f2000140c0300742d00514481c82103619403010041d854581c030a910941e5890300016054600c00d0408000608150000307043c2401c203804019031181d1a903090722600041a141540041c11002807050a440c0003000190000700c11203160f01c05c9498034001034030011107841200998080443c1440c45000400e044910302c43c002007803003500f00d10040e000740003401180740880002d1045480040f052500030210303019102240c03500303800d1901d054204085000e83e14a00b000d65a07090106030002451014080480341000140310800c516022448810101300d20700709010300c1441081c440403d81000200c1e411a400d880c002c65040f06511615150030801d6000401c4015034800004803122140c1c0480c0907294520030000f00d0f500c1c0c440f003004030f00039100d0441d8558003004000c10001030403800100003002016003081e0802c031800c400501e0580085891084081030f00d5040d400315264904449450740c296080b1494040305 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 436513291 1250 436512041 436512053
    0x6080f06040605150d0803090d020718020703031103150909030a050706090f0503030109050405010b0f010e010e0312070b060a080f100903050d09060e07060207051005031305010e070806090307 84
    0x2000d0406003809550b1408907030300e505a403019130b03140c040150890480754006d280500e042c2d40304884000860145108600c112480400c02c801250720781000803003220a4080c9400017940005021030616984082840384a031030200907601c00c0f0b1550754a0300d031445202080c490f440400401e1544150010805840740a810500703540d1200e070408800180700d215450000b40391003a4901c090818880031000203010052a00014448c0d80310f1340092248010403000d00406a00c06040c640c00304100d2962030500754400d0118a00011008045803103040a01c0241400713030f032045606691811980c8104005400c080c42d00b0320007040f114004201003003980c900300f41c1341c4a070000e0700c1d100c0c1070726240b21000303040c03140d01540c4003041d030140300300020305e11450407600170107103480420040d000d2805c00007002400030515a003201c074040c10f0103c000040350021900c40c1c2c4000c1580c00ca0207800001100410707424400d91005514443c000c3c5100c5040001c501e2134104010483c4083e90300800c13030407001840f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 436514541 1250 436513291 436513303
    0x70f0c0618230d120207060608060a0f0603020a0501230a200d140708120c0301090b0907020d20010e3f030403030b0d050105010f091109061606050708010906080f 71
    0x311850200c1c0114804004d45020340700391800a824103040500226030000f011483c0c50203600714080400c202d00041441e00e00b901c199210207903020f00c1e000c0082105501541c1011031465956a5491600c4881302001c0d2040d00510308150011b121607404203a00c400a00c4801505601880217021440724900c000700049507a0030841280007010491104000c0d844093f20040d0401058980181c905140310f9105900240301c0d11401d1403e240d00801c160501c00c3d030144c041d980c242d02070180403004110503680c1c62740e59a42c1c5070744100b4580032091100020301c24025007001103009400e0907001070031104410540344000702004401906030341c240c600580006503001131881c19160301c0b6907c80c202170300105284040749400a0300505000304104040d805203050303541c0e440c6056211038451070210119960359101a201c000c08010000452400c0c0c009090482c0d5503000603001060036035100000c4d02c006079080707030104066200501c020368483c01400041d0240000600b00d0011f000485039443e9 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 436515791 1250 436514541 436514563
    0x11409072112050d02030a02070c120b0414070810020c0c190e0411090901060302100f020604020d08041203052d0306010305060613060503060f0d0209070f0c061823 72
    0x40c10403003038900e01500038004d4402284c540c24086403a4588007490304069405000d044400313815440c0c001c5180c0903000e860000c4141c0041c10320425544545d214810b01c0c1510114481900c1103c400056049040107604414411070001581343c1d203801001031724051001c6c4c109481051803016a074003101e107103280e6a00312940042103409d9501c0302e0501a8030329a000128a400c4500c0008000c400702c81504843c0480303109480807202c0d0318450700115100311101e1118401030300190007060161074001c0022106078065265036141907a9003003150b8518407040c404601054000c2241021400f408082d400c84d18408180d6000e80c880e854075231000fa22004010354180b5a0740c001054440e1261000c0d44c01603c5d510010740d416903195500507289400480b1750340d1048800c1c803441e038011300342903c201e01d09941c00b41c90a00640c6582000740c0d07807078082990070410404024115030101d54a03000d11040742180d10484403001095007400758480e8030195400350b141c210418842a40c2c41c000603904014 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 436517041 1250 436515791 436515803
    0x40b181206010509430909020406050d0515030a0b09060609010b030403110c04060803090a09141306140703060815151012060e060108091209060a110114090721 70
    0x8a448030440c0340392031159801105c5406040c4200c480c1d45003c0c4507164018040350f164040d03110307610704203041079120318000e01e000103405020000354225117811032a002222503811099490f80715000c240b40c003140700c80940320301408406001c01c035071060003580e4108601392a909940c5d81413110310640d0303100103030000b020844505142a402202402484901310000b082400150341c1c40350310f2a601d41002090600c5801d02000024250704141300b011400c18190f8080c4010742e0b038503200d074620200a48001e48a1039182c0008002e00d07040aa041c40c0704000648000403541d0030a03942da8507020580100320111600f440a102036006d54110310024580c00b00d912003841118904100c4004c41c0c4003c0d0160002c0c14541d01092481c0144080c0d8482d901c01c4ea00d41d1800c0e1b4607200001e6580c20b071000041ca80b40303001c000070b00c40c03800e20f040100003881c941d050004041b5038404165003142e240c1032604024036034020602c1003003001130260348020075842e6804081700803009201d4460306a0700710300500f4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 436518291 1250 436517041 436517071
    0xf0903070818030a03120b0d0f030c050a0c0e0a0c0206070c021e060309100c02121206151b0c010c1a0a1407020d02070b03040f0215040b181206010509 66
    0x80342201c2c002e000c10980098203441c560040381c60040c04080e00c01c010444100c0c2481e030312130080c0c00c0441f0f60425950700507ca8001420942d182a2510320051106075070300d0241c60030810204018801c40401850b04480c940000c0c81c00381c0c1c8110444142d406040704640158041c040341550002251030004c0d0126600301c01d0f06024800c0c152500c03070300b00c44a80c120b1400700801101001c081400d0a10340d6000740706001c0c1b076601b024201c0c2c50304811480183c4507035090018030503a0740116440c1d0b5000070060302900d800d41d034250703081c00039030400007203181d0041c600c110315400c102e418000894201d50030f0a00740305498203903440c2441d074103502c282041008014400036540301c1003500281d4114440c562241c005c1c0c1046d510007500d9030300100039040544520070000420682c000116449103420508102075500260b00700818460205000e0f11141401d10010440388101c81c003c1014203020b82410580103041e500381f14401d0b650240041060304080010403064645810752503200f003400c00940c0e2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 436519541 1250 436518291 436518307
    0x110c091e0c0d230105030f06071b080708031e01150305090a0218220c0b03100801050a0603060510030201020d14070c060e1207060207180204030515010e0f09030708 72
    0x40c0c18000d01000801e141d05041c3d1a01c0903114881c0401401061000e0000540c1e80b07038018580c0d2015004d03c00f40f515800000000c80c00b5110344244a01c0d05902150b0300341461035030f00d460070290440c070410390b2100c2c1c0000500c0600c0c03001752084a0076a50811304644503625004940b840d24415036015414141c0700c10018a00035014400e8130707040c81d401030042840c02c22075402c001d000d0030700311852204002d8074075140400650b0580803d4410350300c1031b0103c0c03045080c0900e8a0381d54102808444525a950102050643c02805040d10842c1000320004070749240d400e092007541c0000c0c000d8010322710340d18001e10260b41c1c081003010418106042c0b0b51030403030301055000d05c01d202d41440907041507c0301401066030ba074043c405404050040701d4100c0d200d60a613080d0344d11003c445c495800076a20070700040200080041b02d8520158a0306030040c102652074440500300b0080042c1e4031080107010b001400798440e80708881c0e40243d0f09a0002c6210302e051f20f100d41d0380e0b2250b07660240c0740c04408036005c5 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 436520791 1250 436519541 436519561
    0x10f0c030e0603041a0f090304030609020f09010e0702010b04180308061201091a09010e06043302040f2903130f0f110d1a040303060b0a110c091e 64
    0x4107081d8040c00180d582e1401341041c400f00c031501100da5004507035100120340340300078885a01c2c2c01401d00b0b0003d07500d070a1859071014000d11804204030380103401c45e40c0b400c10750307500d4034102030081040100c2e0511a10b80044002d08480140d01807038070491419000d0601c5d045200f00000302c503641410038140070b07210180050200041c1ca465070881b503080c08032a80c10020f1070002480140406100964180c4814424074242c81c1c3c041c8012070385502060014010892440d800d6103003130609503303520150b82140000040e00565002280780c160006070070040c01090002c035900a088007010321150352040350303180c61f44201419004044c144080082503c20b5101980c00340c59541c050f440d41c151030098a00841c1490f01e08500341c80c0300c0b03100700d0b254006080400c0d0100c1c0d0558400c0e904805040056607031040500050400c1c2c04151740c1d0301c004070307800f92074400401d65180d69840e0060072400840d2060300d001c0c442080c0f64040d9407528180405d04024060f11000e000c2501d23034140e600d9664541070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 436522041 1250 436520791 436520807
    0x1a06070b0106140f07080903030c160e10030506070f030f0609050405240c09010210020d2003060d0b040510050117010501060f080103020d0204090501060f0f1203081303031b1e020a02010f0c03 84
    0x112005001704900d07802449218be074854111650203103c000300c1d0f030301c24030802c0590040d44005442034100800144459100d0f2021a0401e0964100090061310616150003186c0041e0440d00e4034594038401d00050000400c6503020030721000080030303180f071b04e08070101090407070143c40703000c049401003503c225682c000d114207221f0030f80ca43c0c4115200c1c00340640001c082e04001225038017501c0e000381c8925504034882c007100d00c240c4000d02500410726450780c62001c00d0200400a0342d03030740519140c41c2d07a0540c030f40c02480c1c020140c41c1790070207120010402c181d08444041e400740701440701c3c000300c000c20710350000c403c1411207804032003010a4114500104000d080141e10040040d4030308000070035451606095072040d1506001c1d0051015106ca40d0190a240b004501402144101001814180da29260a22010311a15001c204014200704042d100d0050420107000b01d264143e880c04403404d0009002c4d4940c613140300400034139000c0e07000030b41841e00108442c0104501c076007241c4185070082c184 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 436523291 1250 436522041 436522057
    0x1005040b0f0330070c050f01020705031c05040503060103050703031409090606030703090b0702010614030a0b0a0213032009060915060f1204140111030c0d1a06070b0106140f0708090303 81
    0x2069503600d0f581d25101d0385d100b0b8640030312417041c0341c0b42c2c01c2c0d003480e540700013110303000e40b040580104140341c03940e80070214600e85903c46104002d001c10010a05407802d12031280210f100790000d240303090030742c64050a01500260305107200141071050309240e644034030b07840d80c2181080d14465580e44401908a0140c02105400b9080c0d22440c0207008006505510800c1140c140c5454030380108035200c200350b140d02031000081c102440c91804030740d450016900070485440502640e41046690f5506d49000f2583d0f0200300d652041c0d42205180d5074181100728076800f020896420301070346894040c00110083c403040090040b4004540b0031000018201120700b01420000755030341c00e142a1070034102c5445204128041542400e50210450900c2001d90b0b0084044000203400c02192054a40017407075080c1d158500032207190300070210354a40d41c004103805030051101618547c1031140190055084c0c450541076803c003000741011304007262040c1d4808540c40881030396644804c5000a28500034011 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 436524541 1250 436523291 436523383
    0xb131203111e0d03020a23040305060f04061107150902030f010e03220608070f05161506051509010507260a02060a050105060a03020702181005040b0f03 67
    0xb840102d66881d041d220b800582000003100c512900c002c00480580c004d2400740804191108108500c019082d80d141c80760710181c03ea007505180e83d0b40c480d2864090191004480d8981420070f000600c40c017030007440e00e0034030310511551902580340d0351041102e4810f002030340b1a80d507440545013195018080f0b141c102c21168020f200741c240c4149050b480b0340c421010313181102d14000000c500000000036130b6040742c00a8542c40603681d2118001c0d03e900312400c40f83c1d01009420080428040c0c0140c83ca02c008902421180201484580400c0112045a0021881220240196000c01408100b02c5580a60038600543c0721400d905c0d008010050581058040c4810f50000c8000c1600c0900900052421682100c4032911002c4466040b500d0a001d000c2c0c005508001791b00c1240d009800504015101814520101044482e0400881025528000d208658900401c0702d0320306400350601103039045858502e004c034070384d0021340e4410b985223403840f8200088030803841008000f2861004006040 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 436525791 1250 436524541 436524553
    0x10c0c0302062b0606020c090a140c030402101706011202040305010207030e091807090e0f250602010204140f030a1203020a03111c020313020402040e060102070b13120311 75
    0x32184072048105440101d46504468101030400038850045130102c506940103800350301c0c01d00381484410400184808400d94a8001c200320908112a0340d0744654900410203460782807500c1042010941801910204040c040a2220014810038070682004007400c0c555660111409044068051030741f01414651002c180312091580245240309078041c116103001e580d99030300c2021305040281e0201e81541d40d000807024000c500455100c0d011518100c0d04491034520006080ba2030f0880d10307209024103034450200340c01000d584441c1d11001d0a864002541040d080c05070f64200c2441c441700d1144101c28140c95002c1d240c900740110007009401404500500c0742c0c595020740658094020200001d1a006a034081000000e0030f070b43d100d0503132605885911010192a4000e50000f404040700b0401c901d51f03060045e0344500c0100010150508540e40614085001905050030340e8095403100300c08100d50b0303031310000755402070701610b041c0b000c8081c01c032005040490715824903144030080d500c20a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 436527041 1250 436525791 436525807
    0xa1e0c1a0105090603060f0c0d020705010c09060207092007020103150906150507050a0b04020f060a020a06060e010501051c060f180c18060815030d12110a0806010c0c030206 76
    0x500150303058441c143c4802c0c1d4252520030505540308400c40312551100981d9010944902c4001c00401c21490104000f41c104500781d21498219080204040082002600b08100e26a0103100d07490003000400410400400c4500c2032120850850700158030385000002d965086a01036403081d00c8a94010038900c02e11500c80350310030001d201d180142003240e02000d4a40c880d481c070407021200d0030b590140c0500301c4442c45075610181c07c40d010b0400ca034003009030071b2010525120440a006a40c45c16801002c109266003020412941e0541020403e0380038900180410791f01f0100b200c002c884403040c42e040044d59034a5002c0204226040b904e0a8500200000bc0d4403010200d48a240070f2044010049501c1030501500d0440108049000818200e401001014054060990b000b440034040810750710100000034205001e428000000c40d10602d20850448805e21400202d0990b440e50a4034051848001074002d142c004c28240c1004044058a02003250f01c00742ca4005590207031039280ca804803 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 436528291 1250 436527041 436527083
    0x130507060504031a0105060a0516020319023307030302040909060b01120b01080a0c0504170601230607150b0409050c0102150105090604200403061b0201020a1e0c 71
    0x40c4000c1ea000381030181820704c000d83c3e01107124120b450003004285020348401c2c1c155110781000c6451640d0351071307071940c0a0150310280034070309403003c3d00e00300a00f10014610402614114102054840c002155404000719611800828488160b05041c80c2c540e111890203d001e4401e903080121418200f0070a50200f0010390081c1d00d5405090b202e502019460610800c111009101c031140080e400d07001203124a507059002080382000c514010f0b2800e515013581106100740d200c4c40d603409500100042020072000740c4540700c907018007607402c1d90b0003e0780c0002900502601c40040e100840e180b044c4243d504050348000f000c41c2c405001402500a035044c540d8507110112109805401a4110000414040d000e10340c10b0350801400240c80e511140d040c400100718408140202c041680c0150106e040c80304007500c0158807070440419015a084201035001c0c032a1041c0300196070040c00304500550308500c4006440079509904908910403c00898034001070820103400c000b004480707a003150075 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 436529541 1250 436528291 436528297
    0x1504020a0909030f03110c070501140729010611120306270106121503060b0d0f06090c05010503070f080c0f12010504110a020a0305092e0e06211305070605 68
    0x1000d61010011038486064912442c41000121f42c856042050180115802103000b41c118070180d030515403d00680350341d00a40800d00000042c0c04a40300801101541003003402a409041136240c1110401d58213a035103940c48440300d82c01c020050001c80000d05544407034640b080c81c2c11a403c1d0032400440109504481e42100b801000300052680240500a50041c0a01d00b5030100351000405020b02d161100d030001c000c55080305501010030030b10007000c0b40c1ca204a5410b0f15000342d400141d19902841d269440003901d902140c14040301740300308040c3c03d400030a2504000301c2824170709240d41c3d450300781c07102c584104042d81d016628085021112441c2740488181600c0301a242006018205000c2c0180e82c01009500030050303001c50322460010744180f015100401000d0301c0f50450000340d05080001d500720141e00026004c8040c3c42c821100c0d405000c0c029210815645940f421907030118525490100e20783c241076200044000c5500e2750702000110350903d03044001c0c0c2d00e0654071482c00408170b0b4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 436530791 1250 436529541 436529567
    0xb061306121101020c0d080708040b04060917160b09010c0501050a0608120310150e0a06030b030c0a030c060e031c082a0a11010b040608160905091504020a090903 71
    0xe0b210b021000b00b40e5000050806045a00901404115005a480c202d0903071007107070215040d5105000000c2c0220041010b44050896903ea01b456a411722500c0007017003150004030001d83d40100e500814801490f04400c0c26514001407007a03580e1110401620004c5c00c41710011710a62825080200c02407055200d2010b50311404140c3d480c0c00700d0503090001c03d01082d91001c29020694504000d030450b082c40e012041d242e2400c0000105c00b05c40300040d480e07403240c1d101c480485e0b00c441d400300f442e15052180d909407010407114428001c4c219221403068449038007941d01408850091100980d4041020882e5002521a42c084000e030000c001000104283c42d24805114004030304c0403800341d40308960b0751100c001d0300340f14181980b99408036400810b84040032059503030f451424809841300d024a501618103038004000041c0000d6030600c803100356a001c0c0324410300c0d0500340010340f0004103414104080a09403450079440d48d0001500140071903106030b901a03d01000030040680100c943c40f085 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 436532041 1250 436530791 436530803
    0x2d0903010609020711270702060703110a0e060a030b121b0105070812040f02040203041a0a0e060415021309050a0c05070f030c050304170703110a0e040b06130612 71
    0x50b542d44166800340c0c001e1640040c80c103e5517441c40100350415010034150881041c2c11011266a112001080782206540040058000e80100451150103003d8414022402c8488900d006043c03c3d0041000401d250701c1481054000b8820890a220360064003200400805440820341c082e030704150707a5004183c9085d1402d01221104102d0360164080d94041b58212000c1440d1400c1201c0103500164010000c60304003441e240360f000503840f648065485540b003407a44041042d0b040030265440e480c010030000c6040d050a0b45080031000c00f08800e0b400a600084031105460365404000c0680030380340700d038100d480d028603001a0249181e042907008001c810410003c01103200e1007103a8030f204d0020050b02119a00e044100003a00c604281080c1038000c00075242003d444505d200c007030024103428015103500011080c400c3c030003541107400141108171207200c400340c60805400d041d44c40042001d041e0750803010002d003442d2550200e802510f950f01c0010840d164a034200c030741e6480d5070b0901c10307120 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 436533291 1250 436532041 436532051
    0x40f030b09070b03010306020702030307120503070806120a080f09101706010c0209040803180708010c0e0901140d03110607120506121c050d0615020607232d090301 72
    0x2400700100303441c01900c90300d400b020300d142e0850726100301a5109035001c0b40c1610080220300c010913a81d26221100f1012662017956a0038608001420000d01170542c0d8445d524080d0740c80c24038200001d000c407145500400303c580719100d28a0000550007190030054014880310003840400f5800060720f03022400c0038007a000d01e500c030310004440c2c041510a0003500014200d0100b0045541c0e14040e41d4800d01d035030410200380030341c00c000c03a0610000d64808400e5039121001100d1090b04458120492401601c48807002d40c58003424080c1480030f071603828024241800c101c07003411b1007403407088094a514012113401c4d04204400415090010600307445051404010508910b03120040403601119000200140f0440c50f008524140e440207035a414040c041100d282115504d00503800180002c80a5140c9510943ca001e810842e004009400300510340071947c219044035124a2401008180415199060684000090a080c140403140c204092541010240d01c443c01031400c040c0650003030003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 436534541 1250 436533291 436533301
    0x11803020f15090c0f030c0d1b06030209060a0f09030b091c02150604110d060308040806090706020703030c03140d06090b1012090501090f05010504050114010b09090702010e03040f030b 81
    0x32400300654501c11075400c050f14000c041e18084000304030800c801000d0320007040c071143c0041d0811030723400c104036250361400c10714603000801c40810070300070a2141410f618100441000503150310a4a290000b404809400000c5040c032540c01a0061580134000c4600c1c0c1c24101c542a980300b100d00d80c01031510001a8201e409544041140c0d500c01d03000c00c3c0f01030b043c0e44923042004003500301285054100c02082c450440404424001c0c075004501940500ea41c947c20b2070320703c5080c0036006110b42050f900412042080d25800182e1000b02d0b609841d01ca580c0d41c1503444d00b00ea00201d080e0143d80c1504010941801d019200d07400a400c0b1a03900b0320812401440303100744620400280e140d04040340a0100030400c800383e507049200840d200700000a03d40010741e4a4a404120b0b030340d000d0750032307079905c804110400400b449100b13040000c00340c0d42d00140d0700d444001c0d4814490101c6807070003540c507400407030303850790007500010701b224080800e0301d444507110340301d46000e88101e20007540c1124194012507 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 436535791 1250 436534541 436534573
    0x1506050403032c0301020403080304020a060c05060a0f0b040c0e0a090510180f050106091a0f0324122a10050c070f0b0403060f060b09040905011803020f 67
    0x503080300d601d40c0390701d0303001c00400003000040007452201140c2d00d00c1d0841e40c081d165400b0320040c0061032107144900d80380e040c43e00621030308000b02e8010a09001540b00c1c150702243d0009502070740045171003c00705a0004140100e03016201b03246070250030070b08021084c201c2c3c980025858602c0e9206407294071b00c143d6500c2c1c0003001c0c1d80080c0c80300c1c140c040114074103010854440c0081000c480c045100840c2c0c01016041c1281181c000740c1c8800009060b8040c1804003503c50a080f80034002030800d0705041071038881902290344005404510100484003c1840200d52000c5212502000074040703803080304607610854440750400c5a5002c1c4035061120202c100c25101c000e50f68200300a04125840c0d6400402510260301007482c002107445000e0000075596034284403440075060100e4004c0d141ca2452a001d026100d01400d001c0300a403c202c0140040403034942520800f02c01210702060018450402600401000c1e000e00129594481d40b80e0906400241e00c13281d8440882c00c41e5007100281c0b02e41 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 436537041 1250 436535791 436535797
    0x40e01051305190b0d021908071e091d0609010614030106120305130905090d201b0402130305010507021c020709020a05090603130219030b060904060b0d0501150605 72
    0x41810583c082611481940b05540700e182d1410340034005540c410701940010300076091039904070210344907100d030030700410b5001d014440060090300500003444d03141c0c00406098000340d001d220040307980e90602d1209419000a08814042000140c2d205070910100d01d40c003070070050050501e0503000480202c0302c6d0a05201e40c0303007140d402300d011070300c011100c0da811100c0e5486002010102c546440020609014a105031800f60405000030400300d03800d040d0150081c109050860200724170f61085a251610200c3d40400c1c1c3d107210680d81c050001094002002401200e040c44810000d1210200030400c05506c43c50080b0704540072503007103c00080d2806036008003001d1800061704500c0301000641381c143c0151910882500300381e4181201140410200c0e0021220309480c46030703018045065081c400c1e500301c0007003c02e2650f01a0302c0c1c00c5071500e030120740c4054241780c05084100009400d0000702e031302c0141c100000510b818032566640c00c10034042c00e5803000489103c001400002807050040c811 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 436538291 1250 436537041 436537051
    0xf06120c120114070306050f09042102070b0a120e07050d120201140f07110309210703020d0b0406140103120e01090e01060c050c030a0c0b0a020c06040e01051305 71
    0xd2290020840c10700c01d04003a10141c01da4159200c00d404030710558958070541c401c400780e42d00007800c6807805081001c038803480c444840c003d00e042400c0c040459840382010440042464804010001c20b0304100d2034961154840c1d4006c082c013294015069900502c7c403590700c070f401881070001340401c44010383c40d80d20b90f200d03490703020640303258610001d15503c0108245103064000061015403150740c3c45036001c4c08039100750820380e01c47c08114070343d50880c000c3c3c000c83c4040d00041d03041c0b1400388081110501640907030002e010b24412001009501080508043e5901070071540c40071a07245000085031005580803204203081001040d65100b00085550417607800c44a0512800741c110800d8501c4a41404828108461701d20041007050448a2482c0204110380d40c50303c115080e801c041e400e080b0100411417083c3c00003d010340124508200300400d41b90b0812801e540c54011003401d80c904140c014626800c840d01050000d801400b0020310f50480c0d5007a07a40d03540d01c89410450300c04503181111 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 436539541 1250 436538291 436538293
    0x150c041a0f0405090a0b030304060e121506011b0510050402100804030806040f020c0a14100b03030d110d060b19030507170c040509550618050f0612 65
    0xb1042240e03207402c401941c4c00c010700070300003e803070f2150201017421a0300641161020901c01c22000303c2c00c0c01c090010041441c61407015010320070014040300280f10703002c0d1400341004080c0701c1c1e410200401041380080640d0084c111a030741c000c0520454060070044405034410b0304c0d40001104050300542d01140325562540d02c91202c0d80e035410420000b0141c0541080d42c895081c03041c2202810104141e44000d40110717814642038403100141440e020350640798100c0d0700c1c14400744016035103000041e1034103a041d50501140000034008003000501401520000752414200001800c1c07491b100104219402210081201e44c50224254180d81c41585d012000800d01d9107030720035800c0f880e103e0315001030496098500d0720750303900001182c080058803001c1d8503501c00c00b6243c841d5481c08280441500381030310320400b1011214004e0002c1c0c0240c5940b45101300c2c002c040c3d00c01240359603004da0080c0ca101e00c420200442080120340c0100340c11100b15407409401d40200d00c0d40d28108002c0f01e07525100304 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 436540791 1250 436539541 436539547
    0x12201605121f0c1e0c060f09110f0f030a03050903061605030a0c110709060509090601060f03020903010b12030a021b06250c0b0c0d1b110102150c041a0f 67
    0x2c010700d005007601c000010420007070401d15181d4100ba40303184951310020340e845280141440c280001102d0b0b080412640310740c60911031400065440704092540c8104864000e0310b0b00b5010049014008004202c0d945170060b00540c4003016005800703030915050960807503a50f90759084a09100002d440e40b010040b071810320010f0300e000b846400081842030faa00c0c100b2000c0c0480c900d450700e040d10f00e4026500d079544850050125051200907a5404042000240364652526502901107104d03c80312804040e0000313100c1010f0b44003500043d204100140c4000480402c070b0171015143d03045080b8080050180a405481440b0441004524000d00130107561a040a540c0701e003c003022010601c002c0e1520103070b0041b010624008462005004e08049166a904101486800d1000c0202030401784941030740011a43c10200c0003c09055500c00c4c2c518030080d56050050f0b282103d00c1c4c05803c4080507900c10800c9004075030018000302c1d608501110100e015403840b1409134040d1610349000a0000c1c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 436542041 1250 436540791 436540843
    0x605030c011206080303012309040b191e0c020f070e130c0510080a0b03060f0105010507060e0d21180b06030307051e0d0503091510080102130f0603091220160512 71
    0x41c50f04533983d10720410002514030a030300a540c034400348500441103826500d55424031925010302c900800c0203503a101410041703040443c0302030200c0000d4031a82000b030703d0130700403420003200c0f8030407c002e014010288031b10b410404400800c0c9a82c00c44031021041e0501e0040140e1341400101140540300c0700034000000d80c200001107840390050441a109a03441d038002d10221072050258107400c0c400d039982d1a0001001620b0f045030540782801420106160912912a108000c006100101d910101c018616100c020009145025060700505180038881c14482100d806a80c2120420800b600341c800c1d00e00e81031000d44075408121071144442d088820340055420000700102c2e032200c008251000800e885000107401c903003084180070305a45410a0600407401d0704107180340101098a81480740c0000c1c2c0d51489011a55507042c0707010f00440300d892217100c401d188810700304266900111242e0b009130101c0e001c404901d0344078042c015040509000e10005002c104180784600b03240d40000903580c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 436543291 1250 436542041 436542061
    0xc0a03031b020a0b040509010e0c070206070c030b360c091003080a080702100b010c06110405040f050103060f0510062d051b010605030c011206080303012309040b 71
    0x180c2160040700611004944010380e940541c400143c40a0f24441e0b458508040903c403440a06070407240710400054100420f000b03000c4102c0e00e03900d60650341240c5132252440e0500000e015038200502d030703141c000104072544c901e025a0042e0858003803d1110100110701001c150315100b40300f04801500501e040300c42600b00050817036000310004c42d120403000d56a85407140f0580144415800150941c4240814150f0400041e0203030329800408000c80811000041c19005401c20001c1081340c0381c0c010758001c142001c041e0740013000301400c1800075103007126801c4001d003800d01044614070f00d0101003000c0e01017544100c03840b41d01100d000349041400c2100c10344285402c5501642c400b00401120058a4a4005003030150307040ca403511070301c5907510071780380b24601d001061300d00d2070741c1c580b040400c100d076800140c0580030780c001e007420340c00304541c0c014003009400740750030085840c400080001130741300c404a11081d4118801c0300300e14050600804101c0660002d4030068403803091075001c18036041d0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 436544541 1250 436543291 436543307
    0x41104090b0307080105070503101e15141308070f031707050c031902010206090f030307110703020a03030507021c0f140a1208060f030f0d1b051009020f030c0a0303 72
    0x1c002e0842c0c0426035103603502402e5510498002000070f8010061041149030b450525028104240440402c07400c078241308045048184500005070791103110418110340224400401012144080303a0354124040302c1c0080b4680320b2088429031300c2400d0340050301c0c0c02d92920100039250300c43c0c850740001582003120512a00200f106982034003880c1d402204c1ea0354100406103500303d1141600400c030101c1d00019041080052240d51190455807201c1c2c00c4030000f000700e0340d0040160802c0700b46041c0d0060002e03d40b00c40c13504002d421400c081404824507030032601821140c0d100b100e00c404004034003084801d4003540780c10000d143c0d4042c09031480c0021300d5007079142c445807801c1040b10001565070b11008160040c071203154000c10382c11010f018090401c9145042042e005500800011017058629680ca104441081c0c0070481d0b45003a032411200c5010000480503000700403625801540d44c405d41c010030f03e034a0124414880008526101d042c0400c0701e2a4080000b040d041d086851078500b60754541f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 436545791 1250 436544541 436544561
    0x31827020a02120d06050f0303180103020a0c050f0102031006140a080429090105070507020f0d0f020a060e0901050f01020a15021306080402130207020d0314070b0a020a090504110409 80
    0x10203503a10018002d443c100140c03d00b0648910007041080c5041d040c06aa241c0003010b031402600304001c6108550541000a0314211003860016075804010104031442c0d02c080030010100d00a40460009000054010390701506030321152074805d40e80c440c003c0e15207810741944886403400500c81e60381d085000da00d42d558000d0080c010205443c51140a0a031422101180210040c0903541440900442440b070140d00070800d00b0210b10781411034001900644800c00e030b003481044c502800104024100d20006103450780035204030300e1282c651001500c1002c40c0035003640143c912800028103454050a89042001c040e00540301544441d212108060310384400b004015800700504842d5818680190000741550786d2480c00b03508180c070400441d4999401450340460051017030902607a961016824125458100f001c091031034060408814042c0c00030180030f503203240041110b01c07041078000f08201c02c0740e44e42e5017002c0c5840e03404001c221180c86180074071030030041c081440310008a600c90704403c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 436547041 1250 436545791 436545793
    0xb0715060f031b0b0307180602012c070816080d0e01050a1101150602010b0112050c040b0307020a020a120506070804050c040c03020f03040501290102030901030207080c0a031827020a02 81
    0x20f0741c440c100c6110540c01580c1010016501e0943c400e01d08094010000140115100034032540030141c0740b411a10f0b10200c0c81342c00a2065022950081408100d418024070341700e000d461840340501e615a0700002140f1074401680241c04010b140e86219a20400c0010fc05840c0c0074108000303d0401c98a000d228081e018441d940c448a0038134a0415150b91401081c40b40e0021030321441620005105640d50842d50320110706000a103c81507401500303903015500105401c507101e6581a004925001f90040c01030b401c0410b4560100b0702100300e03940070b50154000c4044805580310b0510485048004540240c0190005840b1031102c2c5459004000030f0702c1c0d14500982801308844d0780100c0b550050720104c6e400d80d503820004ca00c4180a80900900c010340c031240112440c5401d0002c0d403a4816a4142da0400d6400503400040003010340c142da807911440001c8621681e15450082e0403090301c001d01ca241d0110000340000c01658507a4500710b9a640c0d400e181c0050183c102c604006500003030021419 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 436548291 1250 436547041 436547093
    0x10918111210050a1401120825080301090b0613051c0b01080d030e030a05030109110f0706090311012f0717040311090603030307270b0715060f03 64
    0x8185410840011442d10895000620342080d046580482c0d2050901d0400080da0340010482c6a00b000d000c50840c64218a8041d640e142001502c500010845076052011041043d20418003035000c2c080c1d410b03928605003c00c80f0a20050821007a03001e001d5403203000c0c0302c0610041c015030030190803070641d0301c8120411018818060b40d49001c0354000360000c1415500000c0545280c0b42d16016407808c00d1a020013451400d05900301c010201d10050051000681d202d500518128841108039480c6001c1c9491890304e4101e0f520f00f0034040e1a01143c20780024529038016005400c044c85401030150422038050303803030015000d202ca03003000184403c1d440058180504404520340d01100c400c0756640d403403070580d114110314041c440005e0580000380543c2e401e00404c201030b1400800c0ba40c2256007418925080d0205489500c82e025001c0100c4004a0b49000002008804007002d452414032540e64021724a0803540040d007101c3c410b105402110200c0c03182040814100d10995044850041544030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 436549541 1250 436548291 436548319
    0x10c0905060d0f0e1504061a1305060a0902070503070201080a0b31020a09063f091502040509010b03060d301205090d02030414060909040c0e01091811 66
    0x41810940c40b800b0f000490400200010040c40b8891882484c9231062080209030001c2e0205612184070074003152180c0c0d59901240e81569100558801480520340965032600349141a0b40c40341c100040407404155103801082002d20079006d007101e107072005414031042d44200f030044850021755845002c0700c0e200d2a83da8a144d9003035400240003100b440d446a080e01c51420000401181e003081041d8200300c1d1014004c80b49851170100b00060102140905082d0040c0c01c10b04e80c0148940714004001806124440c0380844040d0060011110f00722000c0340f450b83d0300c480c0128a171004440c2560301640c0f40c5000c400084546065803609405000e08940800521090b82444541c0c12403980108008801c0032481010f00d004081e40f02102901412500c06413580180d80d0340902e0240c0b440c0c04a078100c4107880f42c1c03902020780d00712150051124185082c41c0c02c0008442c41e960003401038600a007000400c0700c00c810f010303a030018404003011403a0100305480d0982d004122480c0c0c84e50041c100c03450b001c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 436550791 1250 436549541 436549543
    0xd020915040f060915022e090302010501050f01020109050706050a09150309060b010e311a0301110301030c0e04020f090a05090c0109180c050903030a0201090203010c0905060d0f0e 79
    0x90b2a080c00d010702880d00306078000e0001d030410f500034130345582800d517001006035012501c0c400c08114031032a500d045940381d084242c0600100e080a401d10300e400000801d16505421070750484a00780d40c0102400d4a8500483c00d8a2400c60050225441740c84108007441c481c0000300004d003070625241c0e07220754996045e0b4803c00c183c1d88550340001c0d02c1d40f210700148100b13445a074014003000d00704440210200404640b20007102c01c4400d02c0c94080b008204004a1510300441d40a58440c03020400d080d65103039246142443c801c2c14030b001c2e41ca06039110035055100703c00c0b40d06880c0c20007140c0e500e0914112441c0c49000c4010300c22a009103249003002c50715103541c0035413801031009210104180c5803000c1e000c1c3c0380003d0010f00c2410440e050340208005050b407003980c864800464004210300a42d003001799050312501c14819014440021050940b41c1e06620070140c4510843c001c0c0301031100b00408a0360320f007440c010140d111404200c01c03542c00000c0d5025540d04615404081440c0584465507 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 436552041 1250 436550791 436550797
    0x10081e0708031305090711190623100b03040c0e0403090b0403030e092d0414060903070501061a0d090201020c0a35061303180f09050601020708030d020915 68
    0x2c0e40e03c100d49102d0a002615150980591101540c90303c0c0703560055010249544100505010300c20b8422070507100d05218103600903040c02003254203142001400e150708042090822a0001c4c4000c91100c0041485090002101e0090360840c8a1001d4141090258184d203140904118140105074800081c1e0441030005000118000d07190724421490030424821289001402e024200403801013100c0030142e1428207880400d1740015444040ea074500c5d110a00211a0750310074081d00c201c2c2c2c100010700c0c0c80000100f10710740c4100024083d8580d2508108001d8171843c40c070451142d0184803050703c143c0e482e8002c000c12401441242e02c0183e591000c140c1d032007203e4100c00c60700c880340c0c04020025a0520f2140c5c0348100908500702c20a0710450001d03884e180050202d00074280d4002008060502c00c140f100f81248221a10001d982c1e51040464100c4116204203204182080006802903002203042c50403298004080c510304066201d8900c000c0d8420394520f03500140d01003054070a500c0600103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 436553291 1250 436552041 436552057
    0xc031b0c01050c0a030e07060207090c03020930031215010507061a24160206190216091a1512090106090e160306050a060803070f020910081e070803 65
    0xf007140c0d501c03060398004094075444600c0040f01d6004100401c0785a60015403081191212070000440b203c0c0c1c241d04074040d1042d000c005a101030b5030b4012a000c00340040e844954800c1d0003003500f11040554420640303e010f5030f03c01806040702000044c4a9008030700e44042010360514140d442d118107070356018225402524107220303034000302e91041018100107103503450080e14015480c6481c0d11001e010322540c49811201851040c02d0010103045480d0720064407900269010200070710300b030020000b55542c6101118271265140c00da000601000c2c40c0c82411103e901c0380d4040043c002c030f203c0c03d11628982c81c02000801d100e003000b0301074011036481000c6006641100000c5695454000035905131059240380c10556000101252801c07a940c1100604481d4807000204030755940442220040c07130aa4004095404002200d03010080a1840304070118400c507815102034a03425000001350600d802404000d9001d044c004020f550304a01e1800a01c01150855010a4441c4140c50640e001200 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 436554541 1250 436553291 436553311
    0x114122203082a040b0705010207080c0102130504090201020a0b1f080a020909011e0c020c060a110706080603100906180c0807060f0c0312062304060e0c031b0c0105 72
    0x100b8450038801540140752200e105440c00e8440103941004460b05104d58400c0303581142000a03058208102901900c4030030341c00616480c1c44242e540b02c80c501139403080b8508050401c8a10f80410b46140074450688140d806a004107030f02d003015034940134948405440010041d005a0950301800c0c562100440900612005402c00304c1051051042030b060250419800707034100100804a8407100611020b45030040c1c801149a00740000181c0c1031242010b802600220300141c1da50140c0e400c5821b403945000c96004a4810594644085850704070544545a01d504210307400b50514100c0d801c501c0d445401900001348900350740d44041b1003148242000c68120500e15001c10040d4014451500142241c0c10300155010100ea00103007540e03036452008091015100030380383c0c40e42242d885800600060300f4401401c404001aa052014075080100e100f03a0504001243c802040884540a482145800790075074813030f00140c1c1c00c0d82c02d62041241444d00d0030310031010015001d0241c51f0107410442 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 436555791 1250 436554541 436554557
    0x1080309040f1b05070602040e01060e120c03030a03090206040504020a030b0108150a090c122a020703021f140a0c0c1418071808010c0305060114122203 67
    0x4010301040d01d11200848890b42c1c5000c0c5110b12400096081115000080c0392140e03a5000c1881c155000340229000965034000c510000705400e9040640e80c0d1001c0310071601c4001040100000c5540c80d0458081107030160010b10190380e10364040d07008a104d291006100d5800d040d01c441c081012a000b84030710000007030320f070780c0030000710358204e003203160088a0203036101904407081010039070004c00c901c560036a2076550310800791041d2003405100c0801c3d955a4040c00b0101c00e80803203900400c4c08400290b400285111a185210300005160040720f82c007801080b0090851020103400070316500606c824051014250503045c000d000003008000000d4070360007550361786c906240c00700c1909a04802c1d42c10484a10300c0803c1d07aa0411203210380c1c032800c090060b250340c50990484800c103a0340452060001c030440085400300e81908021400000781e902081969662401103841403401e081140c0c80e14410030003103151590718095140d0100440f0344c0528806110ba82c1000c500c1c501c0001903002640030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 436557041 1250 436555791 436555807
    0xf010e2205090d02120703030209041a03010e0c091807030b0c031b0a02031602010201111204140a2d0c120303050a27020d1a1803071203020d14010803 66
    0x744a002d401100120040c036008091800195a9000d20000c9540820740440c07000c04240c07107601103c886c5c0714064420310041c60311043c0c242c030390b10b2080c00d464484c1d401c006250701c09010001d0400388100300205103074490b40380c01400f20a00c01c00c3c1240303100d69005101010000c220045145070080100c0c0585554038500f040041d0305030b6103043c4903210018010003185079856800010b50720418245d00143c0c05050b524070040c3c0c01001c03905045244940040798046510000f19032445c42240100c03080014101c4c04d8120344d40342d02c0301c440e004182a034122600b8440c4403011a03840d02103541100d02729032002040d110081c00650540c404288941303e0f03003200d42090360502139140c001a034210140118040303201c10b0710007980410b008120409802c00d090082d565420341005042c0d402041050f5900802040714201010480300c0da0480d4441002c180c030315050001c11111a00d4005071042c800c4144d01c0002c070080d5101c0380b00b0f901a65180c0c850500380b11032500026000305160300003142d0364280 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 436558291 1250 436557041 436557109
    0x218040e1903140409060f030507050d030507140a0c06030b01020115050a032a030c140d110f060403060e0a0c0611100b27160e0307050d02060c010c0906081f050f010e 73
    0x92f0f810041c09580020788450000b90040190340410344c0c800c0c0002d151a104c100d07024030b00039180710b01030020111f0100000c0c00d41d03050f5105117070302d0200b030703000b031000d21a50712a2004c1c0c3d5080d0b22030a078020446150410100c0c940c40715880019400910440022801c0d1450b08940e000300c3d0015183c1440590007004460354a605205102d0b1040e00e00d8800f40c002505d90800641e05080114003c2042041249281da038140444019642c0005c1c1003003030351718801c0701941c0c80d940a13004540d000681c00c2d022a0445c01303441c44d031103401d4000c0020040c8160540088010b0000c40e0303a0643c20034280500107076461003400300100d450307140c1d007005c506a241595160035809592134008040c050a809258025200480d0120039a042603807641e446c2c161510100e880c41c0f14034408245654a00140c4500310765020128004403021030303a440c000d90319101680d00c0c8600500a51060035140350f80b003040f6030305004402002000f01414540348502c0002c004c80d0000300d00401007441d0f03407809081d1600d42c00c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 436559541 1250 436558291 436558303
    0x1e0303101e14030f1204090c021522080c061006030902011413210303050a180b0c0c010c0806032407030207060f0218040e1903140409060f0305 63
    0x603440112003800704100c08019603104a805002182d455048090381d030350314208100075807026084100c4060034a0020700c40b840390403d0090410380c0c7c1c1003404c1c80130458030011740c04002054900c0401000d07202c1040030b240c204166818038601041c18201e140120748158080c141e03031401207020304001c4c5400c81482d0346241c1c25402110515103450140809070b640115103e1b910780000102940c2e86400312084030386007410364040c4075404006940310b03a1080002011040c05032207a2018811925403448200640b01203105a0150480e1800342001040304245102d4010065807a26860180c0320458142540c110012000c00b041d400d20600110342010445038070b4881500c401e010b5204030300302c82d4502440c8094000b004054001c0340310b1003801607aa002c030003038000340300f0115942c1840c0036030240500751982c2d249204034505105522400380118130314041c1c0403281485400c0b8181c07564280d90a1803074180c54620600c0900c4081030641e0a0700c20200070b44140401e00907a00e00d94580245011 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 436560791 1250 436559541 436559549
    0x50a0219020706020d0503100503030c150603060c0304260a020a110909030a081023040c030902060f161406010e07050a05030a11070c09021b07180e1e030310 69
    0x90701c0341e2803c00c03049602241804112025140c116070381e840f80c04603039010203082e07006a40d05000c001400b43e50b21800040b18803024201c0803540c10159030740c10416480c1d000c04c65002d09203a00c1000010300064019030124041000c400d0b5808104213814000c0d44143c200b1913012015a2103244070310180120862098800001210004190b1928980031a20b074014002c000c0b081c0504000402d240d8280b080c03030070300a48a5041c2a40701441e00c420035003002000b465640780a981b03400b500000c2c162090151191a41d0003904a92506c0c1b1001a2040e55920030411f400305180c2001141001404051280c030045000030000e0855504244059200c0c1c4405060241400010800d0f400a0764006083e2075009170103030310024040d00900100e449901c0780601c010211030403c8030100d640c0000364050441c0b18156040c007100da07801d0741d003800d40d2690680a00d01c140350450503000d615200d103412094024001c482130b51417030807625003071035080c0c01c1d40c0241401c03e400100810030080004410f500080c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 436562041 1250 436560791 436560793
    0x604141b1c0b01030309081605100f0219050d090b0a1403090703021309060c0f020d1d09070f020105010504090c030210110303240a0e1b0c0d020f120901082404050a021902 75
    0x10303d060002032210f000d4420ad101030107681c0d078951038414024045064506080040301101501a280c00c0f51104402c8000d4000700e0451840882e50b5044003066900702e40b8280c0320303907003c1e40d0902c0741464107420003043e000c010320074003c0120058a400f00d255484221070040403880c8030040c0703031000031f8812000154042204411084030440d90000700308580300d009060111000300035a90b003001702d201c000e00c034542004220f4180410594010740204400c40a58020800750f42c0710000c21003514000000508051078242c400d002514025144109041c5a4245441080c013036041050964008172104094620501c80310400f0103540c48440301c10810840c2d01c8808a403c0005886030840090540d104210207041003001c1409035100f11581218048211100c680c0c1942d0000d5643d02c0d141402c003031601908041820700c01418080c2ca1140700141c540340e484da038603900a0b50081c00180402d007400c181080d01095181c88030312500703010b20341a00c400350b510084110400b201e5518010b45c1d45c11 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 436563291 1250 436562041 436562083
    0x1091a040b040f031205160e09280b03070b040e0a02091507020117100602192406051509010e030d1b14010c020604141b1c0b0103030908 60
    0xe03030318145030356200f90300c480703600083c03400c0741030407103001391040300c01e0200c01c0c034080034407140c50288150610000702540d50404c2c21050f0105000c0340d02c4060369020b4040003d00d0b459481e00a26680000d00c551003480300264201407000001d20304107141d446400c12140008041c8264040150406d9008241c203d05600d04812080412804250464100803000010411000310380c030450096a00340000c0c41000550b0800c070880c80310701640b500c6214050b100b03006411500c0340c500c0c403102e0040d94110041c07068054000c2c44010840d5080e881c2014200c0d035402001c40c0d95a81c8001060303140c1920401d054644068a00150890184065a6200f40e1003003010610542d484100c001e07420000000c10a502502494014801c040c8010304501031b508008010700b015030700103110741c4218018441031554400c91500705898a091402c000002e002c42540d011103410454800c0d400515010340c1034003035186944580b0700061086e081140002d08940c0100304000007085a003502e03814540c50072003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 436564541 1250 436563291 436563293
    0x7090605030a020d08120c090102010e010905190201090b07050115060c051c1209050d031104080c36060f060a05030609270102030f07030603030f0309080c0d0201091a04 74
    0x70b40d030030a00310004d204c4c0080c9404c0604214980041d961062240e028412980c103107000c1c041d145403c440d440c1c0d030040d0710b0b0a1503155249414020302c2d0f50950082c01505180301140000a10150b0040f4164107100f2400400102c0d0600d25008144550003a00005000c0c1076506003000d0824040c0e1265007045402c4201c0400310f00007065407005503080c002007034522141440d0660b00307094803020200c11246480c1d1440d003030080100c1e83c40924111690300700148540c1000020540c061401900c2e055840000c48040a040c614040b16210a406000380300b140c0c9005a40e43c01e40342c140f80880074040d40f05040c88498180340441d46000e0508032046404c3c070888003802001400001e124a20072503070b5402262460f840d200354a44031103500c58141ea001114012002e022350703c2600e60341559030154000401080c401e1180c070056961650380c1d0030080030b200d0f00031005080c11003c01e8a8040e0204010b01902c10100103050940c0b403540c00106000c407241c1001c0d01aa0081e1540103022807010017040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 436565791 1250 436564541 436564543
    0x14040515071206080309131104090c0e0627060a050a03051906030302061f05090a09052b03110c070303140c1014060102010605100c14060c07050709060503 68
    0x690345001001444095a50400119900035542c00c050b00000c0c03410078041441c00e804001440151015200d645202e004c411011040350030300e80102103180c01c240001d00804207541c02100d1750a10528003200d400c410440000c00540c8001c610031807501d24200c484901c01102510741e100c2400840c0c4060611104ca0800341c458410805041c2c1010365640000d032000f8002481d0103c1030a202c00204440e54403460042d555050550314031920482000800e00f085c2e14903440c444c10f0301c0c009440c40b0400d1f01c4841c00315028019a03038003180c65001c0c0c916680001201204c00c02e81d00b0601e03100c3d1042800c0a4035000d412903154a6040321140c00402490716588400160041160351500c2c1020001520b12540501c074024000685c4044c01858600703606236409402000300c480d000104480346459401c0160300302c440500c0b81640003000c0302c8a4590507400384c411003400c0c0f4040c117070702851404148e00c40c1c2d00700501110380c3c1120366008500002401001c1050718041e0210490411250303091030002 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 436567041 1250 436565791 436565803
    0xc03141303170906010810060305031e071403091c05060c030423030a0306050402030f0117070b0417010c0c03141b010f09020f011805150f1201030303140405 69
    0xd8031411112200c41020140324550001401190740d80071000390920700341e440c2d203483d020b00c0303060303078511440c042542c0824141c442c100c1166030010040d464408456a542001142c0700e141700d2019009000480100b54407007614007510b14810055070740c0b90b004408020350060303402c1c950300328420280c02d1300e00040d900050641c0c00c64551902d054581c5ea41c2c2c44c04000506d00c581c2c1d06090340301c0e8031155106600000020b880900340c15101488000d88a1003840224003046072507083c45018500104128600180c420011400400035550010740358443d616040d807003540038100004062440546800c028400c60324a6901840c180440c2183e0b510300130070b040100b80072031080500004580480340740c42c0414145401c2500700034001018840000c20013041c4450b0103900403208100751583d1907100d02220002420005145182076081c00103000c1d1698440340061450841044514528940701c2d001e4002031440c1c60000e00d0b95811841c0003000d9919418200c82c0c005480410711000400228030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 436568291 1250 436567041 436567051
    0x8070c0506150d0c351c1412190204080303010e09070e0f0402040e071a130909080717040e1f050604060c030305010b04030305070f0611031302040c0314 67
    0x20725401000500000c3d88644424002041c10040300c10000d0184221140c0060542d8048644011410300e0380c100f144010600d103103010581c100441c101c180c202131100c802d071032100a24148070607074030300c03107108419600c058004002003400c8010004264200003980110b0140840250301700392a004c5140d40c0e23400103000303004e0a404e6481c001541e8000800c40740c0e0040113840030412080c2804c00c80c00788504025901603000c2da04125440400540014400049800041c08103070360032651038080d074013078100c0780708190405255100000c842c18507000d5000310b98041c0042035070f102414600a941c000110803120790420007880108002510340f04499400200020101003d0301035512240b003a802c640c100030391080021501164041d88642801c1950340b29803420446a40c0320243c003881030180d0b120007400100d0030000000060071079904d01c00f440d4807030304000c941035022415903490b5400445039118208a04803980c1c081d85024024044100140d0404210003600a6030600d0b40d100001c213 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 436569541 1250 436568291 436568311
    0x7200d230a17190213030203010b01090e0610022b020f06040804120f020d03050a090806090a03031d0a081e030f010e090304030602030a020a030b0619030b06040b0a020a0308070c0506 80
    0x80054001c8081c80501c4450f00c1c0200da003159603844201c20714030303e141980420790007580b820016a4165005840e850140d5146000700096075403600200048000c100c80300d4000c60003907030840800c419011401c01c00c0b0034200c0b50445c1c1c51303100c030788030080c640036801840d2001640400184408600d01e4421a002d86803075085071030360070005041124651003000002904003106041e20030038154408041c0c14603404d41c3e80c0700020aa911454156140000c1c0c071203a5203500281c07111000240640c3c03250002c2c040c03a0340303020040110608a0b5007040d014650584440d034000400d6940451500e002c580c480040804007811410110490701440d401402131007441481c0c0004506100020019a802140e10000540d84c80c5014140d03c80650032200945011030b0928482804600e40a000d94401c002448000960b00d0440c9078110041c0000725000c6400c940c0821000c5007500030b0788000d284003040d64004150440c103c0c036000304400002031007042004150503410001420128482d07421159140d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 436570791 1250 436569541 436569587
    0x90b0a12061d0a060f08030f0901020c0909070306051b071b0b070311060603030702031b0103060e04051b100f03020d11030108060907080604030807200d230a 69
    0x29000d00c00504180e0042c0a104040b80300d000100720141ea982403007504541c0050042c696260102042e0342201e005e1402d16410a00c4055107060303190002c0e003d901014411201a59101b0010404108040d89d095245800c0103c0500c1032040700e004842e0401c04408240303185100005031104c1501070501d006081c1c3c03c00452104610030709070b000901901c140034400742e44184610303000d40820030181c030b586100d02a00002516502d00031085d1000a41c002e00076011091144640070710000c1c0300c8440c1414180e89400c04103481200d4601030344103a100308014164141c04101031500c0b0400b10501511401c520040600f0b21607101c503a8940006403801c0258407000b0351a011405800b00e2601e040210001000000300d9980001d203042c0140348800c03e40b0816031310703110300c0c030340328075080f60302401054000300400c09940c424090300c0315040704c2803441034070b84054296290074603051500b03050010300b904509140302082c0400d0703003402c1c1c64446803051404001d00d001034500b20110011007c0200e00c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 436572041 1250 436570791 436570817
    0x30c2402162108030a0605030c040603020a18020c010c0806031005010b0406110c030609070e0114061c090609050f0c0307030f0b071e0519030506030601150509060424090b0a 76
    0x1240d0300c03942c0e6489000103403a454980420740003400a0701c140c0d8801d2060394000003042c01d26105180a0300c0e00640108100c80c2000701001008103a03803283c0c2c41150b4200328100c8100780a2080150200385072361142e1076420480101840c00d10408041500b01e13140c40010001624840b080b5412200b42e41010615840900310082c10508181880ca03054098401001107184000c50000c00351340c0d00d07095544299803138441004101111a205903080072040081c1803a94499030140f01011714000400700798031801c4c1d80e0318410307500194400c40d96980001c0e0300a0302c00e282030185c2449500c0c143d000b0101d4030700c0c2d612840d04030500084083c0c145a00350f400b0500d041e104805008850121a41e001c15203510781da4002c0103030b48a601201c3c20a84003c110030103080c42ba0040f6030240c0e80c01030040140e42d0a1659209140c05105480000c0c004200250301207529440040c0c8018102600c0c454148807815103040f01106c0400e40c4d24080141400041c40700400480503035002141c2e0380b070400f103940d0032 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 436573291 1250 436572041 436572089
    0x80109050c091e0415030c05090108060c0711040f0218030c010e03100902010e09040c0810051e090c0d1a18101a04090b07030c030b06040b03060a030c240216 69
    0x1007800290301c40c60b05d80b1808014025103034020012030750144c841c3d0319070382e0360f42001c031780c03a1801611202481c0d501000003a0201e9103147c8801000c61004100091150303818413050126440380062010300c242d0742564990514091007490301480003800c0014401480c0d50000f03860f44000086240950350340c18404c001c0da403203240303404104803000d009041c840c201404c2c42100f0358103030b1203203030103900c500300e81d4401503400e030f00030340e801303120004c1c1d0b80104000c2c1510941c0c07160000031300c1c82c0142d205400c00400f0076a5200c5a003200323140a003902c0210700055901001e20410b00a0100d00c986543c0070902042130000541ea100404ea603400c0019481084141881c00454a02c91140e000303007002c8051082c0132002441900950840d1002c000d80c1004040a6040e01c0f1000d00c0f0651084051204102803403119009603800f030740051035446001d48950340c4a12426140d000b6954030031084044100d1000011a04070455010340000c10360142d1690741c0d030071900c001e80220303a103030100384081c2250011 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 436574541 1250 436573291 436573301
    0x105010f110a0b09100b01020d05070f060b060d02042d05120f150f13020a06110c0301020a03050f0c070209040201030f090b090c030d081605030601091203080109050c091e04 76
    0xc0c3c0007204402d02d003000c6445a60314505003803810241490810041d040390b0000032400354412803903d0705420001107071989103045081c6c400a8805503110100b60b81036941c0c150040c90b0f20300c2d80490058503942443c0c59103007020800c401001e00c0440c0e241e1400b031002c1100d00308404462040358040341540c2e1420a5904007500345c0f800a010740f00703801320061340c0020804094070422008d601840b140da95900d52002061840c0f80194004c4400e000c1031010a100306d100c180012014003c48024180784070200f422a4403030082c1e40700003542c52050100c50b074058541c0356080400244803c0c101b43c2d007500020308500010304001c0c14543d44012000008501e0380000e03150941004144940d8501200c402d6101c0e41c191038114402d00440340f847c4c010b2070068a0b000c2c00b51903400020610444841816240ea60000e0903482c18000300aa0004200700c03003c0c03458169501c00d50310448903501d0480f2000556401404000715041f0501c001301440d22520710341545100042c0764100c0c0511008040740c0241 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 436575791 1250 436574541 436574543
    0x40e15031612140a0201080a0f0908040b0414010801150c0f1e020f011d0d020105090d15050c04030b1f180e1005011211150307020d11060105010f110a 66
    0xd0900e080080c41c2041000d21414050040403243d8481c46030800480d116610700000a01058100010031075102007948412492300344c120300000c2410340b80e04c1c0d40d0503a401c142c1c02a40d1300840041d0031f0042070014071a401e8800700131700304490745504004c003104180310310651000c10040d10a41c0700c01440400c0001e4260a0f810010080c18420350324201e40001c00442001c0c0d0040709240c036283c01a52040d19040ca100700c034403400740640d992000400ca0020700b580b4003a07040100600039244159030b50b103840c10440b40300d0442c0c40708541300d412011007130303c4008201e0400d5070310a000400115600c90341e4541d20940b0a583c0015621013000101d00220345508400020401b011050380400300f01da004002e800d00307540846896281103020034040e10024080d40d10071864242d45440045c1856601041e5064002e000118030601c1d00c000d05c94070703042142d1180050303002c0c0c0900843c0e240c01800e049801d1921001030622507040c5000608880d903850511810020420000f104403482804154042 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 436577041 1250 436575791 436575823
    0x30a0c05130303030c0807021b040e0109021c0501061a0a0528020106030c140a15050d091112012009010e15040e010b03090a0b060111060405061b040e1503 68
    0x19141d00f801402002c640381c4140200da03092012500c410300000d6117002000403c000c500300e5020044c01e00020300040f41904a00d50b498420040c0180e60708070b001008412241c0c2131b4960b043c1c080c02e1032400e550495001010524502e0380030000080c0c62001c6640846050604c5540c40540e4070a021310700300c005405d11045e50075561080401903064100008480c02640411000f586074101200240a4510000c4d44801c0410f404c000705003041240d012450250700303240c2e00740381c4d1840c000c00a8a4051000b120070204000c00b0f000a8541000d0221068490f03070000c00a010144a001c0b21207820849480180b06012803441a030740e200e0000c0d0714181c100a4107a0750400c503a00391510441d000307801130340124080c410020428a540c0c40a8a10668040c0c008080c074501e2902c1d54130394800007030311480c10001406070b0300056107001c0140c180580d209000512480c0340650b44c103c0b400301c50b481040f03c1040c003000208165201d0500c500e402c440321026144404040c003000038a0f0011502011840c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 436578291 1250 436577041 436577077
    0x18030706050d0c08160f181508070806030c0411040512070905160509010c02061b06160f0e10110607080109060909050a060b040e03070f020a0503060606030a0c05 71
    0xc0303564854003404180000003000d010b1440c3d0070700d059818050490341034420601e62a81441000c0c85170703240c035800c0e10b0a0b003000d0400b2410445202c082c81e4880d00100c8586400030b4072075003c0780d03000e01465402007007450021803a042c0390700000c1e2503004170981644078940b00e13414016818540720480d0b00601c80203064641c1140902c99040e1180074038812081c94501d008006050300c02c10410030b00d00407050382ea52070320b406a11401501d000c810381c1c80698000b5800c0c000c258201219081c00840200c401c0c001b0700051500703140c0300e0f03101481080d400d030400440c0500310700d03070a07003110410080402c111034400011b100d141c001c440c030401c480c071905610b00c20038040c0840c0766000300c08907058480d042d0041c844c1a4a41040d40259110b1040c01041d952141c4030f000d022585980c490703030b411540200301042594841d840c4600d143c000b5103042d59848401d449500451422803008402031506070050007803442d00400090b1036010040001003220b84940b200c0003200e1081d411101c40342000803070b90300d0b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 436579541 1250 436578291 436578299
    0x50304170405031506100804020d0b090a061122121511031608060405010b09060307090302030d05091801030b01120c030507060e12060f070e0a0302040f050618011a180307 75
    0x204d01a00350f415600548040f400d40011502c10b1000074030554005d41710310912045607030741e024003d500425913a41809141c0f01c0703400040c0303039008811403011004032942c0c5a04143c42074481420001d03240c144840c0a03260708010141c0503040e5a101c0d503800040c0740e41003003000e070398502c003030b11010f00c41d04500040001002200f18110041540e24602a81c0b1003c440d5550020b2008030344082c014081c00100900c49204103150204c01140c0c80b002c03628005850035900c3e804240b03000000340244011034404108480307a401d081c0900300c413501c3c07000f024460130b5166881d02201080d043c0100002500403030084000c0c0902121510300450f070040031981010350311800104402d1190301d20a106510000e20301c0b90300c070000030b4510702403c18403070842c0140e01e4459064400040c420800c035008030401000101507034517880303451928210b02c4004190f91900d001006002494903030f2611840c041e490040c01102030009140d0150b080b00e0707120075904c0948600c0041d2124041c3c0b80e5035414802d81002013 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 436580791 1250 436579541 436579573
    0x9050c0402220e070c110f120c03010b1504120201091a19020c1f12060b04080106120b0a0207060e060a090203071401080a022a0f06061005030417040503 67
    0x40350500c2d0030280302041d11280a01010841034403a02c0000d2405c000390390100300b00700302d20420f0f020700500b180c6da20028080032402071071a05442c0402e40e04850b511300704500f82070142d4042c540f4222213902541c007500c10b10746c0c03250149001340303503540d001034910004590149507160050600d40c080d50f8180d1501098411142d8809803c03c410200040540e1311194000201000e0f203500c0141f0500704128001c0c1c8448015140f90301240400a048c80d0140c039164140c49a070000c0c004554450b0f0341d80d400e107a00c290943d401a80b101b61402140414400458944a81d1a41200c400b54025903202030341c1c107000c0301800c50664040c45600409051000340c0119030700445d0700c64426001d0308c02a9a89003030701d072903c16000d15028045141080051704031401c59000341180c01c0300c1d0b0b010912202841c0c201603006110f4503c4078801c0c0d40b203068410850300c401c0003180d5001100b00c5d000a0404e528040007001400041c0c8018200b031225840c800300c00a00d00183c50182034007401702d404c40e00c99032900d0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 436582041 1250 436580791 436580827
    0xa14010507231506042306280906080c090106020d0f02010b0907021e0d05090103020702270118060b0409020d061512050f040302370b011503051909050c0402 69
    0x4c1403090b464900000401003000522118200d1a0000c4c11450359840302444210320040c50714148040398015072086100b011403551001c3e21803460b000912a0810301e0300340c900f0345902d14281c412016800104800d66000810001c0a10145401003800c4001c0c1d00903405890b40190050340100a00c042140442d80094030b81c0f015204040001c60b0f2110b002c4000391145c60340c0750008001402041502200c0d40a81c00800e0301620207420041411081110201c0f4032220202008852051000401914140680081a01c80f4040c0e00f000405e240a03614481489640b044481c80da40205124170160342c10b91103440213105d078001294240018038030046c95002c00c44240e005061904010071030000d60220064416a8560010b00e0540c801c1540078090b89550490311132560802c0e001c4500514820003580819441902140595410041c518a40700801e6030107504051502041004101420b6840120402c3d4090002904059800d101c0e09241c60303040b220340c005e40006a480001c500000310 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 436583291 1250 436582041 436582051
    0x30403080909070921020d02130c1e091a13170d0302040f030605180706050901080105030109170f0d0207140610030b041e0f050c0a140105072315 64
    0x8000d000d940e560700035281c8000c5405503038105c2404110190303000c2280c0c0b245410341030004001d480000e0941d80000d20308801190403955103506c1e040d0402815030419400c02100c00c101d41c290740408150900100b10030f859129454400d51f0380201c450320480c003002100d0040c00498800000c03903403200c850341c00d00c0c080125205c02c980306030b44008d00c189102c1c0c400c2c1d80a40e000500c551034135901d5522000042c1070040e02110500c8441610828160410000c88000b0025600c91a45581c0041b0000d004940160300190099043c05050b000050020380180c3c80c0d54080070b5099103031400e5644040c194050700700c40041003480003e10a0071b115510110761544421001115003980c8ca003e049421420f09210040100381260045000100d002060b80703a15084e0001e10340b1801c0c0f59031140d10110305903000030758070794205400c0e450356800d03c00d0103900601403a0503590442d00091000034241c0c4034440c0c01030031215400541e40c1c2e002055606080301914041304440c446840700c2030010b01d900741551 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 436584541 1250 436583291 436583299
    0x1a09010b040806060d0c0806011d06060a0c061a0a1403070602030901020d0c080909010b0c070603020c0c090a140106110c090103020f060c0a060203090106060801092c0a050304030809 80
    0xd1502042046a0607100c42d500540b03000e4a458007805105541c2c0d8000302d503508901c01d00450250350030072143c0c1c001c02044071b2102503c0c68505400107800340140c4114040c1008110040c030107a0003421018500d58440e5000602e001040315004e413103000c5480c3e01d580805601c90000703005031a2400300c02c541c5000c40a65650a41c1d885050382d81c0c2c800d00d048540035030040000030306e000303005045d10000240200d207220301d00742007100000c403010030903006071081d0303d40841e07600221402082000d0103004032742421460120b581a24941d038951030400c55101c0d501410009000c404960040c0040762404c098183d02c950b1200c50140500746a04018245480755600c00b8820389070590405040329005400c072021514044107006440d4480a6904001c0c85822600d05c00240e03d84000c0d441080030000004615040000090201c24180e0000c088241014100341b0b040724801c441404c8050820a01100740300c0e20300556080c0600400082c246010104002040c00314220043c485c50b00211 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 436585791 1250 436584541 436584559
    0x603011418161b020d12021c031b0311031504060305060a050603100501051302030403031b0509040b031b04020307140715060611060c0901020705060d091e120e060702041a 75
    0xc08075029142c4010f0296020002004070008100c2a8113140c292000034415600480d00c04001d0603d040580d030360a90001340d0302d55500b42c5070760000080c507130344000c0ba180500c5814260300c650001e80c04044c24030155080c40000143e402c0d40c0d81d5001c1c400855102d010b4610900e8000b0b08440201400c4070424003034058020b490915a4032071203854169440108901c50500b40151030400a40000307104405166817103000c880619828200b140c2c00351150340d40d0700e50740c440c1030041c801560b030511f100341d001f42e000001c0290060000d0108606064094900589960765400200c078030728081203030449a1140020242d05212a0191102e02950b42c84030505c140303591800103c4900078821107420654100002207228805854010020000c1c1441201d1009486800180060740400d4030307984515965180d60003000040c082114030025058442074080b4032070740f1000000d07415001d007041042460240c102e0350b503851000f650089038000c4c0c01007048014111423061004c5d0540c10640c4038460700 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 436587041 1250 436585791 436585817
    0x103120e0901060801030803070324030302101514030c130605032b1805100c050c0102010207050a14030f0d141602070e0c0c030c150a0902060301141816 67
    0x4807000a0490700700f50f86400090f803030354179807034400c0d0000342840e010140c64016591610802d0081401c1c000b4410107611801407440c41c0180c5041c80e1200703081f07101800d19524801c00a00c40400d401164503005c00d00548001d820b0009083c444005c0005910080b8601d20b098461059400002695000d804458400740080d02845a42803855201d01000c40317100c0f802907800344170784030203213881c0522095035001c15211070001d094198800111400510025070b80003c1c0b2004114100821100780001c41c94410aa180c00d0f8030348054690103445864551070210a04c0401c0085956018a6140c4140c40d41c03d000000300c0508503d81d0006940b81081011500000f100c888030781c81f00c1900e0300208012403130152807007150070006089580f141b4090019807240a42030000340000075055014220b00d4500400e00409120050a0b030340c0ca0500e820b10050042e03c0e0101100e06659030340d103800c8070204000c4000ba551041a05d0762000e005494014445120048000001c1c0e501468881200b24007007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 436588291 1250 436587041 436587049
    0x10e090c0117060d020a0305060a0f05101412031c0c0e030d050d0b040b0d1b1a04060e030316030f0e15090906150a020a0212060f0a0b06070501050103120e 68
    0x300c184030614500e098400b20f80309280c032003820300c022807010b02402c0c80999652616800c022044410041c6180c441c0401c0300c00c001980700311540140c0c204104180f542c14241c510512092416000b0f004180b4182581c0c41006d08105807458100325080041100100c40b21540c00f41206060a5000c1101d10100c4480b41ca00483c110140c102107a5441d07080060341016000644224200f0b0380e000340e6100b140b011181c13140202c0283e400e00496007810100c07040a1402c0380c02d0a03961269400e0340c512900080c5070601c0342c0c111000c4441c0352421034040600342c000a801c5102d6042c01c40d0030318000039082c5081540080c01c180d818000c54440b00ea10103a0841404200a00d40490100041d0100305881c807a25041054540260000e803a15000c0244202c5000b03090748142e80030800359018160410451130240f00006a021010025020702d09040c1d4903070300d200401a210110b42c548900b2960101c2d100d44040e078510030b41103030080c801d6594038248001d411550580e0040000c0700301c40c510199080c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 436589541 1250 436588291 436588307
    0x405130b090408090a0909110a061106163f09020604090c03061205030301091b080a0e0f01060e01050306180a060209060405131a0418030e04060905010e090c01 70
    0x503015203500065a515038030143d00c0c0c0c4c810300545503c460035140120b82c50515126100f580392103900d00780d560000010130440c41c614581d001008000c00f082c1281d4102c800440d80540020201031105402c5481603c10750341032410318424891408081c003441100c1000915440203480da4995276098100e200c0d41c0c03003095488050003e0b4001030108001c1090386501d070b104100c51445480e000510b41e8841c0e02d00144c030340c208003007501c4680c808001400810420f106140c0580b84404414840900f202c801030425407004200a451307a41c0c44c3c0f031985200c0018000c00c1d10741c506c0c00000b0007586841d201c02c802000380c28003449000744540f40002d0000d0301103010b92101000e13240d0003091000e00503aa1200039522041c080b6410501c14800000c55813a030b40e0303450080c0041c8580124000d0060010703c003000310030802d9184a2820300038002001c094460001503015014907111349205003400215015003219480a10100d1801c0c0000038100581c400c540e0158891307400340c0311000e000900440e5411 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 436590791 1250 436589541 436589561
    0x4020909061005010507080c03031e0906040b0c18150a080603031e13032004150f1404090209250504030b0604020a03090c0303052110030219030b0408040513 69
    0x15503801c2c041c403a643c010b8001e008100c1c8200d07551480c082c8240c03000303415900203580c0d20b00092040f242c2034688100400c01c10740d11034500c1c001848030f8582925501811000035000c0400040700040d00e01042c40c0d1448080d00d130b05000f52801151105001c0c202000d580b04800031800a900d400109096180100860718104007111040d105028410f00650856102082c04000c0400c40400040003600c00311501d503075034240c50b4400d50549682002d02054500c0102c03d0500b440e5507400502402c4141500c0401f500e10482054482c1803038000864002c094200f00654130003c080d080146504549010808440c101c048850340d00708a114259058051404010480c240c2c0c0c01c0001c94600b401d078090240d4007280d14010904241e00c0e1941244c4c0b4030150819000540d00041d142c0040c1c3c64140310207003568941144010074034240100c100484840e0000a10035600d006200481c9809540c2c040c01a5411001500e524141031801305410b03172062240718010340c480c800c42513880104c0d100f001492 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 436592041 1250 436590791 436590811
    0x70b1b07051f0c0c080102120106020309011e050403021503060a080a0f1e06051602071a0d050406020405130605090604180f0213060605030a0e010c090902070c0e09060402090906 78
    0x1d4400020251810080904030100100d415000f400b040c0c803004400c00901d02140016a60304195049005000050300880306542c402c0207850801d1b41d0013111440107419042001001140305c5404462600c6982d0000c0c1d44040302d074070000350403030544c001540145802c40c1c80002c56692402c0c00764403400307000ca01030020400690300b0004111103074003116803521340310300403690204030303548102c01c50388103441d9148075203800070041d0602030301001000c02900d41d865654074402542403c060240c0b20b00040200601d032250081020401680c054802130300005021039101ca07a10f07074200e001411a031080511518000340403580c075082901c58450008407804280c004949a5203d800d0480302c12074040703820807610804090511094407c4802500c40c81d5500f90b44ca0070b040440c28155000c040042d41180d250200300100701e500300d642e10301121203a01000d078980c42d150030704075003252155201080081d4142c0030003c8001d404038240d03200c0c5200702e85c6a0038544036079071000d40c1e84204480d40c11007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 436593291 1250 436592041 436592059
    0x6140405101401020102160515062d04020405150c1501051005070f120e0909030a02210d0203010b03040212010b0f0d06060909030507020109060201270212070b1b0705 73
    0x8000b2402c4002d80034001800003500d000e5148540e036260b1105400265034541081010b090030a440411a60b0426811100c00070340500c50900a191303086402075074183e40100032015010307a112501540c000703090040030f0810b4104c002d50350241c02c0e441501a1440d03405404052030341c0910030341c815416264050140c0407030006c03505040d0750070362203107a099450a182018400000b0302d03e0140040e10001aa50840640480c4060241d00d600c003821540e00c907041400040c090070313400545e0462030910845000b004d10160302120545100e00101c0c403404a00000011503030000180c003c4d4000e03071083e1004101c0802500c140c074221030280148030390090031500b000060740b400141940c144c1e40141c0c00019030640d111311002c210f5a12000480c045140482c0c10320a540e0803450b10b00040140b8002800b032a20308001002c0102c0c07202e07940c003448009000c0060f00350745504200101c11843c01040b254429104d900d45802600302c070407003101c4295452036030034402202013850022200041c080310f04c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 436594541 1250 436593291 436593299
    0x4090504050f0a0f060f0b1905100525020114180f030a1101030f020c03180906030f060c070311010e0703050118080403150b0904030c0203010b10020309190b0c010614040510 76
    0x2000e04a000a520003442d2102580b1a051303560503100d083c14911884d110703008c5482d00b018820038440d450f68890501c5018444016104a500410020341031004032509580c8214401038411040107202d00c8203c180c080703114401a041d84c3c4000d201d1100c1101c9000c0071003014001c05684911071000148407003401e032011002d5500030f0b084400269a034a002509100c899420fa44c40e40d0059482d0030440015448601241d052000e819908088160060315481c90401d24103035403040094003028613284001458014984201c500001c0b0701010301c002e0000600740d120081c2d98070b156000c2511a94038003100c020364401141035110040e0fa1001241e414030703185407a41190a61180341c481101a1212000402583d800507018812032007500c9140322441c40c5e0062508560042502500a806605660f6410740e000800e4078042002202c181da040c2e4030068a41c190b000c8036901c03500d4a2000403840800050381134101d03500303a0381403200e600320400c0c51504200c00c1da941070764101820304509000340 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 436595791 1250 436594541 436594553
    0x10020d030b0301020405041a04061a0f090301020d020a18080313050108090c03010905070e0901090b06040b0d0203190611040510051308030d09120e09061e030304090504050f0a0f 78
    0x24480760402800141815070b500081016100c1c858241c410749568900f00386a41c1c03525200c2c000c0a03040b401c2d002c206d9040c2021920240d880307004680c2c110510040303410b031141e9034250104c90009000c12002e54480d02d100c4000392400160a0300c030b40920300b1924011400e84400401d0712103108000d100c1420182c50807005440e079440280086100e1700442c050384c3e015880c24043d1031a03881c400c40040042e6860130314101e4a40c0000b0f0700c066400e9041c100300c100450f1f01c2600b501e401080071680043c03003650701ca00181140307580e2040227415000359802c0c8504010008144c04025024010034840307409000d41c000c4484c4128042e46501115651094110303900c50006004180c590180f10300b001622000450302d96002180b9081c104e58403042c4040800900c07001c0703141c0d8006981041c2425130803090015000e41c40052200740034140e00009962902c04414a6841410018040d00e0f40e46032a41d4141015103000ca17800d5880d84100e5405141e01c45001581d908155000345001c00240c4c42541d40c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 436597041 1250 436595791 436595801
    0xf290915180712030e130905060121020310020309120429040317210402090c0c07051f0f0f0905040906290a1a030c0705031209030307030b10020d03 65
    0x71041e42d12408102043d207201ca80402c054580c020307110008030943c240200049411154017410155042c08890070000d20b0005800c0d06451080240ca000f245080a00c004480ca048101030341c18810710010b43e41354a2958015800f80340c2520585560081c00070401c1c80070301c00c5100f003134400701e0820301402283c120506a0800b00f00300c4a4445c2c42c0035a60303290360440c7c0b0784102d0f00c022000b4002500310101101d004500e045000142418401d92401c3d0b00059840303039000344502034071b480000e1183d081101c14003020300030301001090340e070102c1003c514058001402203008000700303140403880320205002e048008062261a60740150507402c090501c009422605805c40b000ca0f202d0706183d40b0020f440313010a040d44205441c11700c0955510303080020b00c9446074000d00d0205240328003010710505400403280d00c90760001c0e441740e44142a01c0c01c0e40c590701c80c04003515045814081032224980d004001940510304a0740c003804070111120410204403141184407015a00014a42e00c01d540240c000b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 436598291 1250 436597041 436597081
    0x40b01061107030f0501181b0f08030a0806040b0d0606050f09010509150d0f152403170c01020a08010801060b160201030c020a15020406080a0c02030a0c0f290915 71
    0x4100b48552190647d002c8071302070412602540c0140807403a406071a041004003c0014010b1100054a460499a100d00c107180301c810030404400b0014005484680180342d00c208003030301403040e00045041100040c0481c3c000e041c03040400d4940d1483d6850a0300b0802d05903000109800c00d2901d40c40d107540b0090b0608030a0302e4101c1e0329030528001241c0700b14410100d407070040785281c18180e40310071510b0480c2e00d941304121304602a00060700410758081e610000340d0b07911051004c0003080c40c640d001140d00034480b201c0b030258000105422403d511182c098102c84821001388030060f100c400d1b0b0720341402643c4a030510b1a440c081c00001540c442d400c2041405090700644118040035124012050f9540091004140e000501000140e03880f148030f0345d118031402d80400c1402d254903002901c038450ba120060421070760007410001c0c0a200700c06001c65903800b92106d090030640070802001c0b5040d417503002c00303c08500320019184060114510120a041c038100b803130720340d640101e00d55000c41d000032 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 436599541 1250 436598291 436598293
    0x22103010e10120c1d0721020403080d15090501060203091c0506070206070e01020114040201081b030907060906031505090c0f03100509010f15050a0323040b01061107030f05 76
    0x50001881140556014205401642140441410014170811030703103007100080a500495420440141e07804480a0380580051400c3c44022000000100103801550400740c51044001803031030701202243d11090851544070980c09543e0f6441c891403044840034496040560002c00c21241249451a40080c100408070380c41c41c0301c82002d4460701d1a0004c100c41034800b40c1d202c03034107024645802040380700303000d9400d00c003d101c83c00c0d150100081954015100074180100c0c0c0d80030820007000e86209070b524500c54103080d503c4e8508000c0e06603880d0b04500c180360215081660101e01c40b44640214201042010300d070401c0c452821040c030500761801001c11003c208140802c0c1c10608090000350301581d0003a610540e03007420b100410124580690156802c814911000c0001544484003004010550304015480703062404003075024100e9540100000500c00034510030f00810120a1030040d4015251840144e0301c880040d100110454114070081d0f0000c00c0400c0040c810108142c840c5201d00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 436600791 1250 436599541 436599571
    0x601170f070b03190f0504060501080c0d1e05060c070c0e010806060d020102010b1306030203010b010305041223040603020c0d081005090a11040b1b0102090a0905040309150e01022103010e 82
    0x100d041d00440728105508034445480b0007c0c0b205010f00c0b8005d86000d442c030803000c1c10404490000041084802d0700c0001e1903415090481001c3d250740c2e07201490203c6d08181036034501c0c5054004070485501640040720440600d01d40032541e400600c0c4018180c6070a100141043d480c1c0c941004294101008101d04642d2100c1c40402203440e142140404060503c1b004a811400c0d84105403d40340109107150415151408101c0440c25801002100b1750480c280000d00100001c02c0000e0000014021000101e001500040b2a54150b008200c1442c0c01400d48d01c44041c2c3d0306040307501100c25100000740c3c40c441e94090000d0310300220706c5900240d00440004100e038400404103620341099103e41220040422080201c2460000c0001c2019120303000310702d403c0b60000003806a450310b000d41d09a0a84c1c07440000c007054094009070000e006142525401001d50040090600e08054480e500501600740c40720650000314045402640628184d01e0170740e07081c02400400c0b050010040e0b02d03514488 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 436602041 1250 436600791 436600831
    0x120e0a0b0c121c1b0c1b030c0b0a020c0a030201020d21061e0803041211040b1305150a0b0a1b1703220b0115200601170f070b03 56
    0x904000c003411200c20320321060f00f101c0e001503042150311a00c80c80c002680b40e00c0d620104281d210b00301200d040d60084a440e00a01007100403c02c4091603000101020111100424140300e848041d00c5e00c1003440e801c42da10080c142003801202501440001d016900c00201456034074045c5060300c0898500300410345c1120200c001060540e0516480030440c014107240c12091000022003174000f41018000540c0780c6440c003019403600c0204814046c00b210b0000c800c001e40d82d940c58100b0f00a682c0e00902c52501c0280d2119004000e00050b03c3c04030f400e11401c0f904001c94140b003808002140c0c0040385542c00c0030301c811815644501c0c81b1a180080c40409110040000c40100716944480c0c9a0031000c2d840e803500c024007044112a01180302c0c1038a600b030321a000000c1001c44800e040d2040c40600400702c0000351000c0c0e6810852101110091450b40784a984840000810b64120b44c0d12541c02040c4032400c0c04065111241e60010503115040504140100100b140085410078284280081c64030b00b0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 436603291 1250 436602041 436602073
    0xb010905132703170702060a1d0303071806090b0304060203090a050304120b060108090c041a041e200304031b0b0a05150102011512080c031303120e0a0b0c 68
    0x400816480750a00b0621070034940d01952102d15400d5903507810b54a824036440203560381e0401495507030240c0c0c50344401d031814030009141f4840d4030002c41c1142d89a0910040103040c45680006040d1115019400042c0b000d115104980441d010510001d1940c0c50725140c29002c0e50005280c55090312440d50840c0006004000074401880e45480041c224041071410201c2640043d00d41030400184e4410b0018040000c10020b41c104811a800074130707282c0f6060b42186961400042503440381c9070035242084088403d40701880c1c002d04103070030040c5a244e00800810140d0b14820440015000d000140029002d036000e408501d1041c54107210801e900e81d590807020b8022105c5940c0740c6c1c0c40c6c0c0305002c4080c45020300b081c400002400280003140002e10f84a0082d40180f10700d41240201800e00d1b801c5c40005402c841c020322001c4140c0381e80fa11021100c41119060717100c121609040100501ea82d0742c800c690039440c6900c01001c0c501c0072854100340b0403840e045401140403038001c0502002902d41 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 436604541 1250 436603291 436603331
    0x41a03101706070305090111030109090507180207170a0801150306090207060c021c12150504021b060703140610020f0d08060117010e0708271b040b01090513 69
    0x207400041003203180109004050340c20290003495681c2c1070120009048007164141c0341501e5090b00c00040941b51400c0c15454034140d41d010942c0e85c1c140102c0200440c2035500201303031180c0924000340b011501d50720780c02e07003d205910b040380026220800500c44508010840d504110309880e02041094072529a0b10499004080440d0f0141d510041510b4058050240110765030b4940000c0030340e20804d01c4007034011303c11041842183d590b00e402000802c60003102040151401a10464031601d646240150303a8206494416583c03140b40c0004200612074010a080018075010703401e1552200000d0041d91400d07407520005500603c20f00d080d080c9410811600c1d41c207001e6441c0c1c0784a08095001400d03041c0b60350b29a89801c1c41100c0140601314064070308030b07003003d1540b030240455a00c51814881020f07000d05a48030070f07590302d82c20015003000056a800103035035036904e43d50100c100c030042008a131380103a1800d02254840f001040300b4a40803070000d216000300580495440329001130890070344 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 436605791 1250 436604541 436604579
    0x726010c03150503060708190603050601030506010614160b19020706151401020c09060319080306040b10080a0b01030b0a03060e100203010509010b07061e09110105041a0310 76
    0x40d0340d540d1020000100602e80c0c0000746015800f40c003450030a2803000f404002c0c000d10300e049485012859004101e0603500c0a00216007080c1036078001d503101d1505680324039086c858440081c041c001c0b40e01201c0c1c0f00c44c0480700385005070000f00e0802c07100381d990502280c800030903450f500c074040c402540e80c40842d80022300e4200d105081c0042c015001452100c410741c0c1b48c0e007141348680c10a001c00704450341c000502c985400070844100b425a6640800241740c90301c0c5084801d00740554085a0b820000160007550080310100c07000d0050100d001e041c000c0e801101101c4a00040010340815120b508651294101000c10f25011911210a074040f5820124607881140d4540d5620707810899282c1c24010904004078005080d49194940300003d60203101c180070304113900800080e40400c02c42e8a601500c1181095098030410689086040d401001015015150b54248021405041d0b01c0f070001c132030a03648460480d4240242564503201d564100421141d10640d201e0008250805410212074203d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 436607041 1250 436605791 436605797
    0x1202150a02091e010909051b070503030912120a02030a09021507020118030f022205010e0402090a09170f0c01062705071e02031b0d02010c09080726010c 67
    0x18040e007078184590312003600d1004184080595954810f45c1e4003100c4802101c20014010406890722818480a241200608040c0460014450303003044804000345200d2407120060340c0001408143c415454820110b801c40700440e140002a4140010b0380036580004003d140002c4030482031703002c581c6859403414030112540c0080340c40821580d012501c1c0e0001c3c03490b100300f2009107146076120080100d004800a1007008820300610096808d17080442c0500d507072640c24441541c4d01c0b40155141c41c0d0550701070b03006500410008030700d0406d03402440c00045c2d10240c3c200c403a00b008404007155030010307034005d5180030342004407074103000c424050358014004109803800d49803031804444800c04034081104070a181890104003056812940c0c05c0c80d0b208030b40408103808000240304070f046110701e0304002083c41041110f090801000559032602000341d400800082c3d44034801900c0c8110b0a10030228160700c5aa81401045100000e03030300e441855403481c0c0902c8804003a41404e542d141000c507400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 436608291 1250 436607041 436607047
    0x3200d080a061a0904020702010c06050f01090c030203090a020126100915080c040525201605100201090b01060507020a0518060919060824060108041202150a02 70
    0x4003124510a40d40100359004038642c02034010001520240140d850245c8141d40c0820500b082da40a200114210b40c0e0040701040315181481d1032a02345c1400380910403c5500d06101c07401c01c40d009200b101d01400c9030708020101c0803100e40c011a02d80300c1070380740540382c100025190300c2050550454503024012100310084103c0c00c0071000b10483e0b001004190b115682000c0030402032001080700b81c4031040689004c02c0caa52407200e00c0b6083d2240441940b8502141c50150540307070f90101071100c0416400d0710380c4034a0502e03c1c40c03580d95808804042d1100c1500c8203410007107850101035880c841d20260001203100c3d0342030348406000034000da1160021840000721402140b17450b8101c10080c00085400c00710026014240c0c833420480200000d0088400002141c3c4000400c07800b03210b00602d2240c127000c02a00ca4900c82c0c1c0700d84042003070314402d041c88c004941034142c4001c80e1911595041e50f41c50b40d00c4d07980380c031048148031011902c3c006602594001c40403507c501184030b485800031680142c0d03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 436609541 1250 436608291 436608301
    0x4051e030f0d0306080c01140f0307030b1c0620040902070204140906070813031b0507081221090c10090905160f2f1014060910050d03200d08 62
    0x5c20402041034003810045c1008c0e0341c00d4402e8030b50060380c620180c12003031079489545601c82a00100340e074001445d4004a51148401c0d00f1241c0c0360380445440c804c500c03d2101e5040030080c0d0303249030020f90310460004003d110602007042c4a40c00792203502d00080002c02e062054400320003080c082924810300981002d0100498150003646440d001504600640010896520014000d000030060300700100303007014185080c00f4042201102400614007682d0780034525036010303ea41d6001c905400344070141008480c0b01c0700b00d41c030500c1c1e00c100c00160140c42405601c80802118034102040e00060200c04080030500340b98900c50507104004c80399040c4011802c20902270141810010203208010700404050034584e00c800302d00c0e0380c82d012140c00c2685041054021801c2c07640d0020b444408515104680d101791018400480c0100000d0300c0c000c04603240c0d54508580900305014640c4c0280c0d2080881000a1090344100d40001119031400500d200885002d130400c2103d20400c070006002d041800 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 436610791 1250 436609541 436609543
    0x1208070e1018080606090f0f0f070c0b011e050109080a081e03010909112713080c1e030c0a030810030501021908090f0604080d11031305011104051e030f0d030608 71
    0x19088404041e221145203480c41080c0200c11005010407034800b210360102c0d12b8140207690482d00d00350303c26810142507850f10f80c11f035900064490b60000502c85410005050750090025030242d440142c090b0601c0c502540380d41707c55a21118000442d06001e1400c0b00310138110704069800b030b0408074404600d404490a2041c0d01441d110b42d882d100d903095509902d202c1d08111103440044c00045003842d03107591a5107440e05140c104080141020b48001030700502017001081c0030b0340d003202001d103110068078842d02035641c0f40200e0306011704a900c87c003e50b0021034003d803845907208015421003d045034a0f80e64683c07c0ea0440c4021010016004004100746034209521591044098004003814208224003562b0350b0000703800030784600c000080d4122180d20300e81200154070325412205a680c1409000c402c1c80c058006c8080e116075280079101d1000300200c0c01110b08a5030028120314042401c000d440756604145407617258188540c040d086020b50081c4504411a4841d80700014120315114000b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 436612041 1250 436610791 436610809
    0x2a090801140105060d0c030b13091511040902030c1603030212060405100303110a0204090b010e07170619092405030705010c1202120d091208070e1018080606 69
    0x2400e604034070005100b44d403980f10a0310401e01c101c440c0031500c20305825042d0010105d110744903400c2541516110000c3c4002d0300075403203161042d03814008160381165505e04494280108000c00c0c1c808000c00c10182c000c6401542c0c00c1200003145500d03080c203218640184030311071a0201c0229801040000c280007044134001c0d8030000a0354244030b6494000b0000c0040d0032180402010b028156003503210680041003001d42043c2c0c090030411091140f803d003926038410900c40d1507404a04000000d040354802c140c400d00c0302c4406000c80c2c2480c0c9038802088182020310303480303080e0348448041c0056840e140e130003000002031107207840034000100303404c8041c64040a030b002075029501480080007540d0303001d2024490160040c0c048206150920300883c01c01d004a05031030304101e8007040f8210140c9507a4440200203104400b000305441a0720400e4402c1442200c21a0200700e8414903103449062a48a188220345079141c0310120000c00d0f19000243d91141c0c100356690b42c00710040010718140f40d41c1c1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 436613291 1250 436612041 436612061
    0x12020f04290d0c02010f1109012a0305030402090a021809060103090c18060501080906010e0603070b0703030b0907110604060c0207050409201e042c0105090705222a090801 75
    0x5010b4007c0d507003140714092003503644950401c2400b101c01d64070b00164030790f801c0d48140000c0c108444c9035460308005000750801d550580c032a80d0b4403804544515014400c69105811001c10081c060610101304001c20750004c181605160f100d0103a100040e000c2c1c2c010201030000d0341d03081c4424158809482007203402a4000072b040c480854244070400d0000604541100c0388a41c20484c0e6503240b401180c100b8400303070b0104003540c1c0c1c00b080800405030590090501110180c844048603554140d048900c100c8610482c081504420007180220344070350058140c4100c1030045945084e581c01c0440c0c111140c203030003900c002d04402000f10316013283c560361100d211401c86901805030700704403aa8072080f81c00c00d45188502d1780c032105c00c5160784d14098603404075520080411220040060040c0c06030070203c031412100e000f07d040100d8145081d084a00c00d44031a0740c1080d200341c2400040e4030007800d040c0580844400d2031a0f00d403c080d003000907003980d0b100c1666034010042e4506400c103829a0b10f0081 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 436614541 1250 436613291 436613321
    0x109050d0b0a0f0b040e1b10020c1e09010b030619120f03180b030915060a1401030b090103060504050f03030903091c2a06021209130b190612020f04290d0c0201 70
    0xd05104554001603c403081c01048903604200506094182f88012003038005075040030501c000045c0400c64000070f1403041e00f0940325408180c3c040324000c0d407114464000e01101010340703000200424961000d40070001d00c84e0514048030040211044c0b0305100c0c03617214405a0308000100110307107200780409101d50803185204101400d0100001d116941280502e20b403407580100c245c60a41e00c42e40203001101d9000e40340500e10b58682c1403680c0070f030800b1501a03d10344241d0302080380e056000070440b8071900c076000256007824017590410204000081c11388d200704481000c2c1e0400300d00c08055612607451070864481c00d02ca0764180c4144194070f0b5501c440203540240c0002158404050103ca0b0400001c80c0d214503549035410020000309407040303a8640065400c85900f10761814030070f8802c159100b81e01c2c0d5041d0944540e004da1300780e1052031300760b54040c2d1003808208004c42c00d454601c06244c5402c49005400c04004030f25031165009601c1250055482e1049000704a0302881005004000c0307213 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 436615791 1250 436614541 436614559
    0xd080d0608161a09210a0b180c0a0f18090c090c11010509060402040e15091e010b18040f0602030a090c06020307020a150212070503090109050d0b0a0f0b040e1b 70
    0xea03070110140110500404e54030742c2c4640804040c08a1030706e4541c0606440c41d2400c0013059039421440c100c2d24600c2e00d100710912504a4075000701c6c10001c440344d400701044000d00b081c1300104801640c2811610142d00c600a083c0020012062003019040c0120b00203805150000c00602d5000b0350500c401040c0d1425080c0240304801080080e070260f015203000c0785000070202004c3c50440c0103030701c00d10f91054030020b00c40341d0303200840ca4080c5000805d88414045941103085401ca4500000c09603000b43c00c09030120120403680185a403040c003174120000c2248141d110a02a68012280007132819030300c01003007041201c07240355040500034901c0107605100895001c44d407110240d0003440c40302c030741a001d004c003180e200700241012507081d042035076104d002d1858401d940703403c88034841d4003080b140080464141486040c8082894110407000030507120708403100000c1400b074101201003910782c84503140725142c602484001000d810021300d0844014403148004e00360318145240310f00c0d030318 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 436617041 1250 436615791 436615807
    0xc210f210f090d030e2107061701090906020705030318012313020a151805120307030c03020328080a0c020c0415050a060908010c0c020d080d0608161a 66
    0x54159422100180c1d20094410564201a0390542c208000203a22400d170720001c902d00080f1042c0441b4502d01c42d4100c900c016150642a5049116001c142c41d20380c10304401041491203a40041c9007050040000625180464a43c9411580201d401d0382c0e5002c4050410f00300b0000034880c820903c07488184021011500600c00c000200d40a41124071100703080c000c610a640d03815504200400001015a003c0c0b00c2c0c282010b403c0110036104c1104440703001d4800a401c1c28080c0e103625900c104000030b9454003600c0d540503560040b2a19042d81144020300c00c61007000300c025450090b180040800c4007001c0700092004003a10401020107140904206040901c1500054000c86100c01103501180c5100c025440645502c12035000c5a842090f00f000011030f0b90300306030084280c2c0d4a0364001d1001f0070120300c0660700440c80c500000c3d000b400a031640b070003250f0040d0281007404042000810380741da44107041d6151140740c074040f0005012070f000401c4541040003900004160f101c040506211074 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 436618291 1250 436617041 436617067
    0x20d0201150501050915030a0b04050609040c0b0c0f0607090512071a070f0209040827010c080d02090d0c050103060f0b090907020a060c09060e040e0c210f21 69
    0x3548a0941480000f1805c84180d070340755845e100302c1152504c0d03090f40324a401c02291018084050391680031350700e03180c0802c0041c200a800c040c4a5038202e4102c010303407443c0022602d0281e0045011000724001c020380040d0610302400124001d82d00b40e030354405070606140c2003200420f800f50003c4240d40c000142001342240c2c041d0704581099040090f183c40e2070003400c00d14240c00381e81d00002c0d400400f440c100420488510040e0200c1811a01170003141170900a100d00c4102c0003042c2607001c20031b0b01d075407040054200700c010020b034010b8183c0541480c50304d130b022410726a034540341240c1d2021985c8041c03080d544c0c1403240600820401364004941e0f840c002c8070712803c2c4901a1424025158080001d0ac2d40c1e0003080a502e110340c1c045001c10240c0c00d5400c00a003990041c1c0116800200c3c48103c8044a1a20f40603003074072007100e000502075008081c02008840700d50341f44d624074000d4a091501000c0c880034010700201106071806800300c600d18041d625002400c4002c010040b0b4424840c131940309039 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 436619541 1250 436618291 436618331
    0x10b0a0c080a030e030d02120702150a022109150c090d060b010203070c0807060e04050717042102010b120a0b010608151507050105221502040b0408030a020d0201 71
    0x5002021a9a101d0005100f00c015120310f50141d0203a1000091707107000700405500401c805010411602c03641d86840204a803507800b100441640440100049902c15007582c1c01011040390540120403103241da6170509846001c01c4516440075004400425024614129159845444c02c4aa1171400700c014000482c96981c0c1a4042c0040359103201c0b108459000304115001d4036045090002d03015030b50318580d580d0344180d014240000d8200c11003110309040038003c880c0910002e031110400300843c0104d1540301d40004000f610302000303008a07020803120041c008010001d00750b0010403082401414040e80642c8248201d0b800e51001c0090004503414a1015054807028500f07403409449024130407103404507071040c250b8000c000c03c03444a0801c0f020700c010300380c0e540700e02d00a128076551441c06490311142c20360741102c40650740514500241080d250340783c1481032640c005040c0342c0c0f50700b400030458010350080011540006628244260108480e09809846200a0064000303980e44012600 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 436620791 1250 436619541 436619543
    0x50106030513140f060103081b0601030b04120c170408060c0a0801270c0903050c1509040b042a1101020f0a0c030e120606040e0f07061b2009010b0a0c 66
    0x4490001d84210f000c244028042c4040003c212880b0f5612800c1140c201d40c0310045550300c030b050440308440300b44d1003c1500c6040f02d4015910b81215505d03a22000e18510030300140e2000c01952040c19000503078204801c1c42c1f1014602d503000c0d25039040c501c54514004d0040d007102440001030198000e02d0307a0001c0600c0c1510038000000000ea038003e1000c0c01c48160580503010103a05100d07081c110309500044103001c40b80510102c0d4140d00760306052051109000562500b4030074200024480c0342040d40002c401280080d0000a8003508840172502d0050b034405090040c110900d400c42440758407401014003425448000c620f040b0700860980c0703a500c1141003070804e10082aa030070080c54000c1400351b007299000303004107000b81c0341d6103510f035190b01003201d0b01803050346004d49a001d60080000c09002e481541c80003401c03500d003440c401740d4007807400c0c0b510800c082c1400c107004c800080c17031505080e00100c078800c056540410010f00700443c1410580090150203418032200340341c10790101c201c030700417 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 436622041 1250 436620791 436620803
    0x3100228110303040308150108061503062403040b1f030605060604081507030c0e0109120f170304020f04091e02130e0c0f0d03050319090609110103050106030513 71
    0x444480c1825141c0019200c8542800d000c04820042455000440329108182080200e6040d80c0340310010b503021071040c3e81903600441d5241e0038402250340e4500075034019600820056041040000c0c41e1002c401201c0c0000c000000801403104102c0d580c08a0768024542c00b154036170340c08001820560380392080c4006058940c40344045141521003000700c0c2d0142c1007450503211007101e006d4860042e440d069810400280c5800802c0b4800f920562442600e460143d586030b800b2883c0959140104400c624280d40340c4011254a20014800298240d40403101980ca00c0e1686410300400c010b50303100704500341c0201e0034030502e00005460103030f10709190b84556600c00d4001ea103d00205075200004484d115859262501482d070307040002070051321201d0110f90f8001040c9810013404560580d0303c3e00103000c2002030011856101d004101384442c0074010f040003c04140948400d816200040310584004102c0e00d6840081d590502400f0b02502c4141400d0000e030034180072139132400306943d00251030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 436623291 1250 436622041 436622107
    0xc0f12120408090d150c0f0504060c200402040f0e010b13090203070e090a06050a0b040e0c07030e0303040902030a1805030a0c0203030403020405010308040501020d090f030201050c0c0915031002 85
    0x2c00c2da0f6040396482e4035900700d42c402801c1c50402100f6802441b8846040b8040b4820805000c1080d1103401146e042e542ca0341d40348464a0700c40d0359044071202158040d0f4181c0801c05050301e400ea01c0354809070004003100d00d11001114500880c10b001d0ba441138004d10030480c010082d10200a020303000080031a00d194100580e00c1e035940c030044560302d035a00c1409d90b2051492041c40480c51080c2c000c90305840d0119180f01509a40b6105003a492046104031012144034600260403260b14601400340b84d4007074101920004e401c1f400007402d40d4002d0b081040180c1d408400c2c415000c5c0188078084920f05030340c003080c1008259848180d643d00804440f0010030001c4420703101191001d005541c010350380a40b041c03190356103c2c60a0041c0742c0140c02050b00520512103d810414400e0304007034111820303000ba224019086400445269010040703240e02c40c856081c0048250325000079442c4500c5884c0311050100700768004150411900c8040010300600600c807a40f1142e4a05050900440e40c3c02c5a13021 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 436624541 1250 436623291 436623307
    0x203040b0a1b0c08070512010902030604060c021906020a030c0e031c05130e010303020d05120609131b030201020118021c240e0636120c0f12120408 65
    0xb54900400b40020083d400001000507031410005610068038401c80d000318044040448a600b240d0000c0d10180d03056200f0004180490203540c4030402a001601c16517440c01d0340e000e240c01020082c12800c0b0b41e001d03400900c0c0b0f01c8542d03051040000000a62034070b00c081131a60b80c0001d0b0355204020302c8864400d908102c90000c1c0e0f0142c411a150341803c0041a440705607640c119400c8104248800e8016000340c10201200ca4440d1b0100d80999149032400b0700142c4500d4140551044018003188860b058661a9000300e81404068030072209000541100c540c01d40c8002420f490100c035606d410f00419117a200d0040c3e40e480b0349117011043c050f560305c10300c0e601414414410504500e5a00c1158032018250a800c0166000a506120340404441c600d4480115a04041858907001941c1240c282200f000c890b240f03104450000030765604030f4100056001e1100c900d9131112240000e40d50003075880ca0500303601880306004c242541690787c2d0401c0c01546041400c3c00c00100020300c1920009035840c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 436625791 1250 436624541 436624577
    0x1805210c040c0203041a070f0605060312070b0403020d020706050a0e030132060a0f091805010c0e0301050a06080718090807140105060306040201140a0c0b0f160203040b0a 75
    0x2400c644020410b00c0184480c400294895000780500380000c100307100c2600c002c4820b4002c540c2030a5001c02008203d10003510360710024070b80988029450700516070846100000c1c00094224940180c010540e907060520b0003900d0094a1a046001c1d500210b204000594001c400e846402e8194204420340c0e542440019004011301080700c0b40701d40d0f01c56007100d401c0c00f0301b0560b021117148082100600b9110385042110325652807081a981d0b01d2000c0c0d05116008140c0c00901500041c0810550a01065603d50b425640c40f0102940001c000c00c039610031526013405020b030011120b080c20080a030a10140c1c64540c00e940c040c1150501540034109088042d59010a41007a0001d54807500d0720b009190442d001e0004244460b01582080081401440c01041e09401103a05850f8480082c1c01c16215001907048241d80340709200c25a071905000c41e03a002181c030303c2482c030750201d6403242c039003550b841400074188690301d0110b500500c401c1c0b1114500e0003c8901180340c0c0d040080030260480304917 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 436627041 1250 436625791 436625803
    0x21b090114031501141003020c060406020a0e0d0b071805030c0f010915020d0f1b1401020d0f050a0509060408030f0c1b01060e06010c11102607180521 66
    0x12094480840f000081c014090000c0304840702c2c800c5940202405480c0400c400f81d004100103400c807504484c01250006115500600c0d0005842c180721000c05541d00000d00c02080d8154107691001c40913041003100381e8046140c1741c1413280c00011010090612011960310007145030704901414201511155036170213001038800410384090910107140740603400940312031084200c140482c2e00280c2c07030500070340610103080003403d500b01190502e154684038003200c41540300c010606551708104160940c1c20710b00500030082c0d43c03541c02184508291501d00111000189103104da9081003042c403002401e0b20040301d41020b0b1000030688152920b0803002c0661044441210301d042d030122140d851403078107400050480d602c1c0d1181c080b4030741d207503001507850400ea4040240b1064081640750810b24190b090400369002500c0c014000c010401da0032121400c50444090348402000b04120000c0c1d800301003000300245200306880550324140103c7d10000ba0305018554500d081420340300798007010490 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 436628291 1250 436627041 436627063
    0x412140601120c05040e06130c090608070302091513020f090409050a1506080c0d051006120c05150d05060111061f051f050310030803010306020a021b09011403 70
    0xd0314480d580d5036480280344002c0d20380c00c44480407100000101440c1c50310032a62240d500340090038065540400800e80501041030031030302044000320105100c4442d11a002c040c007920300003440d45078103600410454203002002141c1002d042e0821000d191540100d0517800d03a0703286005038a03800340c406800802e0040031100c603001032a206070391050000008002c0d400c5402a60b4100d007007241d80007540141c0e0b1541c0206031240d071010800c0040c50418521310b40324030340a2015034814810700e5010710103603411540900e41c0c4459000d20031007840711358807034100100001c54030b0244000d080210700310039000d0800b01d002000d980d000012007a0b4010b490035040034440c402622018580480040c411010040c0d000000310401031000c01c3c28100707a1000f41200c800300107a03411104807140c040350183d00081c441c1e012800a40e07800170000d0040d0b0301440c0078604c0b03101c01584524801c0c000900d0a00051084081803040c0e000d09501a100c2d56412415251000c16140703a0341c6803000402d15058884003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 436629541 1250 436628291 436628293
    0x61b030912030503150109060e01050c1e010b0a0f060207052704140d020105010302060906070305040b0706060515120c0a02010e0a08030a23070e0a15020f0105100b041214 75
    0x1e8001c100b5621100551040781d500101e001000410001186d0340c03d1107002d07050104444400c0100c02e903010b0b10240c02c001c1c40715821a440039099040040030040b8080c3c02c0d00c0d99030f4403100c5801d8940303441c5c40d64201809202d00040403440c54100c00940d2051180705184c010401c000515030700c00c80c1008420700e0f905000c441c01102e41058075140c031000045034807102c00350145149107106030b07206014140c1269001000c0c242083d418004020207a444180102c080c004200700c000380b0000c0c81c10180c90301c24004c18000541d98078080a0140c0c015440c00c9015840008100720000c180309680c8243d049002d0700141c0e511411840300a0b401040c91800c84000361007200310f400c080040c1000150b1041400c040240001d5100404400b15290105e5401440c0c2611030005250203104156041400c2d030024003c103c0c159035551402505003040108200680248440c8000300d4800d015080c0c00c2801801d66050841c41d090044842d40900c2c050740c00360201504038042404040703084c051001c0c01d00c00c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 436630791 1250 436629541 436629569
    0x8030f0a11073203030a02090301231e220303020f04141c03020d0f0e130e01050105100c03050d090c0e071202121302010c170d0510061b0309 62
    0x401d04865492404020b20050182044201c81c124010418107540450f030b00029819516130a0b2241d0194000154994056585820750070704010701d42a400c0060040135000081803d050150760351140c0b0081c10b00001c040c81c4010b0000500c82601c04070400050080410003500d22440c044010380304071801e03a4440c120104020442c8641c411190304080b07403c4448120502c600c3d8401c40004c001040080c3c05a0070000c04108514050441c50048c00540e10300715050700201c3c0700107580090301500a8903031560711031a0f4405903500348205030140c00100c8005081440c441e80042c40000d4015009003001004551484040c42c40c2c1c020141d034552181032807545540300d03064001c420784100ea081d8001010681d91603000580e520031242a8241200003c030a0341d40c00700850070f0714000d02001c90420449600e00c50100391074001410550300044490380c0d0320382a09506c041604c2c0d01500c200201b180741441000000d400c001512180c103068040303809062036509040e80c0240d0700743d0005100310b8403a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 436632041 1250 436630791 436630793
    0x904060906081612081c29030c040b0622050405090a020901061407060518060a020301050f0105160303200d0f29010e0d02030a0506160c08030f0a1107 66
    0x2061180d0601c00311964000003650b2070100744e1601c5001d0f20f0207000043d007001404440310850100c10340441172004007003005c882c0c5155040002c1051504031450200b008244601071800740103100c4c90300340c116400c0c80a0305007000050094400e00309040f50409011400d80c0690411100d001c0003898001e0003040180f415052041d00c540684400300d20401c80d078000812814028104960b007001c220302c0d9a42491025542e100081001501031007496460b407403001c003001e00c200030303040c0f01d0a24141c2c0542c4035494a0144a030b010f0307075a1259070500c02c041c40f91070070ba9482c82041401032500751038042400c40700c8a1041180c581c0c83e8050070f403240b50004003501410b00c15000000e0203d0b51100c204049261214440d0460081da00c3c48001c0c10b1210303030341401340c1d0322a01c0c0c0108524402001e80e00060321a60000b03107808800d52088075035400c00300030420300c910380c0d00344e1452100650600000500c200e0340d43e1916031100810206030b855081010920003d059441125110304541c03030a6511a0b00e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 436633291 1250 436632041 436632043
    0x90a1704030201030606090b0a050f0412030c0203190b060d060b10090e01050d1a0c0d1505030601050103050408040608040f0b28180204110d0c1e02030306010f05090406090608 77
    0x1500060f030119041450000b001d920a03082101210061111030b4240710046408554550000c400308520306018003020034511405200400524402c0e1612401e9400134130625080c01c00c81e000c2c0c03c0ea04050709070a0740201e40c10b02d80b080d80c402d00850741d521900d0024644074000b440d020900c180c0044129508900040e080110501924100361b034a5001b40ea0f2041040f0072440c0c494001403110400c5850f0142c0740303418184075600100c1103c52142005600780620003200c0b030f03241a1115040342c428040025060510025014140070b2800b40003628054030790260b244640d00c50030042020000020f028002034032054a2510b40c002c23880c0300541000203100034261808000000e05a5071014a083c20040340e1084640340c0d030704100c903c101d044150f020400104400d60084106c1f800c104820104100700e0b101d000341e654160b8507103201e913140d0300b15042e01ca86444850401998010414070042c1d82e003042d16030048001d03500d402e640d01c0300440041406000b084c7e003c0c00d20541011404900b10300 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 436634541 1250 436633291 436633297
    0x1003120206180a020609060310090c090315050c120c04120f061b120209040608100c02060a05010803040905092508161508061801060f17061008090a17 66
    0x4032840c8050314038101c1c4040b80c80d904840700003944000b08103e6446d81d8100b5901444e40400060820780e000c07543c0d501e010099400b042c03052400141d440c00e00348100240b4071b14011003040b03180d03c10491480c10044190040c4038030b100c0e2a050458542c005100c0c000300c0c200f1200640115501610a01d1503803901a0000c294a881240d0752824110358090108115052000390703102941c0d014a004c6840038130390020341c041105548c225481314004100c000d001c00c8038003144010000005806a01480003d003410005010040c100d420a00100704001c400803d450949071490f2000980b40c43d500461071611002880311045144403150150100c0d2108046000b1640b418003541c3e526081c08071142c1410040d07000d04101c1502c018448030392103110b082c030391750f100b20040c1103880440c1000302d0742c600204090f030003400069002c0d0708132030101d0341c0324102d07404281060086100034100403002074054021908680200850303100050310380c0e10100b2014102c250030011914000d0a0b01c10003c0490f8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 436635791 1250 436634541 436634551
    0x1006050a2d0e011502030c120921060a06050919050703020702090a0603020f010e0603130c03020a0312020c01050c03030402010311130806061e100c05150f10050109051003051003120206 81
    0x700440c1131980064004401c030b034055030405c800340c242203d4001c0600403642144071000d03000020040c609211000942c5500c6018121b00700500291505846120507104182c0020b03005051030303000e00111b03540000070b0a1030b440c1c8000f1301061075600e18808600a00034014040d5021400d202441070441180d8819010b070307402941c03903000794020718006490031003c82100f107401403000c0000540c00b035524141500f410348519040394100f55240c00041c036160b4a0740050700d140c43c20f44ca103c40f0283d0100b00160f11003200703007042810510b502552a40340e0000400103414945c8600388101003801d210120f41044292210740740303055450b20811681c40d5000c80300f26019039403001d82408079100c91201000381e80740c002c1c01181c07e903051000850308aa21804201c855101d4180b042014101c1e4060b080e200e141100c50801d86440c1c1414108926015580054103014040c8010301054890307003802407484545050100f902d07107419a4a00c041001603101603c180c880c0c5140031062a40458414091 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 436637041 1250 436635791 436635809
    0xb0a150324120203010e0601140402070c0803121f030b0114010c061b0806040e03030103170909041202190b1501020708070807050918100902010c0f030509031006050a2d0e01 76
    0x610011031b07025540c00702801205940b640c00c84008500d4900758008080311b40c414040450096640d0b04060300d1600100c20b0004c481c1c5541c41041000401c200a011110448c0001c81c0030040c42c0d600c0d581402c040600411840016a048903407131a40a1400481426880101000b42c90081842d1030b44071800d00036810b000031529004500e203442c081c0079054034078505d40b000d18656407942d5590600f8103140c024040d08050188156500b540da000e1213140310300e0042400c5050038160380d400900309600a89074500c2c1141c4401e1842c0460541103140d035100c2d0903c01168091040080141e1400d0800d44c46200030303108504010981e404d01082d0401201c00a4404510640368001c01b900030f8040e80c5e000044952107aa404110485140c00c02c208060040c104008031007219202c100c0c01500584003500401c00004941629080030444401c41340d0700b04008120b6507040c000003601229032442811201c0e8103072001c2e940741c10521301c000001c00548401c402480b0340d07141c0b82032520030300901c21032900c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 436638291 1250 436637041 436637051
    0x2016060203030c0910120e0303010513181b05040e010b1519030906090b04061d030a020606090603070b0313031206060c020919020a0c060b0a15032412020301 69
    0x8218000000e03280035078410110141408900024001411030301d100d45030810001007403c0d60364602078402d0340e05000480010b95505e605000c180416401d003d400040c02070314003100382c80520070392404482d03030320340c410100e01001030400410b1011024541046502c545040c44000c1a100b0540c415400302009584c405483c0b11041190812806040810130340c003144050070100c4a44244d01c46444a8851030700042e00781040e4552280000d01100e00f202c40f6551000b0300745100460900001d2440101e20046190280701c900003503d40501800803802488040d01080503030f60305202c583c000d0032140299949034984007108503200800360350190082030246549146c0c0b00114050241903e40b1520340451480c020307824001420401082300c00303090301c41c034000c00719003046000809100300b89035515081006241402011500b01219140c03184103002c00c104003c064946152001d01c240b800c00181da10200002c0c01e1004c1d00352070181d102c040400c000428a6050076000035022030080e402040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 436639541 1250 436638291 436638299
    0x6150c2505010903030518031c0f200304060e0d062a080408041211090907030311060f1306090c120b1e0c0d02070524070305070e102016 60
    0x1070203c29400040c001800c10000920111000e48800c515040701070b04480b154250440303007400030180c150b01c2d0f01c00543d255899040182e40b01070b103000c460b440840c40603e160b084055103562485644103030307000d000e00c4042d035101603a2801c01264505401031400d00002c0e0640c81902c010160040b15184400f007256031036460944104102032256902200e400d1a190504801d140c0e040d03070598084402e94465580b03440c150310781204160281c1141c80c0101480c60442c94040c01c02416281c05501c2907018104000806900d2038125802c00c0b120300101402c03004a0a1070380140c013121801921070820b400300012081c0c241c00740707105464001c0c040c5000c961074a0300143d2140c559500599043c8050102150820302d06000402810b1407400c0b00514200941d0340322801c0c540c2c045084000c80070303d0720036016038460015106a001940f4581000140b074094070241440301204502400340c07a60611140d0700a00600112201001c2140030060030440c0c07095650790362500100c00f1180e103900e42c000007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 436640791 1250 436639541 436639547
    0xc020d020d020705040504110301140106030609090b1f0915050f1e2101140405120f0a050304021503131b1202040c090e01120302060709030b06150c250501 68
    0x7590501690207401828540b10070003000d008042e0041c1d4100d80001501800f0342c0e030074490602c0034140721020091941c50000094200d8400d41c0c007000c01d41c1c0c1481e4054000034102c0004c40d40c4400e800034500341c0c04409166045041c009a00160881c5103030503054140740b0981300d07a2404441c011a4640b00300e64090048c0311210b40003441100c88440c140c080500302e8944200404505060300e5000100d181f9040801401e40c0c5601600c4800819003400b0301c8240300003030000904802007404018908440d802d200021403080702c10759000c0103030202c040b508558607041c50038552440203068540303d0400342d1011003e0038040034110303134040d20140d550610340d24204480302194110100c507041c0600c01c0e020b010150000540200070032454010104a00111f4800c15020300b8150551a17000c3c075407464040c4c0341000c0a00818203214100a0401c006a49035100507445041558045003242017040240964041c00f054503116005a203500d40d16420170f0340b44402104041c90b007081040e40d4810042d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 436642041 1250 436640791 436640803
    0x7060f09051b040e070609080610030b010e091f020d06240507020a03020a060c0c0f12030c03030b1e0a12080a180e0c030403020c010807091403071205010c020d02 71
    0x30400d402c21504800102e8030030880d0302544402501c0420b2814107110014141320542c0c0201012a12441081c020102c0c10480d070390380260f01d46402e1075083c0c156112004022014803c4002c52003070307580020081802880140c904c03040c0ca1001c4907000c8613550100c4069001b10240c0c2840300d00c2e11400049448100b03c550050b8030060a8486445480d400111220781c405001030340c000c07540380000001a110040010001c1210340c0e1750195209a45c07a1042c0695450703401a1030300c06001c24184038003088843c4403da0194503040800c44480b0134a000e4024101ca46480c55110078850748180d100700d590020482c4149007100d03081c0140e52114044010030001d07000103408074009000d030504141c01650821001810344140c23803109640e42c4a441c0f201c00044030b80001c4100040244000c164041040361b020309000d0811940e90b03c3c2ca0f03240107011000381d2003460107204480d5010f0310a62014020314026041c1143d030f0005007021414802d000c1e201c40510343c4010305c281c07a0301c8500c91b0b10210300 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 436643291 1250 436642041 436642043
    0x50112090c06030b1507050114070503060a06081f0e100906080705061e0f07060e010b0f130f050901020403120c08120a0b09100302010306051503160e060705010207060f09 75
    0x4001c405410404120000c10040400e5504140d940d5540c0c00f009100902805c002c0e84260b0011800c0041000200003e810180030342d81400703400d006000507a9140d070880c3c415598603190501aa507910000700c2c10704680f0740010000e240780d40c0c4010070070441582e00c5520031b407214440690a580c0e0b50a00d4004c40c1c00c0c41c401c40c1c5560300710700018003141c03030b00c40c0043c030103146812030540507002d0315030b080021a404040ca50503c56400030b0102d04015080c01004403003a141c900800c4a00c00d54030108200c0c200700c0791014461442d003d5800d0345980e150b0704c0f80b54002c0818504211515100e2880c6000b9842404259825044528481e88661060b420f6880c6654400603560800e01240d000c4540c414014140c240c0071a110540241961a14040c0600c00e101130840003216038510b00001d8200c6c0c0c05608024020090b06070041b02d14a508422280c0201d45111a080b9841310200c5c211554691001ca40c0d510080c0056010144501500941000c07801120200401460995007400311441c080f0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 436644541 1250 436643291 436643303
    0x7030804170c07090b030304050901181406010c150e0a050303060306010e19200a0509090c03220f0b010f03030f021614210a200f100c06021305011209 66
    0x3d000d211325195904070b9207588101404883c00c2035100d1002407003192098214135124050044a0445c0820341d0107842a038103c1c0c40c0c250b05041c108000020200f0307800c40c00103011407400b80c1910381c148807a039001d00e00c01d00701c0d80c058901d00840f61800c16220751003aa0507501c6482003c2c000b040c01c00c8114105801452003070070411108010b0854140130f80155480220703d0001905844034030208003004205c5d2180c81d03514555141c541004001811030058029a0604402e10410002507034010640c0648440381c00d00e64407141c8185002e0403007001c00a0001c007100c03074800c0006075122090320702d80103591182c1c03903400c10215488012a034035029010000380503450410100451416407084441614015040c1c0c6070035403040070090320358000c0036000d070400d0384500c00302418041402d0040030a00315a290700c46120660400250500b002000c80c00e01c01d41a00ea94105070794090345000d00d040354081030942d00c40721000305544020040f4401e05012070b4044007107050b4000e10b0321880420541c055 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 436645791 1250 436644541 436644553
    0x100602060601080405070e0c030115111207020a05210717030409050403030b150a03060918060b06121006030608060613050a23220c0506030a0f0207030804170c 70
    0x10700111000300018009490034014058081041514400c00030712071403250504603525417610b0501071911445009200c10445030503400300c4007890125090a00e43d240c400c0303507a00c5038164000a0503403050395002a600caa0b6111500003070320588004041c7d140070050988140c01c8e80c84202c40801c00b400c0f480102c4ca038004000074041c400d02c546c0b18642081c028500001d0240b0100c02080c3c141d468490315003525440841c8020442c0c2d0b060050314044c1c14564414484c2c88802e07044200400e200d44070050460303880d44545000d07620341000b13032280440b04030301e007802900301280c14001c441014016480001c0c02d05d140130a01c0d0f4000500c035401842d001e4030090100d10041f41e1000148400352100840644508800c00544480d54a12405102d6000d41d0780003400e04080181845076014881d5500544100900001ca07020404000854805581556896841c51224002482c00483c2d00309654400b2601005142d403010340d492090380708000104440c200200044030302e006520216000e98005 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 436647041 1250 436645791 436645801
    0x30b120c0405130b040b0f011403031c0e0d05090f15030604051506280801080a26041401080705030903160f0602030c0c0c0a0b04060528090305010510060206 69
    0xd90302c90340d40400c0c1000405210345213036854414041c810348080e80c9000f071380e0060200c0300e400d42141e24010f104228410220060050201c4c1c1c99000d00f120036401e010140c10343c505030b408a0f400082d5030030920015541001e034042c07005040741d003107040c00342d0107000b05205c0c1410700e0030900f010b03e61081c1001d814905555a640800000d030000034010140c0391502750b41282c03681c40d00c40181495042c0b499041102c40890362800e1004042e6030420b008000e2404010405504007044040c2c07484d8024800c0c8012200881d031049810113600042a00c0940005000500c2e08108200c16800c00003680c40780c01589035010115070500081d1190b01071078104210204071381e60f0a103200c0c115548100e11480321f080c1703e0b0719040c04a801c119080c03800088006400312410100b8411414035500499002e8081424540c0f020300030f0203140541c4091150010340c001b8900d00c001d20303521a8141324000c5007034030140120300510000e490700c03003143c03035600b0701011034400fa6400c00380e1015a002036001f0850703903580c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 436648291 1250 436647041 436647049
    0x90311060703050d020d27140c010903080315030a2d03080604020c1e0609070b070c06050901030207061b02070603021603081905010905070e040e0d030e1509010903030b120c 76
    0x5c20184084055915030302ea068041e20450060b80e160b80d4400090800003407410701c5010700d030081c44011101d070850030009c0f400760380248004042d0f0b03070849200c1d5101d95a01000c0304a2609810b440350f814070030748240d1001c0101c03284d0b443d41074100000701442450307015032854a110502e404000c0110b000c0342d00040c01410700790b001d841d101c4054000c40d8030000c0301c0c510302001c101001d0001031041d000300013002030680d410441c802c0100010000c0390325040440d120a0f4501c00a8091981000030010340e07000260310175011380345000d410540c20440b900340c5803113401c110704103020740c1005400354002c0000c46500070701c01ea80b000900b51100421304561236804450900c002081400d81e41210401000c5103010340c03003458003802c007401001a403401c007040c020300281c100000c5640324900f00b034100301d4003501c003180b0f10540100340e06000c2440442246484d0400d0b98080984001e000c90301c003000740340750054202400080c060349080203000001c4e01845695030401080c08429840b001e40301545d07082c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 436649541 1250 436648291 436648297
    0x90d090e19200414190e0402060315120d0f09060c0609050312090f060115021b03070b13050a090204030b0c0d020d020406030207050607020102090307060c0819090311060703050d02 79
    0x80786021101a0b610032000110260000e0700b010b8005100401404000d041c004660180c480c0301605071070a8525200a0b4980c984000f03000902070711020000c11203401c0726040d5000c3c614402030216007a0703104903424641c0c034601885c50342d0029105070b4040c41091701455880051350030541d507208000e01c1d1030700c981c0c000e80340c90101124684010011b0312030001200b00c855002c1c501110203488010004041d0b1841c0c540180c11184030f024001d00c001c041d81c1c2e000560704c0444002d1180c00400075804070006414003003540d2081c04404000541d000b11400556000c0d001d4500c201d502800e459199003c440403809580002032400a03042c000c103050303046c0304015116602e1007490161820303050102103000e0341c006521081c08a9000700d506000c2120038800654050304d01e1000b1401c2c5149540002d60b602094071880040c4240b03082d071a014006003d040711480c50400002d01414100b401000b001c0c10284d00c42555105942800c2e03408500d0a5002c039142c41d500b6658860420f044003056100a41c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 436650791 1250 436649541 436649561
    0x3062b021203090904140705062106040e06090109050714010507080f090a120204050f04080a0f120504140d02030f0f0c0109050a111306050a0308130e090d090e19 71
    0x4842406000c3c001e030758803015544120302c5202c030400350380303910301c1c0030752a206194002c10302c1150184a03c03401d0345540380d1814001c81070300303d2240b1291184008640245410961800d00c3d0054004105010005401010301d0920407011502d5866a070341500329401d080b607140b1400a842007100402103090300c0c3c043c005003044079980a20708002080042c0c41104194410054400d12035001300075440d01d4070446070310000c800d0b180f0030503282c070307a40d0922503101d010501418003c84030b5840b400c01c1c2c8641e90103c40a07121110411131801c0c2410300207040340148000c107a061140019035600d151012054072410708100070002c0c14074105d1020341e8425000000e80011544d80d41116030003045042021101c900c0c0a21603020a422135041481040c40e6684042000b103401c0034410000b54945040c034104590704512455140d044581e5003001070076807684400500040c10341804031490010900a5148080b500c2d541c42d0281c0e599881c0392100c1040b00e107a10860080c4001651915013600109100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 436652041 1250 436650791 436650793
    0xc1315140f09360a0501051e1603020c01090807080405090105060c03040e04020f0414090c1012090204290f040c2106080d05090a17060414030d05070503062b0212 71
    0xe00350791400311310341404248155a03580d1110103100340c0d110141511082040802002c0c1c1e00e230714015007441c5090092543c10800c02d076000441c2e0000714000c1d4085241560f000034426a01c0c802810088415003140c02142d01c140e910100000301072400300d04990490f17030107102441c01e0138a055520004440020420b1741c0202c121040a6101c7d9140d01c035002c40300300380d001817001d90300f041030351a4a4114002c421500802801f500d01d400150410300d07804904031501c0700440d09558910204014040401255a61010003032021600002c40700c4884001107040d02c400c40c000b00f801d801c2000b0307030b0341064840d0081400c0d444201030301c5001500c00c50a40c04400e03000300303443c0d036580003242c40c1c0301c102e4a001000620100ea03400351450600c200b071000340602e908030490385829107080ca441d02000351000b0b040c2d440c02c4000c0d01891205000f0740710207160b0f084042040389410440a401d80c1c1c0122000c0b8401c1500080a84c1c0700c4140807002c0c42e003483c043c07444841c02211503090101044100c01440b80f0703 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 436653291 1250 436652041 436652131
    0x4060f121e060905060709290313290a02090d0210140c0d090b070b06062b060303120e06130320070305070f080c1315140f09 55
    0x2c00d00c42d0055003000b0307200d98024040e030f03d413014008100140e00c0c0c20107010b4204003401490104056050800d00e804448030048e541e484d1700840c8020000c08420041000044242c9402c40b01e00c20760b46450403295074171034002d0079500d84109000328840c2940040d4003a148050381c50140c18682c012904c14140ca052002403180c000c0f200d501039400044a84d152580300d1102a41d01c154808006001000c00e181454141703107640d90382880341c0c100140300f1805a8008900500665044007510b80c0851041c2c1c81500d8000100da40c80e800b600c0c1c00c0c00240c010841e001695030003500144210060309510a000c1d0410391030b40031100b45d05c803801a00507000c0140c8685000a614084200750904c4a00710f0010020796185240450070001260302c90030342c000480c0c10400c00c04502154946105c48100c505450358501e0010344402880c0266580781350260840010451444240301401d12000c200d840000303007203802d02041360303c130f00031144940c200c0414110f1004011289201a034662070302c10850345 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 436654541 1250 436653291 436653293
    0x20a060608010209120a080a0c0219060f030621030806010306081501080c03061005060a11103303020915030a2a0b1c0b0d050c04060f121e 61
    0x15180c2940120322165400100e030074241c54402c241c0d94610b140c07007002d0003416105403102e24190260305060340c1409601b8820340d085640340e205c1451101e691031907403104c0d02e07101c41d0000c01d4410400d040d800882d260041c04200005003540a81140c2c56a200e070551035902d036681290012005840241032503201e0784082590f140c1803200c81401d140450005001750300d80312031a440c001784408054080d0b0000410701c4803540c82c4c104040240c1c5c000b40d480b02c0e561140500110f0304401003054524543c014940480000101a003003505c62070000700c1001c5002c41d030100c1a0b101002e1800b040714162032420810401402d01c103054039030000a00c85040b19100f4400c010130300b0906020012141c2c88540403812910070040b00000031644079070b003000405503003001c110300c10600c44e0402407854940d4040341c12900c2051741d007180704034075409408800c850506142c41035460801021881c452070505402045001407101ca03081152802c08220f03804074103503203c0300c10059a000140070344400054640d8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 436655791 1250 436654541 436654553
    0x1207120f1803050307020a051f032d0b1315120c0807030c0611070302130e011d0709050c13060f032301030605090601050906101e091503150e07020a 65
    0x40c0041d0f000f100070303640d503131003030303c10410103400d16080b4034410314200c9103001203a05500784100d180d4130281000129104d4a030103580700541c003c4c047d640c08803401c1c511813107100c000b6040441c401c081660104070000703680550000340c5107100c0101c4031030b0304080001c0000304503208000c3d01e410f01031101c010202e03459020150411441d80c0055805400d400c0c410011250302c0000c6032580001240500f0180d8116030001c0c02c9052446d2a00344502e444061646a050085d8441c51b10b54000503c0105117468180300541c0301d00d218421414910f1505c40020ba00410140031264103c070116061a401410104251991102c0602c08010903a685040c03400111f000a082d0180710300010070a00c1c290f140d442c0001c2a15030040c00141c46400c88801040140c56072411103800042c121424605c0d00c54884e011104240f01d00d2004224203101e603a0b200c401c0c2c0d0000380c1401950140703000307640300c24410041a029074600c948400041d540584040062901090005810010900c1a2200c18056031592 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 436657041 1250 436655791 436655837
    0xc030e0616200d081612020714010609050106030b030102091008070207030b07090302100512040b1b071101030e0a03080a0c050c1c0801060c081c0b0d0c0302031207120f 74
    0x800c21584600c0f852106943c024415642c0140c0c05911001603942c901c030014814940c500456603443d4003c0384000400c002080f9280f89c1d0181d88008000d010b55440c20000508800e21079000464030f007480c01c094a0034180203c590804000c1c1018031000d100a00465216070700519031001c40c000c00c0000300000d4008041280540480e5403048861402c2d03004001c1c02200101a94091101c10001c440c2c0d101009030351aa48507070804000841c0d6900c400030070100c943c00d1040841103441c00140001007100078146c90a00990030399003005240c400d61004c980c0d907840b40301c020340400c03034200004e4201c00640e0406a020742080c60241d04252460028070b2a21180207410300820200d01804042564031100207401402d0030b240c8180011181d8a45000e141726049504140c1400c141380f0640c2035184c1d401c850301c10b04010780460801030242c00c160344040300307500040744030b40141c135070b5003141e0410b02080d140700c5c42d080b25596000032941da0040da45888254060390600803202c405100090080c030403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 436658291 1250 436657041 436657097
    0xd0b0c25050d080405150c130306050a1401080307080c011805100e01151a120c0c060f0403050909040c03050601270513081c021c0c030e0616 62
    0x4504034004918203242850910481c18041118010800c00410303800a80482084042c601d421030716100c80e001c5035268800c41880030311200601f9000001c105440e4081441850030f800100441d103c04542181c50120030322034404c0c0340c0d106028000102d00d1410040c512010300784000900d84001007181c02d40d0b080360f80b0084e0b81a821a00203031000e241c40b40100749494040c10000c116030044e1020600b0825050b000d88020031401400440c80f05000b5822100d407440d035403000300c14904c0c0685012036243d100c59800c1e0900c2c0200d0740441c0c4414404011903000300c4d410f4413244c0c101801881801441e01000b08156101400f4903000804a00c003841120702030090494480e0307514207041c40a0441560913044150028500003c0054100c032840401c030b0769640c407200c000c0e9142540103c0b01c80b840c450905d5600d034207100049003542307002c0d002c2d04001c002c000d08400b403129840d151010785c00c8850f40c000300c455903044400022240c01110740482c0c2124203c3c00c128441000d400c440c0c803030254866613 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 436659541 1250 436658291 436658347
    0x81c06051e120601030b22050708070f0b0406020303070302160b0a1a01020c0a05040504080d2309030a090527040f0b01050d0f150f02120a060f050d0b0c 67
    0x10004181d8101050003918407050080100465450755035074444020000700504843d00200303d41851040c02c005025840c15045811071b01c919854521b000c2e20340100f4424805040840c01e0006a091011020341d03003104c103141c000e90b0542c3d4401030182c0c040c1d0702008032200940703101c60411002a0600a28034060340904cc00068040226032004407482c000c01c2005040d544014401c05035030f540c0300c4084062b0350040d2408200d980711450603800a0080c2d00341d16446508107081805801c8801c000604400a80b010708a0242c4503100415200c2c400c0b2174080c80041c0d04040c06212a00b001035842e8405070a030900004000400e05008050410640c0d04a403551445580c080034006c420354800d01502040f0303041c0c40005c1c02130b1f480c43c2004200b108002c12101d0400110b4000c1d904070342c410440c4c50380800c0d05540e03510b400e0304140028541118100303200c03481e040001c01d20401001564040d5100501160508a035a480d100c130721610003092000095070170420000c5030080d800c44481c0001c81c1328 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 436660791 1250 436659541 436659589
    0x4020d0c080a0204080703150b03060403081905070c1b080d03060f05030705031e01110304030818060c0d09020604090207050304170303190c120204230d081c0605 71
    0xa1005040c0701002d01009807060040c813041c043c039000402e44400312584030140b03135241900c01e401c83c0c015000c00c800e01941400741c0e00c100001e241c0c2203410f09100d5401040301c8044404201c02c0002120341c103603480000503280c00c40300c600003a03d0310007240305000001003503036141d541e401c0c54621302070035138020b0f00020740c843c0420000032100b02d8220020b1700b4200c02605405d410b00002c82e13038400d801048084005054440e40707100c00d000398072081c0031800111720223030b50785041c1c01c0142c40440143c8400186150754003120342c9a20000c00c246002e4107210304030710b1811554011003400380c8640b00007682d00120030000041d0030f4982d0b1000300703616032245014680f034a190020f8090071040880307120718145c00420411003210400340c8282d441070701000d00003d9000840b90100c4002001004c22254030384009408108014081c03440c1c05d10700c0c00009050300043c1805c00b0700c0342c4028510002080c880d01441507400d60484800010822110504001105640da00010b81c140c11605c0e43c0ea290b00200c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 436662041 1250 436660791 436660811
    0x506010b07061a010c1b05060a110c03010504030e0d15090609030f02160b0c0c09042105190302090d060906090213090c140409061a1801030803010b031504020d 70
    0x307006007140c6185440d0180741ca07401c600006003080800c003000500b0010800c6440c0806d20b2400d8214001c7c08003d0000c98039a02d02032400f078035200d0121220b150b02c6c803d45050b000c4515050041c17030f00c11581548c560364a00483c00900c1582c0c24040d07011a0f010000030b50708880f8407960301c610000399000e0310010821044605014009070100441c3c0c80441d08103e8a610b843d040c80003640703048130500908280e0743e0020380c1d00d26041ca07000d104d100e5031245500041c0014804609600504a0358560005000d91803501050340d00344118500e0f1824031140f45100060a4000c1c2d02501118902601c200d030700f80381540d2a4412600098000c50b00c255560000d10194100301b68400c01265419604000325030580d00d450095903810322441008840942400c0c004d9156038001c007107030300e0744108140074907040c0b26145491f82514003600c81c043d2000308050280e0035001300d061070407a80c2180780c0b146540d081c0705200e20076510050400250710007500e0f05036032a44543c4002c26041100850001d07580c681 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 436663291 1250 436662041 436662053
    0x3070b0108060f041502070b04150c0905031509190521030c0d0e0115090b0301140c1905040e0c09090601020c011b1b030c031101020601030b0c0a03090506010b07 71
    0x1040c1c01c1400503511503010031880c03115204034560000c1e00240c142c0340070700711148001301034490341000500300c0d004401448100b00d40790404600d174483c400f20038440300008070422207241000741b045903815800fa5490000007201c410019400210a4042d6041800c0100c05088904249a01261260700c03030b4950106030680c0700503c62928101010301480d505003803201c6801c5000e0856014009a9910049003c0880c00d5100361010318080c1d02c1a0001079503801484010070a100400307010b94204178807071190500c400c00c000d03c1559200307003c2d820203007014072280c8d1a0386a044420705005042201255100c0c251040d584104040102d46541d0300082c000d00c4040b94000d00041e0542d80101c51041301340e078011522508869900541442c804801d05140303810700e03810301020020080c0c21801206005154044100350b9004220045001a0780c2004a03507400c801d2101038071113101a40030071009800030004080340c07041c5250101b0110030035252030703080c05007c0c0c0c4001c025940004030341040101e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 436664541 1250 436663291 436663313
    0x2070501110a08090d0f050a080702070f0b090315040f0f0c2102030c01020606010504140f12010605101806050304050c19050a0603060305060f060105070f0602070c0b0a0903060b03010212090307 85
    0x91305207401c442060b42d070708002c2d081c0c8c0a1041d5a81c04c1c02000c1001408584c42000365500a080c0b5041120016640344480e000907400b6592003402070080c55848040f11840f841e00a000f26842441600000700030385a00d62250b002e18412a03603071025141c0001c102c203211000c0040d000403a1580c03101c0c0052841054034102400607810f0541d00b10b54108111680c00c1420b94040780c80b21403055003e030410b030380004d041d200c1c902507855018070184e0113945010300552200e8290380c0d05448820300c0d42c4100c0c00a5825900c20803e19000c054000014011140702d0006503401500c0f5100b1146007903000c00c00242908110401e43c00304144460003048030340781008002008040c182010408242076850b1940c81c2d032070060010000c50b201402281090f407084c1c08460303a0360307004080d0054080c0c1500d041000782d03006240c2994420703415800495071220325001c80704105880d80300c542040b49550707602d0028103000d8880540c995828001c00b552466002041031280c00408051540c50400380780c0441c0b006 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 436665791 1250 436664541 436664563
    0x20c0f0a0309050f030c030d0509010c020d050a050118080f0d063303021303140a050a0501021c060605031924031403040614090a0906150e1c0602070501110a0809 71
    0x35100c5101d00b02c0581f00441c00c0b002031010303803400701d660f01c05031001a105030b151068000d400c415040071240900030046840010f0b10300c144003c4c000d141c040c141c1d10800b100c200b9409821427404100060503468118002c01400101e4180851110f986030b04004800220b8291030303200c03248134036100e00e4900051500700a000d800b03080440c281384e4005c00718200c49249000081149044a9800400c0c1c1c3e07040148540322548202100c80e100102c2c81c0c1039010750403495002c3c5408103000d031010f10080b07150146105591003613613520f055070740f0008524108064644102403066580c1154004840040070340701044810700d0029500600d1450701c2d03403038190340084240b00d0750001e0009111680e40000301c5043d494442e0b484540300d0400c0c2d000a46450307256480341200d40d180c16000500c05038460a0707061a05c03076540300c0110401344541030080440405140d01600d0395190382c80800240117074003920300d00340900000551035550540c5c03042c003948020240000310381c4207401c10440000410032107c0c00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 436667041 1250 436665791 436665793
    0x90c04061e0515040306090503070b09070e130f0b181c0e0604080d0f030f060f1806083301030506100b0a05040605160f03080603280303020c0f0a0309050f03 69
    0x106543e18000700b601441c040209025182c6492206000d400c02c241d400e40c3c0c0d00880a10038908007102c0f49070b038031705051107000d1380c0304000000039010b241c540700f000c607007a80c02c514018404000d6546084800000400d00c9800da08a1710111821203010070219111a20102003445007a070408070240460349040c8045200e13620801051002c25400b04031203c580c40113050251903a403050310141c000d0b002a07421100b03c2d0b46060070006055648043e02011200c040648901400444031440240d41a9001d1103500b0340c0000507006502c018540420022440b007081082d2400031060038640740c030002c0e0b2054405134007c3c01481000040020000d00902d014003403d45000d0039250050aa4003841c41010244003012071482009846281114001a84184510541d48407881c029082090965005000744501500b811a0064484002a1190140720555911915681e08401943c003108203410a0700440d225035000c41d400b0420403001520035111110020700380f8081c4240811030204e10f902c2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 436668291 1250 436667041 436667059
    0xa0606060e09220503040e13061a1806010e03011407080c120c0715180318030512030a0e06010e04060b060711090a0b03030a0815010f080f090c04061e05 67
    0x101e42000700320100307036600b0f086079003401a8103080003030841c01203511000304650400200200d045441c0d415458140c40b40c4010002d0007942c0811100ba983c805001e41d400071200155a6140c0d0142e0014540c0054145843c0404403030a00c00301342507035402c00e081500956048207100600f83c001c5400b0341d0080a070806030f410020750001d1901500c1c006014008c00800000e0032105102d41c0c11011200c1e40c4015030240a49401c0540c02c0110f010300240c290002400610b440d519444082c00d1002101d400500810f054400d5000030040c5a1014007000301050f582c2d080790124010a00c5000d00a11380d5a040301c0003071819041c5182070f900d0082c00b0034031407a13080041c440010703c035450400381e00c082a01d0220072555090318600003040d6a191550b890f2001241160360940c1c40390900d440755203640c0c081030030785d0909001550543d4040d4031400104500b80000781c0390b002d105044640c840107210803200145600c0c0042406c8560030f801c2141544080c0c8000b4a149400795202c100814003030311180c0b5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 436669541 1250 436668291 436668301
    0x90b0606090102070621020c030a0f180506161a09070e011503090510020f040f0f0308040e1003020d0309050102060f090c01031a04050a0902090109021c0e0f0a0606060e09 75
    0x503c440213406050103000301c0f020f07501141c22506d0902c11110041210840d9100c00c0c1d0701d0415600e4010b1400200010911005444030a00c646070031401c0080896a03015040d003404100045500422420b950744d104000f1000702140407840003645503981c060f412149400c0843e20303d0b003854440e401180385160f54400402c420080c051100c8802d102d2882c3c0011000e1039031030018108002c0c4c000d030101d80b03400480d000034645001c42c0140100c52011861807003946d40d0b20500c084004c16403001a202540601c0104030000c006545103900815407440c20864944070750004240c0001c07002c3c20740001d0b0300400f090250794ac0421401703030843c42989000313181e032800941e506d568a081001460400d91100c40910719030b00c03295100841c0801c010820700140c941116807d0040c040807206a1103070b686080006440ca07620301c200d030045104040c1d44046400140d02406c00b5001c50f40c140c00e000d105222400d80207405c02d10052003540e200e40c10100d0750307030b01e8030b10002e01c81000c03040300030302c10407000c41802 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 436670791 1250 436669541 436669543
    0xd020708031014180403050c0a0b01090605040605060a0e060d0204060309120c0f030e010c0b0a02070201090e040b061504050306040302300418020c060406090303050f0601080f090c0d0303090b0606090102 89
    0x2d01ca0007134120846100c1c0d66070740f038102c4450164030196103003441130f064000d04106500000c52705840250404206055940b41004107641e040d02ca0780390845400c100e607445c00382c410815800140d00291000e454202a00ba100089900640c041d00010381c5d60b000c0e8004004041c003031842c02da40c152800c50b06c00c1c3c0032920341141c003642e00300000f4240141c0c0014907001d80d006040c080f0025801045150152800c11b0015010b544070280032400180d01c90f901054602a445400e40119004140213065555031001c3c0000d9103900c81184400303407000e0000092540d000c0054900c107504c030b035000d13240c844c3e8404008400645000400520101c400446400300c0c03001c075003620304840e04105001c01c151880c03040d110080c482c80304c5071800f5000d0f61041006000841c0c11018103548241da0800040d596114903a0086100f958a180024400d9000c249003024102d2400c1d000002c20003944c41c2e041e244030018202e00c803103a0b004c4011a03118440e171402e000c00d90321856030114050300c031646401030f500d00003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 436672041 1250 436670791 436670809
    0x30f0b03150703111206030d08071d0a0306060b09090c0f0a140c0a05060708070e0906060a090807060e030f01021813090203070603020403060b0307031e0302030d020708031014 77
    0xc15920448040002d603080e10036040603200d104080041c3d680e50304108441400d0314000c9a405009110704242c56560034030940c0a01d1060f940b55480420400803428484064203503001c20316400100c4030300100c0030940d903108890040406035502e980c0c402c2c040051241c04080109007820320b82d001c1c48103555056409023200e0781c0c184603240c010301c600c500d444c1ca00041d0050241c0040a840758403000400c00c01d000580310300407151601e40d6141e980d02c2c0300b021202c0f0300c1c1582c199500480002c01140442c180741c0054080d128082c2441105c1944034504145807828540c0024005030341d194850446080c28810300307040307e1205000790f1804051408070904c0d0008100028010071100070340ea00036841e1a030040f03a98030f600400352181c10307a07210002400ba401501044d20640e20b03100c0640a5841d00280082c120303640038042248034000595546880c4592040640a60204004192120080388000c0c40d0281c0700d0207040d616401c0190038016074510340c0d000784c840312080100c0b26441c1c0c2d44050071 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 436673291 1250 436672041 436672063
    0x312180f0d02100902010c05010507080103170403021e011205091b0f030c061b0714040501090b0f010503100f03120905030703030c3305070305060607030918060513020a030f0b03 78
    0xf0208030200c15100403903141c1011500074142c0c1d460f02007880354043d4800c501d14102c03800703805d01d284510300f900c02e4008648900d101c029813144001101c2c503800700d12a5007680c00e41d8014101100402203505c00700c01918412030300f9102540003030000507000c00049100480d100c5c01038865284070300c03058011980e140a0300860510414020500866108800c0200170008203880d080c1c0d0752090b924072004480e01d41140c4410300c120308100010034071200522030307281100c2000303280041c1124800010b50302e5502c060118814920f13050b50209903200c40b0b102c1c60000f03502c07801d00c05007550f0000500a0003c0581d401092207504600d00400220364810800d6a0030340e080600f1019128003807412400e24422081402c3c1101c140d030b0183c00201185170b12142c400c0300f00d031320b0911891f5070311002c012451142c0c85004002c995210414424945055030416500c014054000391868840300050303104503050150585054000a03034401d500d5050141c0c0e01810789000044c40041039410000e031700c808946403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 436674541 1250 436673291 436673323
    0x6130f0b0a0914150109050a0b06040e240f011206050d0507030c060203041a0a0e0a12050708032a0c120a201c0201020c0402030903040603061409040f03020312180f0d02 74
    0x101240c181c11076640042780300d14004202682d529070354040380c0d04400044944220014030114144000f005010399a0b0505c44000c1030b130b212071111480103507540d840d850448002159904804103607500c6004091072114000c00007131503020314600c3e006015075a2030b0007220854100740010400c1c1102c40d4542c0500d050702c02100e540b12828072a0440c0c803200604016940146041000a02e0801082000d81414000e90170784030455150840700c0d680c0d04c10318101038000c440c14800803082000c1c010958100411800c1900c028058250000d804518100070680850304094916400c11913108141840c0f0a02c8190103003a0419280004841c0300d06079000014482d040302a03030003160720a0200c078070040b50041c0b0440d2a410550902941c9401c40d00800340424546440411800b851801181d09410000c0c11a40e042c0d580f9910b80c14401307101c55048040d413106108500403031a002003450b1154510726030504545400e91031583c6040ca00950203260307904100b0540da511a8040b0b0b0100076005d405c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 436675791 1250 436674541 436674551
    0x9150c030a020706020d020315040905070504020c03041205010c080709052202090d2409020a120c090207030315121a071103070818060c06130f0b0a0914150109 70
    0x707003001029210b81d403001000c0e00c3c800a0000300465081c0c1c048d6000e21459007911140118800034401110803900e0003802d141d100310000c2115103095002088181c100710241c90800b035484560844500744414100ca00b65110000e000109500810062b8044914540001001c6c54036021814002c540d841d14006a850160f0240c41001c01d601200c2d0303d8035000e05032000702d1002d8100151f04040e480e40c0004654041c0301d102800c42d0840c0140840b003034005015084503440d0105240200c6403050048460301d41c03c0d200000e00d0180c3e232000c2c0c607009000380c501058008001c241c030920a420b94105002007030340340741c0c0d01d0046074540c030f1044800428400c50011503190b540095510b08070012600f041c0303120001c0c000040018002c0900440184001c2d40f00301d1072078038010410f15000c3c0f003100c41160b5000300001042100d55004801c40705008211400020300d80b615181e48003842101e4408000741c0b1103000d20b0410501480c0801c24030000005000003401032520310940c030b8410701c00c2d000401d44403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 436677041 1250 436675791 436675801
    0xb1f12080c0a0b0103020901140105091c0503070b090c060c0c040e19060603050d0f02100c140f090906100c060b12030c0610091b0302031003050d051209150c03 70
    0x240c0c00721160001e070300c000c64030200710340d1400301811402400120702a00c500000082c030a13030315101c40d40d5002416100c1504206a400a1040c0500c00e02280341354000da401c505c6020071001d00c02012420f0141c8290400c61030329000c00d5191a00c05540d46006240410039201c20607400304620881e510202c5012450294205100c0e01e0103001c585005550801d410300c82e8108015231307020f9401c4900c500255a500c00018400780c40161084080e540541c0002074001040c89481d03002c101d051105091802c012068550422140c2d0820b5803c905684800a0310303120f01c2c50441e2400e540180d0440740c1d01c00c00582d15000a24480c0000d000030122611180c010500340c0d941d10801400880740c2d800c80f0780780c1c000640003956900c17007903510407981000c079500440c104101e40550f0080c20b0130758020440c01000c203001240254030081880b804169606d00c0800007850500981000300c0310390340c6494603514039071000788031804003030100e03603103076116480d02c6440c0c0b10b40004055100c0700c01043c10f5180e40c0d0b1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 436678291 1250 436677041 436677053
    0x1706090106050901230d021e1c08040e07051312020f0d021f0e09090706110f0d0f02010e0f0d09060c020a0303110a0b0723120f060a120f0b1f12 63
    0x3001d130000e500042019164040782da0b0301042c2300201d01c3c2210958007030700100e10341099040c400d80d0003824080b01000280318a9205180b41600aa25443c040b40303031003199120340e0744040441c0c002c400300040104881041d0310b800007039404542800c0369440ea00d03042c41d038000384020009050f40c101c1d5040241c4010381c02c5014090782e132000d0b50082e210452138038001e43c3c107640703902c031500030072012555103880e2440000740001d0181003c0b40d150000c240d01c2c4031602d0161110303016000c0c4a13003150340715003201e19028000d1000e07803490102d0900900d0144404100600b040d03c00b5000b08081055003803c000c0907030b171220a6101146c1e014208a0045400e61031802c1c1806994103000e070095201c4800c0c0031405520510316034001041807041003000c3d403880701120292007000794262101882c2000324800040000040c0d420003001000c114140342d440705c40010b20880708c641510654200c170071040501600e030402681c8603042d525480d501c940c54440d20a90303081c5030b0144030028180c4078148030030042 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 436679541 1250 436678291 436678309
    0xc10090302031009120203160206031b0c0604050601150903080d15081b0907020604020915041e1a0d03030c03060e180f0105060a0b070507170609010605090123 70
    0x41c0160a40d0500b2009007000d1000c0c040349241144ca80f845112844541407010040c0e4100c641400e034080c60104507502040404d810140500c140140d005111104070441e28000740203000c80d11010740150301c1c02d800c01c40d040200580c4094901868100380f10107243d442045501500d601002030381e1112100a2002c1c000c2c01c8483c144a01508500004030380c003c400503d8074103100c1c03104014010324080c10140404600141c401d0009070344000d0203c1c0051411044042c0d105c3c249801034441a010000020141e07000105011088081e03400021040c03115400303010f0f000c0c00844080c0c61000b50010100e2001c180021014040550303601c00002c40501c6034000e040200700c6058003200904101d01242040015811607010710b10901a0794000fa1906018070341c41414001c00c11059245480c50f848940e6212510849071030084aa000c1000409a0b0b01e20880e504030724004c280524002e28401c1c21a91150000c621454000004000300900101e46910041225007251200040c604c04a15102 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 436680791 1250 436679541 436679543
    0x1209120c030a0311010501090c08010e180d0c0317070c080a0507081803100902131109060703020d09081b0d08070210020303071205040b0f06190e07030e030c0c100903 73
    0x401241818400e0660051507a245480d240000701b0090340da5040407070071164450309400101e500400100180c0c0b01c222500c41c0d01200c080c0324560020490600b450402c01e200031410f0215014030740d50000d2551152419801401e4500a4812030034600009000380c1e06c06030000340010400962141c080c1c0c42107042d22801503001c004180c58622003824002e4006c100b1051600a00c281510307124824028040c0c0d0190301e030003410340000034a580840c44058409889080c4412404004071046600c501c80200a228040d50142c84600000360b0024140300d5103901c401d00d41e03480340301c1c02c0441c1c0030661100340744801c0c00c64280c036801e080342c41c0c049040d00420300065444079030503895003111034010004520821341a030b00c81e90403072001242070701140d4081d2009450440c2d00c00009005140a001ca40d80160000b0010401080810f031030100000745030704501001405402071100741d83e054040d9210300c2c040c401c0510305096418080381d503940c2c403d0561621034142c1448502600740107008000181d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 436682041 1250 436680791 436680793
    0xb16170f07060c230d09020612090c090907060f17041406090f060a0203060103060305190210050306091f1503090507050d08070b0a06120b0702010507021209120c03 72
    0x6421031040200c141d40000300152412410400302001c0d40e481400c101400d21a9403920304003200c104100b40302d2a07003002c0c035120030301c0740e941c1c2d060409a03598030041c0031503080c0c1e04a0036100b03182c410080d0307050603860000f20780034442030300030710040f1800460355005072080c3e40703003c5000000071442100c40200d8400d440802e41090000d00c418041c3c400f0041d9240c16014080b1a515103581c10b1055645500301c1f0004944d801c0800815079248186c1c0013190003103014980407504580325102c09007000100c0200b03070360b110100092401181040300608038051210f050040c110b04e00000820382010b00100380024000e00990460203010422240d03101130701d03441c03900800c008000c02c00500180000002035501c1c0c420346200081d05e240c1800e410300140d900c12540380c00d0003426600c842e00c000029090001d2661078140c08504105e14075401e800442c000c80c140e13040d5090041029003161809821581150040c10b02d9004c000112000c8440c0c40030207170f42100c070400d000c5100a04000d19100d031542d01d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 436683291 1250 436682041 436682047
    0x20309040f1b020f100e030706180618022b0b010816050618010f09031a01050f09010305030414010216080309090f01050102061302030c15220b1617 65
    0x1d07099059019400480d451001d902e01412880380681e6254284000d8000301c0c0e0200200c01100c0401c3d41107061a80c1c142400c4034140800307941c8060949010031702030b0f940484104902014011140074007022031002d40d201c8004038030703c0d401161071650600000440000c0c000d180c60841c40d212100340c18880d0700007031070501c15616010303e10380340c25003d000f00c3c0c042e6040c0500419940740140480e07800d031000304440c060041d42000107450342c0c0d0074149480c060151004000003c2540842c3c08070702e900511044a54640c1031a0800168107103031210607015a1000005100084001040b10150741c4c2140303150000320031030b0b40103e2900d136125191003501300e9400d400040041000000d480c2e508800c030303106441c0303683c5c0003800c5051400074800d03503005a1084c00442d0304400000035584040d4009010b5841003c2060042034900014011000412000145140d0f071810349400d1344640345904030300c9004e802d01e44410380c0b40500a92001040050251380b00c2c00810960b0f030b0b100521102c0b0540c80760b032 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 436684541 1250 436683291 436683311
    0x4020d17070b0a050610050c0a170d090813080312010303030b1504090506090c030403080106081b0a08010302040f180b100f03080c0c0a03030f030f0e01110904060906032102030904 79
    0x6404c0c00d8946900400c01004441050f07401903050314003050810b0010009000242c50300300c0403142010842c0a030318400c01891850012500500c2da1040c040c00149541715890b044201c5584a182c0c04032140d80c106122a504025a1040583c11070b03070189070100b040f0180030001081c82014800c000041c010001e400200001c26070000c0e4422642110003404a5035283c000341c145100480303009001030403800040c441d0500030942c60781c01140400b480310020a299078054a0f85c3d00142d800d80c045260705004208500c0c290003070346108090341c20203211046810004940c002020704c4010849140c82000402c040e0100003084002c0040328810032085580703041840069200c42c4008540e40140303600640320380ad101040c07030b0880341d2645e210026240d5800c0100d00400d0309102d1414040d031103900e82c82054400b4003070401d0201d00c4040103075456000703004120466940384e011030452414000108046000e469461940d44840c0c4103903201d900807048202e046200359a0801c0c0d000b403500728145 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 436685791 1250 436684541 436684561
    0xc04060315051b0a0f030f02160b0106210906090210080a0b030c0a120f060518070e0c03060105070309091103010519031718280e04020d17070b 63
    0x4081c400c4121420466510b401d0f400310749107079102500460024081010010140c0b0448500d03148140710b24002a94035a0b00c00400c05a03070203042c65042540c07000c0c6051041c410307007181c8a4010710302400c00b4600c0007150700401c80c03d01ea2120400701c025540d91500c0081c0500ca4200c220010760040018079900200c000c00350082c14203071041800140ba040107001d003800c0004d4003030b8050000a0591031074515194640c0c68122070f421b0222071003403c6500400c0003a15600980c0d0068100a01c8041c29140e454040362070002c25600a034020f100c1c03142031261802e007003001c4131741150017881d14903a80e46250034242d43d840c0d5603030302418107d4903000031032040c2c00491002c2d5040c0c40c8105c8400c01d0b01842e045124102d0720700341c0000b403d02c8840e0a0242a500300c11001000415124150240f0300d002c84e20004100b03802e03800990024030101c40707001180c9012800300c071029040c0c0e0855203e241c00e0030b4001c140c000d15440741c01007018003109d0000c428080f4600907100d20700d51081821031589490366070700c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 436687041 1250 436685791 436685813
    0x60703110910020d120621060e070608190203010f0608040503040305070e04020f01021f1503210201060f061403070522140a1409060a120b2a07060c020c040603 70
    0x704c80098014107a081d441c45060044800715814998a015018013440c060f90320000c6200086441c269240040e8070351007014085c0308010700c05900c41181518044040c440c51908071003034405660700c1000140310245c688164082600c802e4a40b01800ea0340d00c3c40c08a103144142e40000d0041d2082103070000e0501031003507003d44280e2080c0c401c034102e98004401a0b13612030070700090807044a00019082041801c0b07900c24100d0070070001d8050012945ca483c0d8450040d1540b03036034101010203210b25054140c0900480e00101200446d0610092502000a0204c59403410350540310000001080007507101310152600341e50800614613481540c0e4016142e508054807462011080021100300d05150198450045400061000b90740e0351440d0104034104500801c215442251044045043c116041e8031198079071080e0b0341c0325841c0c01c141782220a00b001002c80c15500c0c400d9036400441c2c207041801a10001e550100f0b000c1000721040300c0603820105110384807504149420f4000041c0000c030300c81 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 436688291 1250 436687041 436687063
    0x3081605070e1b0315010c15090516050d0206030106030504080904180201030c080603120903070b03040f0c050d02280302030d050d0b0a050d020d080d0510080d0e0306070311091002 79
    0x100c498078024035042c0744402c0c0000c1726000200003800c04d8903001c030f502401d0360300d14051058400c41000c10441052204480c80c10005840075802001000e042c010503c08000281c038040755000c024000070b03800111148014002d950070503849201180c10041880c050381c00c1180010424005840511b14000c2d541c404848143d00003824844d1190030310340504540350081c8006000350a0900e04046408015482000e10a42520034248000741007000c3d100034600662107500e0000350b0b0882e508089880304803540025208a8084a00d100141c0e504030905070814840791603641002c201e900c00b482184496407001c3d401d800b440101405080e8004028903c018156504100b5103940b01c06200f200c0302180111500070f031040701400054603180c600c01e681c0b10305c10142203250070002251081074900a40382200181e41c3c034070b814081e00200340002c004541d80c519206040361100d100107a6104409000d00090680d5810303c00c8042245008032607152001a041c0700750144407441c002e50b50020104 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 436689541 1250 436688291 436688311
    0x12020c03030f250206010b070f0503040b042301020d08181005071b080d090c0f03030906030c080f0a0509120f040501032d27060605040b010c0203030403081605070e 72
    0x60b6500c3c61200401e00031402150740101860fa003002900e80061b4420203003501c50003e246569800502e0030001000a0405881c105407683d262540400c81800e0241001a04600c80070040b28640d0780021030803140f001a00d0070030450745550f0048003680c3e08881c0650b01034056100285d004264580213140181c0156590b940c115000c0d514a101050020200801c00038041100640e5000c054001e0345245000d44048010320b903440e1080d04044216074421008036007500e504200d120340600c511202c00729107041600079440c14850a01011030000e1401d110107544070045102807404104510091003c0c43c0a503594040001c50712006810500c5814002414074203e060044004015101600d11806100e4500c08031858114041c203030402d0b00417590035030f182c41d80b5007600840884c01c195034040c3c40c1c000342c0207040a040c00243e40300d410f5518140070800c0260401620000101c03030403280c0180849460b0816046045802d05c010310f0f015140340308201d008503c490b078001880e8052407420f0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 436690647 1106 436689541 436689571
    0x10b03041103070e061302040e061201020d0c0c140a0b0f04290a0507050a17090a02120601091a0a0e18030a020c121c12020c03030f 58
    0x41d02104882004d14140261400c00d40c0c502c01411955104c03d502c0c05041c80e507000b400040243c00c0d00d00032a0542411210380d10f080d07041d00c0c00d0664188050201c900400070080c50b1b1840c888065605040c3c1c1d407008051541c000450b45166540041c2e6640c442d0745004000d1b01c0300d500203005036002e00c0c0303401c91064110000602c000f0903650380e200325151400d001303074028120340000300308030248581040400c005a811100324440c4804000510b042d561712407508508203810808020b410089201000da0280c001240860607110419000c0181d011541e04020011150b441c4250300544112004e003d00000c0058041d1312011850f0b605006c5443c0710140751659203c1c0c0103410044e040005910158a00420071701e100054180c000c08045070703803c1c022100805000700c080148480d012074080c0500b802d0301070700d404044190a030380d1a450324202a2288450880d0f000c0d460710800 = true := by decide +kernel

theorem cover : BRFrame.Cov 436510791 436690647 := by
  have h0 := BRFrame.cov_init 436510791
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436510791 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 436510791 ≤ n) (h2 : n < 436690647) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
