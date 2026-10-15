-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4930
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:11:32.43015+00:00
-- url     : https://prove2.me/submissions/17ae9b0a-0f85-44f0-98af-cc8a6d7b1f8f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 886510791 ≤ n < 886690647 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 886512041 1250 886510791 886510853
    0xd270501090605090c10030b150d02220621020403050d020307031409090601080604090605100609051f050c0c030d0804050c031c050a02101b020d08150906040b0d 71
    0x1040c0310901c40c4000d051101901d64130003044000e23225039040f960b001441c140070801c510f40e010700201215244508050b0361a1986d00c10100e42c83c845c02c02c0300c00c500f40312040500210768400080e00c094140c2512202d24441c40e0300e808802442158801410341c42110a00c801c0c180d008800750007054080d0302c1c2e0350f412100381a1801c82030320407800f0650313100d00c0c00000100250300600c3e180c1e400c56805400054642541d507214001c0f22829110300e6040d01010300c00b0046650300290785000b80a0940e01c04500018940e02c4145429109514400340040400c0100b4100b104001d2150215002002c840c401c403015200900600802e54066642d806001202c0d0342c0d906002032020407500000004d2142c100c0c14802c01c8904e034100c80800d10440c01801c841e401041c1081c0901144003c151840225030300200502074a4001d842403108107202c8803001304000c070002040074038800070050340d05034025500c507000103000b0030f03a00204550001c20231102d803043c0160000382c40000c010323242000e00a0581 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 886513291 1250 886512041 886512043
    0x17012c07090b09040f29150a0f0902090310090c18020a0903140c04090803070206010e13080d1107140f0f0316060605030a05030a080601140d27050109060509 69
    0x2c03015140e5084403aa2020400048507071408440043c011018058081249024905c06082c2201e20004295002e01446205205840004c10840040360106042d0349410940d00e13182a091046502155020404400395281800696407030f00201c6002c00003c1154038104400e440c19010700c0c0130745481600600f83d01d40c924030844000104503240c00e100c3c9071550f40e40b590600084201c40d000350140c4103540c503154a0741d00032038004031b104008098503450594002031a00f80140e01240c1c02c0d001c58030034011040588181c402656422480c510f03501c203411510380c070107040d01c102c1c403070420310002450340244003021a0b0140b00d618000c041d01e440022941c1c07000e0b40c0d600085143d800315041040400d10400410706104101c900c90803000c40c406659500107410a0030480d0180d8841d0000900c00100a030301010441e800102420701d000c071078440700329030f009a000d80504803e115a85681160740d1102d00304603880324104020a407040001145406406452011402c681e00d5042c003000ca02d103410 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 886514541 1250 886513291 886513301
    0x3110705010e0612100816150c030903170f0c012414010302090d020a03050618190201031d060c0c01050c0406080c03040c120c081902060417012c0709 66
    0x20001c281c5820032181c1160451403402c050417003103441c0c2210380002200881401016a100c0030302d482d007040c180c0303841c1c40a400380d0000d0b01000304211a1102103c0043d80003011981a03c1d003010344178000840c1e0814801c000c0c131031220fa10901520115011a086a054020740c48044502d0295103014001c0e0700c0b0051070031014000c08510080d2100d840303c1c01e52280e8003074903401d03000400c080b12904084d000f007403040080c2c1c0c0050307034560800c038108000c072288100c401d00505010b00007480c0c0782c2c52038034140c4080001114000d0404d908d6160b014070442082998000c00c00011083d620390781050319450744260b2110715903001c29400c00000070320040720704058804940d400d80703501c4107540c0c404041c0321596100404c01c48011100403408150b414044a044890500c82e00d80044083d080c41c0850340340172003641c4165000c03001e9680e64070040e141d007401d98003203841c26010101c80e208004202800740154040501e241c078010003080444e501841044403a2990f0764081d922080e03142c8400c0000e903a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 886515791 1250 886514541 886514567
    0xd0801030308071107090509030a140c071503090c2d080709090321050609090316260d230106020307030804020d1505090c0301270218040311070501 65
    0x5070201c40020b100782c2c0100030b0340040403000b0301541d01046e2689541421200180c0701004650f001060414100f90030840728005500090001410300455004140d641d4007103004800120a403d9070020419020342c01c41c0c280f040e4480741e491682a21120642001038125030302d002c0e1484901090340c100c1022080b9501524000005002e00030f00340210b120103000c0e2041c0803400c0002440c000ca49220302c01069005002d20840089054144002042026040505540250b130002c000f050403003a0041c880304a8184c0c8541e28003c0307818070303546880768011500c1c1044045403001808150b07a110300da0110810184001c0410480b0305044070401d0380d214240a1100564801c008031008240500c0e00654403034802080b504d044041c139030322903503441d54052508040b180c0700c401b80008980b0902c103100c0580d406800801c1085410301410f541c41ca80400140d0711039142e9555002503464803da50241c40080028503c12400e007032a004020140300d904071070460041d00b42c04103071503101340540c2c261f00d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 886517041 1250 886515791 886515797
    0x6030203120a0203070813050f0a060509010c05100c0203190c0206040317090d050d080c0a05160c0302090c0315030705010816090302100e0a0b09061b0a051b030d08010303 75
    0x101c40d204005981d001c6090308095100902845000400080052410791100d10792911100c2c42d02084c04641800d510406205800440742407014540c098180c03680b50209103400040c1106074205107007000700300c481a501d00790625890078000340d0000000d2401e554000841c40c00742e030368200101c0e03e994810fa00290307c0f00c0c0c104400c10214082d20b2000151490880503186050701300c10020303000c1103c070802216107800514905035215000700030140d000d104101c41906d80300440d10010654031505842141c2c01c1030904140e070a10400908030000f4580c050900346c0241003102e10246650412a02c0c0d00ba00e407003844d000c50703903801c002c0350007800c030f9034181c4a003000340d100c20103000240701094555500308100c1c05800001750707562603036090141d8419103030a203043d440c110620170003100580101150000412020845403200d804440103000c0050340250401a0070301000e003848481c20015000d4440d00e40b10a040508200001c5446032007202141e00d10b0b05050802d070b9001c0000d100107004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 886518291 1250 886517041 886517053
    0x60b030702070e0c1305190801060e01091524170403030603140d0c0605060d02180712020405060f03100f0f170a031d0102030912011410081002212806030203 69
    0x1440c100f2032447c06c2c46043d000d442400f50b07a01c0780701d41c40c21103071294001d110108a22004020310302d118800e1200a400403c29100c01d80e0a0000380d00e00990301200c1d103143c0b208020300c00c5860902c249146003186420400710842c03402d080c240103028005030300042d035000e621b2a80c50b0a42550020305200038403a991140780211004d5181e800003483c0050806402910802c444001660340150008026101210300300d01424030810082642d03094032a503050305071041105108a507504025107075203500300404959266200c0c841205040900da2087c40202d03c141c10100d40c1c84685c520a4094454040d5004220b00500e0707000c940c0c40d01a40e001502040f01b2410300081410b00c035403140d048080600440c2d00d4040c002003c5520f84500170b4044200c2d940d41da800c1540714088582480d00859843c0f1440041c0d42402c001d01e81b1244ca00400f026100e50001d501c00380120701d0711420920403070300300b807400aa150800380f000703103030141080c0307080d8074000320003183c4050b5003074403419090343c3e0060001e00e8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 886519541 1250 886518291 886518299
    0x1080709051e0301050403021006090608121b12040905102108040503030d02040e0603070b0d050a1d030901081b0a0e130606020f070806010b12060103060b030702070e0c13 75
    0x20360503042c0906551814541c56075a1481d00c0074040c803805140700e58000c01d948862400c0340c50445007241c0000e40c17070300e042445c2000350480006081401c1111280300d01e5568200d02c90304004440641c1610350030b80102110105030008940152048403568a010f004030307034650b4050b0001200a002d1119588a2150303951003d504409003114080c2c4601c02e024074250b00d440020b0310f150008120b160459400040911100e1340644042e81c108038180c0c02880424100305403000b42d4001d83c0001141d041d07942001554a00540c0c006007000300961540b045061460710055480c0e82c4183c5105012940000100703841c20a00345a50300304505a144481c2004c000c400100c9082040d21115a440b5100103810103005460f44201c80062903d50000c2013290908045503090002c107a01410682d00007000401072147d5260480b000f118140c008048140e407040d005070020000e54000b0f12a61b0008010401016000580441034801c0d10301d0004132130356607071041c2d00c05e889543c041a282d00c96182d8100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 886520791 1250 886519541 886519549
    0x50a18060b180c0730051612030c2c010c0c0e0112020310090213050402010c0f11120a0c062105040302010c0e0609011d0406081c02010b0108070905 65
    0x1c45881c50080514010800004000c202198155000180c8203000240c07002044807155503807540d403088865542010070364844070b8038408040c01c00441440400640342c03100050b108443e070300c0700340c5c415071403105010411002401013881043c0000403a41c1229818020140c032102c8881108483c0d00140200c0c3d14500110b808100c1d02c001201c040040c030601054002c002c0c0b80300380c041e100030b80300c0c41441c07a070500406151940300240141021710303010a03400941c849240000388800c1142010803681c81d0391004032080240c1c0302020300000d9441c07000c08100403500826024122003101c400d07240b40b4400c840c143c2c440320350030b00c01019240b01e141c040141900a5000034000503111440000003050480c1c2d09003a5031041703d0440060755140e00d545100c54110b81145919171040c1c501504210329100042e0080c1d6002d52409501007840469070f0042d91140c00c51390252540784290348540c0e142a054070650f104900855002d5400c158a40006502c1a020f688c070468190361425051803802e0140 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 886522041 1250 886520791 886520801
    0x60c080f0103031808030301090b0a0515030103020f01091e090c050f0d110424023705010f0c21090b0f04080412080a030f11042601060b03040501050a1806 68
    0x569003240341d40d04c00140024144051402015802c00c0400d05c017625000300400818240c101c0b03071181921440c4a858002c100301513a042d00d03415591003004121802c01a106a00f50f50b2012035500c0443c3d80b415a0b82c10311494160465002140074452400801e02c251000c0c05100751180440100b4005110501103a40040e80585002448186043d071151030f00c10405070440555007911801c10300d41c1c00ca150341005600104545c5070a42250096002c442d0300e00c544a041d900f901c4000314040381c106116080d03000f0135425143d41d0042004041c01007028000b0b0b00a400d1086a1a0b181104440340210a001b58204c055104004150320f584640003c400100068030603102640180000701381e81006140101000d401030400300c0c0c0f01c003071481005064451070340c3e026540c0c1b42400300310300e40c0c86d40c40e009550076038410030701101d1a0451070074101424001451360409a41c00c182001071000440702c01580200c2c003480c02400341d0798494005a0994a00012043c0c96a0420308140c01140955000c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 886523291 1250 886522041 886522067
    0x30507050f03130812160801030210050304030e061303021f0f1b0c0902034305070b0f01030b25210f0e0d08040b070e03030f0a0309060c080f010303 65
    0x440300f0a03100c03a40300c00d00940c00c0041034014501100e0180b21600d15103106c50402c0c2c45092030908640c2d0f045a0204400610401c03c0a040c0302c0d010000c9030801d4094004c43d48006c00141526443d070300c032030a120b40d0148061100b40c0c0564800318921210440d682030b10b011680d85919603e070907031600701c000c0302c001c000610500003118080384820001237040400e10001c0082200150301e0f42042d1620401c841600100400303035100f400001c0841007001d41501c030584014194003d8070270312034241540c051103203500090a9200f114100080e18880c02003190583e8010b5500350101d0740c17105011120380681c02c500c9075003041c10350713040003c09114070381d0000003841031080480700e00d007000404801c0e07482d03005001100c2901e07441c13549540d5404025102e0b03100303070034504059981032130303140d0020b0840007401d558100181d0411b2130705152010011166203188485070150364400ca13080c020000e00b200a02164014280940340c41907500c81c0740ca00e030003402c2c6034000c0340f216440c40d0382c00c2d40c3e04850f00c86 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 886524541 1250 886523291 886523311
    0x105150c060702070501110c100806040b04060b03100605040b090f01050c0f01240b04120606030c03060207201806031c02070801050c0c07180b0402070807060c030507050f03 76
    0x103000c0025801d0084a000d19503540040c4043c9007403600140c034080c042102e4081940c0003031030b0840030b5514661496003600380c1d4108007246803103060101d4040c3c1081e0036280d400900305500003c507107884400941c42040e0540c1907a2445440d0401243c15105510403030100700002d10645c5524640300f0401d500302c07501410294135000760006094208400800760001c2c59540718401c100700704003181d00c6458008030b1052103943c80c1c18490003280c280038138001d85801300b4410118808200c5140e00a001a5230841e0780c2030221940e07813400c400a54080d9400312486600c0ca501c031141d04440184d41d00d14018001c111580c20300d401e091001d40c039400108021741c0340c490010101344810098161080014040d8040c08070142012081800d503240900000c0d1603000c200714880340344070b001c111901550031401c0d000410106040700784c4041d10000b241a03500600c00940001006294030081040c541b24280900083d00d40d50340980889100701c0700000451801c010344110304440e50011640041241 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 886525791 1250 886524541 886524547
    0x402192604060c02010f18030c1a01030b1602031e07020d02041a040b06071a10080330070221120103032705010c0312020c121306080f010515 62
    0x300399018015400d8805884440d41c07000c04964155080c01003030640c07901c074942480100726090000c1180d400c0c85e20054100100102c40708108107000b517906151070240d9022103101c0d41c517400d003404200c1e425130751035628a444410130541680003106490701c1c50716280b9500b80851041c0400441c940c84190200c0c0d2200c100080e6a00680d07075846816680c00080c01d003001079841c3d030414002100e040d80101031180900b8050000042c00c0140c1074003c01034000c1c090340041e00c0b007000801c541d0380142c11074500c500010841001d409000c2d0701c80039208074071101e15042501240314140c4451400d40791080180c220004100c006001620071140c0b0241c2d580c0b00c149428406208001c5a14003a0002c034001100315190210111880340c14a4030720303040280706000369241c000060640141e91034005c09000001d20f819000e0b50542e13060b00c88445e48007054401d0400c002217a030b045076010707407400780d80e1259000d0081401403081103d58419065034048998603424502082036040594048032020b00d420 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 886527041 1250 886525791 886525847
    0x7200106090c0f03180f03051908040c091406011d09090601030b181f0905011401030b1f03020609030f030d05010f0b2502030c060705070f05040219 65
    0xd10a140c02442041e00000c2c800060600c01041e0414401c1050101802e2030120308914240301c8a04154a620140c0c049480115140a44c0c55008400c01100f07400c5500a40500c000d400c00c0810340314074400c8051000058640b0000400c448080c1145090a100706001801d2940582200d80c540903094050040c94030b11040090710078081169035070b070f50781c000380b00400410410641c00f0707801117034101000c1c1c1c41d406220001540d840c00503261403059201c010302c8070b00d81030326a4031500d44d044c0c0000082c0500008041110100c24003071004844403c04000043c0351480c40b082c18000c015601c900c0c0503415887d540030045076030480010b065150240341e02900656004000a200003998040301007815171608040400380c4203154450036680c14200500d103a000e00034445450b9001c0440d540201604403400804d03e40900203049a4000c140001c01c1020300100103080000c40302840d264680d02902d46040c0801c1c0c1c068480499085090700c0b41074000c0303500035007401c0c041e22460000b043c940204 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 886528291 1250 886527041 886527043
    0x507140a120b0f15041502010c0f081f09050411010302180f0325290f0c0f01020a02032805091e0d08091903080313060603080c0303010f060806090720 66
    0x503080c80c0113007814001500b000f45074440c400200e2411002e000800c02d403500783c003016001100d2403410302e041101320000038401c01480038180e611800018000640c2c076840707907106002000240c8003961010096042c80c50550300c139000310303400e003800d03907006100c502184820f000d101003c09040c1c5605003c0e4017040100b6003038200170b04800350308800e10000040c1ca000e2001f800144860380c03903580400d8050740240643c4c014801c0392403450610101c15603510860325401d0801e0026240c103182d550000135003242c0e15a0020140100041d610004200c04440e40d00100e14010681c11001c0850b40a1008503403610342580d05020201400b8138200d00108a02c0c00210340002100086683c1d050210b40000d507400c1201103111851210041103890500f5916906800d01004045042d003801084100f070401410b508210005c592012555846080c1003041d50b840350000d0281d04441200341d600043c00501c90000b042c000e040142c00d440440d00d92810407500c8400b50305100b065452240000131840b20 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 886529541 1250 886528291 886528309
    0xb0a1b05060f010f06090b030c0d2a030e010204180b06160309030b0108010b030615012109021504061d1c0f03020105090a241e0507140a120b0f 63
    0x75440030382e05a69810494043ca10003032941000e401c00084100c00d000000d2940101ca800034585040d00b5240c0407031400d814064003807200012180c600c102c00922403140c00c0754814404002548081c03185002c0c441245080b030040c0d1050b100c401c0102c0c00c80c4603610356254041c22500c18003600a9250041d0301781c50743c60386007c1c040100d00142c0504010828070900c0d20401380580020b40007804a480c4010009580e51405080b540c81da0040c4410b8000b2a8040c41c40b07070260030300100b05604084905a00d20b030040141541c140d0041e8811150840c491132060216001d0782d00b191240c00104074108a448407150814040507004281038171031422074155644420141340c800c2d0105030511440e89130090139140c1c042d0625085038001c0d001e410000399400b1080248000050038030a038944aa10098040e002d800e200c05584140302105202250301900294440c0c02c9946551011001c1c11031640301c10704c0340390b0101d40011940c00d03112034540c00c1074100c040c0c4100b0082520750701070407840000d51907035 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 886530791 1250 886529541 886529551
    0x70305030613050403020a0210021608010506151e0f04050d060b1801060509060309102a0207030201050706150810020417191b030524100b0a1b0506 65
    0x25002104100e400d00d800c100c5240302c000c4909041c401800e05a0f0080c3d6a8203170404004d00c1401595140c0c03141c244200b112a501c80c105201e08415203984045040c02040142e5041d0702a43d050032201d400030380d59004907019010303181c00c12090100441001d424a070050568031004000030000000d0380d80d04d1000060030180036640020324281424200300e41e404c1c0441c3c1c0b860700c01c0f414100410504e904001a2041042d05580d203503a2a0f4614042c2800c0045800000c15080c2ca011091103100700c58462141c01d01c0b1254000c0700100082c401c0a980e030f100c0350b10000740080c00410216000031899000001021002c0d000754800b640c590200900f84550344040503103c66001c1020040d242900c04120040d4070388401602d2000715183d0510350035a201d02015040010002ea00903403113040744025801160020b069030342010700300c0ca2440b02c18000ca144441e41001c0070001c101d42102c149684e80c22604984015442e080c1404016100740100b10b20071030710320542c0c45864010035020300c0524031032 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 886532041 1250 886530791 886530797
    0x60f0d050f150411040504020f0904060605040302090a022515050124031a010c17030705130501110706080c070c03050d08010e09060703110c010e011505100e040b0f060703 75
    0xd49072031215401906460070010f4400c0b400e00c101070002c00d03030007400c45080d1501500d02507a1b482920100c42140d01c01e0b901701c1074000d8a0300300009182640500980700350391080750b032980b56840302c00050701139000d02c8181d40c00c40d8000b1501f02c4a8590780e5659540078503c5549510320200300803001a04807002680407074200e140304501c2081008250b280184001c5041c00c08024051281c2000c0c60540d9000d100d2506010701510840c042c84890070401c07611202e000e498580c4c0340b030404801070283c0c00a499000020390a00c0c0c0c0815103600030704400504000420003800c090b442c001040310b0405018100c0071034080c2c108101004601c24030307880c002660040004044020000200500256051b4041117028849100740b00780c1c41c50204280742c1007049480c0c0425204030304002000300b8031415500840c55880d2003c03030701050b10190810302c0081c00b1300c40f4034441c403680c40741440360460f95110024000340161403580054a071a5018041286001d459001c542c1086408900607902006055002c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 886533291 1250 886532041 886532071
    0x130309031505011a0430021309050705010e03030d05100909050f1c090314070e0a0c021507050d0f0204080106061215150e15030109061a1305060f0d05 66
    0x250001d015a04d022403441510041d103014075144015410a8180c0e120303059901d68000740c100100103442c640c1b001da64006101c58005400029141d00806c0e86d400101d455008404002900b503010340c411922950025000c2c504e08640029a5401058004d144400303080f090100405d80000e244950a21640b2540040c111034a818805d2440e000b4482c0a0380c8603c810951231021082c2d022031040300b144c2c0e20040300c03402c488039404007504050f0913800c1403e46542c03d004200c200840d81d0444c0358a13201e55002d44040d0900d4440010407964100c81c801d0215000b0031121211024507406900c601c113981e800141016111040f190960700e007030740a040000c3c41c1e1b046400c007810341441000168403c004152030780924100d6440505669150100140182e580050b611500ea0002c6007903040511400543c0d00d6860311840030041029001d001c2c0310311740889403e0b01c036100c40d404a27400036000c2d41a08100602c2c0008102580c3e00040402c50519000c0c419900c1c02d01490150314017509400164042c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 886534541 1250 886533291 886533299
    0x905010605132103210f1b02010b031209012006040b0c0412171209060a060e06130903020715120c0e09071202040305120306150a020613030903150501 66
    0x140c1c04049801c0f50540616050514015000e0ba0307a01c0703955280e00d8144100c02400d10a01c00c0380c0e0400462441100900349014140100704a90010a82904980b4a03200e5600300c01c000b01c1c01c079158989139136007503070000c101d000402c0020300250a44030014500884a0035080c40c40090724002c000c0c1606e0307103074400001d010801140759440350f40500f01d0340c0741c2d6041500d48118a003040c801170070007418660000c0e540491034584130040301c1c40407403807030517101c010706120182560b56841143c0060f026454050301098442d40c0107603050007560000c3c1f50043c203000071f426400041c8103119040b03065110300c1c1000076a8409013034035010f0700c5000e80c0b5000d603803484515040301500d1880d5901c00c1000340a101000d115600c809642d5000862854514100a03590036507500900c076035007001d0564440c8082c94060408000000c0d0f104000c2516000d582c120b4814080c5100c1c060065100c0c0560081e100060901d850390707440740034035400f0b0b103000340c0c13429a42d403a4100502082c0d608024425250f50040c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 886535791 1250 886534541 886534567
    0x7030206061e150c0a0f1b03151a030d02030306041103071e1817120c060103150209090a053304151e17060f07080604060905010605 58
    0x59000740240c40603880d58003150a08420060110b90440c8200e680504482d8041c841c54191082400d00004807100b5000c00d0404004541070404c044401c605401d41c007002407400380c1242c4040303a030f101018000c10f03480d0182980252043c8290f440300c11841041003141c40d80d0030084110482c0b003d4014545c1d03400c0510030f1105079040c0d00380b1014504001c00501c20070310792000d20301e2401e001c0c49015280009088104850420350f448000910740d4043c40041081072480e20300c030102100300c0d4210f4001222400c0280d21030702a40142c0c02407a0801c2d401040498007610401d428001e002d00010702d01341480c1c001030b24414060b6003180c820b9595204101443d4550968569104c0140180c2c44c45070104041c10702142d2034407400640620f4481ca0354250750702090182c0c0014105050465090004042080084000706d10420000c880702e440304665103200401c000e4016541800e0150150780d8040054030401400380406820035902e10001403103224612540d8040c01645d1b41d4290380e200602c0c206 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 886537041 1250 886535791 886535803
    0x10f0f0806041e02010905060406031d01050402061903180c0501020d0e0901050d0c080106080309030d050a02070b09121b010e03151807230a06020303130b150312070302 74
    0x40256640000280004110803c0201d110046104561511008648012a0f41c1c28082e030009421007408500442e0643d09a0003d121500040008182c200b0300e01c900b240c240c5000341c8010f50042020005521000310032845082e40d401681004190040280400800361260440564400720314002c207011960381449402c0050407a0310b003180300da4a1000000d1850b400c107102c0c40d4072447c3d4443e9200100180740e04080014101d0344000c0040a65500d44039482c0d512213118140319002e51405962800e0181c020f4856122a5038010140320b410a0f48507501640304000c00c2d0382c80084000c44c0e0140800800402d0300c910710b42140e0b010b0b21203110f4005081c010306216109d110360000280d8240034016074043d1a4030420a2010040090140d6070041c20544213800c01380d401d100c46c4000034004884000a407203070003410f803241505035654040890f100e0105440c1d00140c0740102d841b100100315080c0c0c04035005002c60810201d40da903540300283c07070103e589419180c4d143c2c001c00c0240a05405110b0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 886538291 1250 886537041 886537049
    0x5071b0c031e020a0e181002040e06060a020607181502070f060e03120a030e25230411040f03051609050402030712062318030c0d030b03030c0303010f0f 67
    0xc2d40415044a41c00070b60181c4c402e000d01714009035084d00059002d1503003425032000b602d840d01942c10599021480d00041d610034000c2e020003d1241001c00d07a5070400c04200d41c2d40040070742c0a8030881d281c485040750710340c040d81115040c4042546003c80c2ca144003e07a82d40940d03402e3b40003001c0c4140303484061030515036107512031030622080220414035914046070070034000706044003030f0366250403d45050780101240107840c0010705c0394541c00c40765008141d4070107000c010711103456001d069440c0e01e1038010007600d6141322000d5a21f02e00300141d5003400d800c862203041c2c0e030780b040f6800d00c1c0d186d502010092105600591341c0b6070150003107a200801c1903645101a10403030005114520340340c2c0110795140050312681d154170041007d1701c0b080c03041da90700c508041c45c044028060032015102c0e0700c0240c2a0305403034107080c07403410004800c02c0c507000100700d0308041021409000450b90b403203030580c01003a40d0640a07405000400c87c10702000e00600056018014141c158010541050780240686989803c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 886539541 1250 886538291 886538333
    0x1080309010c06050603011d0a0b0c0702103c030b0d08090603100b28020609061302060d06080109050d0c0507030b0402040209040f020306130b0a0905071b0c03 70
    0xc1003203480d036400007502d8042074100c030022400c2e48030000806e00403c48411001c048107041c80001940340004952140341d1400b440500c0880d448042c031071886880356510082d801518406100303405809244071031503107d0300031011142d03040b82e507000001500c41c850f02c40038401009100e80003040d0301031047c040c1102d0709a4049407007114035911462240302e2544440c0c440c520100008901c250252600d8010b410381c0e8611356100e9006c0b103015210345024000041202007103422851102d0301c002009031140b40180004c0082d526000200c16100b1441c0c20280c1c1c02c90350812400d142000c0078000d940c020104100005480312080c2003107820400803101000411114402d1807010890005100d01500c3e0052076410140c0c1b84c910000d0020b208038642140c2103401c100e07100c480304a4550140d0711640c810b40b40281009005e040b0b400889980c440c42944c800d004000c04d01c01d101041e802160f00510f43e00303020140e0b811800000c0c00351140d0080071030740c1c1e4691070b00a0040004190111450a02c000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 886540791 1250 886539541 886539547
    0x304091805060411030f01020f0a03050a05190b0105070819091706060f01200601050f032109061303050a050d030212240a060e1503090307060e0132010803 68
    0x155a031a20b9840251018101500300d0801c04481d94080c403043c011003e80714003c56170b41c00c1d1901005041d810104103440460b16000008107200d40030f0043c2845448240d000d030b001254a200268020280500114104807040c03018000240712039000301001c4a5000c900a1001a1180020940041d076004100c444ca2480451449080d000403603d4105600f11000002e6410840040300c140c4200d4400c2111102000141407103080c010035654140c80c010f4940d01a103c4420b81419591a840b0115146840e200003004890484603c0504a044402880b003072a204d0030b0340035201c035400319401c151840e0b00070020010402c5001c21018000400302d080030350030310060424800c892070300204038180c1910406c00c03140c401007041c494040d16560003808420495250140188814910102c4d64010510700c008502201051025a4454848a070055190055a030b84038005020b5840c010b9160350b40300d008100c141c0c0000d2500c200403039000d82500c182a04101d1030803045400690041c4500d400c10 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 886542041 1250 886540791 886540793
    0x6140609031507020a06020a08152b0f050a0b0109180f02060705010e011a1503090a021c050a1101200c100908070312233903040918 58
    0x30403990030109904400328110f0303403051002e904007003500320005c3c070007440082c14080d80d035080000b50b4014030107954000c0003e20098244070311040a00400e00d161040c08200000e580e080d608030342c4401d0700c64904040c1203051613469900d07103011110210749401d2410010f21010a00344241403100c1407110080d055007a0070f07101c504200d1281e0001034080c074800154001031007025007210a4801141000f0015144201d081400495060446138480ca80300547e502003210310340283e03405141001c0244c03041300c016908100400000602e20b9005605000d00c0b000410130034410000c00902a10041c009101820001091052440d503240366040d5120201d500900000902424044058a04000c0c1c4025858207982100346988208001e00c1a4a00841000000104030030b000c0f031151520700e1300780d0988004a0110b2a1a64062100d00f410700c001089020a401802101c4140d05040b031261041d65901ca01c552914512101955200150400c000b84040c4507154004032201e4a0503400462 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 886543291 1250 886542041 886542043
    0x50a210c0c0b03130b25030516050901090906090b0117090604060c0201090b0103080a080108030f091306050607060519021c050612060907080d050301030201020a0b1b07060614060903 80
    0x72401a004082004000500580d10b10000980303040d820007020076041c50119040001041d40b2590758074038403c40841d8240890280c012a4024583c08c3c941020282076480101d403030f60404400141003003d400d2002070040400d210700005020144404540b4031807820014110b460200640005258108204400543c011810a800c240d01c900b0102d01220f00132002ca026102c9503801810a6800100000c2003082e03001c024000e410759030300e681003160b81c0c6165080e00e9015807000c40407041010040c0307c00c02e2400740f244d10503115645100003070494807000454055041060708070344440e900d078107000038402456010100c02c00c104e2815407411895a11a10b214ac400307090100313201d9210300104402d40d0381e05400551502a18040f110545024924940e5030001c5e80704030b220f54014600003000e091f104104a0303068030f40603001444100070783d03642c500c3e000704010215903401c028031070b900c0d41c80f0742c05400401c507e40c018000414154100480c90b000002e008500f140f2500040100669a0720 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 886544541 1250 886543291 886543313
    0xb0405011b030e0904142b0503010e0f0a150b0711030706050405010c060914060403030516090302010c030e090901090c0f0509040206030a0605090c0d1a130c0507050a210c 75
    0x582a1542c070300da0f84442c5011662100c03035910b40e02450084007292107c519080401d92994200802c66501c4030005243c1900d441c8002c0c040d40c0c0740c51074014002610114004883c7d504070303000540005048840d111105a452071940000c04080000180030007800b484001b1100c2c000c4003100030b0f081061801c0070281c807a100390711400c8d060101d030003c6d110622003e5070000d08006d422850704085041d50b43c403443d490b018215811000310385007801150842c4500b041c081520161038407041000c500719001903621f003900d40c208404110700d590741c03039555494030700b161401490948008200f13000315142100d90401c00342c12008420710f05000412055594421264000d134050315140c1c2d6a840d0310400001604141c6c21098205c1c2c100c20500c04007054aa008002a038171522081203020302c6d40041c5070b1300d044401d02c00742d840079210310900c403002c840ba4084d0023a61a035040c041c0c0f0700180c0d90390f82414015010000d42d10a940754000e40480c1c03080d0b81e50452400641d207440016100c4a84e500c0c29804 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 886545791 1250 886544541 886544567
    0xf03050f0711100e010929010e0a0e0a03050a020d0216030f050a170921120c0f2b050307050a08040c050405090a021e0a120c0509010b0405011b03 64
    0x80d404410803240c481400209000f4050600902280146081c101d000c0d0803460700480c1c0c1078000d8400c00981c900c817401d841034241020107007030300d039039180510300024114050a0320114940c0c41024030080c01d400c00c0080d103898425210680ca40c0050702005c3d0521f007100f0510404c3d9007082c0340c00c40a0300d10402c8280d05407a070103545103544082c24106281741610000000b8030300300e10034810f1244162070750302070040358a04545080c402941a00f00c00160f10701c8889400041c4d01c100c0e401e00c5905da50502400341c9142010460306103140c640c0c84180f034500d8001030315220071001e4000340548a001d81c00400d00d4600c42c2005865801d085c00c0052031482041052800c21540b48089000c00c00c1101e5807000909008000f8886801c1c803107440c980b150142d000480c4125404141c000c0c940202c001c012518600042c8980c1c04145452060782440c0c5403550211200c4903412000300349507030354440307031030103800507244054680b424540003414000851600c015550507100c0d08038002540b06601c00301c03070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 886547041 1250 886545791 886545797
    0x50d0c14040213031704270b0d0203060a0b1c0318050406060507080d1b050d06211518030207090509150103080904150b120c0c060c2203030905010f03050f07 69
    0xd420207503817180b250b0041e90071400c0d9485100b001c11481d90200340281d200e01a40d02c03400c0100100d0082040506206448001d4250304820000f4807107a9855122a1500c5070241801c08514003043e041d240c0c11103000800c038049455240551040140d000303110b00580002d40d020400c5a05010014180e030007041c000070902d08002864212600032a005414001001d0000301a00d03604003c001c3c108d500921a80c00104c0e00d02100017660042d45020309002c0d0910380041182c19038030352120020081402d40e03d8400d162103544a07c100301401c80b076a80114003d07405440135038200003500c425120094441809948503c90342d2000ba020302407160304580d44a4001c0341d450b05181d010070080c00280d0300401d21000c65510011321201090002d01440100102038101c1d80e807090307807941c858021410380c4a0190b000d1800121441d000200078250001c0c2030603c1c1d0a0640140707118400080350360011000510b04050411075540c00a48014100b40541024456842d00f1358184400b990001c10b84810 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 886548291 1250 886547041 886547063
    0x6140708040801060b07052a2b0305250206030a0b01020c190f050306011202150f2a010207020f090c0d2307090308030c0f04050d0c1404021303 63
    0x4114514003141c0040c10000028080243e544100301c0407a0000e010548807405184c0b0322001e40350302d888002c040a02c0071440b100ca0200c0355000d0080b114525130010402001d08100700f10307449240d1980d19130b003030310a41c1c03101d0b0340d85080018039280000c02200a11140161841c940069613000b0959034000e01c02000020748030784460040389801500381e21103411080e07014501c0003046000341130170103880c844903018600981e11400c2c55628002403046108801032001c114005240001c06c070108040560005820300f10308010140306a0705c10f010b245000900b880e00100311440b4600c0e400300c00b03403022000b1030414403140c01246100c41c0e01c0ccc1005100c2c06440000525180c050b00940300c0d10100784108000c5810300608045145841c0c0481e000340100301d0001903c42031107103d019081e07031340c00510b031425500c0e501d0b10b0f101960028a00c600384044103001c04129a1140340d0881c0505004804034030340b45140079010030b00c40c54440c4410b40958010001001c4996481301c2440489500c014102c503 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 886549541 1250 886548291 886548293
    0x12421110a091d01200405121c030c0e0a1d0901020c1b030f06131b031202010b0f06041203140f03040c0810022701090504061806080304061407 63
    0x444840030381014840c02d140600c2d1000d00b203900f196501034000c2d00c1008026880b40d224040c00f0740082505c811610b001d003044103000c1418002000150001c800c4116640da103014002c6220404486030694000399603000304c01800703503000c1000c460100050780e500f01c0071801c0c00c48001d107101d0001c080207540c80282c808282d0001095044540500c0c05909a55100080d242d20140100020b28094407070712440d01070020680021901a000d0401551880c0700d82c00c0c2550340038014844156002c00032506010300101081a003484242028410f80c0001100d605480c100b1080c0992212407a01800061006004020750000301904081c0c05040a01860b0490912009203101d000c4410301d100102005100130001403099810556807008144d44440c8036040d5481c00700d0040c50080f0f0310b20102c051010441c840490b883c000072580c18504000c03041d07156000f15055644650001782c08007040d280382e0121030424818640a096a40091841c180c6032990080c04414882c545d805c000c040010914 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 886550791 1250 886549541 886549549
    0x1005070309052d030105220302010b1003092f0f0409060911030d03050c0a260702061b090f0622080703170901080c160501242111 57
    0x20014000100b0b0a84850202e00820480d060b543c00000b4407940a0b05502941d0700e410702646100d01c0340008100c459504810310300b44803c42801041d020342d541c43c0e040714920b132500304400c07101c81003984000c5014040b625100700e500301d80900209444003141c850b000051401d82500681e8070088407140404203034040014028240c405004000e01c2c50801c000080001010246006202c21800d58841503140072069050b50700484681500d2002000700d1140307079009500741c4d01400705e5000c0e4607800e00320000900d0094801903403150702680c001020482c1403034001d104030008089503640d90382030007800030200c1c00c64030404140b41d04c6000041241c0100034803c41141c480c06010b10711071150541d0b00c8a42039200c050b607010689950f0085800c0c0201d24070302c503003100c2d810101030b982c0106030b0399007240401d50b40d00151186012603010f0b042242c00f08609029002c01218020b540c07207000302d203071040b00780040880d42c880f4a9120511804520680440c1070303640c2d005400c415072001400102e000a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 886552041 1250 886550791 886550807
    0x907030b0a1e08100c0305090a0305090913050a060e0715090e13080403030c020405072c120115050a05041512170c03030f01050906060d0e0304031a0a050a0b10050703 73
    0x780c4100c1c4101e031070100c0d86052a0b00b09900220b03075a10100110b46800d9207032911002710701030180224a0800c660091428542c00300c0350311400d6481c1184000d409a2365071703414096202ea060f281280c544c880214845002d00c8503030010000c0761000040f02c000050047e1801850388a8240000c0a04d00005c0564008003403e4080c035500c400d09a41c1c540c3c507480c0140910414510aa004a203040002004035000e5103034009500b51012159800381c0c420311f00c0b0403000f007050b28007903044520106c1d050700625090060503c500d006214a20403d400d007000d11001c0d1030f07541c1c003a600c140d041c0644100003041642885080d103801030303040d00c0007001e10b08040c2000800080a03101071540011158168032010002d50701a41440f408603200d030341d03290104224003506490141d8407450800059040060b260701010b06a11140c05990500303590741c503402c84c00303070b5002c1d1001078451242042003642000d41c810136600c1b404078007082000c0e10b01d4802041e21a4410800d64040c405c0c005545001e16001e8408 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 886553291 1250 886552041 886552049
    0x19180207020a05150a0210020a0c0609150501090204090f02090603180c0d0c06230409150b192c0108061f0207080709140408090a0b0f090907030b0a1e 66
    0x3860b9809101c4241131950000aa481c018043c0c0d1140d202d0100843c000c42e9211202d84d510701410310007035180c4000501c2208002c80b000980198035101054050003668000d045508005855034904005001035400c0c00700158941751041204480d03590b288010b682e04400e0160054800d1620403007107914045500030120b42c4880840403c0c020414204400b4066035200d039101c00781d090020001200d00840203584904c548000c1c0000d1000c0f00c240c3d4000c0c400d07898106141ca04140d503c8480d40c516522583d0301c1c00000d0021903041d080aa0080c91014140541302611300c0320024100c23164100024801c500c03410800c008000c42e00c03544d542642152000f14203010800c82040ea0000a55182c007981329650b010301554100040d1040c3d24455442d4080641e011619140e0f501cad134500b059948011501584a05511808a40c01814201411030b40c035080410070740e0b0f80e800804102c486803004002204240c280105903e2070380314402c0480884400c1c2c1c06581e207450300751004411240c07003500 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 886554541 1250 886553291 886553299
    0x25030210090c260d0806010504180f0506010503010810050711190b011502120c16120218090d030902040b15041a040f03030c02130c050919180207020a05 67
    0x103400000d002e19102d140d012518001600c091602d2800a02e1081d0700710043c1c00341c03050300200e020b159100c0c010300d0703466481001498070324a8030340c46080009a440b0b0400c0316400041d9140c42e40d02042c4003501c504da80001c1f090034110308540c503005280e659117549042c1e90607480e84900210b44000d00a61180d80c4114010069491003170b80c866507402003c001075410b1382c0a110401c0000380c00002c9690105040801340e02a1902d5000d082d009102580200c1001031a84198090444c242004180360b40107001080e814070085111401000120319003600e1100c080d10a00301400150080056001105212410082010000e500008004102f460b481e0351f000030780b140c07410925003c1800100243c4400044c4199541c0d000d071080c8551f40218050080a00d01000c42440332a0013071000388440c5100901c101041c2d02c0b1403110100303660071380d1039040c0440c00210708004146400d403142e03130010340c60710645028a4038110745d840d528400103090200040d4001880780035074031500e0080001d040050 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 886555791 1250 886554541 886554551
    0x1e0612040809010210021908190204030515011409041101030e030d0b01110303061005030405010608070f0311151b070b160b150f040f0b150a030f0225030210 69
    0x1003400c00c8568071001e40c10f40180030740c648440c1002142e10036114541304240c1809030000d42c0706020303103600601819401655841150a40701d0341101e0005001a500c120050b10341c100004015001c1d042040e080110074140880310307144070381c0f80e4100c0d83e644241c104a9450105000c40300580040103000c0780300605000c0000e200a043c030058200010a1900f0b07601c1d111a601214601900c90005885203035114140060000c50288a00d01454200e805a0000500c807503136481c62501c0c00c10300381d10512622034048401c006110000040c142c644a06440b04802e1407280c0c03001202c1e40c42003a107400200300b54007602d4a100e40d400c11801000d00b40d00c40d03840d0b80e05e10950302034200c02c02c4044812158480f40313400090b64a0400410030303034400800350500c18020b10180410002c0d0035908015041c1030b82d510304010a070b5681c0d4121541540d070a411041c0c0d60460441c004060b0b07003408400400181c0100150072000c41c000040c3c41c252010483c5070f03842807003545030490502190042554403079041c8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 886557041 1250 886555791 886555793
    0xd03031802100f02160f06030c21090c08010c020606040c05210a050c1e03130f2102011a12030c0703060501151d010e011112030a0c030b1e061204 64
    0x100f24010840c4540031907207900c09103029807842c81e0081c0a4089400c2c10400c0c01c00c42140640c000c20960790443c1001421115240000501d00d9040f04604516545420740c003c01d001890442c40c0280c10788078000d110018000c1c40203551000082c01c880d0059688110307250045204e803081d55141c8a02030f400791112420300f07a102c40001020740d46004440e180001084214401500300c0f002c200d003104c4805010540d90064100e00e4000802e41206000300c1c59451300003030102d4201640042c82040d039810212406440c04040080d4606000e082da8940360501d1407105107005e84a041d08002c0340ca00f2030500c06060007078218003402c2c0b2140704078415540084200201c581190341a00c8038000e42803189400300404480d8000240302d0826510450f00d00d074100b951003010380b042d04080606126210001c002906444d140b81e11225030040c100210901440c91144d00803c52800076a2409211032601c500c0043d8405c81003250450704541c400c2d00083c05611400280d440000d040d4103625010314103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 886558291 1250 886557041 886557047
    0xa090501080d030e0a0f0c0b120a050702160302061303050102040b1e0a0804061a2101050618060d03091a040e0a06210201050c010c05090901140d0303180210 69
    0x30301507420107018008011000300d100388554000b210200e0010048001243c81d00c0d0140380104205480c9502e8010020803441c4070480206003d24035140300403040d1800300801422a4409400d0000715000841c000c1c04c55080c4080e00001d41c2d0301110115903070003003c0c01703003120b00d640c6900c010301c0355002040c00500e00904401502c44150f1004c28146607503030741c02c010750b1144941103150021800345008500454215070141c20b2588003240f074411420a528001140b0400300c210081c0c12501c040086804101e080c041c4a80041e41693f100541014011442058500c020440740c0184422940038080c0351003001c402005010840180c080318040000402195000d801031410740071038800820340c060707624855401240d0411030021010202201d010f404800355000aa04220090120001b510000e100e03480c040e84540e21101c0e55914240d0030b1140c6988142d00411280d1403046407200640c46042400c03204ae84d252500050354000080607044482601501a401903080e805418640350 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 886559541 1250 886558291 886558301
    0x90f030a061b0503100621050103080a090801020306030a0803310b0903031b09010309052b0f05250f03020609010b040908090d0501060506070510050c16021207050a09 73
    0x26080300b5031024441c00e1079040c2c80521003691039200e00b450340740301000941c4c410a0b41c280d0440e5013078000c0800050846c00c80b004d998007038105540300030000a84003005900104602c0045c01030f0402136055103003400019495008070000074041200000000e100000c00c103108800b904002d20103152845188483c580d000c0c841c08404482e0a200c01002c030700380c8400041628401c0d8044a58036100e4051504581d070301c0d405c41c11910f414140c0b074080c1a00003034000d0204107014a42d01c040400204150b02000707100c00c1d620001001802100246c44014603440710403606805000340a0400440366280840706e1075a05280240a10407842c102100309603000c501c5500500006e0020321045905400700011a403902400521002d800c006900180c01c12514502c0300b01d0107400000b0b4a20f0341c640108115a01000c0200c44640046501020900880c418203400007000042c03641003a0300c0241c2119080039612010f8810001d260bd41c2c4c222007130070040c04001d03000240075040c1580d540d030701c0480170744 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 886560791 1250 886559541 886559561
    0x120a0c06030513120f0513080f010f09020604120f02060a180608090723041b14040f050d0c090c0302090301051b03040305160501021201032603060105090f030a06 71
    0x900b4840400c51000c400141480c200d030b000000400c14000b28602642c0001c20003d0703038824880d00f400307001d50811000e80403800608500016010844004804508581ea02214035802da0325141c051005a1556405d4030300360358080c2d41042411826060a4002491544c0003d61082c1300040072415254448940b410303034080000352014a68a03080181c0d0620f40840307000025038440300040011030344c1e807901035421680c0c041400d049081c0b00030118042d9112000004100e820b0700e14404149039102034501c81c018986600982050304100c0191310078a014440c2c20310980e1050403040510044014600003010003a404121305003c1550140103500003400d00ea1080d4a0400064004460b9203010300c54445038000052450341d85503002e0703038982c01c040b031908103091312454541c0010f0380074030061460040746045000c8962641c54110703000c20907151025901010440740640340e141790700c00d6a410820908107280c80308081d00220712440701e003122160b810702c500c80300e41091240e01e41c811503041d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 886562041 1250 886560791 886560797
    0x60b040b071a06030c0409020d02030f210a09030212012c0d03020702181e243321070e01020303160806060903011d0c030c0a0b09120a0c06 61
    0x590702c1c0d85a10569501c08859003505078001074964070f03d03841c2c940e0298481520081505250702c4850f004079241c54048580f00c3c82503030110106040c07656100912290b1100c0c0c04595601c0c0c90140749000300110501d00c40240030341121741c583e00b10108203410460032100c2d80360020f010600c40340064141040309040b4859070f4022010140d02180c3309000f241c031070a401500071090135041a044821404006140c003044440d203e07070001c0500710100343c0e517000314820304440d69064840380c00111000c2c40c51101a202c4d00c0c3c040c0b03614002ea00416505018400385480d119100402034080385c8440c822010007541002c9001143c404000d102645079016004175541d510303030040010300590742e0348010788048250a00d41c4441d40f42c3c40d40320310042940712324042e045505012600c40420300f9121410b0483c0d0380d04142022058030001d00b0845400300041c1100101049a441c5001c51500c209070300441d451000002144905900e0b104116050902404100c407464210740c10010038010150140c0341c00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 886563291 1250 886562041 886562063
    0x1d150d1a030d05030c030a021b100c030612020409030203130b0d06060905180a180b15030d051215031e0d0c08090103020c0a020402041706060306041e06060b040b07 72
    0x100d420300142c801e50300b03845501d03450310f19110280702c6103440e04001c10342034845808011080c4c4002914600000300b007031180c01040440070840d5004203a41340320265800305031805804120450705c85980400264041d030300000c0b020036a00f0304a0862060700050308400c5401c07a4002003407444840106420032140c0010450142c49250444003070070240701d4194030103000842420318000b00c0c400c3c03e0300544020000215003440001040030303441040030a4500e4091201005408180c0700151403482400300c001d052241000d54010b080e41c059042c4800c0c000c0c4d11900092042c695081000e015248001c1c06c86400c04045884442402c0c1010702101060061070420b9100c1c1d1f001c1d9440d00d0500e90b00c540c016080205580045000b0342000c1354000c8284104003000c1d0240c0c0761480140041d089203d500d5078902c80e500e40c501e00c0d0001c0500258000c1c4d014000b0040850f4003848840b80b90081e081480c40d08075580d0501c031001e00a03c0d0404002010001000106001000010081c251081a4200c5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 886564541 1250 886563291 886563341
    0x17070915050306010b0901090b0a05090406030f021e131a0904082205010905040c05130b0c0d0c0f0605060d050714012607032003041101020c03030403031d150d 70
    0x81c5d40c0111503107076000c43c6980c4002c6c003401d00d050000d8606014149031a905140c0500c1c0010140c0b40b0a0780305968030202902140150706280c5962140580310700c0382c000c4401c507081c0214003420032110101002c3d580c0d642080014190082900d102454024002e814508240c14503582030380c41007801e5160700568841540545c03042006030011103405840701c404c65440c4c0010b01c0041e100c100e0303003041040410029001a0010b5100310000b511200c411540c6900c17248001920740501a0f00f158180112490603c000810810307080354103e5002c680819281c0302c91011641000d404c80d002010ba00074241c01103210b116800300103d00345000d9036541403000446100c01201e48a40c040708003c4181c031000144e10502a40020510440c010300c110b140b0032810515443c80d0b0016541188d56a4064003256131542c0d0402c103180003654100c01841c030300b41c51a075002c0d06c01c03040030030103186ca0042200c14816130b81d01d080fa90b241007490f8103070266071102c1500d0324a000745580e00e440315440c00c60411040c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 886565791 1250 886564541 886564559
    0xf060a0b10020307020d152f0f0304020402160b0c030a0c0e131505040f02090a050612010e07020309040204090b010908010c1407020f1903031707091707091505030601 73
    0x18001c0303581e4020f1440c01e003450302848210104808151846010120307841402c80d0184181c04011a00030001c50001c085601840d03400e1034005504800b001342407013044a0302840004803500a1f5044600603550140034045040440000e807000c6c00101c120303810400400690300042d072048a450008102e1481d9545059840402c1c52a8040c3c01540e001d172003a0700314481d544100540c40c4600d1050407016950f0002405072002d0b110a5250385070089000d100034100b1449602c0034103800c0700c540e4140210480034080e485014410000354023103a4010030320140c024004c80ea400341e0040c2c0150750712171700c6000d0782025000d415480e500040ca80c510000d048071041c40390409580c03241d51480800f40c8104807440082c1c104110990f40080d910460003034039582e60750781c0741544410040d0441e41c1407031400c000d0900b103030724205800840200020003104503849102036056600204081d4031901055a1062802c10380d5041001001d1418008072400149007c4980071200210100c42680ea2a5500c00c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 886567041 1250 886565791 886565809
    0x70b06180402040c090b1605060a0903050f21010902040509130803270a0636080a03140a0515010207080a2303031003060c300e0f060a0b 60
    0x503903620120040030030014680794000113140c10f124a015003610362901241000ca42c00b00a1100c40d403580107140008002d400d110f0706a0180e844e610810030807040c0e0720050818450001108901c2d50b00181d4000e220740d0390302035882ca5270300c1c50b00a0b00540da103d140e100029845405951302c504400c0e400954051000c01c0e06950603544088400c4c00c4d601d4044550510b41ca00d0000c07040000c01928210101510070420180402c2c001c52000c07464410701c030510044c2240303000c4412040e40781901900700c0d01e0000880440030543c02131170b10b036543d81f804d5411030041c881e050344040200842014045488071507042140030302007410001070403411440040e039540c584c078820061150040090701e4040b40150725050b201a2104841d001d4200e200e00700306003590702c00c0351490382c10841c5540600c24041176100300c43c416013180c00c00c1d128452602c2e101d01b045002901910300110200480500601144d400818105981d90100c1e0700c2d8111182d80c1a880e810101c0b00c092440786000d4805140780340c003000e4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 886568291 1250 886567041 886567069
    0x906060e04020d02040b0d0204020d0b01030501150f1206050d0b06040c09030218070e0901080a03080a020711040b1216240813020f10020d032d2f070b06 67
    0x28034030402103d0381c01e000280171240307070f6a40d0022040380c0d89005a140c0d40010030341900c41050000d00c1d114100009001c44a06802000d801180101c2c82075005e60031040080e0300b1081130408a208004c00c42d4207602804203a0403654006a214001c54104581c0c444014040c42c02200d09101d0045a6001181c41c40c0b1144406544841c6e2204804d0400c01c1d0f00500c550000a41d00d46254902c000c94085901240281d000301e000c5c0d030002542034249507001d4480313500152403880551406220761901181400d203488600c2c825503854200c0711465868800b0342c2280c00000007500d4881c2002c2c2c0e000c0c3c0d4128200c0c42010008100c1240c4c420300d00c0130001c0a0744103030600d81c0b50399105481e110b80b08044e418200c4000c90300480c0112845480760381d00f40d9120549542a40140b0313600d19102801010f41e0321b9000040045050102e8400380c10f51402031040c40c00c1121a000180d5004107002144c5000040a004131492003081040e445608040018080940500c0600e040c03030301c4890a010075140005030b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 886569541 1250 886568291 886568299
    0x804051e070b0705010204030c030c060305010923070903051606031803021c230c010c09030209180a0b0708071409030706050c0c040609020d0c080f0720070305010906060e0402 77
    0x7003400300070b04240203081c40c02d0068000500f0641c40f0303500e00307102c800f071a0030540782082244400c00c4215818000d16001d005589018441c2440041c1d0078200204500002d90400180c0f0b000203500911402c070600056403c00304a42d040703d1401d42041411006003c0c080001c4e0410030044e84525845e01100003a65141e401407012828203080050a911081e01240800810803401c00810302c00c49140380e49402000380151343d400e400b0740320500b1034111405100911907066400c10240c1d960300b6696034095440c4440203070810860510074202085005d008002c00c0588050044590b0320104c454462038090302c400d440c0c114401c1c0e80f41c040b0300074281641d030b1662000d081844420b108401038250b0b4070303002007286c8045c941040082d090b10f010360020684e40d54040340010320b2071518099111010510f040901c11410028480b820b0b0540061103101884010309540c06041e05991400c0902d00802041d65034107a101d01d0700c50f02030811040d00362001802d210004c03915400d4820118041c44d4028 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 886570791 1250 886569541 886569553
    0x20606030d03020306060d0608010c0f03090c060e21060402090123010318060203072109021c08120c0c0115050607110103150e0901060b040806150a0b07030804051e 72
    0x10002c4010f58002001c0ca03400c914140006c403105160f40c05403002400b529400858040102000100b11003119145581054201000703000421304051815007600c403c1d2416059032207012020074a84581c0980c0c8d014251079024807902c0c00b10001c5801c60080e0300c03c44d1440f5060341d035410b80e01005504000340010010a24044c3c0605e50f02990082102ca02800c1c0074940f800d8082c0c641b48226042121003c2c041613440002c0c0c000031041d0103441c049044403510801c14244d060f000302e460003000322f82100c01000c1c5086980107100c000d4013528106a205a204c0b10b80d403420300151001504500315481f110360802c001240c03c000c0c0c411102041d00c00203082103003454025151200f50120302072425050558a0490b00b2a0700c100347c0c01080130f401c4445038030800342400c540b907500f144c41660219440b40014882880b2611000c01d40f00d810222058290100d0700c101c0c0c0011304000a15806049100300c0005c02000301908044014401d03070041c0251200e0030300145044500c0440c0035113040e10754200c9 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 886572041 1250 886570791 886570813
    0x1181d1b03150315090d02010b10140f0c0a0309031202031801080604140a060305070e010e0402090a0b03070603050402090a09020108070c1403040f05090903041404020906091003020c0d02060603 85
    0x2290b402c2c04800300102100c1008480302e0b03566911034016905020150080c1c0c0361840d86540901403250940c42c2510142c0080e00b100c00000d18041c8000a10001403900185403400d003106081651a00c41e614800d0b01c0201115140103864464144401c0703070190003035004070200c54000310907541c100c2017218400f01820135030b43c0119040800107103070b1540103589816a2052590b0403101ca8031640c00c0510004146003942409450400540e10020300d201441d03005010881c40b120355540c11030340c1601c02d00d01644500c0d290102501c0d41030700c807980512400c00e0006000380e1540105008500981c4e2490440c0c9a40b050001178503003194004e8003050030704011800031849007011090300d47c0901c0d9603185100201c0c8156046030310583c440021206183c20600130b80c9041b10855401c80e0701d06000750324040c034010341d1400741581ca4004a10540d4089101201e0f51100002c8070b040400003003202003070701c00e2003001078000c0d04840064a43c6104001486040301e0000600034080c00e0000d0040041c101d82c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 886573291 1250 886572041 886572061
    0x506010905220605010501110105100905070210090f0209090d170c090414060a0e0f04020d0c0b0a11060105100507020d03090e0702031e03041101030b01181d1b03 71
    0x400391030b00c600380c8000305450700704500e032402480e0300601c16080401c45524010004018005d24142940300f64502001e100f000102c601c4a403040307030a8480e0100700d6984c1c05409074100b0500b0300b0f032188120300700460541041641c0910041c1c0c107100310b0300000309072959415a6540e000c0c04c4403c4010424610f88181c10190742e80081c3c1c0d03c2950120081d203003540340d101081c10340f003421a08004010a0ba018443c0e545452000040035290b503024803411880c015501d02a0f80b80064400f034000c002500e40c0c1011f1080344820079001d0b01e042281c1956502c1942c00c028049001168244440d004070340002c16241340c0455006000785013651074a08200c00c0c1d170200080b00a02000403014080c1118000032000b4042420500c42c0d03070943c02664a0b02244000026403a1040240360071459003042080005881d60812140d071007001e107030008045141c900182c0b015030542926940c0c100c0f29102c009000300c880007550005070590440840c0540341c800031a20300f04100807104210207418400185c02e405 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 886574541 1250 886573291 886573301
    0x51003110a140412030801030209090105040c0605090303043819050f1315020d0905011403040321020c010f02090604030b090a02040f140f09030f0903120c03071a0405060109 76
    0x25142c0d0070680b815035100c01a02c202100c0150441c04a86140c004005628103110882d50080f504402404546881d0b40e440e2144002030203610280100030401c204152001c10a5501400c4040b0405a07803400d60712079800f01002a1400104c180c4c4020881406a84014141c0d8031502d5542200851700c0d0480c2019515500b0040003907152203814403031441c0c1540300008039802410001d220300c4507405ca0503402403d141602c0700103428400708000401076031740c1c4070760b1140300e00100391007150b143c0d1035a16044400301e4500f100d041c0d40c011480344100d1265542d50080c49819100c030000c20850500d000c124003a40241862603501402c00e1008001250000e540c051344031044000755006e481c205c0d400901110080c030f410300c81807a564041201500e40c1c0c602c460342c00c20b000400308034042c5002030502d0303500e200b51809002c00c50400700d01c2085030f8034100031404d0341c858900841074442ea0074580e00c5030740307070040d0030180c520010055524041c2c8180080c400d000e1a000000f800844c2c0c20b06081001403c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 886575791 1250 886574541 886574567
    0xf060311120403031e05010518040f050d0f030f0b0d02010e0d05070308030114010c0f140f0a080a0f1b0602030429070801080d23091207051003110a 65
    0x480c20010015542020003840784100e10036180010501c0400044010003000681c44145a500d00401030015a441e9034981d090111740d00900050755030b03a450500118194194010300768462a00090001c5030440305105180d03a0640d0208281c400041c0036000303a1310038405150b08680f8a84030034015500c13800071001204030280107001d241034250340301d03850900b0b10fa10958080c80040010700003c0c1c107106002410140c02d2800b001d4a001544451541d4200804003e040b07a0940d100040108414004078054501910540d81a85581e09180040e5401280f02e1000a20351041240d51a8000d02150031980300c0744101c0c041030001590303504001d40c8080c0007a1000800c508842c40000958429109404007186042d20503061040000d802440180c00000c51500820340c5a11020b6025004c1042802c1210b001717280d01003090011900d5100707034100660070a10443c0c500b00d80e03020005071881120401d5528090611010008804960203040b40101c100420008941003611503a6810701c04 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 886577041 1250 886575791 886575821
    0x50901090201080103020609042c120301181505061b0c090403022509020318123901050903040e010e012706170f01050114030705130e15150301060f0603 67
    0x4580d0322140c110180c0f070308210202c0ad007490034150301c00f441081c06801c0c0b08200c040315050441d41403110082c0e0090285000d03110460781c900d000c68bc1100030542000c01000040c00955640b403210390103d400040d800342d11729961180b190084200e00b03210148030305c12501a4080d10354504955800c5140e070314140341c1c0c80c7c50311400e081c004c00c012803603100950240000710103180c2e03032224a40c0200e040c22020180014044010300111006101700080301c59002403000a281d8940142514416910855003286d03c0f0340d860002080302c0c3c190000020020303600081000000e03682d0700c0d081c5105402c1c00340901007100504100480196068018002c140e030000d000126030951a840c1184400800b441545101d41c0003040c0e105100b10b081c41040d001d8154074070400d800c4101c200210369291000d03c02c0038001c40c20106c10010440280d4081040389800a0a44421b0031406a001094001c242c5a0021144400c0792380540762805101d21404c5820402c0d401c000513142010940003800d00f428150a4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 886578291 1250 886577041 886577051
    0x50f01050415090305150a0c0f090909020105040906060302031b03090c0402030411220c09050312090109090e030a0815010206010504180f080c06010b1e030c07140105060405090109020108010302060904 88
    0x2c40c04c2c41007800c0d0886d0084410344902d4180b0001007600c0c20450000c040c04131450720512007a80c40b00c0e082050307031003280021800031042d10040340c4d03038030550f84050b0400345841c0c404209903605400030f50281c00452820b41404a101e2150700c0d80f448142d618442c2071344003803040e03a42030420343c010b1a13005000d10542e2042c80040004140d041602c1e01c03242485401c1c1d1660403442c1c0c503e62007281a00503082c82c003032000501f400c010903030380d0402811072584660040b9402006a1051040c0c130040d100347c0c81c0030300001c00c0c0002e00aa42e508013000d02d801107042034000618400d44c02c910005540c07016400bc1005920300024000100301603202641030700d00141c5014080341ba90a00c140b00e0034444c004440e40c44200110542c00c2000607045041d1400c810003081074404605060b0f000c030a00300c1c0460f2582d03038031202c0400190303106400c001001602000c0c000031000c64198869441100c00303540c00c0c02240c0d18400da0a00301c03410342d074000380810307040304c0180094100180540200780e809040095 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 886579541 1250 886578291 886578293
    0x161d04170a0309050706030908090909010b03070b0a0f0f0c0b0a060816090c08090d0503250302030f06042d02090406080703113111030a0207020406050f010504150903 73
    0xe940d401144090302003030b2101510010004100510780081805244c108680148d40d5500006845000880b51080d04040d0201e400f1080a50011003114001821103103066907034440e085407500024409004a0395812104104500440701d10403805c00c0790f641c1c441c5040b0305540d01040700c000038101d00440c0f0383d03603800441c6000c81002182c0350304003c6401e60707180134a0090510141d62a0308040300420110301e0900c1043c0c0c100003809100707071059041481e1295100c0c0913020b01c141d510a50000322442c040c010800b0300b90194000c1d4001c1851205200244d81c54009110a84540041020211030003151521041508120702082e10010540261a050710040002e040d50510f800c22101074012407810001c0002d03c083d0b8070750906043d68002d500321041c080c0d41c024038040c1c044a50204942004054007800d040e0b1001c0b0491302001141502c9003803843c010300082d00700d00c500301d00451800384042a9807a020508001000b4140e50b9a4605810028548420b01145180b003082c81a1000080 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 886580791 1250 886579541 886579583
    0xc0a0203011508010e07080d110f03191e020304090c0c020901031118090705090403180b1905180f0d14030307030b01030203060d14120d090302161d04 66
    0x141c2c1080d10b0450214941c2d040c00005800c40e00c1c030f4001441c0c5079000f4441007080d12404142030f0062281401c000c85911402407000b4106a040b0022080a000c00100308845409000c06441032000640e100f03035400c03441180c00e0000c0240e02d0f68030740141c1d105110402400800f0703000300082c19140e00d0043c4251000d5030120780e1088080c0c00c200ca146180102004040c03c03d00031505920300c82d41c800c0000e07402d04000c42500c80c5840d00640c2d000e00c04141c00942818003400c00105444141006083d2407591103458510a400030b0301c13a4030766100d9150384000a07501c0b0b042500d03560310a09a01a035940d4240d01000940c00c035800e50141c0007081071200314042650300c0147c007404003942c006560b881c60301b510018111000c101b2214141481401440340540703411581c40c070140d5100b20031042480c2c003035008a20340b1458583d180707a034010000e84176000e0304940e04002d60f800d00c46e07002c0b00c02001d109142401c0c00903041c0035403030019241518082021400700d0342c3c80c1e0010b0141c9030032602c3d00c140baa190 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 886582041 1250 886580791 886580801
    0x1020c01090501020d1b0e100c020d12091e0905092103090d2c1504170d02010618050a02040306020414010810050d0209091c0801030b0708060a09020c0a020301 70
    0x341c409075408285c0662011081c02510541540307200d040d0a070b244445000342080c82620003080c040c903058188969403e0140244e4034020b60003d190322202001c0c0d00d015801400201d000400190416200090000780d20f0320b105901c44644000461160400e81c80b04010000240001c003544200742004004910f030504203450b0b9412215515901e103402c1c1c1c452803401000040d510204111110b40c000043ea0118102041c01c940c80c0100780329800010004002100c04005400003513000240013038240760000c0549420f20100301620300101603108180e0072668140304004001000728551420001640d000640c40b0303009020050800b520307500e8a100702c1c1c1054001180c0800518140043d40d80c00c2600d25501410a111260005c2d0903c0042009084002d0009001d90112000f0444825047c884140300d1030070044044480b01940e040181940020704c003c7c2c80081c444e41c04500251711940201c0e2255001a0210034842d28294680009500515090030640100d5142c000103a8082c021 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 886583291 1250 886582041 886582043
    0xf080f13080f0a11191d071b0b04060603020909030c100b0d290709050910060f12060302060c060105090c210712060b030a0b010503041101050903070807060f0e0d03090e070201020c0109 81
    0x1a440e80b01c00c00c0641d60106000d005841404031078581e103c40b00d05044848c04009500000c51400c40c1c442c0d01d454009459541c0000b54064441c01c100030802d2400400f0f4101d204101086602c000da440b0070300c3c0112180302d0f400c1c0c0d0304100400c003450041406c00f40110f021210044040c5150943c4c4248c2585409080d6944800104465010001854410400303900140f8031050030081a16024000e00540c03890100b240a00c48107400708610032100c0c0d13001100441d0084c01d0a659403403103501c2d080d04e0b081c090096521424184010034090320103002a2091466500001c203909511a03c1c0ca01d000c00b4000c00788000c00c0a000d0903c1c1c0225854003400c4000c08010004541707074245487d42500340e8120206003410400305100700f02c0818000a0080d030411000e00f4540d5881f09281702081c2002d80b16004409a8031910b84000307400c6074054061030000305a507072440b88148007030701000100c3e0044440900080d0364110240300308042511101d0f0409203a0000516200c1205200c509450b22080 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 886584541 1250 886583291 886583309
    0x2071d010905060913030e06070807060b04050f09030406051b1c120e030313021807020a0309050904120807020c030a030c02030706080106080c070f080f13080f0a1119 73
    0x1080101070320701038282c200204a40800e601d14010b80d12030b0072041400c9010782049803540078071199448040448680540081c80169500e102c2d0904001034003c140c281e81c01039143c600040c5e003460307440e20024041e1004201461405160503000c850355004140494002e900f240000c2ca440b0b0000c10140c0f40304640c405081c41002e106040180885c13296400600040d030400c11030a00000b4007104899200004d5141c8400341505030000c00c80002c8000201d110b6004c0d48001d100d4603d40000c0c40c684c41500c03e54034808031940305c0007130141080003078800526001ca50444c50101c00e005d001002d80c030800c18030450b00441b51400009107052001c44081d00850441e82c2240306604041c020030001c2d03d05400c1c00398030b651601d0002002000020408030402202052010070024100780030030800b50421200d41d11120303240020046070780505a001032051504100090704880862400c1030b1041110141507070303500c00d407145003000b0849019540e0107201d00b00c03803449071a00400c020700940300f078134 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 886585791 1250 886584541 886584599
    0xe010f0b010f0e010309050f01021b07052719020f0a02060a02040f0509091011220e0604020702031204140909010605030a0303110d0f150515030c0a0207 67
    0x40005800c89565a81440c100140030b0594080e0703507007180321042c45107002c0c83d00040c02d20030f40c00c0060409403080d43c148441d5000081c40c140e2046a4280c001c0c4080303a82064622090f601c1d0104150701000149201000411442d16070f540180e00c9001075009160000340d401d9074042c031404104a030b00c09182404154400701c1d0950785240d04201d025070240040f0300443ca058100700c5861501a11445198400d80b520760005004daa81840200d0104840000910903111903180001c0103030070503a0814015002d201444001801e001140d00445149803081c64082c2c5450042c840607502c01702d42079800d0321a188102550542c41070003840105028200d04031111107080c1000843c07440074009843c5a810a00d003400b0540c4c022a4a8140c1070b80350600040d14500701c08403000da800b810b41044040b80c0b80c05124203c945103a003100c0803484030768820303214168a0748104030010b40f202107d0803c03a0400d01c00100164240001000d44002500403228040c0d0740d140070428269040c001c4191010b80b00d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 886587041 1250 886585791 886585811
    0x308031609080307060b0d050d0305071b1a09190605061804120e12010528200903030705030406090302040b060306010503070c0c050a03031e020a1a0702100e01 70
    0x4405800d018414a190800c9880e00d4840c4442d5207008a10018103c580e4491203c070340c83e43c2e010001c06031554030900307072100c440030180050000c080c11104034010411b1152008941c091500305404a15030100b144600c141855a42c2406440c0041031309015205000301c0c5002c2851071003000350444e10070313507000ca018901801809866460b604113070b031144d100c2d0418040052507001300d1442218003454864031002400b40000d51540b140800150294645018001c4c1c94072052810810300c2024800c030307001e4940d0b0408201c201c403080c400c01000542e0400c80760010420041c0144643c2000500305d0342020202e40710242035603c607502000100f480702c1760030021070825001c1e1150000007150742c18294a40180003034454440103003054104049150003c0c2005482d09500000c0e000c0640060041900c0786009081e0f04003584039030000c9009103030321022491001640c03400140d400240c40c508030704207854000901d0310107080d0310198022100d0881c0628024819201848400700001c42d0130a50 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 886588291 1250 886587041 886587061
    0x9020910030b010f030f021c05150f1e06040f0e0717010303090b07061b0c0201110f0a0206030408040801020a0504060e0405010b04050d030e0301020346050702010b0307030803 77
    0x600100c0030305041000080403680c0000b10107040400500f80401d003228401c210100920a8242e080d501d900403400c1400d54008030740c400b40c441c1024580108c1d1a44071078003080180c4540d425000e074001502c400004012111308089100c40e04043c0440e0704003a15440c81d500e401c03585401403140e1000e8003040015142e884008003600c1c481c0300030710610550461f02c004000003194040c403848180c002644000300030345a8000a14680b517060603049001004400505c401d41d2480c040c0d0004a2841c1e12845002000c2000307003003103d045c030007042200c01da070307090000303d400081003690030799400d11001130650000e00003007000e0b10b00c03603036a02c1d9910304120018141c0c00304020340b140614500300040c400f171000c00080700c0a485003100e02c000c40140d94038080311101e024488082e0154000710134404020074142c40503000d441041d80d40d220240d030b1020130044a041c4400c0b18104116a00458220204103920594102c0f0030342c400030500c000c41d003000c0b03490054142e00c00c40d02100008208171580c10 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 886589541 1250 886588291 886588309
    0x5040b0c03040503040603020a021903020714180a0e0a050a3903060b0d06021602100c0807080313120206010306051b1c180507090b0619210204090209 66
    0x11442040c50441c2055281d5650328003881c020f0600f8182c0c005190482d540c020420740310100311303000e59580300038001d2600940360f01940c40b55005c0c1c4203040003400c07000c1c6041c0404a910042200340018582d5814044c0e001511580b144800035024094005010a10a00640003003900036811007c035107180980304d0580f0034164046550640700580c0a449804030701c500c0718201ca4014801081094001001400c0c42004040080c62288001201101a14110307002c20b181402120f5a00b41e5001180702504e80544420000b400744a04004420015942d08003850300310040c140000c560380090303031f10f480c1c01000d01d02e49040964442401001000000d00620741d000d4888071a588229203007007004141030148401350007080610181441081c4419441001131070883c0c4e08503a90b044150034006c3d142c007254003c00030601e061a601d8100c50a00b42d040b00c900d40f00c000000094110094030854000030660b40c0200c0040a400c1c103c0c00b10003082c0040c202500c23104000503070711040c1c1c0c010003240310 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 886590791 1250 886589541 886589551
    0x30e100518151f03050d121d07050a0501020706020303010314011d0312090d020a0320010213150305190b041b02010e0601050a0b0f0d0b0d150f0506030d0e0f040f05040b 74
    0xc0c3c034480c1c05000040012548000103001d904041d10b501c8000d440d004040c01907200700c0301c0c4511401c0101c18031401300003015011142c042c1c1d5090380c0c2c0c940742c0c0012a2a818180150b40c051b0b4000c000420004000850340b211034110ba03000080d04201c401440a4840301303078402030701240e201140401c030040d00103c1c180d4100b40b00000511504103040c0f070203922031004100140501408440d40d8004454800e030180320000000021981c555a11904d030356402d529004880c002c0490380c030180711480c001d20800b030281501c0c00300350f440400c4c6030b0348030005030605046030b54000d912a000b80070301c4006c1c205810300300100c075000882e1042d504c490b52840c042059120390b20483d13420380c0420951088508032070b450745a0641c2c05035982d40324a9400042c0231480740385034200c0c1d500c642540a00907034150034000c44000c04030901c0703034401c001003550585800b952110b5061300a0310802e0170035801481181c059040180c040b440c0f0003080e030002011166143d152174032958541e010401000000100d459101d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 886592041 1250 886590791 886590841
    0x409090b1f0902090a030b010815010906120602160b010e090c0a03021e0a0807030c0e01081627020304260a0203071b05060c010b040c030e10051815 65
    0x166205000c41d90901c620802644590001d400040e681398031050202440d00040340c40602e5a490340d0300c0b030340c66000504c2c00601c4000d590004c01d1980da24000c0b64103c03482d030300050300090310607120300000350310459202d10840712100015001a40d9151003038000c110703542020701945048030159080c06c15490706d00c2c1c030404804000b4801680d90894402800240b0b54400040c10743c610040344005030150002030741803089510010800c207000881a0603249072612a0882e66030311400300d56a009500f20103048105030150601c00c15400d040d00b4801801c40d41320350290032131000b011108a900c00d03181a02e0203261421144c5d100401e1340180c0c000c2c807900651140c540001948001c3d00d900070650000c0110641c10503070358100c0d802036a04005440c00800160781e483e407248800c3e0081c030410611900550400720700b00140c0d03029110b9091060004409483e40c001d03154100e500424000f44032008040c07a0050008940f00100038a01e4418003101e08081d0904100c440004503111080c130074028 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 886593291 1250 886592041 886592071
    0x4050c0d050303040f020a0b040e07030b09010303211e060e010b0306130506010c17030603010501081207030e0a080a47181c170f13170409090b 63
    0x150000304a84d40b1580050710f5802413a0144000b5220150540c440d01201c0341c0403402050682000314280d000b481d0f252020003103800d500c010f00103180d030300b4400900030840c220030b40d40012038000400c042c0c1060300d403400a8040c406da001899014440002840c0c41070741c41d00c0c1880407548000a242c054200f4401950841c41d0943c00200100f0030070038820400c42e1550080fa440d640a070340c0e1340815a0340300d11394039860035000c0180f0700c06410884080c0d100390f080c90000150340e03030082039081507000c8031184e0703501d00825500e0549614050b01c241e6600700b40001c00000f48a4000d00040d401e151003511403818005402d0300340b41d00700c03080f402c450100e85480d80800440a851004296400c003c107510005070740e80715400b4145002c401e00c40c20b02c642c010080d1000c0700c2c1800c40e0307006244800c11388400c02c0d0f4640c0304e4a40100102d0071241c0364181c42c03000c0042400340701e01480300034500b8841e18a0b840382000f00b54080700303140c000c0e0f4040314242e902c40c41500c042014029045074090109080c1200c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 886594541 1250 886593291 886593293
    0x3030f011505041d06040507090321020c030f01050f0703060f050d03050d05010f06020106321c0501060f050315010504050a0b0411090f060301080a2306090604050c0d 73
    0x81a10107100d218a0598903107284001c4501400a48008041c0c460034040c54525050510b01d04e02c2040791680d100e145824006003295008e85000d0080c0da40007030f100001003549041010800c42d000b2a00e406620074144000f08c503035800c00603000341c03421800021806050100c40d440700b075480640a0002c0c141800e170107210500c0700c0f00521049a00840b0401c0780d0400504007650984a14050400000d003440c001140903c50681d031138085a8495000b0024280e03542c01001c5003524207a04d5014826814000040b0341d40c500e0a4003400040007882403041c01020403681c8155080f144c0300301c48907511103104000031400d031800b80000b000300794050003040004c0c0e0401c02900e501405200c0c0b007681d9503004215503903856070006c0c0da0510040d10800c0002c0d403240005000350804080244210b411030f40103000790800f9030a5a040f501ca0000a0001c0d080607520403055040c0d0024201c1038000c0d1141d4a4400c5c2c508020780d90040403040d010302040d00305414420f0900034500441805040c0c50201d0f00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 886595791 1250 886594541 886594561
    0x5150f070e1509060705010b030f010606050304060b1f030b0a0f060210050901020d0207060b0a06090503070e04081c05090d02120901050309010902040501060203181804021315080a020109080303 85
    0x45101c0c801280c040e805510300742052034190040310995030704110042a030ba003c1040540c000d4210210071021142c1c50358a06003c0f9090710468024803001075424008140041c409810401c2c03100c0300100603106c40c80b00c0300140c48040105588620000c0c0e100c0c549540141400407112016207100040d0020540c24550081d5a030206110f0300d1401c1607a60700007030750840c07003981901e2007050100d030305640e1908c0a0034845c010740071000c052071044060080000380c240c011b10b10b070411183d000e400341060714506215600802c4000740191a01c44082007c00c074088403c444003080c0c1c0007000e900080c035051401c540b51034000f4501080741035511060140500c12200e10035521020303000d28103103640f562840145809130041c5880250002c0c00d1100104017540c011003c2d050300006040103218100d0340e48104031a10034844109240131586501140150805120b8000480d0021201051314201c01000d02d80030407041e4440c00302c58200c81d10f042c0031581d102903034400500415000350305608180003c4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 886597041 1250 886595791 886595807
    0x90204050f221514180c030a0e1c0e03010c0f0c030210061706060d030e0d0206040b0c0f0d050a0804110103021b1f150e18120714031903050c070203070305150f07 71
    0x5415244007c00000c064604c2038001c840320b040e0b03103c25611418081e1024001c0c181040410300081090607a201c0703042d04052064604142c0c0982d9010402e0440800c1581c02c42c0c02c08400341d00714011006c03a000d4140305405600d001780301600100006048844206080a0029055622410446048401296004104a050402c01c9500e5413202003144000f641c184a16800081c4511340400e980d41682c00214003c000407042c4010743d810380c0a40041107503548240340303179a004246510040341c00b084410003c81c40c081e0040c107006107440c8207101c91640241d090014801e566003c21301c410003444d04c0c5005d03100c0307020080d00d044c04a0040c2c03002501d6a08104d01400403801da101000800c0120626030200c114215142940c4c4601e90030300e05845950312070b51041da00c0000f02000c2c0028200000122400842040c000036844240c0041c02c07000f904024000d054011010711a65000d0f0307509100c0000194418802003886004840344c0b0242c0c0300000300403134980500202004812a0080c0407 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 886598291 1250 886597041 886597051
    0xe04020901090e0a050414030307080f15030115260c040b0301021c050103031403010e06100e060a053712090f0f0b01090204050f22151418 61
    0x16845410500040b240710000c0c0d406034034200300c91800d1100c2040540d10003402180600911030b0405425100b45da903920066801c00006084000010782d000b455100c0550001d01a00c07040d1907012680c0000fa017914050345000f038185029440400000ca00041c50200307448505196903007040004110700d4580c892a003205d070240d51940300410700c5076002c2d41121401e500c824080d85400d550861564002c21003400210041003940d000c040c4400c0d80101079074121180e1000001003541c0340c0e402d002c17060501031401001e000b02c010700d064085d59000c01030145035069541e2a81c0341c000448a030800721a00c105850400b8448180254220841488040d1080c0003828070f481e1201d00341d40c000005081a060140058080b1002c0d50300b00904410700143c99400341c001100942d8031070001d1412841940714030740d44502d661074140c042d400d0040f118240c034840f00001d4803004107000c03104401c0e10001c00169085a0440d90140709111010b120214441c03000e40e8800c5510307001000410b40c0d0100580 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 886599541 1250 886598291 886598299
    0x17042705160302070507090501080708060a110706091b0b090a0b04031205210a0605031608210d0e0105010305100c121802100806040c0314012d0b21070e 67
    0x144d15003401000c01400c030003444019010800c80da907820b00301d83c231032040340510940e502071000403400c2841d01d40501c04800c100c41e101c5614020003552968020310110008841e0100842c024690482c03503070400e80000c101d02c4810580c1c4800b0101000303209655500b020022800600060000c1210b4100340e542101d140d01746180c1c2d403054a4507860b88a4070110544041004460400003d698a6000a821140254112034203214160801c8406492500a080075a0f120850b4402d0902010f40d8640782c0c8122018014a0410800d000d101614012407000138169110001042084410030800340244040d640400401301401801404056a40c06041c841a243c40c1c8001c01421300004449150b40c2c000e0844407442d900c0d2a018216820403994248210301c1c0c80d4090b98aa4001e0044603451041b001c2c40c402540c0c204001030105614a40c0c2d000140c1c04956104100114a840c01402070305100c064075807910350000c09261405041400307204210401c10520641c0c80d0001502034031418222 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 886600791 1250 886599541 886599547
    0x61d0715030c0c0807030306050f1c060f020c0319090503030a020601090c09080d180b090d0b1f0b0702090106110c040c020f01090308040209010503010b0d0b0417042705160302 77
    0x42e000711058100d000b0060038030000021000c041503003507800f00e802c48009031100b40c200e440800420014a241a4035000200101c984480015109a216085148401e40c0040c20001280342c02451038110601c11182c84040c2d03060f0f50710042e040715a103002010210020352800096420094460300c041c03042c181d450361030b0910304100c94060300785103010300007040480c4d50a100f101c10007014810109284c40300e07c01031003004220003480108885401101400300b80381100a9035980060910040c404c90b000b007103546c007940c0c4036580317100403600074850390101586404c0c40d40108492407030180d00603401d00400041380600504040b44488201804440000c1c0b010984c207001c0c6d0030324040340400441546808100030030150000c8a80f4011402034402d041640c0c0c82d00145405c0f120070100c4e0030307800001d454a01c400940d8540001d54847d00c6000001c890101d0626000200d80190700700048918071a034180341c003280c05129411581c28642000e00c000e04144a039044059001c002c2c0808160f000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 886602041 1250 886600791 886600811
    0xc06070f0f1a07030b15041a07060204030506011d1006050c0109061104061701080604020904140615040c020105041e0302033f1e04020409020904061d071503 69
    0xc031440c100110380090140e210104240c00b014000042118100d0100f0700d00041c803010350030122803c04003500501c4040c0e16043c100012071841041d03441c04030300f0489040250000003481400908000d600c43c03001400194104403840c0c1100c0542e4058603c80042041002101c000042890381101c5050400760f9a50403000ca106d809048803174005880c0c13500380043c0001d510f001c10020800c0302c203d65190b41595035032a003040d00402081c403a448140e804100400c2c05032500c1c107002030300107101e00681c1d6081c0581c8881e50382403c20482e80d0031400b41c034603100716000b4101801054940c04640c07008002903d0300d5a20285607048080e0703c120103403c0d4080d0241018020000c8401221032b41520040001036804103a4021503403500c0010507100b2084400c0e403104692400c0c50044800c0e644001001d55000007088140710010000c2e40c0c49600c5941030300c00342e250110701500490107030380049000f01d14034030151030410424500c03628541c0010020041d0f5502100b6a902092851502007685521 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 886603291 1250 886602041 886602053
    0x80a11010b041b0e0d0b0703020c0a050a0c051206040203250e090f0717031c020d090606050f011b120311040b070b010f05010507060b0102160311120c06070f 69
    0x3680e1416a002440d005400c95401c03c031403051012032490b035460391540c45801c0c1c2070102d00040307080300500b00316008000ca802c090007600030f001211074550480c2c290f03280c1d607110140b40410548007503800846001e81889181130070407a240c0701c181d50100600c0c107400c155002ca40d94040140d00044a03e010440807114a210314039240004e00c0c0d81103007000d05040181c0d940b034032800e0919201e00d807442160800655021200b5130b10070403500e6103010303605025130090f81c800f95110444100d14607036800c0000250080c854420140b4040c0a50800100c1034100014028a800c400c4209414040c00300b841c40080300b01d0800402d80b0a078400805581c1001850b410780183c20040541d110381da05c08640070400035440e40190041070b0043c1e000704026682c892030b00403404800c2c002d141c0010010400a00070404640140c0503015040c8120703034004a1650102c042e230480c40d081258041c040e001100698900604d140d0452043c0c0b1002d0f03c1c2035041c82001401d42d204500008160350b8401d0004010b001c9 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 886604541 1250 886603291 886603301
    0x2070b0610120207030e0f010824010306030605090d0311040506041818051b1e0d0c0801060611011407051204080c0a0308090d0206060a170c04020c0a050712080a1101 73
    0x2c160664440000307140140000f440d1008440c019040613404101540c403a959041c000c4243c0c0c03040c0903a41003681b000b030f4480f02c81d1810f01c2e0b040c9911484000002485c1380704051007180050050101c024598030024291a0720401c1e521041c1d07002d210a1080350340740005c940c1294000b4a40b500c0c255118100040a1308408502c000d800b040c40d070b03e0509000c00072440414800b0501c00880d18161014204000c0034804001d000c2c1003020301c903001c0c515003441c01181e4100740c0950f0700c2000082d540c3d45210f09407030403508244005010541c0c2c1e030000310b03802d002c0e035918200c1c501980601440d0000d0014100d01640003420103180042010038140302d5100f0860355020440c1c004d613854000745090140c18600c00b03071030070036051103121007010078544040796040c000c00000f400e03d1201440e00d03100040744100c08040302c1c9a40034240c803c10041d508d610041001414840103802e006142d404c1c01824074116a01c000d180318441c000e0100050044400c6a10410007410310b01540301c4440c0c0054018a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 886605791 1250 886604541 886604567
    0x20d030b040b030f011e1109010503040f02030d02030a031a03030d110c0a081b03030f180708071815060f0302070c03081219140103120c1505010608010902070b0610 72
    0x40183e413213207208001c1c10741046240f00703440030250001410604815084840c480d869059034501031011846561090380103640203409006007a4a4a40300d40000341048122040b40c805640001034988440c2d400d805003030800f140d8543d03582549642c0f0001300e0340300d12a42e10301c00c02c00f558070416000f80300081d205407510216000308032884250240780c84070965000c203508a00c4a0403c0030040c41d80840003044903c9609000745842850701ca0b00085095205045081100c60048140201c0c03a844200056001040012009c0002030040c1a0480448100203004404046102c1d4284003050f000702c0d0104400d005407500607502c28450915104920158100078400e140000d0706030718041c034139110b0038000c020a07020078411210010b001d208941403038680e44010000080100086440c0703c224401d440160b04041c05015103c7e40c1c2c1022038030b0840b982481c0f0030fa0301c00c0103214156200302007a024020aa100318a0005940c84440c2a0080200243d2040c010882044051489945030400d12 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 886607041 1250 886605791 886605793
    0x171312230a03020111031501030e0c120102030f06090c0304120504381e0d020403021c05060907050a0902130906061d0d0b0f09010e0304090e0c0907020d030b040b03 72
    0xc040300300310311a1600c4004034250019801c011030070048140050449001d12191039030069902034001c0194060032240d03502d40c0f041c1c000e0f041068030036140c0d40a09034140c2c1034400016900e02d0440015074090401070071460142813081c0411851038541d4007203e42150708200e1442117111000310407681c900c181d4010404c248407400e62240500700710000f0207210f1350380c40014042d4204030803c0109a0003181c18440c0400c00b5600b20414400741c21005109030138065001510301520782e00480d00d001500700e403422040381c2c4d541101041c003400b448200d4001850703201404200d03160500003015602d0a006440e61075074005121000e601c11315120304003c1810040030300441e40da420001e0142c51074814800e0103103188464208083c9440082c2104280d403050810b2407030388404400d040d0341d01c1d0085c01002c0f1507503030700700c601d01e2580d04001a00082c8040800070842114800ba213500b0000c0e00942c1c2d60044008006000013a07401103008020301c80c2a01e000240200180d00080240c2001c440540e01 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 886608291 1250 886607041 886607093
    0x80906161b061e0f0e011214060907030905060a050a0b0a060f020f060c070f0503041805101502070e09151807081606080402010e030105090a171312 65
    0x441c0318901128111005900c503a00d20034101850610014030074034400002030180d10365010614001c890810681c00189019500d20300b582040f0021543c0f00803510300101d00e0300d0300b00001458400d6941c2d07403099070341c5014421403003107503101c650790100500b0305000301d03442e280095030326941039010b403a01100050004010580e1580081c0c03040b54960343c040014000c90360091561840010458002c80c8003100541c80c0071902c0d05c40710320310420b44800725000d0000300000070309143c2d0941c0480d0300070b1092000145500703060300600703100d0421360301c10f0700c0c1c0180b910000003a00e600403540c4c0089940d01614020103a0b00e900e041c0b410100c43c014030305034603001c032410311080d84402c0003542404003c1d01e0484406c00d0700c590fa107944d1400c80402c200d2142410380018800b07144038000300b0380c1041c41810800c01003104074000900b0b40c3c000b00d8000391190f01c0040b07017005209c0c80c000c9420001000141080c5050500381d10420000201c1c042c03090f6030254046030200704813111b91000102d41400001c030307a03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 886609541 1250 886608291 886608323
    0x60d05031204020a06180b0a172d070c0b04060b04021206030d090f090c0e0a0e0604060e010503030a0813080705210f0306131e09170708090616 63
    0x101e11410b0b2816400350b90001d0001c9101c0e801b490b40540036000c002080701a461410340302440641c0480c0c414002c100d14040c107203038075140203800709000c1c0d1744c002180c45a25880700701141c2d0700c102c40f01c0b550301004250310501c034406400c803100319206600310300030520558460070000c0141085599240c1c00c2440056000d001351544c942c40e90080302c0860035516012054902102c01c00712501401418821039030081044d403066901c0f100c0441d0050510650820041c40040c80c1c081c0c03980d008440001c04a010020a8a4030384500d4026055001e00b4aa9650400010079580d01a025582c4184005280410b190b102d041c86594402c661003440a0b503914a6480e015446100222041401c10b4415840c0c640400d141420b485d00e004448104605699a5800300650383d09807030b03038400075907a130b45080d00001070400f039100d01405a000c80c00308400e000e0385050504020100c00501011406204281c00110500d044030503070030080f600300b40c07915501482c806400d0316825000f020714070198107a00e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 886610791 1250 886609541 886609567
    0xc1602061803100f0e0a0201080606030702010b06030403090303170c0f0f0d090503190f020a290a0e0f07030b2d0a090b06010e01090302100c050105090105100510050f03060d0503 78
    0xca504c00c50b0350014080740080040f0301d50360300656400240480c8504000901500f0020040c542c4413849100110b4840d441001165540c0d03c160b5017900060425802801415003011194008a0042412444510b40000d06501d180140542c10884c0c0d0400900c401c1040c2d51042a58801d07020813404000d10f412510b000ba580381e1003281504200341c0405244c003030700d41c064421040384421540251205c0400760741c400b560f406400e8100140096031280c1640c541c408200c5507807080d030070100001020b0740b40140305482c046511072050f81580c00701c00f0a03c005000d0501041e00300b031404504501710100c00002e01008116000c80180c1500040104030856513140c0200960b0b07030045840c41500c0e10342600455a8010420a45000c1481101c0c1000141080701f11000360001c0d52a00349a41c208903034442e829600d0640d031a1603181c1d1510107211003c2d0320000110300920b01100c820001d68860900034000b405060751310300d550840400021429140c4050704240c06a10109503951001002205c03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 886612041 1250 886610791 886610801
    0x204110d05100e070906120902062a19021e0402041805070e0108010e0711030c0307030c14010e0d030506210a200303040b0c0120030f0c160206180310 66
    0x10943c0c1081c2400400e208500600032035040c0c0ea81c90fa14a1a00b00e034020215001e00100740c012a007100d010403800119125420040c5000c01258109602081324440d1a80ca86030280721300c4080d00d0200030704c020050707507940340c00038903130028040e01c0710201d00010000d4000e011341e5100d00700c05c0543c000d0322503801c16664130861103250f05464070400f4846540c011a40b200e4240210b5102c061070801140456000b801004074012078101201c3c68801804021030854001d50801c502192021140c0c4040040000d4403815045148008002404c0d88203c080c0d901d40c1c0c0a2804014940d907040410b40549a424090002400c0c03600b000100107c988103a036076401c0d885900340d0b4410315510b86600300c01d00170159401e005a004000710b0a190034900303070f280c9942c44061041901d47d82d841e900e01c1c20314134014074460b0280b4950307182074880c501031003484000790000700720040108082100c039900e02440d803182d0305200d8040e50b079162102410249040c0703415070b80801581c18071851201c815204115041 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 886613291 1250 886612041 886612049
    0x50f0d02070602160506070c05060d0605090f10050d0311060c090306090c0907050a090e0405011d0c0306011413050901060602010c020307080a14040e0408030f070c0209040204110d0510 81
    0xc440c0c1c281c2e503800c0226181e950590001a050000301d0041220703140c03d1001c1e05002d4007076000d0031510340da6a00041c0c40c50740640756840f5040c2e1620307020825850000021340e48005000d06a005a00d810019010402c8081c05520304c03409103402400141485084828070102c292402c85078142032a8040e82010f400640303840c0c0c440e2048000240202d2008100f2843e034030005800590103483d01d041c107a407283c01855030001000901e441c00600c50201c100450b0096006100000f0400e1003083d40007090010f420301500d09d40e0007403808184c00e80b07001408504585840002ca00c018001000003a0040400407040f26021b05141c1800705540046d4068021030398a03400030080d58110000582c2c50b809076440190094406002c1004918042c15078503640b0b900d8454107030301e0162501454410100d01b80d0342540ca514010040244001d1451202a00144e0508018540080300d900007004000c1c000e0000f8021500c50010307688004c0c106081d030300c418404080c00e0006207011404801440840e03c1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 886614541 1250 886613291 886613293
    0x61d10260f07110a1202010b060d020903010605010507170d0920010e1503010902070807050a0605070e0a120318080a080309100c14091807030213090608030d051003050f0d02 76
    0x104402c1030050118000c0e814142d006400107058980350030b000000505c01e40307805e65403141c44c81c504c65518000107246007503d000005071248030f040241b50840745540c000034140300c0c040007480d010440100040312404440c03010320b40d40c0c4850b15100f0b405800d1071a00200b004001c103409816079600c00212241c0000207996500100990340700300041c0107400c2c5035a8020310000c0006002d0200326800601000d07005e02103062600c503441e03a80d24a040d21014094490070703641e5040c00300056001d45560060702007161031684080c2850340d619144411700c80c0040511202c000c3c0c0b488800d508080e0079000301424000d41e071032801e6031f0400800c2540121002800782c004c1045032083c50701540320741a6040c14542d00c500941e030740c0c042030b03150a07440942d10303ea204144040221145100180c494480e45040c2d030050780b05c8205c2070760005414107030f800c1880a6810024280304c81071001095440e135400155012031281c980c04841c400045080c0c00140c01c030b000d61401c40101c010001160034103901d0a41c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 886615791 1250 886614541 886614571
    0x3020607030203190b0a12050715020c01140d1b050d0b061306110124170a020f1306030803010306141503030a050708191107061d1026 59
    0x14049040f44422181400002940a00020805055800104000780252050141607102d05d0401c0403002c0c0200100c1d10303070b40000018013000301c2d5400141d800f5000b42c0000d0601c1b5042d81c0c0082c2040010004d96450301c2400301e06140c060340103400041084625210149005003603030401089a4802406516000c2c100107510720300342441e400301c3d501c000a84120000e00b5003410f408492004100840711215900c3d001070018500c015628050400d490b5080c205c2124070f041c50346402c50340315285100380f94000000c0000540ca07081c2240d030492200301d6011500849c80b038010b030300600d99508007520008011001204018190b0b200c5036404050030904078982c0da803500200d0380310b0318200350103401d42c0080c803d039190301e4094400341c8201071184c0300721030415103044090300ca034a01c0407140a0000c2c49149403800882c80522988010f0321241c5031401d40403401c2030035180400150480240601030382c50745004058484c8000075007000700c542501440e000408a03003400e00506948003c0010050 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 886617041 1250 886615791 886615801
    0xc0a030b150d0c03062003011d1317090307030f20060310060c06060504050405210a0519030b0612060901140904064206020f030d050a0204090513030206 67
    0x40740220241d80c82a05058600e04660300c410203003200103000200d0074211080480c80346c01c6013024601801c042c1001c040500c01400c0c10300032012002c1d180d05d1460140caa400b002140d1641c10035203003c044150348aa0b1007008102003454240b159102030700c50349903030101d08204241d43c3c02d810001c038129403070981381924180c00c12000d0701c0140c13202e866152042d58104841030103101020495402038000044082d03807640824181c03038040390f0446580c1c00507045245243c82c440b1007042c00e29021302100f810521902800340051182142203013141c1c0e81c0182d4058014401d400542c90403402621081d00c85801d0381d0400c0d84c450381683d4080c0704804000000c101d80441c0302d501c81c0d11401c0103000c0780d074946581d25060001c000c490400f01446680d141c021211116002d1526200b801d40f02c03c80e490741c203011031000d107090b440ea00040d0454200708442529000d0000c1a10700c0310700e180c000040d49480e0101e4070710081c803031603100840d942d08203c00c004041d0076006000e07100074001d0b001e980440e990 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 886618291 1250 886617041 886617049
    0x712050438090112050604020d02030a05310314130b0408121809130803011e05101e031808071a100b0903100e030703110a08030f090c0a030b15 63
    0x1401d02d2190001c2c044910000a0703480607001540c01020280005151690401d041002d84c1e004403201000551564144527800344400c0000c041116035805401d2300d506142c2e01780101807407014024003000f0202e0080c0006404d910101c8140440072410607440903690800c40145400030700c18552103010b03c11500d1685041d0030205c805401660130b42d40b4040c40c004040151000f8090000c0c291451004040800500c09100841c0030380429a0222010b00c000030445042030101e0300140c1c0a100c5410303214401d41d400084212946d0311402c0c031903a031528a100220020034200704045041a00c10310418248079451004192150082d0300c4210b0328902c0d070400d01c80c10001600e42e4041c0c0b1100d90000c1100d00c0b444d1010300b02c3c1c141c0017000d80301d03010401c1c4950800c2d2940c0e0b400140a42e0030018101080641000441031060004005000030041d0354558501e24003000300150845548200021425001484501c103000d20017030100c0030b015122b05000584c208101c03600e81c02950b45a003400510702d4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 886619541 1250 886618291 886618297
    0xd03051b040b030c07060905060910200901080403020a06090b040212010b0307030201030c170f090c030601030f15110d0c03061a0d0c02120711030c150712050438 71
    0x5442402e45151038810521416074050303181503401c15540d440d560300203103051000b40c0c0988040c400925540c02200c07420030488800c0c1030301030705ea0301040e41c5445286e5010010f640d41f200d0242130038240350703549080030b908041c1c003400c00500c8680303803001c0c1c4001c00402e10050b03400341d8000d4070a16032000002041908890342d0320b0b840b070341c10350005000700700541c401e0708445c850fa01a031030207404448d4140b11041d020340c015901c40061030701040411503c5101081030003a80481180100340551568880c104d0b000f904900141190321074210842e0301c04881d0700a46046507042c0c2210b0ba4400000782c503a4001e05001e0344a03400203040c10000501030302141c50000b82e08620b120528070341283d0100c1e1200501103c800070301940104c0d0300100001401a0142c503050740030307041071018136600704205402c15290541c1c261064075000508816a2406000d643d002c079407081c450400c0c480040016220750040b9803045205481908034900b2003043c0103049441c0034041a8100c4600c0e10710840034003140 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 886620791 1250 886619541 886619549
    0x180d0308040f0c09110403060b040603020136080f070e06030d050304110307031a1b040308090a090e010204050108010f0b0f22090c121119110d03051b04 67
    0x99410300201d0089041690100c040c1d922415803000819521014041510310031303900d011814801080800a01000d4005c100324814100c03820801f99003954006400f1000318040b1500c00903003ca8561f0009028080030880314001d9229050340750751300c140256459481c08641801c50141035400144054010012030007903000a000c0c00041c40d8860b4100d9243c1c000810030344141800c0d00f08080207031010f01402010350702529940a01c0c40111220040d00d440151000300c0c03a00007080130310036541142c0c0c1500d05483d84868046d540300603007800140505070036040b00b0724007880c04203c0303081c521055005108842003030700d8421003681e840c000360055040910404800701000c1005030302c0c00920030000c202014800f00021368221780040410080b010030341154150396600c95a00040c5a08094054410180c549080c00002c0401e401005c181c00740b0142600c041c00491000700ca01030007220000312010f100403c554040a2050000300901410307035201400c071482094a18500c1c10300c0c02210243c0d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 886622041 1250 886620791 886620797
    0x7054609090b01031401080703051c09090e010e06011814090312180f0706030b060c0a170d090c030201030b0316300b06010f0f080a0504030c0b0408180d03 68
    0x626001d02080680300d4200c600341050340d20b50b103441c1c20080860310107020f0204d400040418505500e0514a0448031065503400403c081c917104010720b030300025076810b40e0341411010904c0c0c440d444440f8054421081c00c005070f800351400100d43d9520f0201c9459105031881c6e800d02c0303240f9840b041d40c01c04540503030b1102c1032a00100040c100d0032443c0d84805802caa48a0341640d110301d024111581881a40c07002c0c00c4003500408400c01500c0d500d4003c8450f240c504856007450000701180c502c0d40c0e41c29142e00240401e002c1d080644840c603242058078400003400c0024030400003945000385241c007080c041240480c0c50300440030018240055071607500c3c10f20310358041c0308a081014a44024841c0c0d44429440c02c6019080d044482030010ba010303040b0300c90340a0384d5280c102000050001d04441c007800040084074940d84a0042c0e005012640050381d9482c001050780b40c0d42411204640502406441172002d101400304100000000745201301e02c0e08000c01040743d1030307020011442da500d1405800 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 886623291 1250 886622041 886622057
    0x303181e03120411030304090207110f03100f060b040f080d020a0b0c0304020301060308123405160816050c0d330c020a2612070546 58
    0x242c900b000e16560828018001c0164419050000920350f070b000760000310035260040b07409020013801001a8402600c1203d07404a4920307a403011903503c9c0b0400301000c2040b600c42c510000c070020658014000707083c402c801503588684452030380d07003100303094030400000744103c050100e0718a1000ca800c0f060313254040148409900c502101060582018000b40c5c1e15550ba0407000000481d00b4006000b100c003e1502071032146062114403040903800343c00504005160f00070700402125a030984001580a400c059896482c405603e080e0b4681e0080020a81040010198030801c601512050000e00c10400c0314503100c0e8a000f80a50342a03a1440100313050f0b07500700308005103980c01000c0c03a150f00360842040700c06d8000c88400011790b002d020400c805078101003440d03010303c00089181d201d400180d1a41900700d030006840542148a003009c1c05101020070004122494801d00807103201400300d0f00301c41001d1140222807265a05481c1d0312071026608200c590301422414021002e4101d181c0c0c8441d15 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 886624541 1250 886623291 886623307
    0x7060c1403040807031202030910080405150601120906090c030b1f05060a080727150216090b0a080a050c130c0e1e0901030c06081f060509120303181e03 67
    0x100841d801d40306c413400d50005008141d000e4840b00b4a05a207800c840e07032048094202030504c18202000c0803000080e0a04da40c3c00c010741039801c40c04a12143e8a00312002074806024101000217008160300101560382c119400424410400c80190040e0421114101842c0188084004803407603481303000d410110134010000110f020380190b645c800c2580c10142100c0b060650350701001440c00100385030051450038140603407100044019004d101c0c90000f04113290240340982c1c403c0c3d5241c807544440a07218294541c072a154203e8a030000c0041070304440c0c1109035841d0041e101c40c0c01d200d07980d0003068013160b82000f440a5024501307081d4000d4454000c40e943c140240f10880032240c00c02d04001d081e002004040d5103d05000703a000394081c8035642040740c2045c034010700c84100a0a034401c01d8190b90300d000c220741c80340088107046902030304120303603104100c202058020244140303d41c0c06000110801c03c02490401200110f2000f820680348400b41d220a15052881e025092610135402800240 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 886625791 1250 886624541 886624553
    0x10c1106010b0d020405040203091f1e0b0102070e0708062412070212070c36090512040305010e0c0108071403040f0204050c0a0912031205060109030507060c140304080703 75
    0x10b001c43c1c1c004400343c0b42503120400300301a40d006a461104650082c0c41909101206c0302400a592074a04070900182d90b5015201d02005218418640c0c4180c6d501050b09180e03008200c0000104004100b040d02843d0264000d400c00b0401c0b500c2d1405050703d80355100000e004805012150041405100c0c00c106243d9004000e0090041001c000d501c07900d6903a51034040001d016001e0188245680c181050078500d06036188081000c41c1204601041d12542d2101030341074000039514049200040d5444490900c6450826006909c40e400c41c7c0014010041c0201034000c9030318440194219046035107071070300454203004121030a400180364030103030280c1c4031601001550054000c00c00c020017240c164002908640041e2a041040140003580220703079504441c007100123002d07843c1c2180290640384c80241c205d01e40700c095102d07801e82c2c074400038169038081c40c804400f8503004021619820785950700500114042c1c03206940810511221950701840001140d0a40301340340080d0261030f04c0d5585074 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 886627041 1250 886625791 886625797
    0x90a030c03080a1103091b042a05090a0f030201031a01081b070818010816050906070305133002280306050f0a110702091f030f080a02010c1106010b 65
    0x28908464480320b45a1804c200300c8003840c01280040c0c060040d0000100c52804981000c00c01d0318026400d000c66402c8000c600000d18081c1c000320b40c902e1840c1001520210307818440d003010103a011240381c00124044500e0b000c0b007400d4074070030780301003003588540c1d08100703401402a0041400103a003032000425450311850403070030f91309868154904103500c5950300c884e6908080098042d124100100300350360340c0d20907840ca80140104560300002510700000500758450540f2150042c0780009015040601c03440448420181d10101c00801e01d444109010b4001d11251801e400031301002e407281502c3c6031604140303041c213034010007403c0c4c1042030041c6c15601280301d81c0c81c070503c0d030703412180000480e1050080c940f0803030020500307034418503100101400301c4401240322492201c00703000c40300060315408942c035007210b001003180c808a040b40c510f050042c103058000801c0360401048030820403003c82c0151a51402c0c80d0000d2001800b0140126003800e00240200344503446140100300d015642c02c01 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 886628291 1250 886627041 886627051
    0x5152209020312030405011b1d120a05061f050a0e2d0603070f0303050913021b15090d090b0d06050d050c090c0306010918240905090a030c0308 63
    0x2010401000340c0d00042d041a94650040300340c00d10010410081100031b01c9001510740c1e15495802c0c440071030302001000101500741c0383c0302258100c500e08803c0e0b9211032030000d08054500403919451006d02c2c006803514400e440507040211500d05a100c82a040304402060382c1018068500700ca14180c9a20809030001d808080d0126880f24080048502d94002d14a500e42c0c15145607524200882410b280000b41e90000b25502c000141c10710002c0d07400002c9410414084580400c00003005c50705900a204c2d04480107401e94000080e010000d40124a68030904201035210703105503504d01000d900c4240c1048042c00043d81b1400c14000102341e440079001100b503200c40086c5540d00c440101c0e054021440e801c1c0c60540c0400c140c8021840c0c18588541c1c400428081c0508504040001030301d1101c03140a140300440f11030b210a90006800e52000e11070000c1d03252268a80b9044030602940f59099000340b0785100c2c2041c0c00941a8900041c01820140c1e255880800324411a00d0880c1e40c0000542 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 886629541 1250 886628291 886628359
    0x7020d0816031112161a0c0703080619050405180708070905060f031f020f0406200d0915111c120c0507030c021f051b07050a2c0405010903030515 64
    0x71406810200d0019151090310386044071540d230051030401408600005002c60700c9078421404903850f100114106038102c81c020b450109258541d404484000990823940882d14803400800140b0b8020010310101101c002000400c02501c41d1000d0004e044840c41404d5050f1748100180e03000b0b0401490060b2001c0301742c000c01070514070504600010344c0e2140d03002000150786a0000d0940003000e2600604000d621802042c2421001b840074003011641c0c45880492000003d036468610f02940e2400c40b541400c200b501c40307058456a011007403050380c03c24600050309013595007080d084944600c640e500f406455445c01c1011310b5070111000700b40c00400700d0300304240e0418000c140381100314446003100b9a840d00354407034003450315441c1c800141c2c0384020f4240c1d020000800094171581000810740341005000f442800f0640803c104808a00108602c650450420007060020662015400724820b035418022a22a05c4a506040d0307036241e000780d07102c1c2014807a601a400405550700072415540 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 886630791 1250 886629541 886629563
    0xe034806011703190e130912110c13050403110304210206250212010c0e15090d0c03030206073609060902040f120b0c07020d081603111216 61
    0x10340410071000b1303880c51502c04541682e480c0c0400d4a0240b00811080e0a002d0080007451115110250b0300e005104421061225440c0c03c5c059161081c0600c204915003e4818094800c02309844801850216000c0e00010302c4c2a0b610070501901200b11740c00c0303881c0d00e40c81d5903030703c1080106011015002a01282c0c861410011004902c10a00e1030140c0f80000d441604420b22680c01408001810802000314a900d00314105401c542c000601c02d44a45099941d44250512501e142c601072040210250703100c02c0d010b103020300b0880c0b040c0c0044107491013903080c2e0304d02e07846001d001d951440061203066030503440401c00d00e110584801500c0c0c0340368401008919215990880081103901c0c42e0480180749400140521803000280040b00c01400503104a044440c001c8c0c8411500d048046d000d0740014000061a00030755480451240c14181c020090568440100128410180d1050f20441c00301c2d062540400c0c1ca0341c800300b480c403440400d102c8035900d000c00d02d060340c50317501c10240411900307880b8031 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 886632041 1250 886630791 886630807
    0x1a09010603180b010e0601030608030a140702061b030304171603050c0a0605010f14030c0a0303080a0902100c1506080309010f1e0c0c14010e040e034806011703 70
    0x15941c2d8000c00c003001700500c450908030300040c1503450a8000c2e1200c1c0d481004400d0701e06a20a81a05584a00450894803102d41e84002a40e5120707900d80030380c0d424421240303180d10440110003540a42e10605501c17941c001307503242a60781c3c1d0040c80d60600010031102042c20103e4007400040111078495010b0f0342981000b5607e1904580c02a04409643c4075580b0060140f808030032a04018008100d000307019890110780000c41d02400350100404009180380440c01c4a03c258202e0096184d0061043c4100700e00468001c1001c40882c405a0b052003640d001140c000c100c601c151020390318030305c0c0590b10340040c0b0001903400c25030a55808041180c80c208030180000c483c030070f600070f804036a5501e83c500716580c20074a40c0d242841d0003903580080d60f40071540c003d0f03800410b62084420241e0380801c0d212070f01036450f400c50044024550240c0c0304c1d08180524105203006203015408208203020101406600c412607103006d50b4022041a484100103004212011020704207610342c0308203ca240900d9 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 886633291 1250 886632041 886632053
    0x1140d0c0807080d18090b0d05030a121404050706080c0409051015020f030a1b02030604030c060e192316030b0c09010c11060d1d011a0901060318 64
    0x168810304041d00041028041440c3c00d02032000030540718640f50300740218124564201018a02c14100c203030360b07034032290801900c520b504440d503143c00005890f1103070815400a420445161b0401580c0f524104000c1c01070124000c0e0b070f40c0250307040f00081130020b09016003600e1010000d4001c2d5000743e8180300000314220b450003600c1c41740d0300500c0e86840e40c038a0309222010b10392215a1903001c0d500006000c038000280081510811780c0307140b90402c0c442c8084a001c00d00c0310350106007c0d4140c0507086c200814940c200080c64005417080204000500b0a04d01c61130f1a9554a454181d50440000b03400c07001c52070100c165442c040c902200d18101c1c16109100c0e51a29024000703a50718007824840410a1240610001c0e51100c0e001c40d01340d1410081000090245e000404020074605004100f0980b507282c450a85e000078511901c100120800552004007180120faa0412903608150fa00340401e6004124001d61010240c1070200503420294190003815142c06900307148640b040c5240f0100e81 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 886634541 1250 886633291 886633313
    0x906021b040f020a0c11060c19030309150516030c05070212010b042a08010f030f03170907170c090105061c09080a020d0206010612020901020109020d11090a050103050601140d 77
    0xc41354840b00102e000d14500348089241010135213108102c24440d5050090012034003c5006582c0181d281c042c0310b0038982a4014000c406011f8903411000820400d0310540341d002c1801558085c142c10b040d860b07280c0044040d99000030320300001900a02c20b110060502c12030103d00c0001840010408400c2d41021404503580031034555114804006403400c1c120744214000f010110038903110150790b04150381044244181d10004001800001c0c0c5402414890440c50968014a003507a54040c1000c41007581c2e5400b6a005001b040030b0080c5100308011000100803801d404090300c070b1492030780382c0800c101e0b40750418060410360842c140e1011000c03464911a40d40702c507205400c40d9071100540c95000f413420300807209040a5601c01d000602ca001c0c1c02c800301410483c1444c0c4090380e60302503440100c0c05014210002900038520960150070004082000120301009030307240c0d041656003054100130781c0d4003880013800300d800000c014040004031030070202c0c803a24060040300d44002c140d40c810325201 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 886635791 1250 886634541 886634557
    0x1305190501290a0e010302010801050f0303070b040b190b0a1e0b04030c140909063610180c0b031506120702070902070209061011101b0906021b040f02 66
    0x100a1108110b000d140c52010035001d40590351080c00c10790304543c00a040e071350040c09013512a112110b0800300a90b800c100715080c031580b2945920701c2d07060601c0c041003101d0307081d1208040c0c60b0712503250341115521031007451010300d4010300e016a0380d460b10021518084076800381c00c24a2040b04408a04041c00000400045200742081445180f0b0309402c10f42c0c50454100c064450303090a010301c445c0724400580180c02c403640145289810f01c07104660841c4c81ea16091050b1311002d0961501c50f0310101003408250018800014010b04642050000441c00c9000c0c0c010194402441e0034010700c54450302440e40070400c448080e0312010200001030303c0740c10101c1c600040120200402c0301c1d480d4103005403c000d0000d0002581894283c0d40000e01c24a401003606005101d036080486030144904512240d0b10640740c00e4818814000c911403001d8402c3d030801b85d243d540b03000c00e0344810b54826a4140b0440740070b83d0140415452694003801c000c1040344104d0360003900c2d1024560301c02d41910042c0380072 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 886637041 1250 886635791 886635851
    0x608070b0306011803052508011d06090109080712021f15091a040906020d15060e0907050708090d051c08180304120602071e0201081305190501 63
    0x1910b081c0c030005004100c51900d960307040103040400c20004100103600680a0410292009003091085410107501c1e21980204101d40c20404003216084200701c0d243c07030704e0816006407095962140001800d86112620042400c0002c005500200c2d00000200c4052207442c419200c164103062045e04450310440e100701c5007640d4685050005600071444034008100500c000d0042c44a0030341420308555661300d50901454030b07080104104000c96044442030002c00c081000003c402d1b000c0c3e010f500a45002c0c0c50085040c2e242000365519155515600c1a40303590344003490726486544880342900035a10181d01320450500507000a0070500250032201000d5070b004d10300544014000341102c0d400b40c01c0071041008014640d0100c10084221401d50303010b126140103582c960b1800700d00034428018041c1083d00481e102c410201e01c0a8030341045c0500036a6030603060b45800d09068078400103048024155480b0740031161030012003030320001800b0302441c00055001e40a5003048691a01078101c3d0001c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 886638291 1250 886637041 886637047
    0x807030b090615010f03020a020304030516150804021507051c050c0d0504031707021507150f050907030b06010e0607110301061205030a03020d021908010302010206061206060d05010608070b 83
    0x41c40c1401c0003035030f41c80201802070511501c1950006840c58020203c0c080c00c06d60005843d6441034000c20490340116070000896844031100c042c1d020000080b07001d0440c55800940780b41c5042c6100c2c081e141e0050350020010350b4107154021922180b0f03444610203c450f8028070900d101442d800010030003034902503856040c0d4440c0f03e01001810300325030503500710500100f404140007049515940c3c248084142e0300c0c0036a00e003054000209001d031103d40c0d03440c2c5d0083c00a1b4000400020700281241345081403428440311200300620410f0710400c4610910079800050304102007410301d28045d410110605150300c230182c40c00e0104200354015601625402800104200c450400f4403a40d0010301d40c020380410f031b9982c651340e01522841013501c0c0d00c0c101500130601802500007641211030545c41441d0300d598458040201904011003440f0176030141c020080003500e24100b4040810640e9404c801400081c1d4601c0e003000780b0752440c0390003035171190b603280408034224808000c218041d0100c141c584d07403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 886639541 1250 886638291 886638301
    0x501090308090c0a06090e0919030314010b030123040b030111070b013303021c0e0c060c03070b130501051326030a0504020310050717100b040b130807030b 68
    0xc585541c204540740038070025013041200c02c0d8031225003001c0e6448000828000c1c3c6655942c03515140d0108401251031004c50340c0c403401c06425602070403481c0740c6103203240810781c0d80f4443d4942a010922941541242014150441c10301251560104010017803002401c140d588001ca400c490721030314003101c0c8403000a0070000b0311075504030081c01401a01300c224082c0d900e14110f02c05a1040d0360803943d0542001d030049111070702980680c2c0b4803022101d94000550f00e802d031550081d25002c04442100d0041000080c0181882812101c1d01c1d00300c3e030700940c07400805503500e905d4104000c01046494101014540000c1c0e003e00445000c0c0e840c502e074000d80310141e0305040050b45140643c50551044480d91601c40c850008152903008003280d20000f40d0380d50f180080703410100015005454145480d0801c2403031500400c101d0008500400c041c1c0459691400b000c40c2c1001d5400750000d072000600041040400c004018012083e4061000f0032450707480300360925013002500122440714007001002 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 886640791 1250 886639541 886639543
    0xf03160b0f0403050a230708070b09072105010b06120f09010c020604030311070204110301210c05040b0a120c1802090a1e080f0d02071a0f031003050109030809 70
    0x580c01540041c00c1080d00e0400355000760161044122031818070251100240306003c10710b251036007900405017500e03a594a030f072030142c40c2030703000301011a0345c0305041010480009000445c0002e59402e001c40f040d1008e4070082030100c0c1000b41790110b07078070341d2110003440302515001c0182205a00d012516080c41c14424403042c1402c00081580c580c5a00d082c100e0f90a003a800100e4507000354142c00e001070715130743c11000815503105440380a90880d0400080b8207880d0700080040d41200c00d00004801070880e030001c14110100700700000340c10445071035000c0c001813900c0e6020700510400240300326001e50380c0301d1720700c00070f12210f40d4256071080f200001008542420301442c42c20b1500c5030303401c502c0c0800c00e0300085c10b000241c3c05031203480700451000035580c1e07117011134000c090400c07030b41242c206010b6215199500c41c1240045001806040b00000c3d131040c400c1c508680d4100400015400c04104070500c0299410040c029000c50502640c00004078200703114003041a80295106503003458005040303 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 886642041 1250 886640791 886640813
    0x1e010f020403050a0b16350f0103120c08040e100807090933050a0b0301090524091f061203080403030e06101a31060504050a06030903020f0316 63
    0x451584c0101d02403140c0d8801224054403000401c4003032050741d5041d500600303200011f01e100d05d40d0942014400c0c3e0480d045820390407a8805c001c0f4070201401401c045400048114006028840c180010300c4410358113080154888100101c0301d42640c1da0b20981440c2c071459501200e0303600e58404410080c041d0719000401c21460346210496144d01c4540c000c07046121100e040b03030106594201040c003a0160b40c100d1400141d0090007881401903e061240e2180810031032551110742010b911300c030803070141030f140380306521007805007040c4c00d8018002c078400381e07032041a0603080d980d501010450740200c94a80c4074040c020341c1c1d02c0c02540b8040c900a0b044582c00300a82e50103901c00c504024034079203c18907100907620721680b095102c900c040d5001015018000410b00d580f40c42581400c030100804031061101c008501e03d401e46c0582c0c5520540b0a0300c203038040d098100b41306407018404d082c083c2d0041c0c0c01591080c811910705604280100341940c10140e5011f58800307a14002c14180800301c004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 886643291 1250 886642041 886642051
    0x1818020603281506030c0e040f020901030b100507020d210e0102191709011e05030601181d0405100e010e070b161103070905040605041e051e010f020403050a0b 70
    0x1c1002d08403a16640c070320f00c11144030380000c00d0788454044144d0b07849080c0f001d4000c2e0001e00f06002d41488012184060740000f42c4107070000c0c0ca852134603080c504d013480008a81c00015100d00e0715000700c0f80c091000482d2082d00594514800301c6485543c0e00341b40010528240e0f03a0b5075a0049502e02c4000207007840e01c01d2041e801d40900140142d00858680020005074840390307000305980e05403610040c1d9a00c00801941b40708240a841504256600000198840c800981e0341300d03030a00c2c000000c3c40900301c0c02e010f868543c0202d00000040140800303000c94101e40510100d5030304040d641c1004040c0d03041d03c01c0b1035031503946034036046401ca10304121a034040c04800080741e04044102807210010005910f0242c60020f110344060300544040c42030101500090205218074a803d0400c074005e4401070b81c0c225a001c245903042a001a00703109004d40183d840400343c26500c0c0301031991034075502c49196040455580300d1811107080c01c90310060000b18403a0000e03150810080c18103030f0520310000e04d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 886644541 1250 886643291 886643371
    0xb040309080c22060506040b070501200d0c031d011e3308060a0204180614120c040911120c100f0c151b02071818020603 53
    0x39141074581c0c0da0a40d4070b44002040c5440f0380d01c2c030400244500030300b000b580300c0e070f401440004010079034040306001051014081c400a02080045500d1003001000010902d42d01b94020301030025100115044510b14070054030300070030400c129014550245900843c4444140e42d40e1102c254682c082d0b501522710030f0802c10040007102100300c10700e00d101a450a100a4001800c2d0440c1c4110b640c112040300034000c00011102c40d1300c0c2191500009500a0281c08840310000c00101c420b041c07240a40410703141c4090056903802904030500c41280c0741c1d013608101601030300c0083c1c200d0740c903284549143c09002d070103003802d1016084240007151526002c100c00681000e10b0000b0315840c0c484051000c00000d20b84090b031020703102c108949412503424014081704200b5180130600c030a5412000c00c51610301c555401032300b02e0202c141c2c0d03900080c1c4101c4076072602c610704035401842c00d03030302660f80381d04d1b4414200031041c460307030015401d03900860781c2418a41680781c10a15283c3d01c003000d0082d030500380c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 886645791 1250 886644541 886644553
    0x7030506120309040b03190b01170c0114030a061502071d0615130e130213090506150f060a0203120907030c0e090f0604121106010518060105040e040b04030908 70
    0xe000741c0d40303074494402e48500450f2203000c03411040d1000c02256040d91540100411605903d1134000d40301c0030300384628841c05003039500c0e80e140c404010511503109941616038100081e5401040d01150b04001d0030b0080d00b99a600000540c3c120007d5990110080e40e8068409181400f0f10380710040c44040c00843c05000c0340c0c2c10031029841d540c800d180c0320340350110926280d40c60448008958401504079412800401c0c0a0100380d03840002070001c12032080b0760003c5803484500460080700c03070a60780504039a110303a0214031404c050b510364405070302d80508619540212000410400c2c2d100c802c043c00140e000145810f602440b080c6101d4000c1c851030007900c8030354556114103204980c240540b105c2d005a94000c1140118100706080e41284101d0541d5105e1030141480442900400114008142500168586440007148050507168001d011030401d41c446990b00281e000d00512341414048100404135805141d45441407080e0310a4441500914191900610216050303204000310b920003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 886647041 1250 886645791 886645819
    0x4050901030b1f0303020706090902030f010b0f040e130b1b0702042a0804020a0b0c06130305160f022e030e0106050604090615090609150e0a09020307030506 69
    0x114401811a900103002c01016100c0c1e038039070900251080300440000301820400000c140e00810400119201500c81400306540c45002c10160700c1304a40d080d0b5100031043c01400741134a003034041c00c80e40c1d4600700c0d02030600781c0710500840c4054080d01e284100090310749180f0304000d40b404a1683c01200c1100c1007000d440200001f855a00515078020300c150f481e0309200c4028041a0b0103040101d107031107850051b0944254014140304404d441c1079000340c40114010488080500c121160048800e00402c040ea446020202c500600101d08a08000d010000f4004041c0d000069051641c050940001d040d0003e1042040c0d4514100740490301e80d15940c40c0c1104030700703619013400307000c1840d06001c0b07514110f00d801d0305d0040c8200d40255600040210300411030020301da004106582461484849030f0030340840c196201a4176202e50000200400028400c3c0088010445401241400c101c650202c1d00d00001d8298403aa40040008540c0841044903041e414080c003900540d00340d0f6161500460 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 886648291 1250 886647041 886647049
    0x30a0e0d02031611040903210c1b050109170301171c03020306030c0913020111010504021c0c0e01120b060d021e0a050301020703090f0608060307060f021e030406140405 74
    0x2d8590a0300f090f000146111040c04000120690781c0031008004111845240ca0050119990100c4e03402078a80244000c41e58042e00f441100c04900d102d880303c141d907006040303d003216060000b00c2124ad40d500c0c0d0722280005055105620300700c1403844012600c0c2c0d81000c00c3c4420b59400c1d108028841d9000314007640b880008084484400c2c0500e00c1c02590300c2e81e0700c0c4040ba26102500c1c4c40b554004088038104045d030090040c8080c11180701340d8910164807c1d9540301030030f071801510060f501c8000558a402152a00924000707464800c40082d0310460ba117000400d1800d400340d01c0320340c2d05606034401c4020070454804440c1d124000315901d18403681181c003c20b051482c030380b060b5500c800c40d01c3d03004107403569044625030003008014000d55942c0c1107031400510f440d4192103580d51424030244003085803806452001d01c078901c080c00030408140703001d504803203441c0803804840c1940241c2d1051120070f00c40704102c1c00c40d02c01d204000c42d5a5868084010011300c00100103640d400c0049c00148010742d1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 886649541 1250 886648291 886648297
    0x6130219230f090913050a0503030105041d0304050d0c0f08100c02010c1d030a0c030c0e011d0403030c1e031407030207030c0f03140d2a0f0c0c050301060803030a0e0d0203 75
    0x80e1844203145c2e8072903070301124070f07041c1c503101614a02c2019800c20403c8000001541a11410388040c00940b21145417001184084201e41a55800c00c0c40241311303a0410074101d14240c0c3c025200c1c00503541c1c2d00c5800700812003040e0080445600000000c0d0418a031038000c120018a061000300302070200e00c0402000d40000100d8100c1000064600190380c0e0f50800492001c1a0001c0142194990341e02e0240c00c4500710344517002d0400701c1840001000d03150058236404140d2507044e031808982d1256030071002412054540c0d42400410524240310b08070340c0340040003001450300d00007030b0310b00300c1c9964011842c80102507000300343c0104000d20000b6846181c061545038886105d0803018241d1400340e40d194020706080401000c0803941c1c086100494201100b01e00e500c00a107501d800380840e00340e4014010301d19500c0070442c0c860710105480e2055210b841d8980c001c03441d10a01d40e40761400a800c1d07c03450ba21400d070641c40401070040856140c4211405400300c00010034480c41c813041c0c003a440340 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 886650791 1250 886649541 886649557
    0xc020f12060403141b01060f05150a050d020f0c0109020a05090c0703050d14040c1403030301050a03020603070e03100b01030b0d030c031b020310050103031d0906130219230f 76
    0x4202c1090301030014a4510070f03620080708945c1009001c11806a0307071402001c00f4861026402040400003606042c40c0c0e1602c040c211160600c11307e0004a03210079143c035803280e0340e1410300d5582004401d005012102c0a400c46410000001c520405c02d401084081c42c034581016209007007400510100c502c00380201c81e00558541005515040346040e0742e0000e1505a00780c10134807003a54200801c01c28141d80c500150741c601c0040240502d504028965603020901410303401980100301880545000070207103610004034680a80b01c07101a03404682080f1481c09001507403034480c00f140b0701542c0c1500a80c00d1102013a00c00417050380090328002c01075100108042d0501030301200d401042c2c902c08845018464000d03040b0380c5059090880400140400d200550000d9800c1800d04184081d4000d4940d41351402020821543c5400b41000b050990501500981c141e08001c1c040030583c400c0e507101282246602c544070307074031217400080361906034018000743c82c1c910801512800600c20000d42d1128 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 886652041 1250 886650791 886650797
    0xb190b0a120e010908030609150901090f0f1d010605011706040c02150c13140d060f15080c04060518010620060a0c09090b030303130809060304030c020f12060403 71
    0x72512414203002801c1039071500e070180d402c080220f014018000029400b60340c2c25603010f1450768035400ba0203c541d410002882d4480849001001070380420b41000d103040381d00e2800007802d0340508200000322141445205000350740d02c000e020444000388a144000c1000b03003040012a490b031984a2149034000707241500c100d41d10b1442083c0203108201c0c3c0c51011003241004840350505240c0b41c6615000400c01003041082d0880108010b0880055132110f010003421080e030b498015507a420142400d425113488071340e1b452504500c03200019803864010b0441c44060304c2c0d41299501804196280c80e0080d40c05000300d4601c5002205500c00d0317003811900c0d075140552043c80002c80e15503e651882400e120a44600000d21001055540c400703007040a542c0c60714070300ca40d500d0b0703600c0058648194a15a16400c00d00004881c98a01d081d2906114480c06c00249007803075070750001c0c3d0703035410588040e00001c01003101c16045003000070203400c01050807168a0b19440300c0e2101c1f6659140018401030030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 886653291 1250 886652041 886652057
    0x30c09050402070f1520030406050105040c050d05040813090f0c0e1302090402040e04030f0201060501020d050f1e040b12100f050f0f0901061d090c0a23030a0b190b0a 73
    0x11808540c00249a111b590b40102d092080304443c501207600203a50a550091400000040c00d24151140420300403a58440c00c0c1800c3c01141020010000184182c481200400c1035001058582240b00041c0088042c0001d1821214040404076801c01d0032034028401d280425000c283d1f03075440401102a4521405aa41c2c400c1c10042806802180c1c400312413441800280000c15130004088020351210742d0082003459600e100490380d405090143e8004540d00b008407203010421030001b4101220250142400c01041e803100044551141d8007800901c0004551020b030404000211500700640d01081c5043c5d9080405050740039000d071054500c220030712061030803a602d41151001c4c48020050045401d9a911036007e82480c00b0b52950b030300d6000040c540303005e003440c14585082c05210b20000d8030b81070440062040d08c0e0440041030019861254400c1010911060702c001c5100d02405030001c00d6400414041c0030a11042680c40c5054500d2204140712035110503040e6001d440d2a40b0b403a0354 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 886654541 1250 886653291 886653323
    0x1060516060f020a03021206090103480f06030b0a0b030601020109020d061e02070b0402120f030316030b030f0c01080711010905010605210c0d060f0c030c09050402070f 74
    0x3001d100400c001c2c41800855100d4445030980c2c0904407603055140d8408107603441200f04100c940003400001c0c030812217500d4400b1824080301ca0000d01c1c4100c040b1440c100f454500301c8070300070302d00013003070342d4100d50060b1041c0700d8040c5081d904001402c90341024804081002c000952122003806040d40d6024003000042c6960704c01d41142201030780240013014003082504000000c5c0c004e0309003072403070034401ca03c0560486646100b00c03a0401d4021601444a4446508210b2007205404282c42c2038440d082d4019800c0310144011405052926000b02c1003c603000c2015050362800ba460b140b02c0d800103d00c20390f801002065180d02c1a90910b849103082c3d0341d00000340d40034400d10060503103a602e80101c4c0c81c104001540210162501106c3c44109482140718468025482880f9501281c002460401d8a070824007070700782c00144502d8020508005400010b8200c440c92084039001a4903554948440c54000b10401c01400058406500e06019a1074254039038070340040040c5a41d0243c580c400f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 886655791 1250 886654541 886654553
    0x10f020606011d04240803130b0c1e0a0201020c01211d01090f0c09060810090302030f070f1101030507050a051b060c180303070c05040b24040303120501060516 70
    0x1e01803450081080119040d031707a0590f0a40880065070104440040300c1c04034020a000096502029500904000450608940700c40c0e40c0c12480c9094a40c8c440e101400c032a846001c05415100d00b0084c00504c0140c1e02070000a151030300462545040c483c866826980e0300004480440301e0101d400c1c80407525000c4013000c402c1c8041403491840303955280c8203c41080040d90001540407501801112a581303894040e10760171a880761080e100c095203c070a0401c0003240c190012010603000b401520306000540f0700741c0c211a800184111000d44000c2224010000c1c00c01d0f01125402e0280780130815454040c001600902c00c04025005000c404a10340ba20115044101c0b40002c0160b02035076070a0030100079650040c1c003c51412600300310040d442c20035506002050303900c159080300442d10701034a88070034440140400e40c00240c0000c0c0c03000c00d9210f000300d40054140d948081c452915600e03491400e000300110760358a4007020f020b061100406c10f01d42d0002c01d4442481e00341c3c1052031040c24030b08c0c141c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 886657041 1250 886655791 886655837
    0x60f110c0d21240b0c0601081b0111010213030b070816021009020a0f08030903061608010311061207020c0102010c0c200a1a03040312150303030e0703050109110a05010f02060601 78
    0x1d00c403201c0800d1021540015007406000103c03461720440c1c90a9880c4e1805d1078403406001e200813581000000c030004558411584100750f2911680010b242c9194416070186d40e000582041c0c0320242ca2005105801c1e90000384144e000b0501e030f2213034904212003603000351988942d001060550b40c41e051250199510900c1440091404810784105650764441b40c0342c0740c2c0c20100300d040c880d019101c0007a5503413002084803c240985a80d414440c0d81c01c65940d15010007001a400360400302c14406e0410800070000d8440c0a649560020002190004002820368581010480c208054041d90b0030000300d0540905035490112400e4001a08035000400c0c0070030307200e90022081c100041c8481200b46200c2c40150300840c0240e40c1d55584c412101c141030f043e60851441404200498030041011078400e60288000f1400384058488584e03490701d40d54255055038030180c402c0c0088e004410418a00001007100901b1f017801c0810003005080ca000c0c0d00e8101c0200482c0c1031040211001034815000014 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 886658291 1250 886657041 886657091
    0x1090b15040e0303090f19030512151e03100e100b010e03070611070509071704050c0d0332030705130504110306030d031116060f110c0d21 61
    0x222600c80c40c222417102d0340d6240041844031640142100c000a400301a00740b80c0c0d440d60540c80d250315040602c031300c0d2011807030001c203072455035885d0b040c0c51065a901c0d94160b0b6401d4900d2003686d0380d818224403c06040101800742490868907040303407100021004030f030000d4401300c00180051181d00d2030005a56031544410481c0d4140203594020803075a810010304006400c84008649506440d10305206480a0036034001e00400c06e00903013401e803400c407846142c2e441413040040e11000e0032120041492503000032270841c041101c00700201d00e02d481c2c480150f0742401d1095004c210400d000514400c1a100c040c042504008000078250b0005d00254030100080070080c00c00c000300c03040c0b00c01c002410b41040d50800d109015006004000f6072080c06241c1380f02c0c3c03110131402e2030a580e542c00701da107185008400b16090341e1948030041c50303084940300b05021141a10303c03541d5107000310000c2d01e0400b0b00b101206014007034088011203424100840510f60018aa20006242d407000120700c0300e85240044 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 886659541 1250 886658291 886658293
    0xa091d040506010608160c08044a06040911030102031801051e0105011b08030f070f030903090b130305070605030403122003251e020f030a18120609031101090b15040e 73
    0x2041c000103202079082c1c04842460602003101c4ad8103600d030488040c50703001c1340c07881105a42c0407071150301e4641d100182007440b6008841078142c0c044042426030304201c80d01c0c00c00d40c80c0409810055807080c0145580301c4d00071070a098014400e00016061050306004131170402441c0b241e98500c1c10103102000d210171f5040101c0341d8480c6003c01030f80e140c840d81100d8540008814881e4240307014000d010b0107501e240c0c1929598607807400c280032421241c0200000c04241501108000007180003070202201510142c0d480d04d03541c1c41c040c2005130000b0380304882148203902d030051030050342c2185444401014542d010040c0c3d02d4841c0386070510968281410102000c1c1c4c5c0341480f81d0400d800a0780a04800c100d500c4c4040100c15020302a82c480c17000d498002d0b001d4008100701c0c45034a1055400c1800c0010500300e03109080d860701252000c000720b080040346c10030780d1074011009141e00034043c1520f45020700001d110460017561010850b9030054540140074031008201d09481d80c0f542c001c0c200000d4010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 886660791 1250 886659541 886659569
    0x30903040f0f06091707090b031002030906041703040305040b070201030209030f01050402040b030f0705040203180a08040303171909050c131e0209150a091d040506010608160c0804 79
    0x68203a02c1400c0c1a116980100d00c3ca9900014000324041c44c240c0c0248283d030103043c10314505906000075240020300070f9814029040d04409a00051015500400303030300c4010811442d0901e03040c031009000e1581e441c0d6022080c003c1000103a480400c550594406410170754584040f4801603020317000c1c10312100d5040c024002c000e80030b20b2056001d03910550003100c3c00c0c403d0354000c2083c0340d180c559801d4000785507045180d06001d0b80c1415002160041c0c4030080d4020f554a0303d04006044c076240c6a011034030420001004c00a05903c010000741c00d200340c0035120201d080003020f0100a1021310b40b00000640c454140340140b082c1800f10720040080a8184540300000840000040410458540c4403402e01c13912600400514801d80305000000351015066829a0030201400e40049544004014080d040860408050000c002c1c12407204c19244000e401c0030b183c0310741090070580204081181581c100800009515488004131404e82018035030180c050031310b0b0040c0d204a410007801400340f4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 886662041 1250 886660791 886660799
    0x60705030918131e0c090c030f02092b06050702070e0f011511010608060a06080f1902060d0608010c0f121b0c14030711030f0115050616051608010b0a0317030903040f 73
    0x242e04201e4007401f540e60b0070042c00c0e504079000c070101d0107281d100d80d40010500890b2903200d20551102d0160418000c40070072114220360314103068800841d0283c005070421401000340740c2099443c1a006510140114608d42c180741c00d003194031616003c40d0782042108100105610307829400315002d401700d60241c130780c2c5181112000c0098544e503c640c140c9441030000c0d108401c40c0c0400c0907100300300b03100d613080e0134810350760204104da822101d20040001e41d24140019009401d1051042101064a40304d07120004040081d180c0c90202041003c0d80d41080c840c1e016103030612600084121031414181c02d40442030a01840500000100c004540700006802c01031111510240c0b566190850031514005025250903003610f541c0f008040708004130380303800c0c4610318201010b0402d2283d03105900301c4060664039450301e4a0304100f20007403620302c400010b0103400428042d900d08110705941129840785199a9950340c5100145030303604030600400410007115050040328001c0040608203c48a911 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 886663291 1250 886662041 886662059
    0xb0a02120907060f0c110d031b1506090e070302100c240e030412080d0f051503010e010c05070f020a0509090d03291e060705030918131e0c 61
    0x1401000c0114078040c4113007020301c0c810700700e0120f10340c2d109141c4040080d4510038481242983c180440a00c209100120508036001c00700d02200790040034002e2155084075802801c4074003e4020b00901404c1800e1102410702c0080d00c0b00c110780e0b066600000089401c1c1d4200d400151990005011022980f03013400e0450018106403e031b021442d07400c20804201d411080d07030341e125a01c55004110003c0125402180d05038010300340c00d80e403220001c0380c11141030b107808085a200711b0b42600d0007422544e1a070300c20304003441900c0141448000810181c0d29044015100e401041c1005102e4903a0b04451400c54454078080380c003c110141c803020303480c103040c080c2c0c03500c5011240c1c0c0035001900e00b03603001110b01070484600308545010981001d150400a0907c601125001c850100103c01e02050000c140c507030400030403909014001843d00e6054403410050094000000b0780d55040b00b04051280c1406404000f803001640240082c12000040030410205840354001038044000100b0014010312 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 886664541 1250 886663291 886663303
    0x180905010e06040c14070215190f050306010909050c090a12050120040501180503030d020d0e1513030c020409060902030c010f0f11010f06090915180b0a021209 70
    0x281c0ca4400d88030755581c0d0511084a9400907140c0009503030000c80d0071001c4d08040101081c90014000003a0081e94030b00c440d595600500f081c0050781c0760110504205c550212004180e42598646985141024000200b1100045c0201080650360b1030100780c803801400100c4100344d0b8046d0188894640d12042001181c0c2880f10a88155003003003250b030f500340c2040540510502078000c01c9401d081c20308004480c1513400e59603401c04001d9804001c5196a010005898102810780c2c0c003590350012105690152030445101020a40c013030541000030a0310101d42c650b2050110009030340410b1a41000c81d252020210080d4000d458880b95a091100750b410060002d8000d03030885030368006100c01102d911240b4415a400140354400c01e000c482d10030900c141c07000400e10b0003c540d51010968813030403034506a00050000d80d444004208205140301c0d00b8602c2c00a07084200039201551001540c000e0241a00914158602001409000b0b075030341603900c01310702a50300c414145021002c1070b5650f4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 886665791 1250 886664541 886664549
    0xa0c050a050d140f0d0216021504061d0f0105090a03060c081509041212060b1216050403050a0b0a18061d0d0c0f020a0b030a05060108070e060304030f18090501 70
    0x1421201d008084000d10380840e07091110704e94209280480c0d01074040300a4111162a404098840c0b001c0009662419640d07a0b1580e5a07005490391030341342c10000b4104905045401600e4000c0c1d5580100395a602e105056500c0c2c020b081c2203585050440000b900c00d1200d8100030410b0740b9040390500c50700c0e4003400851007010328058100d9420301e81820045100c9048800410360085540072400740c501c2102c000c04190764080380429066201c400b8015190045846851004404010004407044190012100301e400c1d06106113080d096403203d43d00c50051150184c0490706a5001c03420500203a170100882c5084142c100551000c0d40c9003040207030060840f118040c6180b490004c01c11140030980c81402001e645441d01ca0758000e661391424070300c141000342c0c0d1100400034001a0010a00000c603c5103400150000c0c103464010009401003d01500200c100f014443c1054076585542080305d410135050f062048841000b4242190f041c00c01507100480030300e80e20b01c002401c00700c542100d07050b1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 886667041 1250 886665791 886665797
    0xa120c020f010c02030a14070f17071712030903040f08014505070b0304051e060720070b0c1f020c030f16080a09031103060906010b0a0c050a050d 64
    0x4810610011500030300400400ba6264001104040018401f40d0720b03c81d005a000060310398255455100c82005610b42e4408201e0b40302c0c07502490070402082c0803881c0a405009181e00c0b100700a52141d55881030300c00c0c4030030f040010010100f14840c004001b80d400400d00303020030030317200c545980c550760292035115002100d0040035901c50103002c8100b20f42a03a0703e58401171122120f0118404900342e10182a0140e40c61300901101061403c0070000a500ca240514010881041c03c41002b0022100706181f00015421481c10301030115840350070401d1500e088460980c107a66100e8103541008035580c845041c0810001e950103d02c1c401080a200b41c1071840100c4140081c0105204103901c611180b858468100300a5081600f05100141407052581c2c5110240d08905070754000042c2d015101c0d00001c100c01c05010010070900004543ca405800e0b805007080e42011100c20382d460406000d419042d40001c0744180d41e07103114080510780742e1b03084801c0751844050303800e14a845d071101c48607081c00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 886668291 1250 886667041 886667059
    0x103031d1011010c02010e0c010309020103061206060f09020405030a08210f070315080706031116230109030c1e051005070806010203040b0702010318060905070e070e210a120c02 78
    0x11490043c41005544400710008d410381c1401c68004400400e51900200e042c19690b00011a03410394041400d03960920030000042c0c8a82003407501d0f503c01000364001e51049004003c1400b0a403030100700443d140d07070700004072034a544140813180480405101d220b0f03604228141008a18010b6800450144881d80c40c10041c408004103044000348a0340200905c90344030060801c040341c400d51109180481c109200c03030601c40d0804281304040e00741501641c0c40300311407001348140e0341d0740c018403d00c51070044020404100e90b80c1d000f034404030410102410300101658105200031900b00f0401c4682e03840310558140e501014104030050074141e40060014040200280f40fa50000040300d050340c01c0c1c080c1050401c43d180e80118060070750300030482c5189032040d80140000705517010f2049030507c85ca000c0c1c2000d504202c8100d2035014014054400c0125602d07911503603454100030740c1e208a02d101d01440c0707e820454062490805040c8005103030144c1900440a0030742d02000c41140c5901c00c1f104030741 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 886669541 1250 886668291 886668311
    0x1308070f110301150b2109100b0d02130507020316051501060903170d0207210e0f0a050904080f0310030308010e04171804060b09130c080103031d101101 67
    0x4200c4212440e80b40e0103248281e828000f05d0300c0700019004031180800441114014a44102003a03c000e031411086540a00e658030440d080a0081500078001924040b4502c01503400281c0e8055030045100c103026543c402140e10a4400e104580c1e00417800c101503201183e180c82d000e0303681d000c007520300541c141111002040180c490414003084a40215501c3c00c1d09892002c03500e0030b40c0c4080301c031030030042e802c210b03a0340010342d01d1054800d140c00c3c54845595102001401070084c046d580e903103d102d5882c441006401d540c0f410403003010f279182030b02c647c40e855803240340c0030013507104481d0070040c1500b01200b0000215035406100003074921903603a0309180d90303035800c4c503d00919064038010f0100703a030f03141e04000c0f18100c20054a940c05508040020542c6d01380c01040c00c803002a000141808400148d41e01203041c180921464607049020400610310013813001070601c81d06010080030400e03550f11050b1031080c103944a04030240300402c030000b03001c07181201400361a40c08000d5101c5501341440f483c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 886670791 1250 886669541 886669543
    0x23060c07050c0a0b0703270b04241d03030409050f0712110304020f03030d05070504080c0f100813141014071d04060f120c0b07050a06051308070f1103 66
    0x24046454844e801c5080c031010340c0d001c4c0e610440000c0800103404924034500c505020241c8a8401480240d0000d50b986080490802e040c0c1150943c0d41260340401014035552648500c00301d1581075810f0220303200040d6000040c4c107520803940000081407c080900107488035010040c1d00518564403069191950034188800b56030015010a540b000c0a0001030054103206406155600c03000381540d1030300b80d0201d803c2c002c80d40d080e600b01c0001040030030184036201b41045180c200000c21142c80008800c0c40000130440c10740c1c2c0143c13804000d40c09000c5011440140300340148558040030754403105070b001c0381c61a40c80c05034601200c07505050a5a0902284034290214040c41e16550344049108604800c1c00080320300d241502d40060343c0d80340010b50b40d800f00c1d1888000c0c00c41115250504030302030520445c040304580210071401703000c0010b8400604000b4452206030f034010004500c03952442d000d401e0381f10b0360100251120400007010b60400c0036060000718801d100b440302c901c050022a0030700d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 886672041 1250 886670791 886670809
    0x2f120309030d08310b090709060b0705030d11070c03060207020406050a030f06050612010e0f0c010906090608130b160801090b010504060e13060608010e0108120723060c07050c 77
    0x15604000c40c51307409620360b071015034860104240e200d14150a603c60380d89449052804032580700f032641101d0f01c01d1101c94220701409000b405445202c5042000a45503592284108032130b0503100795681c10000d00100b110381c281d074071668109010611896403424540c021b0f505c1900100d10a07480c1c6840810203191003602102603c1d04905c1054680e03074141c0d141c00040c0806044a940070f118107051000b001006d01070100441702e240e01500b078100345900f52914100c0c002004078180129041c081c401c0f9503002c07082c00c007101c2c15880c050400e40c50395019102100c4020380040c1413000c038103003080719a4980101035180e48503da40c03546142c3e07030382d040c1880480f5641144c0500040b0100400c020061140d1042586140e00401e50440c2c002c11000031f00403141240c1c48500070410101c01008001c81030340d4030600400008002c0e003c034143d1113400704454800e04000030f2640802d40740c0c80c15000c194010207500442548200c03459428648221000c64219602c111641d1190020070800b90a000d005 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 886673291 1250 886672041 886672051
    0x50a1704030c0e2e090b0f010219032606031c0e21030d090b0a05090a0f051507091809202215050d2f120309030d08 51
    0xc8018590601e03080f840c40d20000f40004035142140d07242d260303580d09002d0180e540a000d03c0a020411031500e0300d1803040d2a8604d40452040f04980ba0720b034200d2343c0200e01400030100d141d446019007811480d007a03840b84040b56806910035900d2044500894031811080e0150700e003103045420031001101014004001c51100c1000079a0b5209032612500f000351040600307060090320304045c00780e4004002e10316040440788000300c039240d0b102c1c1424406640c01e8150082003548003030080345400b8070143d0703031203c002c0d20081c40154003440650900105000310503651010000d0f001c60b03400e201900900300d00150043e01c0d8000c10a0021041c004420712508541503440150000d4888041c2c018002000205144581041e0a1140c40030003281d50752615840d03504400380011075027000c03c00b15000302c0ea40d40045001d02c1540104c00003050780002010600154540d143c040d076148684625440044007840640104400258200d0107030044050321807030005404903400b0f00c0344d4001c102d43c0c030300059403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 886674541 1250 886673291 886673303
    0xa051303020a110d0618021c200d12030603050d050a09050609030a1202073002040c2604120503060a09020703030b06030a050a200f0903011404050a170403 68
    0x40c0010000d8143c2ca600d0b40b500000405280c1e0502c1d090302c42e10142c03180c050564540112103075000045150916003c0c98109840c0c40381145030045541d0b1030304400700e000c040c2e14030b002807810000c1c4a55680c200041195841031070540c5890101002802070651340c0000c4400d401046040e0341c503940724034251144407000396101d00003545040140b090700e07417000c83c0058041c014405004042200440700c5509c0310340d10340c018200b01e03280080807800703e0300000c003030503103001000c46442d159200481200700d0341760115400941c0c07800c001d20079078400c80010042c00c0298025a64800c02d00158501d44d1b225a01900c0c10301891005d208044031540300460b052584040108810702c2000c1495014101885c4241000581c2014500020304113400c12a0420401c1b03417184204580d40049015100b6148801c9030040d0485891031071890b203038020700400440c40900400c07421000e079001d4101d40240910300550002c40d0070305003403254484240910542d500e40600c102100c485a001c4100c50440750040307 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 886675791 1250 886674541 886674553
    0x90201031d1908120108100b060f0301093b150402101209080f041409060303040512030d0e0309181005060703031d07050a0503150f07020f150a05130302 67
    0x720b0591001211000d4846a03018403a035142d01070144242c6003c1c1441d40c00a01407804103101641c1603540c0c00310014011003050003039103150b1401c0340c2a681034401402020529a00201084201c40810039810300c5150003800e081419a12144807842041b1480b810f48400030840301443d40550b0055a00039044030044100c035003418440c02e8440300748070780c030034001c1103002280d25030212035004600e0b01c1d41005c00008080008c0080510040c800c440103894101003850725000198481c010b51042500505031940c0c2c483d0350700003d104880d2030b0210010b0070003241c030100880e9a686d80102020390302503400300c90318103000411311036a944100c1c1032030030051045003400c06200841c0c1024500320103054079109032203002e48009800d48100303408030006181940c504020400d00308156800030340640c1001d90920940304000102c980d10406042c072240c110349407080d00300c0c5004100020354030705000d004803000c561131181000034000c0c40c48000600658035034180e0002d412103d1040140542e10803 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 886677041 1250 886675791 886675813
    0x30603021e01021207050d1209051507180e060a0e16050a0e0405040506070206011508041101091a031006110a03030b0a0807080307060f090f03030f060b0706090201031d 74
    0x5101000041c00180b068038041c40e02081c1e1140b140c0c20000c0c04554a40020401001140e8440c908011000c10100c1c00c0c002a0059210103845c0c05008074050701c40c110a2000409a034002c81782408440d0070b025042c0f07902c1e40d03035004d144042202640c0c00f03841100c118600080d280c00000009000d12041c01c82102c002101c41d109070386503805900710806010843c2c0b0660400e07900c1d03200c2c861180b4001e1018143d07620701b01790000d00b0108160019420a5083c0100c82030041d40100181e920039803140c4061641403500c0016900c1e0708080d0301403104440804d24001250060030051409800c5ca0001082c400e5150601950b03150301000b21901759a00109011011034441d40014040310030103402c0d200225120010f09003070031000c2d04080ca240c1d00003c0d0035000c0000c1c900ca400c02141840504101c00006aa1001e02140c540200501050f0710340199101480c81c3d58403000040c01c11100c015511300c0c60f460004060031b0300a1090707000c80d02d4240000403a00e40b068510071000c019801a0038000c0c0c20b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 886678291 1250 886677041 886677079
    0xb040b0f09150703030207050c01050c1e0307060507020f0f01180618020a0b07230601180f0510050f090f0a0c030e010c02010204030b2d09030d06170d03060302 70
    0x10100c1056408035100700005040002c00c0e00038440d150007030390050b9544443c0d08065140100e12903203181000001c01665a000c20003042c0c3d210910b004400d81d80003401040746079861400b903464003810b845d00d8030041c030500c981c0001e15100d203c480c540980f003018040d82440307806c80302c401c000003035403400d0040c801000903005c0d4800c0140c80400d09844995254680101d081d8801603001030303450700000222441132002541d040d0501005015070458003810800360aa10b0345018441d082c1c040da403c50752080c0c0d6840c0c3d9040040042e506440410061400840d1070b109404a031190a00900000c02c4010140c1000c0c0600c52060380318680c1c500071510380c848804010250b441c050010140d40b5000d40403d201d0038041c3c15104440c1d50700250b203560542c207005011a001418104001c80620005c3c4008500c09004100d00b03804000e001040359100e58a8908511404000035070441c541034000c00e0707600c20300e1100c0c40c00e401d5a030222144290007180a80c02c941040c000a0b500c820403d00c10307904468 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 886679541 1250 886678291 886678297
    0x6090509070c0525050415092f090a080102280507151d1f090c03020d0311010e0a150f020f0c0303150f0f010e1c08030a060b040b0f 58
    0x81e40345070201400140d41ca8060620034814002c4014003ca040134800040c0d203020f0400143c58129001c018807880300399851a020068070070340c01841d445000c03c1da0360780400244140c00034000b0f00803150701a102100d50007140d0204400034491517111002240b030354014401c1c0c80a4051062200c18650040d145103401e06103e40d602703004100307040021000040c0110000100a040e1110116604400d07140c82d003a0100d00c14a0401241c0c403800f111801c000c0760340309681401a041d03c000801c800e6509103040d110b5041c3d04041c1d0802c2541ea2420201940182d030044150b034000000c11000d01c450351016142c03003550f030303010380300d42c0224035504810b841581c80322403250024a00180f901c299000303550401e0308590300e1982c490300044104140c43e2400e0742c4240c03a44508079804442c0728002d230001010480040750341c1d8108008110f00080c140c6907202008809060896840c542c20744510300031207e68002c60b0f2a038030311410204001010880c10080d1801e031215040c049d400c1224003642281160 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 886680791 1250 886679541 886679551
    0x1b03070f12060906060531230907200708070b0f09030601060f0906030924060504020c280f080f0f072a0b031311040c0c14030406090509 60
    0x10766079100000e284050f601c00e0070b008000341e0303c4084d142c1c41c80c170013502c1070001103816400350303458014602c2d41d514881a0081b030a6030701040d8410440c0d281c049110b84052000340b0003540222614050105545c1c02507000f41c001c07090283c000d5080c001410080c0c0d1250303603911a5040c0d0f60700c8014240f0001303200001401240380002801750404110f1000203150800070703807001021072001072048031886e40c880046000340c03589041c1405000055a541210440380440c103c050805044a018285185800c460002e0200603c199200d02c051a007190316822031032410305001000c0c4060b42e10741111100a060055004080214180000e44070b5040c50b60000e046100540c208020303010061140350090084140110300003850303100d8600580c54030244000b00940001a064002c0001940d02c1003141e40c0003610b15401c900080c2145054030424005a555943c490308041c54000c0c400e91024031240c2c80760003108407444140030482d02c0380c0c80e882540502d5000441c146401c0c0510b0800c002501d4100c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 886682041 1250 886680791 886680827
    0x2121f1809020915011e0507030c0203011820030f030316020f06011203030b01030b0a0302040b0d0f050a020405070f09050108070c230c1002030306040902041b081b03070f 75
    0x240794000781d081d2008980c0300d000c60000107130407140ca5a111110184003050203504203605008240003400310b0058800042c00c11000c140c00e442192006e411040b42e4002c0501c0704905229103241421401d03001c1c0d07008045185c9404000901440d00040d02200c0c070700300d00007440c0303141c0703841843c04081c068071100402540309440f0503900f681000c100050081c5070120310511881100c0ca402820303541c9c1c2e10000d604040c14840300000503a00e803028902101d40c11a800101d4030001400b00b00c400a100b50302414500718041c0f50b00a0160108641c803549108480030011079581d51f07419a1002e699000c20400103452a000388503650080c45c256810201d84e0400c80c02e0700007103655040d213122035403a5003640e000d0102c0704049590804c00c00e805421400720b40032801c14039000402541c07400010080b900c80c5031a40c8140c002c0d511550302c800e21000c01c0781c5c0c0001c0c03008008036000d030540c042900c81700381c2c104c1c0b00c01004104208440c20390b4025911580e0380486103a05c480d00701c41404001f5011140 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 886683291 1250 886682041 886682051
    0xa0e0c0f0c030c24160c060f09030302041a071509030903020d06020c071410050d0e031b070608040f06020a0e0907090501090e01080d1211040902121f18 67
    0x104507003040a40101a50310380148142201501201c0140401c116071441c41071040c3c050082090401402c41c09010340c81c1b07800000d00c241c40c01c058015100319030006039424030b008404014154550000c106940d44240082e004810004c0046001e101b420000b402140300e80452074101d03007c6170806440d440c000d15110a1407a140d80000d40070104680c0211803140d8001014005400144803034170003050f41166181c1c0800700c000105004881c0d07894103e040000002c0c50060b07409042c1d1044100400034400c1b030792503c4041c1658034bc540070003141480c440c800d80c18000340a0307110b00307841803160380c1c006840c0c8001d107103031354030030029406c083d00c1002031001c800008051a261911410321420a03580c03511401131a140016000d250355402c1003040000e102d006011702000003c000b83c0d01c51003480c4c15010010207054000051280c01440d803480c2000207400141c0149a4016100000c030a64842da10b607103511010314171402011400c514144042041006480d0303086d1400000310b640d204001c07075 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 886684541 1250 886683291 886683307
    0x9010e0708011208041a030a0f0c1d120703060507140c1209013f090b0121060e1c03021c0203073b09150d080d0e0604110a0e0c0f 57
    0xc090301003101000c100c2c1001c001c100a0410340d0185900d03501027401c041014140c0750b20300510311464604103484080e00200303800c1030784d16107035011445403584d482a640340903104e180c6080070300030075100c00d0002410f205050032030050380411641324034040030040c032203011621000b441c10303000201410706008109220581000603980340d050114805907004401c2e980a100c0c25203992580e07460048000d181520040005d8804511035054a02100394480e02d4074141140d0107240d100345000a2110341000400502d5042c002284c0e403180b4044080c040440381039020403001c03401807842c61507483c100b00903e41500e520f40c1d07004540180c520700d807190040d284203d001c2414054503103407aa020040020a203041041100148011042105c0802260915000b1015118024a07400c0d214007641034000041102d03204c01c42d6100c2c048201d050105400383c4035120317121402100d0035078085420010040d114500070f080401503850640319059652a40310078181c0641040d808012489002c004100c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 886685791 1250 886684541 886684559
    0x7020910170a0506100f0308030a0b0d0c0305010614011d0a1a030103050c01050c06012120030607051c050405030708040f18090c060e0103060e100509010e070801120804 74
    0x25462031984000d090748606031403d42e00e0068014400c80b0394034103e4000b88281110002003504580c0c00030b800a03104e49030b5110100c001c1c030244880310303031000308900368a0070401464140ca00b100d0180c2c008001c0103540310303d00320088070812900c0c0d0002e042c00c04510b07074a401c0c45442d582041c1025011108613601d8117044050680390030010103c411000c801003081000070007401541190a00c0c01506161852100940d03600c81802a080303005418441c3c0d9490141484002072055080002d217074010311050b810341412501c41300814040d008010014455078001c0c0102e84115490100c3c0c01105505640e604d802410007600c01c8806010810907c000b0a0f00c4030060009440780b801202e100320325080844205050f0141d00d0345040b41400c104402064000202d42c044038458240714400d4241c0b00012401400d4603000101090002414880d001d841c0e60381c1d1405075a8140d681101d180d0b264411481503c00c11601840040c5502006120700c503056864108090b2182100904054440c03a1903 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 886687041 1250 886685791 886685819
    0x3041a1810021c0e030726030109020301260705040b0f040e0d1d0306060103020703050d06080c040c0306290f1204120804050a0605100923180307020910 67
    0x41c600782600400d10211441841180b1800300101c0311082206a0880c850141c0fa80a4145c010307102d1905442880b0160b0203408002d044601d0894060f5034035a1075040d1603000390428040c5000c242003440701c03100a0500689a01e40f56113400000f44619440e013030401c00a0b20408261035001482c80002c4c5003c1c0c0c03914021060511035141c00341c10310804010b070003080039012600c0007188031900c0722a024281c90100e4065040796080c42c0c00b583e9103140d403c1c140c40d203104048071254454a84200020890408034200980c0403044505001e0310100345422401e0312000e0080a03081c001990040c0c00d81c060b040b5810000e041c100c0e04c41414210f0141e0100b00e40c0c0c20a01000c0c0d40030b182e21040001b0003016101d40403c848450901100c03e060640f00c46035140c0d02840001c20f00742c0c0e03580c04610802c04040910000713000e801400e0205044402d40001d50290148405207003250100c00300d09101c500d4070b41030603040720b170320019070801440b50200001270802502078845c1034040744021506070818900 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 886688291 1250 886687041 886687063
    0x6060c030d021206100c030f1d060c1023060603061804050f0d0525020a180213080102070b0a0906023c0a0207171009151103041a18 58
    0x502019203404c0c018091205030206002c0200201010100b0010b46c1041228040c1410351400e1a400958400c0c14460020000380d110fa01441c0419101c070000d50001c2c44048502c0160424030004050400780f1080300214032403420500240300c0000c0c0030382042e00c09103501c50380040c40442c0072302d05680c2042008409850659003a040b1001c81c0001200030845000c0d003500b54038005140410f1040b1742d12012220f00c0b00c6000c00c826280c0000150750b43ca61f01100035100000c0720381d009051060b0760400030b600025081249102ca01c40001d45036106100340c80d105074001e4031001580d40c1d507540e203070020841d000301140c100343c1c02d020f00c03011442d01164021115104d0314212140c05070008010340c081c89000b00c0581a140304200200c0c8981c1c0c0460380c941151081d1180e958000320700d0455900f07000b4210b400d11103445c50114400144221000340790749000d825801040315050704061404180702c01c907806003680c2c0310741e10000d40601e9010070741a0300c80c21251528910145802c0000d00b0828007502c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 886689541 1250 886688291 886688317
    0x2060f04062705010806011709031e04080d05071703010f17060105011d150a090626010e151302031617040f080409020a030c0e061206060c030d02 64
    0x1000d0141a40000014051206807164044200c07140c5000300d030b00c51014024181002a0100881d0700d5034001d050000d40c0c2c00a0210400991500c60041c5030b07260040104181d03017494043d01c440007211000200e0b0140c8400b02c0c00b51518203940e802c142d0b440ea2043d4400c41d04a101d416441200a042c24082c40c0a0301c00d042a4105191610610100201202003016169000200104500c0c0e8001000d0307200d0001c0d1460402144c820103001031103d07003100410301143d40f8001140411254000900c0c800c1d2030f200c1e101d0b8101c0344d8924484d03601034403401d414114655651801485000c10103c000781e8014014204d0b01d07070045198000c00c405008000300495426004410701080014003c216510380f2003a2034003203042d407100f01d0121740718540900082d02c490034039146d243c00d0100030717400c440140484000c29992088508001802001e00c01c02d0140040d040a200300502d1030440e040341c450345060305004803103488010807c4144d5001c0c0905011912080100d8401e01c8628000f030078458181c24 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 886690647 1106 886689541 886689547
    0x40b010c0c0807170a261b10050a0c0e120c1203270f120102130609080c100206041b0b03160e0603060d02010507080702060f 55
    0x5024110901e101408184104000b0300e000c21240b45405207500000142806511043d50f00c0b80207000301c202c48286544041145060968440c480c41e407a80760100c03107400070030303a000c89040580d4030350048914491a180d281c8580c40d0301c56011b48003402040c1d5002c1e0001c00100441410600ca58058000090480c0c3d003040203c6840e100901800c001080c10104907a0300d8103c0c2113200020307028405021010080c1c1d01d207112524070040c0001074079060b08820000d00c5c0b2074803480e0500c213640c2400f200000c1f800e510001c000409483d01c3e0340c41c0309400c160840b810081001d1005000c0c40108220041403a8005520396016400410118480d03210062920607281190b200940c40f11002c814003e42c071884100102c041c0c4801e8440044030300340700c41408002d000440e94150b002500030303e40c501650041d4001d0030610b104008943c58100c4030b50008450350044442d40752200004 = true := by decide +kernel

theorem cover : BRFrame.Cov 886510791 886690647 := by
  have h0 := BRFrame.cov_init 886510791
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886510791 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 886510791 ≤ n) (h2 : n < 886690647) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
