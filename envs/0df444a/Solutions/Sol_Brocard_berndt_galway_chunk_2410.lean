-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2410
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:38:11.082811+00:00
-- url     : https://prove2.me/submissions/98994f15-6bbd-4e58-b5cb-7ba5f1c6fecc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 433273381 ≤ n < 433453237 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 433274631 1250 433273381 433273387
    0x20703170409050a0e0f071202041a04020307111c080408030615040e01081c0503060d06180803060307080d080c0c100f1e06230402070b0c03070e0609090c 68
    0x80d444030090140b640001c0d0741c1400d100030405a252550410380c0f0701400e071000c440d035100001403240d0b103a9815024000e1400c290043d900c2c00352500b03130442403410300400175640a02d4a403502150503684210342000106186c0c6140c401c04100400c407820103046802400040442082001040703048080d0002e03151a0000c004a0440e980350f220460001e00580001544c3d21395034a109e00c103411f000d02c60700a4901582458a040b5145241c050440c20030550f10289565103032400c221500244041c01d5a1040d42c4240003001d01547d82080603016000b030956a449181081c200f40c41d01e10950400c3c3ea60741c20043c12035003695000916281c00107028403403da2a042d0b01d1010300c3c60a8400340460807a00e0412000751a004402c0c1e126001601140d1103503801085041990381c1030391090720640340c1025998040b070000c103050040300b616824005002502c2c000a0380c481011a041c01d9403000c1d03000000100740301e070b50f640003070342c03080c130358106442c90703810b0106000000e201040020481c1201034000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 433275881 1250 433274631 433274663
    0x40b090402071b03030c030206010504110d09050f0102130302120f06010312020a05070e011e0b030610050403050a2109080606060307020c030f030c1b03210f0316030f0c020703 77
    0xc1ca83c904800c214100c14580d580e040091010107040310a5026019042c004109802d2602400981c46099400c40b4902104204650011b05042105a9140c0141c890044400101380028070a0700d0070704270680f048908500400c20074142c00700c0c0000980d40603081688644002046860440f41c112801d8141507054600c182e05040c4803c3d0700410742c0c001c9510118035500002c6170306040c2c4030840f803080c48010300d0080d04803000400e0b020303c0c000410207100140340c620b030801200b0b220300840d1401900702513413551a2481c000c01000221200c01c400102130743d001400c40211041c81041d441d00720040b614100b07030103484001c060b1400707000301e5002000891060081004803d854006000c440001e010b061240c0c1d22034210b00d0301e0165034021650100020764284044e0910b502006010745140c0005010280b414444200520340c4000140a0806516150400f443c45062200801c110a020058008084407102180da50016280c000c1c1044165070000d403001c1503950000b1000c400030b05c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 433277131 1250 433275881 433275893
    0x605090d0803040c030b0a020a090b0f07051006060e0a0b07150605030f06060307050d1509170c0f060a0501140f12010f0926031504060f170d05040b09040207 69
    0x800c8001030182107001003404104800541c014007224052110352006031030342e05910007039104900c10300001030000b01c410b003c3c1c162440010840c601807000058500303202c0766112810020364803921581565291300800c010b5070403440300300c803146003203440071035907801c0412401070750040140c040c00402e00200000300b854900d40c04100500002400c480d11941c00113801a030301c48040300d8003070007800781440c001030303508203140c40120312503000d0740c080302600e155441d1030000c09101106503a03007d603030641c000c51002024001d0100e5114903000e89204034400803050300d020000b810301048035140900420050b810300030344e44043d5008482d5911030f9008103000443d030382c000000410040d4030305070020130a001913506c0355070980c0c400c40c203d0f40c1d2460080c41e04034a001e1002e114911741c2c801000007848485c01c2034161040a1801440050540d480b0f02c003010b000611500048404001c40240452100c0200885865080c031481d080d8540380c10b00d6003c080c94061030341d12500858022a0201c10400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 433278381 1250 433277131 433277149
    0x10c05180312070b06042018190e041a13030f0e030303010906090b030309010212070519060e011a130915020f0a080a09050a12020a020d05010f0c0302070507060509 72
    0x30b580c100541c549103107041107211410169011031185203040c0f1204800d02c01400c20b1619000c0082d0100d0803c203407221001e40d00f9541403040c0e648003005910070200304240c0d00054004e400a030a4003402451b00e4a401e0100a481c1c440096001e1601e00c08c0148040e4005480e2254581c140341800041c0700301482035407111a550f401c030364140808000400d485400342c0c001ca0803a64005020f20801c40e8203000d1523240d10544200c40d0060f081044e50034071800c10314004250292081c4112080c0c030010002c800c0700488400780c100c400945030104207018030424007400100a0007007419020500c010000600c4440c3c92421150803036031034a0005080c03002c01600c0100c0040c1d0f00b5403d5546440c40400912103500c0700c480d10340402c07039450205450352428410b0710071040d802801000070981c5911030102c0c7c02c2205000c0700c06c5118401c141801600c1d1807114210041c0305070300224070245501c10308410f07101151410000c00d4814803948000c60360010380001102d081e8101a40e40e00c60400108413100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 433279631 1250 433278381 433278403
    0x6091b130501080c040b01050f040e090a12020303040311061603050a11030a0b092206020702060c010213030c12080d0b06040b0712020712201c050f060702010c051803 73
    0x361515000154200011440c1302503084211020010715083d1070041d030b180d002d03803003428100080502085c0700002d452000b550700840013400301e03001508a030703440c82142c198a0450400503000031007840109600324007001c80540301c1c840a00128a04100350714882948110800d0825854502254110040b0350080100d041305141780e07540c900c0c2c088001000350031041d0196004128410009010141d492506254103114020003010075a070f540312030303029401002044c1ea100a041144403000c503000d01c020224480703e40c01468030b561075402c0100c12001c1507840034000740b00302500180040d0701c0100712102c040c9448000200b600c00c060108400c1d009582002c40d03030000c005a01c0d0140240e005241640136482e07803c5550494952090010706510030400400c0c00c0546102d9440e145040000607146000241c007000304841e0802d181031888500c440240d41e240c0189036054000d500c1401082da02c40114002403040d01403d00008185200d42c8040103080d18051310700140701e03502480280441 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 433280881 1250 433279631 433279669
    0xe0406060e0909010e120705011b0c020901060516032f0601030b012405030601140f090906060a0e150c060a0b1c0308010501050703180602010c020d0206091b 69
    0x10345400001d0506140d004009201d004201c000400da100140112074400701e142c000340051419421414107183c11a41007220595215007200d050b030451703da07a031100680556120880340407540180301000d441a000541000010008080081c400c5550380f02c0071641458542c00b413141d11590406040c407000c266250301d5002e00c0341c00000d00300c00280309042c1d0780290b01c0030007282d0380c80f20a18914691840215891a000d1300c003111400c1c02000995408081810a100c0310304240d906030788140d0001101d60803032180440c00809c50706103003000d00d6002d0019901180f17004005000075007100c041c81c1300c448c810f845c00d9001518031354542c0240e400101403402102c010341040546c80c0c5c040d09140724140d02a454040482c0a00041e00345c100c031415405403074002c0300ea4200401182c09500c001029000d0010203440b4100b405a0501c200009182c16070001481810340500203007440f041c90701c040210351081c000c1c091b89510110701203040c10300b06031081e6200486038012902400f48807000d1055 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 433282131 1250 433280881 433280891
    0x10b030601090c02060106080907060804061803020d03060518270d080402100e0a030305090307081902010905220203150d0b09060603030a0e0d0501060308040b0a080c03090303040308070e04 83
    0x9440043d041640360b40516000c0e504660f8a4540481e42c10310102c40c000d0440d807004100b04107050103040d809070868042e02010074421101240c208400040144c104d005a0120440c0d440d603c0d810710501e40500003c888902000801c03203a080c140700310191100c513060500101021074283d0840003400000c40100554101c00c5c02e14102034441c03a000c907000c1c0c1c01401c50501594080b48134a241c200d0000700185102600c60650301d044845800440780c0030341521968401280c0b001c403c005101d260624009070f400c220038244001001e1140c1603010034000c1c00c920300c41002c51142c0c0d002e900308a0300d48a00061f100e0359141e61501c0c1150a020302c0301e40007040504980c05004149260510480e01030040369840d448000501d6620711500141500045901440a24510305101043d40690061002090b00b0380c40c3c0d128003506a1066124041c88440040e031822940e4001c014642e2004412015a083d0f1818104403522848002d0000b401c03c800302002407000d9000b440b1180b508900a841088 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 433283381 1250 433282131 433282139
    0x120c0b070314060612040f0c2d06050906040603020a17180106060e06070209060f04020324030a080304030e0406030b1305010f090f1b23010e0102010605091305010b030601 75
    0x200034080000724460812541d0000380c10f80c1054812111608403010a03641e0381c1d82c45403641c4507203291210040340d0007040070070001b5a0040c8420380d0340b0f4040e0340c0326028810460180f40340301c80d40b40c5540020140070b8207000e40d043c650381e220245c804640356030a0141c1d0310034800a080351304138042a60541d20100450900180700110141170744c40c6400000200b04460b1180416617020351602c0030f40d54848420491a4010b05121129603000400036001c01005580f4400240990300102c0d001d00c00010070a40c03041140c0f4030246d070800c20050580c06014104126225003005100080001d014040088446071803522540c0c8000000c60308079a400041f810031030041200b0217400c2d0001c0e5119030030410f400030841e04038070030814102e0b0b1002c1c651030f41440c184c0c0c40e044030300480c071032031082040d40c654002440602640f181d04090903265040c0c202d442900000740540312040d46403411a03140900900c16500c54000058212040c2030031411810080d241c03007409880700030451505400340354000a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 433284631 1250 433283381 433283387
    0x31407080a0e0306100b160501090609031d0303070b06060714010219170109050c07050f15160e0103050c0d090503041d040506011202040902120f2404120c0b07 70
    0x10035441e074241d440c10003181a0703404255607810242c51607402d0040c0340b04100003503840000200510030103001c608254403a00d03280d00f821030f101c1c06001c0e1545911501000c003010351006040201a07c14001d00c84908210f60100b9528080d400000780100e10f060007143c029503c50003036400c0c02d40e0001c42c0c0c2d00d440c00c14001250203900001c8112030109200840340f40c07024003e03100d11100c001218200c1d44142c0c60801e08234003601000d005460021020040100812700502c980018002800f005040c0c0c51000e0342600c2d161903004103002101e40040c4071034000d8542c8141040840b520034038020a00c2c0d2100300010130584945403c0306052403030f2805881c1040b1010001c1d03c100d40d41001c01c03c0100907180303060710703c0d000107d400a0144d0003050061182846001d05000402e00140c000100480568007040c0001081041c1d030741103a11800c90320120352420009940c50040ca1091403d82d50401d813004422098094401400710111005c0c0201c041d10074490441119044140500d89007000400030f = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 433285881 1250 433284631 433284637
    0x41a04150c020120030a0612200103020c15100b1201170d0203120705040306020706020d051501020a02150c03030106090305010b0f010f03051306050a0f050115091203140708 76
    0x100c08041c00c0000e2805014010300c15043c1c4500703800754040201d01c2c4c540c0c10803c1988000c0c841c1100d180e64940104100e42da40e42c8015110340b00750076403000d1000c00b2541030740000c5400441410907004000f032203030300e0304082020500b00504645009003030300d40208045058413180c2090121036008900c03804a01100900981200d1800041186509020204640301e2a18619a030050b0f401040b0f008024080406016840309092038210708140c0c59030750b20700c160780c031560083d900c1540201e500c010038522132080c1c9130000244044030102d00304c0d01c2d00107500ca101004010307220300c0d1008030000159420504441c03140d5404d0050360742d48c0da11080040c14204882c00180c42c2c540c03034880a501c00f400c080a0290045034140c41d12200740c5040041240505402020340c07144868607107607400061a03a010b41ca0054645041c040f80d031081c0e103441c040884105034071240c0b000d4011400302541c0c0350000d41e000141d40000e480720003406401c2c1005c0d03500803002d540d03d4910200018068041c45154409 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 433287131 1250 433285881 433285913
    0x7050a1502040e090f0703080a020c040f09020f04140a0207031b0b040c0e0702121b06040804050f1c080f0403050a0c06030c0302030f0622110d0c081509041a04 70
    0xf8014154940b03041e081d0fa070b03000c540214810717644959402c0c004119110b0103480c070f00c03440c0c0c13049400300c1e40b5942c00701d02907a0350354000003200780e00c44442c8021464041c0c6109200f50064404210a60600841d40851800a00000b0482d580000d81b201854442d42505a1240c48844841101069881c2c208a1050101c40a8800a050300d1000c0b401e030030546156401101e09500904a0000b901c195020075480301150800c0140b00e00f440308200c160500129226a00034100c0f80e860718582800d001003800c01d400058854840827034a408100042c00000c4c2180703420080d00f40d11402844c0b80b40d14248900d800c040c0040c410030510400700310302c424002041c0d0303140e03036010b00180c00310650131740030303030005588030300101e4406030004129040103a001d4003c0d0000801c0c102010705503000b82412104401c40c003d845400000f24003880c48000d0140c6051000c081ca04003c107882e000c0840d903444c0b8445851184203009250206003804103800301c03001000c82039071151845080078030703000c2200c103000c0c1c407 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 433288381 1250 433287131 433287149
    0xe0f0a141c03080f060a05130e07090c230c06090f0c010801050f1315080102030105030c030705090a05091509030a02060610120f0f0509071d010f05040207050a150204 73
    0x20820071a1201e080e1103108181e4503840b2a030007074a910500840000c0014001030300542119800903180c1e645004005e0344295070706000864031901021175040031707041d806c080215410321544900f80d942c04001030302e000c540340c0c00085001c1342072195514a4031582a000d102c5114440c05d10a140b44041100500510540100d1b11540d20381c0e001510303041d009216040e441000c65080611500381441c040d13000110520001405580081b4000207441a82d0440e520aa50120041c4124102008421901d010403002821454648030010b5100c080090031812107540f1500802d480201c10000800c04c0c0d07201c4c6104070f41510f45070021035960307003051685000501c501d0011a0250811650032010030b01c4d2661800007820701409944041c258542200c205140d4a00c2043d403456420711485004030361041c0982407507454180541d4400380c200c441941c0da01000b000400422801d106c000d001c03548150f40140e110156070800a00342003003035201900403900840328042002e4181d0003081a01c00b041 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 433289631 1250 433288381 433288399
    0x31902070e0f070f120e0a03080105030a210203041211180601090902071b030f0510020f0301061b020307030b061305040f0204091b0603060905010e0601020d0e0f0a14 73
    0x80d1102089030640e100701c5a00c40036000310310500e2295140448920050410024400342c11051008071810044414441d41140720920308055218404a00401c000c8cc010984242c0d240c4440c400e2046840700d101408a80759140c4071260300074002c1d200103009840880810980c14284682c5c04210400300c00e00c0f5030703540d00500e06640c582241c80d40c003c001c1a525220814103103c0310200075070114006503000c01508904403075007000b00c004680554464041180c00110310f2508515016148904158040c010305c104c65a0340240c000b905c2c1118007610700b4140a2084144c610b100c0d03542607202a4142c020000088217004465240500940c01501c085035920100e00c02d000484070b00355001001d000d00303044000003610309030300700714001da0280d444a200c81369018801441d83d0603603446100400d4a5100030002101d651160300e004116501c03007000f003407401d140001e4403071281011440903c03082d002c1100807500c940c044d40e00d00d4030011781303200c0c0560345036010054600e54000141740305000003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 433290881 1250 433289631 433289639
    0x12301050103091a06010504230405160e010c14030d05150a0b0f030a0e0a0f061404050c01030e071505040e06010e180a0209090a0f06080d090605090a0803190207 71
    0x92140c0200203802050003e840400300344d0724550650040c204904009040c040803034002c500b440c80351880c15841d01c0c400460818001400182e0f540182491541070a035103103418159005601c081541801340703040e44002c080f92501002095176822030803624400861051021102c1e9071100c2d0044415111018405d02001c6c1005403421081c022800c5080090008107802c7c041c0700301554000d43c1424020510f2813421103068a09500300e5400d54841e03003c0034007101401140e02c560301044030b85520301c80b13042c41c080d1a016520b00e8038542250426680e06055035140c00280302e4000641500c07018009541d80100780208980c0042c001c5020541030100850440e6004d00001c0c2c54014010f4045208540c1d41a4040304a40006043d0b40c103a640803c000c2216554091002d4820a1061030024400842c807810f00d00b100d03c00c0d04045e0349030384010682c0400c0342d0041411070460361a460034958400152000c5a4107080f1540909141c0c03001184180c030807040400c02515240c01039003220400e80c0c0c0c07 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 433292131 1250 433290881 433290887
    0x20f0c060414030a120216050d0810050402120103030810030c060f021018020d050c0910090b030705060d0f0b10020a14010b06040b0f070c030803011401020c0a0905090f0123010501 79
    0x1084c0b15500428038060000702081e140e038001e403d8502080f0261044481a074540d5801d013080382c2d42c031000168404040007070348a038605101e00980002c2c2c4085042440b506030154540b80103001c00340a11a0080008080c88080f0500d40301555020605042081d583c0c0c3c409415600c12142420141c010f081c0d010032080e00612a00e13408a920a8480a03100004c1c2c003404404501d282c1c1c1980c05000e130106500c0b0340c0c0c88116450b4051150340118000d020310f4026004101c070100040c880c800c0d0000881001103646000680301d06160041c0001640b15038004800c009180c0580001c2d00704848040340e150131a0042000d4464901545419014581d0420601d080341c06541035207600035070031300040c0a146015800380c5145241c16448a00d001500d4070340c807800d4200c590044880b2440040140201128000c45011090003070005060400d0f03040b0004952016500031044003039901c000050786500100030101e1040d000300006c0010780811010a4031003a404015030326007800c14000010a544 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 433293381 1250 433292131 433292137
    0x50a200103151203120606021c08070c0b0c090d060b04060e0f0408180d0f0201020708070609030f081c06030209252001060914010603020310060e04020f0c06041403 72
    0xb41154a09003182d08002a280c00d40d5a80b0400340e0400c507245030709400900c2c580c81510060115a00202080910310180251280b42c100d80c079020054450244110701d50407074a40544190700c003243c2041961140c2074403c0601038110030661100d6600c65613002c2c441c0c90380c0300f80c0c0140c0b0103540511010b6251051694070b03860999032145164107100000300406e1140016000c49240d555440f00c0d1044194000f541c5003600740c2041d641130041c0d000200456070100030f11310040000070f029008542c0b13010405495034400f84405071203500c10580050400c406101161403440813102004006400036007200c00400300750004030b0090880343c010544090b41d000315400044082c050010f01803004940480728141007010710074500081c08400132680704280140c030f01502e184500001c28059a002420341c0200c181c2c0034900781803040041c40f502c100c07200401008c0c0e13680f906003009480c80e0580460000d02ca62240040c115201040140300150f011500c01e010324002d04544414000340e0083c0c907141c0c8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 433294631 1250 433293381 433293401
    0xf0411030403110705041409210901030b06120f19060b0702120106181410050d2a0e090c03010509030901031805010c02160b070201020c1309050a200103 67
    0x200600c00500001d100e98002c01c811250401620b0400c0d5940010a054172060034458040904203410080f00c4903041050300c28505040400c116503c0c494a1040c1c101d01c0707240c00c02c90401d510b03010a90101c3d11001304603004105e80c4030144102c1d1070074004032a0400390070342c2c0800c100b000c110720040c5014850b0080a040c0c900152503140703030800310350820094503107000500103907540315040002c00111088482401d2450311a0104442e100c000e02e0500d0000300604285010401410612107a25040e00880095070711940801307584c0729480010503c00400c143d05000d0710b0000d140440d014074040c6000d401a042a002c0b11320340b0070404205400e0b24030894400406030700500840440d0341c80790704411a005001000c491103020107488840c03c1d21185801c0002603802040b84864001091008100070904840b1b02414034240ba40000d4440f85081070192040c50715500c0079a8802017980a6000d01754007004031442d207640e43c60300e4601200100c58034404005c03a00704105407940a4081e0040d26 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 433295881 1250 433294631 433294661
    0x1409120d0c2f0d02131409070602060f04060e15040c0306180209040b0c09060708190507051527010c020c0a05031e010914070e0106090308090907120c0e0f04 69
    0x8200c0d442c040c0b041010558000341d030301050501c0c101490710308030b200d481491100d03e100000740b0714044006601c0c04103280d000f642150310003003c02070317040c0d1700040c955007242e8400e5020402c8030304584e003030b4a404107419141241c6a820400d0004001e08561100100c1f40701c1c02c1c0c00e2025003038115012600c101d80032000794000c4501c000140004002d01501540143d00b01c450500704558034011075400c2d00428011188d40c00d00183e400b40501c03001e0107100d00014585050340c5805400e5486c1c5407200082400c51110070301c5d94010031032070a607001380c4804000d0440359103580c1c1041c00d04200d001e840101c0c440c5001d801208202d00072810144c0c0c0d00d00903900040e00800c1c00d0b060440420f042c0b00308c45462441c90b9540c0c1c0c4800c1c0000f41c1c1c070074141c8203000a0741005150003410000c40c21400c00d410303448141400700c03024003000028003202c2035039901c000896003e41d4540c0d40079000d65040c1001080090f20070f04d086996680a5040000c00444040c00d94603141c00d03880001c144012a42999003071001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 433297131 1250 433295881 433295963
    0xe0a020d020a0b0f041d0403050f071a0903031b0f0418111209151303030b0111060a060602010e150115090e041a0a0c1409120d0c 57
    0x150800e4459000900d101412541205550b0702c07840303009800c800c0e0b00e5103200d18005801c10504501062209151441c003000c4120740c202075078045d01c030384510150b4007030646002c9121001c1c4526049014401ca01181132801e641c81c001049503200d9200300c1c0c101c10802c41c0764540c1031700b450152003501c03900e0300034100d6280341c20f080c4980d003c43c41c0351700301c0d902d00007544910012580030341c810090401d8058130b00b0031030720301d042104825003400c0c9106444405080010b0401031000c089601000303000f5098180003c0030004c21004a81200310b9038103415841c071615040c480b091025900500880b14503900810251034121005a1107907a92452150810b00c60001030004800c8048091078200c1e2a052054a456071400c1d4107044410444003503811304080e00e80258106982c5803007035400407c4041c00c002da0101c0d04405460990600340c00c401e01340000c607818016488480c46c0c8091800345400721202841481701c0200720705504a8100c5003071070000000c4280301c0120000318541604144d58002e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 433298381 1250 433297131 433297133
    0x50a0905100e1c020a02120a21030e010914010606050f0a0e060403142103090616110109050d0e01080705120606040b0c0c04060b0406090b030c0903160501120e0a 71
    0xc050072842c40d0020041c06000d10301441d1019101c3c5100520703001e9000340c0064196070040004604d00078000c071816400c05014000007907100131174442d200302c1c0100d818104441c0c8600440043c0640c4400030700c40d40c40e1880500901491504a80e1442c80920082c00b000c0e4503160115076500840180d02d00510041c07140b1850b06018100700806410060402401d0030b41d6034440b462400000302c840e441c1ca8001d81042415200940e01240a00105a9643d450741c1070007110f00e43e84520040c1801c079204001d80006040c01d10900605040310180f0000340411740355420225261080480220042030b022841400203502038101a4410b4000e5158141480010a007240c01c901d4020082130307014004020100302c0d4038405001d0081401004010404004c1d00001d0008888107900003c00006e070500081100560098020302903070004404182c6941700c1c50811469405190b40c05503150140d0003c88200c4400241820110740d0309a9501c8512412000d020b01200c0c54240c284000e40c20040c6850 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 433299631 1250 433298381 433298413
    0xd050c031606090203071d0105060406170403050904021215030f07150509130b01020111190c11180f060409030c02090601170702100f05070203030714120c0d050a0905 73
    0x4800d07a000c1d5902050040c907950000341040c0c1c1e01e400160103a004500d408000c1a4081039140c098a02034072460b14103400c21002500b44110030084402d0301405800040030544281d050711400f6801820543d242d4206004c550300720141101c081315082c0c120000302c80c240c41c00080b00c8a816036070303031701400045041114500e01052131681000910808000c0050507880e00032008070301402a0400040c0329581070002429541811411048405d05000d140713000d030994800d07041a684075041c80c074100215494040000c0036840031071980110342c02144440311801400086c420584070340c4050890740d03840200000c0322269080600041c600c08140b1005003040b94810390048014108202c4200050302c00c5495001e0031030b031160068100e2880e040501c54517001d0100e1003820070600340010b140c03030034000350b80340001028082000621601004c203503580740304890201c0380d9440d05103d545410022200998800008440802d1402000680403c43c911a41c03034002e51003405020310080050a074 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 433300881 1250 433299631 433299667
    0xe010b011e17040b1e070f0f020c1207050109090203040b0a24080d09060305010311010309021309060501061b0203071a161202070807060503010b071109180d050c03 72
    0x4001408404080320b031582d100b62545501c200c0c442c146840c041d25105c50700c14180d4071244900c03006003030000140540150040c0f0325480c001c04502e850104201c007104120b00d0030b403012880c640c03c017545601c41c0d070825902094440c181c03002030701c40e10542039403540a00103e00c41210040c4c940c401d903002040c81011180c00031902400c08a0704002e01c84071510041440403482c4d07021403002e070312100300e1924003504400f50100a10490408002c10762451300c4d0b5101010b21020602e04265403140303580f0071950f400d10070208191606030100203604d620710344100240000e000710800310303101503182030205c01d0041d50550385a902402038260580b13018000403810301d00460101d8451800e024030100003860090406c1d920380258580e42d100840d032074019041a03002d8102034225008240b0521120703800c501104e04441400388070316590130841c246100e502400103645548004100107116200c403100b1100c1000146020a072254980282d0301500d03684507028840715150000d00400c0b540c510b00e0506 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 433302131 1250 433300881 433300937
    0x405010c0c0302040e060f15010909051008070e070e150d0c090b0a0305010905060603070c03050715020f031009023103170c01060f18150503030d0f0e010b01 69
    0x200c001c000c0d84a40c0003038151900219988003e910100c200a64090910380303041d0072403142c48103502d403182d451000900100040c080c0b008800e40f210301240058a0206464004200810555070f0f0640c842200d000c60b203100303494140018110b00001c00c05864242c0001403800d400c10603503441d00c600c01c00030801030072a0764492000d001c070455001031403407260340061810051680d800602c1c0d40c10b100d0150116003025007124041c3c90140200801190070200303030721080e84c1504049031648505c3c83c0c92907100700300040e007036650b5001055134914200c4600286001e4000b200d00042c2454031542d02000300d02494000c5004c44580310f0112201075461115510141081080080c1e950b841740c0360302c0323035040080c14180303580c100000e0300791001c0c4001c3c0309807006002c03070803040f03101d07689403c215038000c6141607040c180c01eaa4465200070710b00d010210300001024098140d030341b00c2813074480078070003010301901c0e24550744d09007e6a442072000c1803080e82c510040507120003c0001090003000e0314810440782c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 433303381 1250 433302131 433302143
    0x301150309050f0c041103270c03030d0605031005150409060e011401230d0b07030912050408150124120f0501090c1d09060a03020a030c03061407050405010c 69
    0x7105002040d01070054294400100f00100740025203102480102e0310071200d45039103000c003441400f4003129a45079142d2151403c940038000d100300b00400508060884482d95030501c4000744a00071049030303400040c103c5404070250b4200318400c2050005a0f081201d5034140040e114000200728035055014119181c0200d400154071310340d04d14454211140c0041c80550003131884010410400c6810500c0d800300f40742c00c3d05959000c88035000c100b250501000c000c0140300080b000600c0244654044108903070000c0e17030800c81040981001d012940319005124560180361546020742c440c0ad01a43d040781c0207aa4003000040c103c2c21041900341002d0034080400030152070748600c01070030340261000b4403205a130029141d403402000d101110b60740d201c17510a1101c90000343c0381160618200d01c140d4101610410b2407551190f0000740d601c4281c3d00003d5100c4a01c40022080c8002c003144d210550b0305c15802005104094012854001d0040b03603180006102088140301c594441d140d2030380b00c5403041d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 433304631 1250 433303381 433303391
    0x906090709090c0e0d08041517060603151c03140a02060f070302070b01080c010e010e210304050a080109050c09010f1211060a03021e030c04090207020a03021002030a0f1403011503 79
    0x44c000070b441a082e020241c403010342c00301e020711250148e01103003d070810b4a810a00d54038000c6059500c2c09500080c46544143e60120000d0340750b00c03c002c48203e008800400d40e90000508031006041040c0746841680064035400765503600d50f807044100c643c04440390f002416942d0703c1702804142001c2c000c11010805400703214550003c2c98000400e030107072015030082c1012a20f940c0004041020401d080380c10800c0c45030b80c040140c1c071b0740c642400340c17603180d4481711003a082d00320440e40c07561003603500058000e071850360b0000d04508c041d44892074003031290090301c1002c3d200d501004200c81c1d0a02071003109124811040141a010044c0e0a0101d885142c060415008060014040760401080b10000c41c0c0c00181d580c02c440d15094991802c8003a1030115800c500f445403050506004900885103540e90014484007550b94605130003008545c000d2004804142101c1d00a4036504071392258004200404522202d80c1d025080800907030481135209802c503072074403080e810306042c1d0040d864107140e907070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 433305881 1250 433304631 433304657
    0x90606050c16080a08091801030b071707080606030901062106110705030f0a030905060c03040b09070605090f01050f070812163507091a0405102105040609020906090709090c 76
    0x307140030b64000c500a40303040340d8620781b00d5806001007011a248405408cc041c0070002c600e500000300341d0f0084000d8079810307141d0707440d2560a801404240c10203c20398006501e100d1744030b101082c5401e903140c07181c0c0050028a500740c864100700e004514004003150000e00000d00071516030030141a504045103004aa003085903207406007825016a1954141c40c40001004140162044055045001c01006003001d61418100800c14090030b18990711600080841c511103078400c42c19103c00c00018861140e446551349411841d50f80043d031f04603102a00c0c0c0d400103005440c2c2c0d01401d005408543c0311482503000084002100400340180d0390191944030a2002038501c52119a510400850b15450113150610903072521000c007418618964540c100030920044d241c9442b5020a40d15a051802402c0c4042000422000c40490482507851070001000705004032034010729815402600c031601c09440d030320140f00741c4a038206c13050404a2031289042245c00c1d40b80c3e00ca0171a260051411352145111 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 433307131 1250 433305881 433305919
    0x140c0606091b0307090504141315020f03010e09150c0304060b0a03060f1410030c0b0d06080f011b3e2d0a170d0204090606050c16080a0809 61
    0x1098039200c0015446105c113009504103071280540e1500c0700d6801419502d4401c40c110407800031207400170418000c6400340c500a845980684582d0400b9038102e40c0c03250b0310b42d24050103034841100c10040912400d808a4030724040045041c2c003484400240601c1c5070740d90f80311640600010b6040d66007040101a0003c0400c155125a01a44c425070201080b401a0b101440c0383c40c540c05800c01c04002c00d0030004200258420040314200e41d40b102c903803a1a8140c0140100050002c2e030b01200c014002c90130541c01d9801f042d4420001c014860300c9415807100703400400c460301806a1020b00c1141ca0031000038060b20310240b44034580211480203614640a4110340600b4070b00080f98088030108010000065000c121404007441039003080200366611207503c8175500310444c00900b8070b9000c0005142400c0b05403d0701210058030038060140710003540c6480c02002075100010460710303405003da910395410740480a14044a40e40c40007070001502a0b189d001e00e9901400b50554805060000050180703e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 433308381 1250 433307131 433307137
    0x605090a030b0c0901030e060108030702280b1914040b0d0b0319020a08030703050702012a0b01031208010302311d100207150515030f030a140c0606091b 67
    0x805403038070380d813201c1d0074000140c1601c61485820856800140040c8000e400000640e4889501250b11804100203902e00c40d440d40f44100205500d00030340c42010034850368075030003040c032280d400d04c8519406241e40800c80d40039204924828503110208400c1080c005c00c01d015001c500d007110400205440c0540020b40f41064000c58001c50060305001c2d036040d07150095200300200100380c095480c000141c0d400038036034401d5a000a0501c80680d1400d01c4c4080003071640c2d0074001d00c1c2c520717500c01d0038280e013442400c04400744421648046084825050f151142c00b401d41241d034058402e424101a601d214902000b01c02141c444180c02080301c5d4441c07401e00c1c00750142d0a808014888034110004540e98101034144100b601600d0040000d070b4009500c1d401c4042400c803200c03d0018981d15400b8456003441c10076400184e1610403444144038450001c4001c28090140791030340d0f8282c2944448e807181714013480605c002250400c10025005003010314049a0242c5030624500c403c03e0007812014241d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 433309631 1250 433308381 433308391
    0x150102011b02060a0b04061203080c070605012301020a050703081c0f020a0e030714100302070b0403320f16020303120405120403020f13020c0706020f15100605090a030b 74
    0x2034420b2051001c94100c620896003a880c0c103403000d209050600c011a8004103d08c04024104002400000c2c01d50440700246e40141d58801d030140210750395490707900c04072021413211030000380e54400c880ca40c542c000502c40c0f01d61940800980100ca145440d05c00094201000091614001030510500c400311485414200c0044610041c1c0300c0c4138a0100a01c03500302c84d082940258010b100038030030403100d9030209400d160210f600d6010305801c9002113000c1c2c000c032880241031608260a000405d904058500c0c086c0010000310526245000d1003600e00d040040302c0313405042010451242c5594042004102601302c4502074401c03040141d000c02d185a00c82042280b03c45209000d1000b005024000f50881c107412400603411f046c10360700000c0c0324490605021744100c2c140c12045c60140c01640584444040b09000d44e00056a01d82c000b0b903c8610120031029580a0008102c61100d0f080d96100d015003442261b80348181e0801005940d1540700b0f081c000cdc0e02c032512160020000302c142a0142c450 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 433310881 1250 433309631 433309633
    0xb0f130605040c0c0510050118020706060b0a031a040501260a0f030c110102060403090501051e041203080606030c0a111207060c030e1c26101a12150102011b02 70
    0x111016080503414070a50200c0c1810b41420a0010814000000e524030700c0709c0070b403c10044c2d660f00d440c50194001c064940c0010f03109400842c403200126015846661030541e241c40010404002c1c008000c2210000d02601e210910700036002c5040070800210015400402004c03128001c21300e0321440341600038250203d0025605000000401410000302206448280000c0159050541d0003515a20300750042c6070411902080b94500208502e6410145010203c00c055446d230716608040303c9045080001c0c2c02040180000c1141c0341012002c50b07110b6a0b6001d40242021070050742110410906002030102d88a18100d03034010515460040090740d1003840000f40c00f44081c640030381510004058240aa04403000e814000d0180c92810704c1604d5180c501b107081108100030030010f40d00c1d01580c800c46000c820080110f00c90001d41d80c4000e4400302c07101c1c084c2c442c03810f120701c40b03107481003068146010385610b000c101140428424800903810500010405040300c2d0000004413400c2a008801 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 433312131 1250 433310881 433310897
    0x110d020a091a0406110c040e031902070e01050904031403071e0206040b0c030a060819030e1c030305130204150e100602030f0a0c0507080615040b0f130605040c 70
    0x41600901c0c0c40d402800380700c02d00240620b0000725031849006620505041c0020080e0b60000c12005210291003540d006104000048c0c1486d007481d5039800000d549030044c0b0b00451070090b41800051a00200d50901d0281c0315a6801c00045c40300040d0082d00c22000e100c555269102d041d0702c0710001e588030b24265666002c00701c00d44090320a150108590000c19034100740d040c04045180d00407003581c0202c075800000ea49881d1240848001c0826a011981c0d500400070115103c48c92001c4255055000c1c0e030b5504d108070080c4081003c8800080d81d00c2d00e0040c280b0010f100001e02940007240d001c0c590380c201442c3c240e110380109040c0c41d460008040801d407111814032121039100301a41d0001242c60782000c0280c00c1000181d9a44510800802500004200c032410b951103010082c05055000341920011940d031011aa40d0720b0054035584c00d00c494001040601c2c0c1414424036039400710050400361140c409200b805021040b02c00c00c02c0c04a6180c500210346910380d80203002070f40030355a8807004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 433313381 1250 433312131 433312147
    0x403080c12040302090a0c0e0a0b030a06090c12111c0e010c0807050a0c080f04150210150303200f0a0302100902010e13020d050c042102030619110d02 66
    0x306003640410300401a503002e000030b001580f9506000b0340c0c000e64150000412904511701030307405025200f0251f034810100200480c09215041c0550300911400a09001d07082d141e010310420748071060040e0303000441c0105455000c100c2c0303400c550034280c1d568000d649404002186040180c41480c1c20480d650703121050711203485c3e001d10914600e80f296203001301c840e0400e0100180305100d0f000c6200108082c5040100078820104115181d08124890040e034969840003c0e440040da5840080054091007815216001d002c2c0540202107400002101010341541d030306850340902414000c0c81082e0074014550302c8001084840082c0165034001e0a1514082c0740003032a0021400e54056041c1c00d01a0203030051b604103c101d110b0410842e0078018001900189400078020011035500b0302c0e06007800d12480d4802d00000b03000303484490b00119851540c0c1c02a400403c0c15800000f5090742c0a203000079030990f08004202503080742c0500c0418102488030407141749410801154610b2540003541c12 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 433314631 1250 433313381 433313383
    0x6110606040c081305030c060901050103020a081c11030c0706020f1b0303180613060c0c0506030415110d0504061d0d12092d06060b131404020f0403080c 67
    0x1a600400454007400b1000012a00030300c0203070050f041a0000c00d20603110800c009050055411140d9603808460841ca0090443c0d80600700078401a80204007445c0b020541c00c00200b04100d401014819000c1c2d445c0590130211a014036281c1074815501080c00b4555a00109100090040095a0040c000e90310361410407403d0040e0369a40051280038072504020907103011003aa2640b03482031102901510101010a60900c03410f042d000401e0b0143c0000306515400480c04224980070b502d0303651b2002d4803013050221600c03041d42e001c0c00a0350885d5081007a0007a0341c1022002c20700f040089810101001d0807841a1201520211a982d4581c0312458603003411800c03050081c0c1300c4000404883d10a000d000e400070800041070070403c0c0c2c44012460038090032400b407203d210322080074800c181108000c401e00c041c050281c22106142000c000007010700184040d00c003140c062125121246113004624900b850010031150342040d02440000150b03200d500c080c0c00114000d12031103640d404030108031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 433315881 1250 433314631 433314643
    0x21b061b06190f1509020309210a09060e01021b0a050d080d180816080906030103030c03110706020c0d06060807060503100501020102030c03070c05010f0204181521030306050a0611 79
    0x7101242c43c00c1c140e10703004ca00c1c1e030702c450040380c26440c0010380c0d1783c460301402d60a0541d14280106440003a08001c17149400300801072103010001d98402a100c0d40300c0380111550500c281e002801a80100c00950a90720264006601680000c0101c0405a6034101040d285500104160b5014201103017002110342d16020344500e808241e400d4003007a6519942d020194000e03141d03821452a00742140004008072081294030303094000701925103030340e0749150041c500f0800d003404500086946103a00c40b000030000d201030544946402a112100342d000500003242c511900c00d032441c0761190000a22580d09001c03400203850541c3d10700d03070781e464032005049155956034007040c11a03104004120070b0001d11416260081034918185a0302c1085040150151000000290005100260010340894148401c1014000107482445060507a0040b0043c04003107101d82c6600760700c2090300740127148900c1c0c003906c034041c82420005a515181c0c80490340d21551500480d01145c500742840685001c10048 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 433317131 1250 433315881 433315901
    0xe0f120f0709150509010308030a020705010906050403030b0901030210030903020a020a03050c15030106021b01050903060f010911190503040804090510050a0929010c0f08041401021b061b0619 84
    0x40c440d0f0b00c1c9400081801e0410500c005000e8010200209000004603012269541e030480028804004c0c1400d00070020901a10120042494008002c03490305004000e103040302e03001000c0489500c0500000e50280c000c21008504501403000c1c5000166160040d01014501803401400541d4031603090081d070345480b04559000104c1030004100d810350000c1c5800c0200f460f10449298015100c0050310742d4000c8000c3c0c16410b014010402034600c40c00950315040701c1101c8424480e1420400315040644244a13500c91900301c50060300310b032207000d03400450b00144039407000762821341d6070441d44007122015140201d4a0719941003c1103a46010401c0d00054080e0007400c000d0000c11004112590320544400100d404450400d12511307030140b0003400e5807942105900c0c204005918103020a50301a000342c03e00e103008c0c5074203c01c09500c001001d41c230001200c030340340718219800e10801c0500d0b00302408900550400903d0701410050500c2101e006001c05999094480c118040700c0381520141c03d8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 433318381 1250 433317131 433317161
    0x5010b0c0d0e06040312270503030304020f0109120305030f061206061002120406030b042403060203040204110c0f0706031506081e01030f0302060114010e0f120f0709 73
    0x100c0303260000041840d1002100604200010181c01c60104500c3d004542c00a01900a09011032010300c0d004000310b4145100a503614020090071920488079030014003038140c041e8000d00000300141000000da580015050611326081c0c1e58590045150b0511a42c00b100001c20110610065007020202d0b650041d07000c4480c104038000800d042d5a036104024840d038480d02440e0006080c4a0080c4a455140805000300c0755540e5140c080c080c01604062500307a00480c50300c0384500010f0340006070100d40040c900712f84c103191403658031030303402031340000d007090740e100340d4804445c40310004070320042100500d05800340203000f88030030b03030641480c285900042c02c0c581090780310400c0c0c91400c0403001c1611000d0800780002c0d20385850b11004050407244200750b13a9607990020092003e03102e5081d003d01c0c4a5401c5427101c2ea02c1c0c601e00030540640d014402d0114070f11026401c0705182c038903c20300b084100500004d04070005104018038050000804144a4000301414005039190340161480c40252113 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 433319631 1250 433318381 433318387
    0x61a0c100615051b0102031003050c0604080303070807020c0a030b0612370b0411030d090f1404090209010b03060a06170c16080c031b0607170601030b0405010902090405010b 76
    0x1d101408165408116a0100500090240c40f0442c05020355138441402c131000715100c0c90800c000b4020b00000d40000c0d07400e8071440e400313680c6500e011001c980c15515078001035411510307042010b8a061802400c803c0541c05031003c545072603110281c81100650085461640c182400b0047c00706401d00404101d20a401164021801000e000c442d00c01003401900d0800d40e906404000c01c03000f4042480090035080707900244414413081c02178a4005e41340403025244060070a42c0140c1c0d02003050310842607520103800042001c0e070740d91818120402800b07403000c50031489550001d12100401d801130030364200b010003400100d04200c2190000742060b410201c40c13507030300d41e403460f4035030f40000340300344100743c2c0019030507032000c042c022040e034640e0b4801591398440740b125068584075013000c0c410103813056400141e400c1484001031020302411181c0c54081103446000d52406060310000c3c00e0505041d160003250306140c48a200c0d003402130140c254010389500256081106882060b88040101c1d103042c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 433320881 1250 433319631 433319639
    0x30a09031106040905090703032c0112020c030c060a0b0409020105090f0607021c0b0a1a04050709120f060506150d09020f0405070201020c0c0a1203080901061a0c1006 73
    0x1840840a60390080c103403010800840c00018a940714603040302004d54140014806210400240003059074840c3d00c43c0a01011010300400b07034020707a0070a820380141c14804401c450f500030510820f03180300f5030101524000200c0182841c41c0e01004904281d68000010004046400c0c41b56034484a0200c03403c0c02a13a000744c000030309034002c200d00d041c0315480c252404445a614482183e0455602500d104d0008c01d1040303103400c24821601c0287c812061000000780903600c02d00c150243e0b03103004224401060a418244001848000c11b03203000d00c1080c601c0455002d0104082d81d07040c0348912240c0c41a44964680304054400140285010740b5940304a0b06032056010196017800c2401c4200080382e0503a0300025500103001061181c1192521007440a025810b4000700b09506941088804051950041c006110075a100b1500412101154000000d20540d45943c020920200218180b5110320804039003003541070140074000320014040c0f00000007807200001788111000100602454 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 433322131 1250 433320881 433320887
    0x1d060603010e10021312050d080c070209011203030b0307152715021c0c05012306120a08040b0a080c0c07030b0402030a0c1806240c0203031207050307030e030a 70
    0x104641d00300d1030300400c01c40c00c0005d150444500038640800340d20b501c00414140507485140072100040091039200c001079085000c80111031141c1c0e806011103500d82c0c40c00019215400750200100c04140e00d94013400281da0f400c00c800c0700505103082c2e940000f8103030741c08041c2100741042d60003000168966641440e07400c811060908980c0040c1032452981c0d16440f040b030800011420488a8020424179070700042d6000e5045103e03944500020045080c0c00c1401e040a8450601e1400003024801d002446905013a481140390901200071501c3e8043c03950782e8110b094016800c529119400401c8524050b0360000300d6980041000c21140d203014000d0b805a91584060f01010b00207144010110707046480c10409000751070b8000304440c404680711929104042d50681c3c241814600b0400040342410341a4078004810030b002003103100480b1340700c80640d8042402a42a641800305100c1c5101000f43c500c00d00f80f1540e901d6580955134a07244601a0440302d469000c031115038000e009844070590 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 433323381 1250 433322131 433322143
    0x705040e24060d06060b04030201170906010303030f092306060d150515060309010605100905012c1807030c0c200a1d04021e21010f1d060603010e 64
    0x81c80035071030a0381d55540c0040740a01074212001042e103480d258001400d08402c03000351060b06e1003640c07410103a00e1600c0074200c007440d01340c410041a401101c010000207010354480c0910782440700010420ba00b441e218001050350760381d400484881c02000002e183c1e1010300c07185903c12011100c00b4007c2c069501d541c1c405a41040d1200850707655400800c00c614005a031143c40d0801c0100f5940d07980c034090f10b903180038100d1480764602034005401e50305441030065207120156841030b940c000c2c1041e44a902c0317050258520b4170703c1d019a89103070303101c1d8a5034541c1000b8190411507a02c80070031070f05204000a0466400142403020800020340481c00141443c8c0e20040e1500200c5001103851603480014542904c43d5001200c07d130030000c110a6041c01250200d0b1185008aa9280c0313a0700d00281c410113100c84240d070607680248110415250206004203421084c2a80c1e4000550b41125a41000c00c58410503d61007040c0f0444030b001624800070000d01d0361042041d8004c1c42200c4450344181e41c0e8007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 433324631 1250 433323381 433323433
    0x30f0705090604090c0c03020d0318150b03010c091a090f0f01111c0801050a030c0e070302090d0605060319080306150c070902090112090809010c1a0106020705040e 72
    0x403000250748803203036076030301d00f0f0741c0107090314010801c11442e2100d00500446078281040b009406008080340c5054060311400c07030800410700c0e28290320345140d074407800240c2d9181d8911081507964284008140ca091240e4900d2183e591101e555460520700b5981d803020101500c0c00880b07501700402d220503200c01034101162070703003a00c00c0103540003e0300040c0c400001203040c03202c0511600c44044064810f0321288003a0503407079207544031266221400d01c10f500d000c5010180480e4160941048030104949545034011600c0c03800505002442d00062010385c40308000752034040e110014801e041c40c061241c0001941341240101070342000385d07680150782c04000c01041c459a2284003c0c0a4410802c084079042001107095452007500c1e03100e5000250050841240060014030160001c0d901d5882547d4065070031409003800c00100b103004445012003098100c03040703048500075401c0b403040b00912501801c2070350083c04800c0c0c02e00382480100c801602d0610220386c0440c8c10300030b1000f40c20400396085 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 433325881 1250 433324631 433324637
    0x110f010c1e1b11040c020309040c030e0a23010e0304030605010504090c140d170a020706090315050601090503030a0201060e06010302090904230d09060206010504021c051807141203030f07 82
    0x842c2d1075003000450800c102100369003090a10704400c0c1d2850b4044000c0621000132030b07080099030200042201266800481800c09a225110360004101034541c44191040c0840803202d4000c001c0c0211825111018a056001c0d40086030503c100940c80c0216070241030165002c010f00d03400c0340c40b82e0492030701a00c80e07444180081c4090601341c1d19080c003412082a00420062100380080804c0f0b0704543c4900ca4040040c001c0c09800b051140c41040c00504503a0803400d80400c09404403909001440d02400250620220000020349500c0900182440b40300c16000080c1d080e2034040c1000c0c8031400180110304040c810016810140d988a115642040c0c100520001c0001400281c4c04030407003641201c03180d44a124201e41c10700360300203240d00c169440c82d400d41d41c5590742c400600040e4080c50f8414008020942a540464404e03036218991000c07001403040a03c0e40b01c001d142c4e00b40121038112182200c044034419400d41424400d8907a60303080b102c002e44ca03615100c03070341d10712140c0c010f4150420 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 433327131 1250 433325881 433325927
    0x6030307020103111e04090e120f0313230c0111100b0a0e010f03290103031d0604080114011502070b0307260604050711071401110f010c1e 61
    0x20409002043d50b003800140c5c402a20000101c650112003600940b041c0b1103454100075045200400120f004044280c000d06014100f281440011115810050410150940121942000c07030303c40c01030101c40c6082c4201440304100310440c0903081c0314a010845041c0882e40790100c2c1250720014401d00980d400b00c01c0042c1d0b10b40318000080462185038415404107402e4000494074004641010049a00c54004642224001000000140d00300b000c1c004900a05000400101f80a0a401c4a203540c1e600e1900c2149040c0c000012a20740180d003107500142c0d50340c0c00e042100030360040b0107400b4000c3d80c504a50b03103484080000356101040e0248841035080130000c40d940c00e00400c280c10540300c40380440d11301d40441a004001c00281110514071450070300002c186220b0291040412401a68028003c584e0402048440c40007900042a0412a10040440c5561740901c081d515082081c400400c0c200c4602078010a05104034030550800c18640c2000d038056500100700b040500c111460b0191 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 433328381 1250 433327131 433327151
    0x303020405060304140615220f050a0605040605061c020901020f0118120e10140c06100501021c05270409120810060804060506190602150f06030307020103 68
    0x10190159078001074000101105110410012004281a41c0541030494a8035541c000151014802024403103401001500038121026400900310f4114840080040341d10140c0c07000c0f280885900310740d0340c2407040d07403010300348401d00d0300f4001c020040001b114883c0c10800003c00c010708240f901c01000b2456a400031351000640d0080c0306005a096041c0d000b04156081007000c170f0194643c0c0303482242c0c0740258000d94400c00c1e019003c040351518000d04200c08440029005942d04000c03420410071691040c803140e546528208000e030300c1410744503a2116014134000000e07107403401114000c040b48000c0002208580d50200903600010b40c4100c01c401d4420000e000094400750015105070804e080c03070402c9050105400c031200b2014265070741d1100d40d5640102c090110030b0305028940000e513145c00407501050303241c0c20240e04100024852100c04210700b03e14103844a1950010002d80c1151407048111480b580c8065404840c3c01034011540c5440d000081d141d01c20803500a0602d40d075864241 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 433329631 1250 433328381 433328387
    0x20915070204090f03090602070608010303051605071205030414060304200f180f0c16033606110106030b0f1008100915090c0b0c0c040c110c090f1303 66
    0x9208603402c8810141ca00c080c4d414020042d400300d00030003001d440745410010b000f51290404504903501076440c14200b0141a164000480500905540d0345c452000e000c40c580903104070354407100d442880110f60743c500d0320400400c4100d148081d24410314081c0104004100c442d4540e002d540d01d0950001f800d0380c07074100001ca0158280c415030307400066124928681c400d006810318000c00c08110280a25030711420080c8191090241c407000003210074040da0b001900450300d0340c1d1454101203a480000d84211120340e40c40c001018003005980041c0420040319800140325140174000c2c2009100752403c684600c07101101c0079201401c585904000180e007150030306103a4000d00200310070b03100309902200b10308000e0a20002c060718066420800008544954491842c000d580300c03500a600c2c514011020045400500305140c980c090b03410000065a80c41c8a024500c0c0401e40380d13128a40d1242804507c5d22004d140024002c3c02244217202840e200300302420341c0700b1100c051003160550030f0f10f012 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 433330881 1250 433329631 433329641
    0x9060904080421060f050702011406101419030203010513061a0a020a060903080610080411060a11031215090402010e0402210124140403031b080a0e100201020915070204 74
    0x140403286400385da00c2d500743c0c4981166024100940c000d025200540090b01081401502e24aa0100d80007600c1f00810b40140748107402a07102030442c1d0b040610f03401d40315090f280d54441d130000082e40040140207501d040700c44807400c0d1488540400102c0e00f4060000f41d14101000490100f08010a11000c0300c3d00c00c0006007001a80984248144456440c000d8040e040990709a84940700150f10380da40c0c11f00c2401007520940e00314070b501c11003040306400c0c08410b90005452404015024000605444041004020120488007039007120710b820201c03030856901c21203841d8801d41c00a001c0c080981c2e80b2140e610342c404821540160f8600008040c441c0e01c0784081c0c4002c0e45584014000034210f60b00303c0b400a01842c841d41414010f90100d0821500418904444d0540040078441800803134441c208410319984141c03d007005400c3c0c3c50f1124042500640f44d41c00008050030b4010800707080031650040c1a00050000f0b43c00e040d110400141c0e00c05024494045181707012410909542e225004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 433332131 1250 433330881 433330883
    0x708120c030423120f0706030b01270f03030f1d0906040b0a0f030f1203180311070b19020f0303070e01111504030507060501050904030903060f0b0a120209060904080421 74
    0x6001030444910041515503030781c410a416107005003440056010b00070b000308900000140c0d1481c40741212140c00515030b0071000000d2f034144451040100d00d1a803000c102c1005580283c542c0d012012040e03000a1141c2c0c01c6114814920b4251542c01103d80c44a401007a0800412603005ca01c1c07403004000f2401045072075020781706001c0361000000034410b90380c100064950051500c525440b1171410150251003068041484401c801183c2d400800d210364091002690710000f594611559040c884c2200c0d0002584078040036403000000b000780c1d07010420700e401e69500001942c00c42c541000003400c400800141c050501c903c0c603400c440440801c2c001018880c840701883c20150410342001061500b00110864905160400110b034914100103030510480e803550328a5442800d55544102400580d442d8102c510b4440b44441010390311605003101a0080640001d13482c042401003210b28803000d0a940d00616084080c00041b411402c215400c1c0d5580d010407000c0c5084401c8900d841c1c044078a4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 433333381 1250 433332131 433332139
    0x5040e0f090f190308011a1c09061505210c190b030721050609040305070302160b0a0932061e030a050105090601080601180b0c0708120c030423 63
    0x80b02140f8210300c680903801e402903070750000907030f01c4d1511956240a480c0d00301102c03c606003c0400c0900012a001e5400c404076040842d8248142d51107009803000348a0030358039290030390f0040c8010b0600c0c03002c0c001181e101030301c4a58412881c444581e155500d1000d41c030f00540c0f03c0018548000b400306001c0c0c0041ca80c8601c0981d692a141800808a4500c030141c4500c41202024646803511304d809202e01a03c002000b4034031940b919a4141e520740d0040c4021000d5000707110303030b0f4540e01601c018400b00412001c0701c1d0031b607104076440c0001d1105100740c0000c1065111600140317014400044211651040d580001845241110000f01140160b8100080340e0510311080000422100040c0d4020381d00b2030400c0c8826600ca008003d071402e41125840e000944520016995611500c0419504a000040a907840d52152003000007540000d42c44400d03540005002c2008600c00c001c3d1074881d00100c0011030a0a120200d01034a80c4030344d1164540da0a01c03120300c458154454107107080c00c0b0b54010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 433334631 1250 433333381 433333393
    0x10080705071a07020105060a36051302030d0203070c0e0c0f130918030203030f180a050f0705030d05030a022101120c0e06010c1b270c05040e0f090f 65
    0x3029030b41c100e00d02102c1200044d42080081080ea0030403600c10815140398160b1002480d201c0001c0310b1443c901c601c0c034882c00c0b4822254103e40ca26403885064003c00000708540c5404a15005152504803040100000c41d070040242c40040b0f84580d4000301910f0000c1014522511841110311a500980010f030b00c3d854400035665689180c5045000112001034100303002d01012034000400a81c0b006002034056001000020691180c2e241c031150301c4540e400b142080303006041c0c0e0076460440348260444540d40308400000c520130040000000900040b0010b200b6441d603088c008019000142200708016004185888030b01104c200c2c0c0e007034400002c4a008041e40c1d5403409010329a0081c101540c6c11060a00c0208038514983c0d00c1910498041e180d8288404081e6680204000400c00510030040c1c00c640100c0c3c0c40701440d440415486005218521610030814188102e451684c100c10034000d003044100442082a581958050548a0380c14141d80d43d413007800c0d09000312440c440c2e12600a01c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 433335881 1250 433334631 433334663
    0xf191e14072901050103090b07050309010e060109060303080a180803040f0b13142a06130603051f0303170405010b032a0a05031009030c150501061b021008070507 71
    0x480070803140b0070b410080c000001e90b82c0d1030040d4110f901090380a050309006e000020200d034001c0c0c00468000442600009608c80211500740c00d0500030f0300690741058544404005056010055540142c9414410020010841c050b8001a030b1240402400000040001001c0c0320000400e4403006030018446852031906907034500803103000c20b004866440c1401040401c40c00001034411030310080b07182c1045802c1403a1043c0c1c5040d042c0d01d0300154002800c00a00014407803101c180d100030429a1008201801e18140c400b101035640550b50034032001604003000440d41c1304007900d54040e02d92110340c5142d2290709105000d007122202040e0140b00368020202c0d030211000040c8040d0407203151610003080c09104110544d2000d1203907a5050340a09100c1c48000c00c107030700140c1d04a09c80e0905011400082c0d961038038025400500b01980f59481c0010400305402c81000e8107140c1c0300030070b5280c092046600046408490761065820840030100081c0914040c00c01c0b1443d150700540404900145 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 433337131 1250 433335881 433335923
    0x51b01060611060714030613061509151209140118020f1203030a020a030605030a050d030c05070f06090c170601090e031905130306020f191e1407 64
    0x20501c1460000340010005188000c004184107010704140c0e039851100c400500001e020304d80024101c250b00189941202d101b41040748114070003003d0200311440d013080e01d40c13000740c80000c8a500c41199910521809148503030311040b0b5910804c01c181001540d04a170f03042070f080c0c000283c0c084502541c40c2035070b40302060f0910b405840c4038500c01c86400c4119036070300c42401040040350360107200315401403003c5401c1040d69005402240903500d0000340f6603650b400001c0c900301214405560a401c14445950350941c14050399030750b20250b00707089291001e2030703482d65045890410040c11f190350700c0c0c19200410001c80d20384401000a0280c440c0c804155081a03500d6101c28403d0550a40c034040b9038800c442c0002c000d40e02c401a0010204080e04020f01c402d031011b038400201486581001c13000840012624409454070400f1054060340710034003c203039039269008002c1018140600e62200150b03486107a80c9042d401681441c1c913284c00b022080b180b04850041400c02442404c981c04110441c0030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 433338381 1250 433337131 433337141
    0xf072001021308010b0f04020903010e07181407090504090c0305011d0105060d02090402060c1207030c300e131113060c080304020d02030a0506240609030a0b07051b01 73
    0x51000c1080821503a403d402404c841000718019003000101102d0000d030300c2c055001c2e080030b100240010482286402c0f10606210158104440420151890410b410107501c02d02044000c8480c40c0000c5017803540000c0c245035280d21035240300303a88903044103040005405182c7e0041d50700400a1080d04c030b10581d007176500d6030301360702c244031300c0d03113880000389042c80d10784290395880d03030007030310380940c0f80c44940034000c141e4850307000b0b200c941c82559119840049544000d00c0000e02a5480051310155442c041260600a9504888041c00c441c5034a20a60340d40500254509540c203140b103802c1d003444049445650b10045006010340740000016209050500a00d69513000c41c3c644210701d600d61070159030740c10300c120018101c2d010034400100182040105010381c0c3e0300080449100780b5032a5640c82c9030420803529603e2200d1b48180040500e10417140e8918a01e10468186081207444408680e6410b844140a4005442c09010802c203600540844188030900030f52500c05196080259010344 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 433339631 1250 433338381 433338397
    0x12070603020c0c180a1808031f06020c0a0905070e040e010c030b1c12050702030a060b0a171b011112221206050c0d060306090507050108040b0f07200102 67
    0x20040603000b00462820342d00000403000304000040103600d45e0003104008020b12606c08002c0d004044400300800d0140340514403440c040400e8142819140b0202c01d600d040b039502000946d80903d01500c160b5580c00c191506603203280c2c42c00036040e0303200303402116406c407030301e4030150810300e004549080d1001c19080500c01040030344043c170800d0042c006001c2030758000c402c241200e501004690001400ca80000e00040c01c4038601542080e82030b0b000203080042007501100d00540d51303130f415545070a000ca0313404014942da079120588501000d120584403a9a042c00741002c100b100080141680150000004408483c04964030381800e0034006a1079440b48400c0030751134a1003042d05826050100012059400f40d900201406840d0f9451001030316001d071a800c01c694003840f000003120b42c00d22501e001107008070004240d01d16039080607400c10010b904158100b0180c90100300c045241e140c0c0054000d031600001f83c05c1e0b83c0d210700341121a40c0b03d21355503403803454800d44810f840b0001500a40904 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 433340881 1250 433339631 433339633
    0x40f021f1e0e010503040602070f06050106030b04111e0702310b06030c0706150902030c07031b02031504030215010b09010f020a0308130c08061e0703020301050109050d0212070603020c 81
    0x6540c021400d442481d15000b89034002202000040c0000f9666005010342610814900e5030401c40c03a0f5520056450903040000007903a1a440010b5500d0f203400748601c19203242184504d040c0c4952010f00b0265016001c150300078900103591403c64489010321000c1140940c115001200880041d00806a00ba1170420a0500f00100746111307203800d1f41242d025515a01d50149090b003195200d0000d0000c1070481c1000140c0c02d01c0014008110740002c521400c000c40810707a841c1d00c01d10b000f9007501071b04958030800c488141d51000058030001001000c0f4a0314610b040d4040c1d485141c100d10382220700c0611482480d20000002e41040b04134041e014084c42621134060402608104980e01c40d4420b02c0a000142c030600422409581c040e01807100e00d003d044880c0d869500c2e110403503d00101a215400140740038100e040705201e160301215041903423413500b0b519551500b40000c000b0603150003001d01c918440030440f42155528480c404000c07039075100f81d440f890741c1d81101030029000181980c43d2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 433342131 1250 433340881 433340927
    0x60405181608090a0201030509011b0921080301260d090f060503091005060d0f0f0302160807050108220f050c03030f0436020306010e090906040f021f 66
    0x41e060241d12030038480c2c50b100004200e805090b400440c0549006080030350155620303200c0d60700780d2140f030b41e03250310706d98298941190240c1340c140c1082800141c00c1c025040402d58007001400900039404490444040011045c110508000e0340070101e01400c0c015051449420116040160009205800c03141120300c007954145d03540605490a100071141060706030041c901040030362031282d0100b0f8000c1c60140c40c4408275003003592401108181c0c040281c1c0c95054040b0780c0b8042650401800c2e030310801003850144060700d8010120395407080e41c0a0107041c0240d80001425440c454046010100c211010610010f0228140302d840f0381d4080c1c40a49050041d000c00c007086003800402c4411000b01c06030090f1070305140c194440e011096403054040600784010301c2144e008071240c05040c7e5001e540c480181d030783c28144005030284904044542c000c900010401c50341140108506034000c0d0055443c000000391480001c4e00c805c8425204d00c840030341aa403503080ca035809460208444004080c00030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 433343381 1250 433342131 433342171
    0x14041116061407031806091410050414030a0f12230915090a11030c0a08100b01090b0a05130302060c0d0806040203040b0408130e0c2502100e06040518 66
    0x45c0d5942d140403040f0310410601c3c500002d007540c2d115481c10390240030804000010132269900b4541180c02145038a81c5440c03c1c001448084100172444000800045240111000300074004448540419050040040610b080001d036601304007039110b613032144075070a0911f4000420302c051040c0c030996101d11403155062440301542806d140500c0150004180300400c680d1075113241c84c08a41000c1d09030045d201d807003000d80c603904900c40141c043c88001e090001c00d003801820448030072440150410201d84400c00100c440202140c0024500f4a0910b9590f0b104c0c030138640390400c0319072000390092000251502d02000c04265001ca0050356034601c070042d1200c9040009a00054402074443c299481c049400a07590354010f260640c1100b4030ba2003030941c2c92201414002c03040700c80790910640010300e02651034101c0018003021a0408020b103081141e600890f586410b440005000d00c15410303030003e440e544800903500148002055030809159062400402d07900595160200c4401250105 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 433344631 1250 433343381 433343387
    0x203010609030b0f0423030906030c040e1e041101051902010e12091f140313111206060405070504030209010801020703030e07032f0306090703050d030614041116061407 74
    0x40c0141e821000811484642c41d8218046d41a28034001d02c8900c000c000701100d50312040c0c0550b118820255003c0e0b1518030780614440c407160014283c41000303e040401743c4c0c050301501500c0d608141c0000b1001512001140161080d11601e47c07514203000c0f10603035080300305a05402c180b002000d007009607856903040c07105032641c902409a42c158480c80d085094040e02c0303900d6915040c21042031624030480346000c0144045907005407000e031900c40c088102c2c2001c1c001c2c01c400600c0b0000381170316803902d44002002c01c144ca942c800b4207210b228549840100c0d40e4284100c040d9070155030028107905165944020300c070b000758003940c01100441d0410304440600c01e00030400b0800c580d00b10520310454288410388c1d12400720784d1403070194003007015400100503440c02c111aa2040300301c0e20042421904505040d45800441c00b0f002c810141820424042c031500c804070003000c08030a03540820401540803001c00c150040300d0f0040c40d10a00d0344100803c0c49030342d0300045820b190201d00c005190700c40100031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 433345881 1250 433344631 433344661
    0x5030d050409020307140d0b040b10020a020f0102120a110c06040501090b13150203211026011514010905100e0a0b03070c1407050a0e1008010203010609030b 69
    0x100000c114244010000c04903203400555000d4580e207000c15013004548603880968010400b10700810384d031074043d2000c50420f845440303055a000c503212040c007064050300035030340c06000c80028012140c1200700d184a900030417184010304c2c609041261aa1040200203110204032059840305104001501005e0b04040b81254140c44060b03403411800790030304030041a44d50100305183d0018401510004108981c43d0842c1041c420b82e82c00703503a5602ca4684081c0c501c4100c1107001040204103018400c118603e0403640701284c0c0401c00c80b9001800c80d10075000e14a030344801e044444d508040e01200f814852404802c25626244444842e40d603940004492100050042d15004540814040b44090107040082c21501c0b00403c1614100c2e00c030a01114103400030b4034a84049540040306030f0400c10094a00042c10140301e006001903880d100001d01452024843c0545000d42e0501240700a03188c3c5107140042c3c26484000c4d5074a50b511800103050f401948015680340006c5404203801400041c00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 433347131 1250 433345881 433345903
    0x1020a0513050f0108040b181504120e09060d081902010603150606020c0d020409060f15090212071103070605040503040504050c19110102070c090902150c030a03090309050613030c0503 81
    0x3030b01800782e0321070341c640c0901c200181821a003030882030f114541f0740804020b0480c09c0c0e11025541d0542d800d2519021801c4201c81c03650340b05028044009058603143c406100750300140071200d4001c150f90303030b041221951240c2480c6690841c0c065521680654054104200300c0303103d68080c030781e0560060700740811104203000b03070750058101c05042a00d03032030840c15083ca2540010000650700034540d4030b540841d0249080c2c0c80c0e90381d495020f0000c0420b000d150000060848040a6181807050030884801c85002407250090290070075011204200400940380c00540c415402c0002d0301302410503031769070b8101707110741803080e406c00001801090340c00c07040e504e0f11440c4105242c3c1d9890041810b540010007101d80480c199070910000c80442c040e82c0c0000000c00340c14000141c121603d0041c03210b122500501d54060360307010001c407440034030700000302d03a002c0b00700e490001010021443e0032035660303000d580400c0d4844030110b000071001c411041081d0849104441c5108226512824561a032080e864 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 433348381 1250 433347131 433347137
    0xe2206032906040c12020304050105091e030904050a020c100218010504081b01031b0e0a060206011a07020a0f03061b020105011d0c040f0303051c060e16020a020301020a0513050f01 79
    0x404510142007581100c1002c0100d4100070700e10917031012031441242c008890585d1180e440b40f0034466a4407080c4403101410040240b0070034820794103040b80b0340c0d81c41200c3c9103601440c3d5620000d030f0206e03803650607500400102800d0760b5484c450030000c41d01a421078075008440640040f0b003a0980e6000c1d504441c01c1700d4500003c0d050000c641c3d004e5907100aa40c0300018140b61b100d0309030b88081c2c282032500704001c030740c41c1d1903184c4404008001d10100d00303a01e8000105540c4280c00600002e00d5240700e0343d00030601c401c50aa03940049101064200007035910064000e144a00080704124582e000b1100301086601480200101854100e003a91420701ca60401e1451900e849080e102d030403014a03038800c8085110781d150030390f19410481c8402c00d81d032003640060310218612005043c0c40600400345282c0c08014800365060800c800e500c03e1000c0c00203c0311701901070b1000f14032070090240c03480003a001402192900010304001e4a698400e803820810301c5480900450541740c110015417a94006035 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 433349631 1250 433348381 433348463
    0x180c08060f010e03010f150e1305150403090b040f05011d0a09020a0219140f070f170c04110c010e120a050334030509030c0d0e220603 59
    0x29006680d180e410791883d54041d500c03811300c081000902d000300c07286040d00b207003045142440c00b0001301000401a02a80e000401c030400708000c20000690b0500b00700603031050392a1925546800c1c1c400c0f0042d503110104884001c240002c44141c00c401030f031704039402a05c0c3c0f4042568040340e80d105003100320110310b80c0800c1c060024004031030940d016051602c003500451702c1242c0d40f00e00c50005115034103401c0764540c100e144442d011040500a41d0180458040288032560030154804d0340c1005500031800c01c44c45002111007100003c101c0340348640d078098420089410140840d65956101c101c01e551158284410160980ca000441580303014940031654141000c095040718207034405049040208040403800c101c0956041c900c050a00700416034141900e0030003400750503104000d10545a60b0400d10040c2d4511070301140760f415640c120700d00707248070501d00c03c0069000000c000300007000c4021000414004103180d0f0040d41a01e000f2040b1040680c03400d40c0691040810003c1c1680c0220b0314 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 433350881 1250 433349631 433349659
    0x1030e0f0709050a0204031b050f030a1101140d0e06040c051504030221030406020109060f06061205190221060901050622030b2505030c120a0e0304180c0806 69
    0x6500c03c0ea0040000840503285c26502d888140201d0110b4003030b1045034850103400c100707600d800007030561620000d5002e0b12910500340c0b036580e01c408050b1210fa050001c00f603081e00f020f4050300102e4030f10003c0007500300b10746400340e5111662090304442c200c46100c0c58410120f83e51400110000030301180c0c0c0100c074078260941d42444000c078100105a802d000030350703501c4001d0f0344041c0003030300161200303500004168001781800820354246080342d50305985420014070070107502200c5251002169803001c20749480380300038120410f0407041c3e42c2805510120b828810b2030800103107101e001c0050070250707946031100010440038030001c0c418954024000c00961103400c24445070264203903109414400d070260741c0e0311002d400c02000c9840b1003440c0400d0189105d0522400000141c40d18103150040c04d500d41000d912040348101000f404611141c01d0004980e07803603035041030991260090959491b41e5685d5103d10322240c169503000411400e280b50080750f144100c407540e1103800c008110721a0940d503 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 433352131 1250 433350881 433350899
    0x63602030f1218040902040203090607140909060103050718060c150c0930060603051516050c011104080d02120304020f121005010803090f0f13150e07080601030e0f07 73
    0x620811960070517101c1c00e50300007503560361001c1d51240355620042d004c3e41c039186100412101c03045c0403040340000c2c140022000c64032050700c1e02d42d0007042800d000030140c60303540e030036548840d94810842082e2084d4101291072035100c02d645000030b01c42c1d004d4074078070100d8186041c00d65100d0014800020f4040b0030800801180d512503030078009580e58602035800c0c42888020140c2e1640b1400e80e0f826071903c4080003040303001c001d0003071400c024914007807a9003442160000498000382d200010000b0100ba00c1100071070a41c0050800ca441080483c0d50f02d41c1e540d05217480307122180d4101e015008a11300514040d211500b2030384a164001e082c00b904074640700c1003040310b1450320089600c5101c0c81c208040c1d03a288910030076020300343c1e4100440c3c542142004018000800c000b0150085010a400d08010340380c080102c55031a128003008260342c1a000c0004665044582c0130398407040704c0c8000d00c00996046504103004c3ca000780d03801d004100340c1024017a42c0d00d40c0d00003001c126510070141001203060f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 433353381 1250 433352131 433352167
    0x40212040f0c081614040b0f0f040f2a0c030e040c0923031c080c1e03040803010f0f03020d1401021c020c06130c03063602030f12 57
    0x841401d910381034544800380c036071401c0000b190100007034180c0c0d50144401d5030220481d40b41c5d50001c840c24000a0040b40c0420322501c000e0f200640901d07541d40ca146101d54442c0c0210303a000c0c40302c0c03508101c91010024104800c4403000c080658050107010078526903446aa0302c0f1011a0701a00e0700d5403549506010f01c0020305400140743d04100100801084041d4140042d902401544440d00e030410380440801d4280700704041c40b82c40e544050720180c0962508102182d134403c100f91082c035112110407501e0380203011b06203030240e80074000100300820441d0170340c00b850584a4104903a007000703840789058004090140006075020010b80c80401c00218440c8600301052010000581050702c450103112018001040c503400c0c10b500840d014510103010007280ba0310600e1492840c0c0008c0c1c2c0c5450350800300b803c5000281406469400d4030142c408041c6070300821070710000382e0100004030740400041c56010003d08902c64002c4950460082c4000a16503510b00c2c207501610f03141849040458107124 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 433354631 1250 433353381 433353383
    0x605060f09040902220608032508090904150c0c03050f0c010624080a020301211a0a020c011802060315010c0b0708010515040b04060f030f091101030b040212040f 71
    0x83e880303850a10040e01c0d1042c0c600ca0012214135900d104a030091055800d403000c5401481840c2d1003800300c0d450803070704400b03d45105442044c842250b0b6140d400c210310303e803040c0b241858104519005010800c400111200240080084100320481c0200c0d0101c2d014034600e100500011414481814040032102c01480300c51259000040e45660314030410030340f05010350003000101340744a1003050058101c600c0c42d90003130000100710314640c1400035041c1030300001c00c0400102000070700480100001c060205101001c8882d00a56602e0807030352250103984250250a09035003810640d54001c50a084400071036030340200158155510086092100081140003504001d9485070403c041102d92951501440280d070724003100d50304201c14810300d2032615002903070101d8204000c1180400318001e03071301510074a00d404200404020b5049001d40400d9440707807845450808100c0c2001a13118000322b807102c0c03c1e28241f180700d1203617003000100d0055140e03901282c1c0585001400046030076078404805 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 433355881 1250 433354631 433354639
    0x30812060303070212240c030f1018020a0e031906050907030605040c03021f090303030b040b06120402130b0a05040203071806090608010909120c02010210020d05060a090605060f09 79
    0x210081d000640846190131002561b9003244c0001516044c00742001c40504a002124180e5806d05d02e0001a25100c000d0403400c1403031003040032410320714403400c21800915810405180c0107008180400095120128071004a002802c041020b401c0104031105801800c0280440407030564039280090300c0014800f01c07460041c1580800055030700c0c4501800b88e8001c0c0901c001803800e44c8141321001c040003101212100190f528011a603038800305c0d138010780e5414500892003001003004200130786990701c0c0b8140d01c6070010130306841c2060b1080c40c161169000b10750100c1400800c0360640c00302d5000d1000160072031048071052100303050a40045810400c5072401000310400c884911200c414030350803000005044000401101d948000a02d002d045060701c10801244590b0741e0510315225690b0310350034032400550303a02c15a0700074003840d120925843c100790b6aa1000b01d0020000b05411245240300b5948580c0115000000740b003000d0545101404480ca040d002801c08103031030b000003500c1540 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 433357131 1250 433355881 433355887
    0x20c040c08190b121219020712030309050c060a121406030d0c02060d020f0307020601090c0c1b0503010213091a0904080f070f0b062e0507050f0f0703051204030812060303 75
    0xc031010407020350182d03408103c007a2122484108660360003071300403886c030840d0302038a0240000c03028014940801c1c0da042c01c0010350300742d0702c0c80c00c1d1341000c0800803043c1d40020082070f00c40302590403d12403044a000c2c00ca007002034145c0c0392801d049a80f81900d01c10340592000040500540c010f103c4062540c1c002402c607400c02c1200d121000c1613034040303c604030941c500030050081c020f80421500c0e014124080c0c00703100c80e42070070000800e6400301e03400c00b81100c0c44480d000365400b9030840c61600034203000380080d940c840c0e144070800302150703440c447c250183e03282250111a60781e42c4081801d0f020070042c00e02d1543d0726a5118041c19811a480d142c04119081100074001080d4100b00e02c00b03030f80700c1e6070084031505d0309100300b002c0070704183c4865a000c04414995001c40705d0085081d0b81501d018201640ca0742140e0400c4c0340740070140c1010080611407a621048100000501c0c0000c40b480742080715150010b210104583e400f40d84401403d0400034041000c202c003c44000030343c8140e000d400c581c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 433358381 1250 433357131 433357159
    0x10c0507080d05091002010216061109120606010224072001021224033d15061809090f1a040b0a15090b0406080a03020c040c08190b 58
    0xc1800020b0b00000003003070340018a0070503400c01802d502e14100740c50000b1401c0ca05000d02e08040c0380e44418001b80056a50065000001c1c0c1080a40b022580040c0c44140c882c00780c007490503520302098902c14094403844014541e000300302800440b21003006003000200e5110a030313040e210b900c03000c07640e143d044900c0a1a0501c0c0403007403014205004150510081d107080c40b8640640e081117083d211105445003030b044001d103807400a0541d50026401b00100302550025000290b0441d50f00c188400c0d1071614840950148000d401100e510800c0d49017211440b03039104d10039070b2440c004841c04c4812002c40b2804000c0c0c0c0225500090b0300a000c0c03100b049815003c1d43d10550203650705441c0c00280c0035601c0601050100000689500c845060340400440000f10012606034020740b0032628181e840345071070140c83d112a041440104280d82c110303144814186006904d810000324001c0c00360385420711030b00c40d15106041d4a402500303c9000301422040010005000c0e00c4000d110310b81042080407042 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 433359631 1250 433358381 433358383
    0x100b0d021602030d020a030e0901031e020a050d0507050907020f0d0e03030912031e0406090e0a06030b040c15021b060304020a0e070908011805030a110106091119110705010c050708 79
    0x220001140d030140a801c2e06ca8980036015506800e062400303102040d00503c00590341c500f0000f81c0c10b180380f00220310900e40c0c1c40000d52200d0142c10058100305190070747c900704030001901d4030079100e003119110010340d11404101c3c1d480341c02c0c48581c5125841803640448242c040c0c840c1c1d40c07040201034140c80c034003110440840d80c11b6150700b042c014039500000e42c60615402184540314a110390303000e01f03803802c1c0c0742c100c004041c07200c1c3c0d00510354041c00090100b015200c00e40c0c000c03001554003d8011407245050708010720801085d1140b12030f0714052114411550b07101241c2d00e0030444900d000034003030800c0c0100380003158100410490f00540800c0010880410300b64240d40301c1e007800c0e6030f402a1a400c08904c40c1c2980c1d440d80d07001703582491445884000400100544031103a031103143c00d006000300b4445450160481da4021041549001c0c080e050040070580200300556940c0418525040000e004407251102504d86110365084044c043c0140e6128070400315600340640100c030035031905c40d0621 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 433360881 1250 433359631 433359643
    0x602040801151e2d09090309050a0b03101202210f0c121015090c08040606141003020913050c0a0207081605010c030c06050403080f100b0d02160203 65
    0x1000441031044100b01c1c008030303e40d00080c031035403040f42c144981e46464064021340010504500281c2020361084412152030b10081000b000c21000900a9200074140642041828000c180c0660040340002c168001d42c0c1040303a000d03a0b401e91603042c1082c80c00459403448012460120f03809850034581162600c040401c60015070304010160210043e0b65403068609032120480c20700901c415030382404481c0000c101004410a50600803805510b030300328142c0c20400c1d52b0400304d104c43c6000400d00c481940b040c102032143d403040b00200021519081070444003002083c079a5131000c008041c0f50f10143c0701350003a1200d1300d0042c1003a260480c0c02103884060310000c41c5c81d07080078040410800c0035254100710310703801014504041d14006d900400d400451008900035941070182078081c032000c06100780b8040c2c400a81004040001741414a0010030075101580d25403034020100b00440c0e07100d8214010710b002c40300d01552207481d180324501010301135000030f07002d15440311f0603000c0341c005620705000c6 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 433362131 1250 433360881 433360901
    0x40f1805011d010b06041e0b04031214040503060402040f02130e0405150915070c080309030a02070609290c010501031a090a030e0d0c08010606021e0c18040602040801 73
    0xc5141c90003002032180d2a03078a03040c00105a03052440103101910380b9000c8400b502c4581000740910041c4000780d0380c0c1f441c0d442e8001145a20009000028000405203104195485a13110000d4806c104a00700b0706020f01e00030300394582c011002242c0103203810390252524941060015082110b0354400514001695001c2008001200100020080e05010f038080881030319247c024070b41070900d6215a40c0140700340146074041d40e040403030403286c0034500c042c560540c4607244070f03601d20b005615952280c00801402c03025110349040414010701811461068805a06c22000f09100e61217400c0380200c544d1100c0d01d82641d0403c0070507032a1800307001381401396028915100c081c114100c8426000d0100030710580241d0024045100001d6000321000c8105200f1030b00c02e04a0002800d00e1044083c0d60b034880c5040b5840e000d800500b454000c40c9941e5515609070240540a06100d021906d905803101200c2c2d21005101507180700c09016021076030424019a401801d042d200c0303507000e00b11428404 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 433363381 1250 433362131 433362133
    0x3071a0a09140705033d1515110a080306041a120601050913050304050405090c091501030e0c03030702040c020a0606030606030b0a0c0804030509030c0d0c08060705040b09040f1805 79
    0x100c01d120074117040001100c4241d401030410410050703081040d600e120301004602082c152510851008107280d0007407040b0541c41191806075507590710f024100058401c410b603011900003410751460500c04a111519642c014041c2803030740e503580e0200001070070084910510b608100201e00d4054844805c800d03080c81c3c1540040104d541498200002d0030f200030002084150b20308201d100165011040d2000c0720000e480c04141074440d1200c55050010312108a50084102c40820a815000f441c80c0041688203880030009803c0050301c2e140c84040c1a5541d58165004011000c0117060540c40021038100c0d0344195003009656a907138000381c54441c0c0c8180d079296110b420030302c18040300081d1250086141401080030b902c5115003c0c01024004001805110300801c005000f910107204007030341a0401400354400b1162441d001034514030500801c1d00714400d110018400034010b00848060f959070b03100d1641403003801c108200140c20442c00c10b510007034842954401044e02e148111041610030b40c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 433364631 1250 433363381 433363393
    0x3110a060e010c0822030f0e0d050109290105060a0903080a050901091d041103030f040e0a0506040b22020d0c0c0b06030c060f030a0605030a05031b03071a0a0914 71
    0x149008000f150054200411024068800700c140d4251700884114168107040c400e0140c00340e02815200b450a40030250f8114044141c1001000010340c015414a84240c410360b801d06100c0441e45040701144880d404144502001400589464009020605054070b00140115140e030781c0c01440340c003d40302c0d0501003100410440309644e0032103a50000303407410f5031100c42d00841003000344841020240c009042080e02d0207030700280b91070500440740280c08900d400341d51155201842082d43c8402c4070111034191a001c040365443ca014003a046403003c00400b5a1200c1c05840d8103c40d09840211340706a081d542000013540190090158103060380d441c1c0ca844007026181d06002100250040078180319070407a101c00d00300c40d40c0d104103407002d81d116440c0d019140d07a1229111801401c0390b42050b40c5c1440340103102c00c00c000c4c00100410710364040702205c0c54003074050040c0030b99901424100904040b0551a00c058110f422650380d0792160f139100000c00e604a0b030b5280c0c00d0050380788010b00e08580d0460 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 433365881 1250 433364631 433364651
    0x10207021c0507060f08010905071101020a02030a1202030606070312060e0412021501080729070b0103050d0806210c0d150e06091b060d050c0a080606031303110a060e01 74
    0x40c8880c0004005034108000f0f60280c5c5507000b45440f405002d02c0440564031400310f074003203228902c0103210403400d0300210740d41d0100d80c00c065030381d0f08503054004c0014540100e51000f035002e402501d00890018003100e0511980f581c0541c2e240801100f4180c01c6035076140001460f12466030400d00a03401204640003584441200034200000a14020b0007104004010000070000042c2c40c0126058100c5900300d00010b0282404004041c09900341c80b808c0124488003403046485404c0c1c1281d100c0c90880b0400300c0484070030b64801c1d0045951941c8240800d41401c101e800e000e8404c6021006d072400e40d020348420750002452140385590640e158158244080314241061103601204040c2c1402400c1e2031408411080c0d5800109607d04182c010700c0c140303844161203010a031841d0082c642810b000e10303e4020b60200c560b400452041000400200c0030078194144201200d0280f422006140d100e10381e651801d4920240b402c211183c0c45c42801150380124000c0d00c034a9000c41700e1800081041c82c40 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 433367131 1250 433365881 433365883
    0x52d07030c020f06010b0a02031b01050702280618200123030c071a0703090b07090b12060307090e030d06050a050a0e0a150305010b2b14010207021c05 66
    0x920340c40030030355001c44450f403899080007403503504640d807016900f56100808a022820f5018440e105d45082074038116402c15060190805842421703103500b11140441039102004004200d03261f90110383d141d4810071b5011512540107105002c001e00c800c0c40b81c0c45069543ca1b200c110f10041032980e42c82c00507060034015a4020403d80c0420261824a090108241003410852002070242103086100103072000402101c650280e02c3d1080b40000e6202e0352614480240140040c81d1049030724401080020300c4084c002c891400c10b98141409003402c1013001586440c903c4d0001d8100d96042c462902c00040c1460307513006000e886160800a1600e581c000745a150541d0100d410051280041041c1131242e40c80301c1074550222131180b000c140060729914802c00091001c400321350030341d5620a10110a101c0305400c50300d04d865050b0355161444104c1c50510042c1c8070b079800c41000350200304a0450215034220368101e052218103000514004181c1e00248021105090080c03d15018840311014050 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 433368381 1250 433367131 433367141
    0x160305030901080c09030322080613050601081c030b220212010512030306010f09080d0c0b06011806030e281e08030105090c090a030c05100903050c0103052d0703 71
    0x700040c17400d02c11a03d00081d1240240003c2c0000400c00303400d5203c5200c0768840744d07001801d808054030f0240c1403080e008090805502c00554592040c0b100011700100c001031481c191090b80d80c1d000c8013041c06c895084018101c102c542640c4001c80c100040b455003503e0040382000c848050005941d558204238401c09000140c1c0018411003001014456840c0b000c0300f2243c0c089002d2a00c8020340721200010f03100d00c1480d40200203684505000b0006141e004a080c8082c40c7c001d22603155260341e1200111819207444103c81610f520f10841004110b00a80040c2d00c1c0c82070640c2130341e10a41c07110a0720302861000c0c1c100307a070082c1c080800500a0140715505d071100d120320b54010241104850315948070700d12042c0f26581c000c00d10f060001c0c0074110b1030b106031010711500600e05000b841e580d0402c01004005805103030f2041c040c207511060070b14000c032010003c603540400035000681d0501e0055008010003030280981161021155421020783c2c41148811b02040110181a00781910002c040750 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 433369631 1250 433368381 433368391
    0x4060e010801180e07090203090a0c0e04030c020402130b030c0a090e0f01030f021c0b0703050c0a02060a0b01030b0312040305011109130c02030d0204080c03060f0708130516030503090108 82
    0x1081c80018409000b8100c01d004074100b03205008600b00e20340000c014908007141d402001c0091011052000803c0081800341c3c1d1607024424000c81ca980300c0629000000041d2230082c0401e8041c06203000500782900909103400c0d40880e0f2050003981c0b017040c049940c0c01140c2243d40c080d40000c0407000282c03c40e603800d000c2c001c6900752040341e107000b0881c40780184060201500040d50310001804641d59043d00601d100303c01035000c4000f482e14500902c06180658080c400300b8188000125603004950a0702d1152965900401d04c5860345030781580205003203c4a60704043c0c403a440b1801c65102046841744020600d18903941d903600e182000c1c1d003125800b0008500e200800c02503001c01e5075807a2101c8504044510340091001240013043e4558800d40d58021080c0d8004078000401143c040748060402005074156581c681c0c407811b04601d102e40486203200464030031000b050084195020b001d4100d0305c039030101c41300072030160402d02c601c0402c8c0d032049803540d10004080c3c90301d5a20200849d004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 433370881 1250 433369631 433369637
    0x22e0e10020105060d060e120f0c2a040b0411030f04151506050901120e0102070c05030105070525020307150f02010c1b020d0f05070317090a061b12020304060e01 71
    0x21304180c000503108095240380031345403a480345008000c0420078850a6807420701c071194159201903001078403480340c02c45039080106000340c1825940c4644006075101c040920010140242c0d070b468803c01001b8109981d000350030a644803d0060008041d030019801898540c418110a1a1a01d0000108104c2e00c010303861442c05c144c0700550a030320600f824001c2e100b00e414080e840b0201800100c480e02c00940001c5102418080600004181980100001c81c09140d08041c1952505e06160a0314420b85080d40011010800700c140842c4d030070980d20120f1002d00da2040d1404c0c07aa00001c7c0b0740005a0010704080607034903902440d898101e5001c2c112480b0a000a01c00100030641c0540b015000c041d90f034100840d8005040b0866843e17440c50615940d0051201e41c0942c143d052896641d0340d40c0c082126284075200070480003d01030020340f08000300003801a4081b5090500403246259541000e60031002c1610100e40012401900075124007000d90042d51101d103050002442c5c2050319003100c0c14 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 433372131 1250 433370881 433370891
    0xf1e0a17100e060c18040510061d0f0409143a0807030b040603050a08040e130807030e060f0c210c1009020609030607120f0203070804022e0e100201 65
    0x102e0103d0800d90040803100b95544400c010403004c5210000303095801c1e4040e1600040145907181410341c4400d50301030b941e481c030008011f90310302401d0720001e5100b141d22031103145100540d80350a80100004501c105440150001400c1c4c81d6803504d00b0300c481e85a00300d00800514045921000d40011045d100040c03101d40c868483c0c44050700101029022000300f60300c0d440d06011913190b42e000790f0000c562140441c1c003c100c1d035040c1074845030403600400100141d2900810b50080090310b00908064100c203007586401580e5500303071541118901c81c00e800c00c8080c40941001071400002d0081c2c40010b4001c0d240380c0e07414500c004609815882503c81640c4140400b0a99020001d000d00000382a81d4000801091500000d621130140c071003031641c184078001c10004c1300c83d405101e80358519003540c0280700e00c01e03030001d514041c1d02084a1042c00207100c07000080c054582130754040b1172009940c20701861038a054a4040d00c203c2408042e00101d4030402d90061302e400e014490140d102518402000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 433373381 1250 433372131 433372151
    0x40f0b060703030b28150e011e1206080c0a23010c0507030506011e151b110306010605071109070e060d0609141e060f1e0a1710 56
    0x15050007418009400c243da00c540408032070712031011602c0d0242d104483c40881e10201219000130510a00481c0150002d000030102d481d80100350f00d1442000507102c401141010380010a214075201c2c0c8450100410362442c0e200e0030100d17102c0c040140440c1009024808092408e21448109030350002c021f000805400102c01d47d00384c001d803401d4100910704104000c0c124100710f458080a1b0304042d2003800740e400001240d541c00401c608245507100941442c5030707036880b40c80b60507010403945a40816a1034080940c0c0c10442444c0420722840341d03450851407822540440e1412609800c80d00104800045031410301c0740d00c1444000004007102c202d900351800d030100411652401030b940d4001d0001282481d006030182d00442c0290692070010015804000d0007d82a48810f80e071041c0348280201c500381d6860a03c04119114071005045944200989400c0c007106e0804103108403092001000321080ca580e50003001c1c401858140e420030159600003203840e003440c0d4500c0780001d0161800c0300101c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 433374631 1250 433373381 433373389
    0x9140108040209060423070f0f0f02030714011e0537051b03040303050411030321090f01090c0303090803040806161106091e0304050901120f0807060b040f0b 69
    0x5a130001d4281c8004c90108202d1122824850705110b02c0444018100c013084140b81d40580f803010800071982e03901c510260800f0003a03030040f05800810005070020040ae0b400b09001d0700c3d01200102104c40009a030020709245604000e545d520003070b0507151a0420310009816413031980d83c00007807511700f21000d41c0140c400200c56104a80003001d50340e0325000061500010031488541440d06101502e035070b4500303850b0090040004079401c0360000f0441c264058182000000d448110040402165248020344a20400901c005108414070310900e80345c1e440c124801e0040c0110380e8403408590368602c0c218076014010044503001040c240e842400200b160a100240868101c0014008800d1030249400e044511440030000000c6510076007040c0820b051001a41c201e502c800714070441c005000e14020280c07280300364456207a1280000f00140085201c440c64400c01d1072086584992102056480540940014106642032551030308100c4250400d0b00410580c0304040004102c2450b4010000d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 433375881 1250 433374631 433374649
    0xc3007020d021b0d0804050d0b071b15051504090c050909010b030304031707080a0c03030b030c0a1403010912050301181103070305090c06180f0f0607150219091401080402 75
    0x11303100c0c041104a5400384100c00080700c01070540608564001200c43c00c010b4640c01040d102040024080d02401c4845048100e40e40050b55105580d81d00c0c040719401a04044c0901805145010b654811107008a0740c861065050b8a403160408403006460b1504010164000a140d400c069040511850803136401104403420740b07a202c4890100e202510b1282407160040c1407005050b03031070020310b2013821500310700e105004030300c603039001d1000f503040f80145a10b41c0114600940c020308000014010302100c1e201030b00d0440000b4000041030740a0b0703105c40c0000910302050340041800040188004052400500581184080144901017038a800304180740720090191082580c0e4074042900c00c1420b000d00b0341007000040096071102e1008115102680000007101d1144115608a05250511140740001c8207001418281845056152049070584c40640d02904a6003003100342e50b40441c41d52210300038a100e90300e4a500b241803440b4001c0c00d20314498494144510081004016500c00c1c01c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 433377131 1250 433375881 433375933
    0x305090d05041e1a0301050310060305100c2616020a0503040608040f020d0506101406030a1508010908030a0f05060d20030712051e060c3007020d02 65
    0x2090044032443c200d031100400003034114803014003039070f05081482c1450401440c140d8000b02c00361025400300d21180c108503401440000c3c40c80d002061012070492031540301e00e125120600b0540c0d50040d82041900208003048807000080ca080070520110120801d0500c01c2182e4500040102c0c0c191900c40380d40d240140d00c154030400a0242c00201000080e82404084c15405003100600c070300a458035544880048507020b007070180e00c0b00c1c00115001c5484c416915020b001c3c186502d1500c514100d8406084404040e11003802d40d0480094080340920480003468014104141c0300d0410b809000152540f84192124003814401803020603980c64413080ca10399488440c0c64440f03038003210801d54a82041c025682d05000e41c000c00034044c6035021082d0142881901602e022804001074100000010104121103a00c0300700082c0744400400c0042c8401c1c94032102c02900c550707962a0a00342ca051440041030000001e070f0030302c021190104100e001040c040c1c0090010320a0000500f1a106e201c420 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 433378381 1250 433377131 433377149
    0x4140114191b050f0f030a0504090c090e040303050403120204031a06040f020d0203010305010b0904050a061a061819060507030818010e0318010c0c12020307170c010305090d0504 78
    0x2200607503500588240444240240c1c1d0042801c2c0319080c091307161107001e4980390185c040c4001c030200020703011089031103090300d603220b00e400c00307052505520040800100403002d00c8803402000c81c0c40e91582d80031a115610039500410315181c10b00e001444902c02c80c00d24001d8900600c4280006840581446085d0012000c8a01150b0300c002c002006020703807080c1c0e2050340d440000c03480440541c640007141a240904002c0c4400a45e80d42800150302080720302801c1c40d0080390014002880540113a0501d485222150a41040c03042c0002c0244d0700140c03041c0300f20750400000ca006070400d1004800079422456100004529101307007d02540701d03020000f020405100d00007002c40b1820b07503a9501c03032040300008000e80340d0489a00b9589600c00c01d0001c0c500b900034210074804e584164902810f280e070203d980001d0318a840300440c0d4030a01d8000c00c0340e150040b424007054003e02045c258444038050740007004842c2c0320000160403180040d2440b44140c00491440305c00c03d80101c02c5500f20b0310482 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 433379631 1250 433378381 433378417
    0x40204030215091305010f081203070503070810091802091003080a111009080417030306030c061815130515160c0b0a020604150e1f020f0f04140114 65
    0x1200140290010b40303903000300384e80352000219035a0804401e42094402c444100c440449100110340d2490004855840c002181040003542545c0f243c1c1c05c050700440f02002c602070341519044080141c45601c0a0904c1100c6600c64900642c900f240880b90880b0f0400910040300c0e0554840d495644a03507008081405210038000e12482010070002000c0040750328104015070440c070b00341c40d01d039204d07128400b11800c010503003828101c07010040724081c100043c001e080d00440b030b0090150302e8201407003410110703c40300c1e17201402d0f880c3c0d481c43e030307031400c030301c0d8406598424443c1080c201b44101a0051402082c81100c40c0d021700c02c8480480320040701e001406840095a4074040c42c180c0d8040e00310030140794011628071080e9800260380c50181d84a03c0c045480303250b544168330304803001a40e000500d0ba01940030300240225460000e0f0350360001240240c50124a50a009059449200c00006103800028104003003140032964135074161003442c20780c1c200405003200081600424440701e601a00706 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 433380881 1250 433379631 433379647
    0x1113150501050a0e150c0105070206071706130518071409010314012a170405030703140d1a030607090b12090106170c0405011e181d1b040204030215 65
    0x503481d03020b020100200344104100816070380c5c00c40c60f007202410b001d01e50b00307140100f00c0f0a400452a107100f045103959035184d40c183c0a001242144001d02600d803c048a134480944400103030143c02d114440d80c01c90104048480d81e1a1441d00005505c64207811443e401d45820740da0364411844d0440340c10031390b40b00d404091030818070700401040420301d140e194440440c0e820700343c2401e40e10654000a851742e03030b40000a03076004c03c9031180890300101076030005c10280d00000d00070000110304540d421062800c3c180f000f2000811102c90580203203101ea01040444a1450200700b05076001a80e86840500c40d49030140500e054058481c4c0c810020750b44d10b0008102001c01d51001c00107081040384500060785c0b243d03540391035209640441c0d000d1800d203800460070781c82c1c0000c111001c0845c4c2c06040c440030f18160210000400640f03c1c071007240e4640504115038508142d0304c801400801010b04500b02030340401090141110f08030310f0060740148410409a1b8030341340d0205104020703403000d40e507400321 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 433382131 1250 433380881 433380887
    0x504050603100204060906080a020f0412050c03073f03050c0c0402030f06031506130c09051503100f06090302040506061210090e0303191104080a1113150501050a 71
    0x410140c0c2d261510120700000d21301d901a0781481110b016464821945e210640148183e101781c0b46600c030100420002000040b400e1001402c425000d082940c03080340f45480001e0500b0300c1c1d40d108403440510b04080040c1c0024413044000c401050340f280c14641c00800020303540d418014107014003486808551441a00c20a004c895048040208110740d24035110080d04421801030701c2d2035000380720700d1000d82d90358a0050003503070050000401e6101403000305c0ca07081c4041d080c1420940200844a80005240e40310007441d1b41d00401403a0805440740390a81c1220038050f803d40c0162408542c0040400c03d581d081682642541c3e0180d41c082540e60b265000314105200b1481c07070354400d03200f000c10426a002d20382c1004042e5060b0301c00a01003501468030b020b0341d0b03000a442503a40c040c503881400e1081c07805580010364908040c040d0500340b5649040b41070801340e001f01f0907155840c0c103c0c0051805d1401c880401c5001c140c60408000035030203440a03501c901c030306014490500000140001d02c00d40 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 433383381 1250 433382131 433382143
    0x103031809061e050409050a0b15090108061f03081911030a0e03010e0c0f0907020109080c0303041e0308160302040f08030403060507110a0b070c0605150a1e0504050603 74
    0x140d03a003080c401c86554010501545460003440c2e08010380c1043c011601e0301d00741c007440c24055003002c021301002c8015141d103081004007400c0c1d0115510035003000017454607080d214a00030b103d11000b500f01481c0003c804240b000da0606444070000d4001e00c10300c0040c003c2c6007901c0c001d07000040000f1100c0d00a0070251007101050311a07184612001c40ca44001e1540401480c010010580c02403020307000ca9808159503011441b031a0740e200d2028040c00d925814440740d0160321174410301c00400d07400c2d071913150840e8560140042401c0303a04000204010f10400009031030508041052102c0148001d84004058102c00303441c0500c1d0000700c000b503e580f40e20a4054a0141103442d00d01942140e451000743d603245e0084c84116010303801e0400054909000312000c020000c08140908400942c503681d10102840040c030002c140800c0e2640391020600c0d6205252045a0105140300c070440c690b001c001500340140d01c000c0b112031100c1002000007984510071012a101a80c012810341c403084c00190400c2 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 433384631 1250 433383381 433383389
    0x601030b0411310e030307020c06071509032a031704061409030d0f020903071a0d15170c06190219031e0e01050f0a050c10020a17040b01030318 63
    0xd81200c40b5600042540c05a0703480f4041c45075002c10852111400035074a80c08111403000241e00725a21950640c140500100003d0380b0541000402e60f440410300003c82c0c09001081d000181d042c040b0400e0040f00b40309240184900c1b60414a500b0320903034006101c912041703486007240909101280402c0360036046110b000105c0200c200c440e15003440015074039081140c0d000d8000d0b06012542c45415401e100f1034400081c090080c2082505008001d44107095103c3c1100b141c0e002000303541c411020b244a540b00405424511100c1a450b2040c0d006203914134621407041d58004400c81250360355502d00b102c0c01d2480078060300100d84424241a42003491840441070041c504201300c2040503030240c107a10134100300200d1809940b102d507004482903a00f01803240e02040d010051211072000c2c1c04068001031f03e492a0083c545440b11062500f171400074001000496004286030030420b0304292884c45103016100c03100510314094680c0071b0312540600c40503041c00038210f1901c401c82107102e41d26000d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 433385881 1250 433384631 433384669
    0x60306120c03010f0c090e010e0604202a011e0f06051305011a03070c06020906190801050405010515070b093a050712030f0b0a03030c11030601030b0411 67
    0x8401341c182404003625014a000703000925444021030545403034a0f541e0306039084040c18511a03501c10b4244002042900303038880900071842604078040501c1d6000f02800003c0c1c058400071445020900c441420100000705016410844290346260042e8110007096100344804140c084400185800402030b40c7c0055800450b910840f04100d0000e030000e0b4129910801061103605028405a215020564a0000207a101486900810f0031078000e0b04218200400e070902d0301a08803204403810345070100880108000100401607403500740f00d418014601511840b0058a0302d102c83c0741244140d1900408940d18500424104030041010303c54000304400030a0918110101011050007c642d01c48c1d0002c80c0d10495100d4544110180c03181c2e164080311099043c10505400d8001d42500b8003500c0b02c2c90f81d50b81003001c1e561b46000010340254002d0f121310100560741c2c1841210f205a081c0a41e010350b01c98001040020790a400d040e900c182c12001600900700803030001820b40030302034407020071 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 433387131 1250 433385881 433385891
    0x5130306020301210819020c060301120b0705031302060715060b0c07050d0b060d0f061d0111071703070c0203010204091a03010c1d01020304170a051002030105060306120c0301 77
    0x10031840303500460590703509503400e090158480110f0403807032100d40402000104140061107400403551510070b0180710500603a02d07001a40c1020400c0c07034100740d101c843c580040c00b0242c81401110740a507900504c080c0741030781c44e5181c440b6180c411014621002130140000040000510003480d0b05441045041c0c1000e07c183d81e40c41c0d580018540188428000e58042c0c00c000003020326000948100c0c140c1e2044051321503643c0c0e03800b00003000703007008401e580858988140b1000075000d4403400507490b1080034408800501050322908641c0003c111030265001080742401084d04000c107070091641c5104120303907aa4401301c01712001415010f009405600200300442c400d00c140c0c106407884c0c0c07200d40c0781e81e1700c2c0d54a41c0d0415090f034a011410ba404500740b03442034a4852548050b40d060f44006004980c6402e54481501c5115060b121003481c941c1c01841a140c03c01030305028054581c1d40c01101903086504000018161f803101410300b03031003900b0110100c25406000d01c0b0084907ca030040007000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 433388381 1250 433387131 433387133
    0x51c060303030e0615010926011401060f02030c030706110706060305030a0f051812160e10050a0e06102604110406030507090902060c06090708010c1106130201051303 73
    0x1400e9182a2560b0f5805282c0c00100c40006000b400364803a40141e41c0c0388445480c10034100c0f4880614045100401c00400050f9070440d400d010b00c41c2004507051400c1d039290304d0100700900c040d0792404a1002c64004100b107850415002054480594101c240002d4211405c01030703000c28480e003400100b481d410000c00209100020025062084007a15004050540500111128425500c00c98072007240015008054200340b1340902c1c03084150000c680440050010400c0109000e0784007900308041c5a04010315a440c1c4521400100b1080d6502c1100324101601c0d40c50703041000740b00c14014581d02c144211034620440010030050a480a510503650500c1e8005000040441c0c00780c51010502240b0b904a08040c81140c040300d400c24043c010950602c551030010f8400e4507420f0303a001a090169503000d46060101c140158030010003803000f0340c90001142e094400c2c138021681848656105c0707060a80000c500d0f41da020060303141600796400144010b90b454010010039a014a051603800301c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 433389631 1250 433388381 433388387
    0x606050f07380405010b0126150607060b0f040203060a0e130f03110c03030c12030c040302060a080711030304020a03080a0201060918020109080703030917070b0304031d090103050d051c060303 84
    0x240c05280134a00074442a0003031401900d2a00070480030840c00105e401e40c02034400284d038442600302c1160085c2890070341408000a4003504180800d8a40503030b0342074400b0305c1380340000703005034000c42c00d40b0305509524000c030004100c425184111480003a00e18000388903100d00b140c1800d24a40c0c0190508480c59550500901803802c0f107880503110300c0f40000c4518145800025200701c003011074010420711515a04c0c1034500e4001600105920701c00b4040800107a5810000d001c40c41c0721031ba203544040c9004640100144030304101c1501c079820800611016840d080100410340c0d81001d0115900c00007003070106e006061036409044000d2500b018903241e00b107460644072066000766035900545071103102c6280c030351004c4d2000802241303454204000c00c0c051440c0b11003a1101c860140c030000b40e030720384544150394421201100001c400c0800d4103200d45080307204010650060f100a0429070441d6500d5a5841e001904036052020224041268003400c1c2740c00d25485440d041c00b4030107240d40345406 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 433390881 1250 433389631 433389743
    0x240306051c060b01080103200604030206040e1905060603060609130501080d0906090f121b0306060321020c01080a020c071205060c190302070215120a0606050f07 71
    0x80702c201d030901c00d0b18101c940c400c18105042e0382d04196070035050522280c55420300081201178540040092000001507610a4040c000508560040c819145800c3c028501810307a400b00484100340340c003090200e01d41700c0b03c084c0c80c0d00c040700b9500580c1d07584d050400123000c0d140028448400a081c40000f00d501c2402064440302c0700499107070440b200343c540c0750580b503d4245001d4a0818041d42e4010000d1440586801c8900da001c2c0c440d14490300000700c07040e069078080d500180d641b01c0c0c03901810801c0064286029804148a8880c451800d1806100944401c103810480b4108858500440c4a500880d41240d00c80c4417000e044a0342a55928480c1c01200c10300102501c8a004100c0094031003a5500701315034600240d141040481090440203400030340260209a0b0442007490341c8103c180a08402821000c1104000710210700c0c104454106980441e0420010040240844200c04019070241c0d56016848010701e10360820904141e910740c032041c03810703a98010740020729804000c0100e8603 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 433392131 1250 433390881 433390883
    0xd0c0c0b0c160602030711040b120a050d0e0a05060306090402010e0d0501050612030403030c030503040c090c030b1504050a210f031d01030b0105030a0c02150a24240306051c 76
    0x2c2168203640d10742059899025001c00503100312038480e41600e80740303041e40c03108500e0280201442d08205454410518000313001c0c1c41281e00394005804004c00c540c0042610150500460b140e42d075150070100400d40034000940540d000740843c1000c90116030148182c00d0303082c2000b406024076002c01c5c0c1820350281c13400303035891409030100841618221001000300d40c103a94050f1103000d405203117070750100c80d280e2000b00281c400100d840804104400a80540380888803680da01080303082c4001c0030054070121600040c8001203040008004903124141604110740100001032201c0300c81c0d080040c86681e5025000340354000c69040e80d0201908a00303045c3d5058856000d402011400000540823581d152071400e020800500014804d804242c10003001410710344180d42842001c80404103900c10140d400031606511414203e203600003100c851000070344840da100d0040391810580c640d034580000e08000c880304032403560b403000ca40070780c00c01c1d0010580500902c80201c0c4040403090f0030381540c40 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 433393381 1250 433392131 433392163
    0xd061a04060b2803020d05070c050f0a05060112031103070302161e090b0111060106090920040303050f1213170304031202090a0b030c030f060d050d0c0c0b0c 69
    0x200402c030810501d058a41002d844150700003400c2c00403026103100d102c6483c402c000c05030200901d200c408514010036000304550744685800e00d5071440c080b4101040031048000552044500d43c0108000080050444200c0c1d141720302030396120304084403031043d0a144001395100c00a07000040540c00200c0e10300c9a00c0c243c080c01000c0d074446440a0640145a0011140042c40f00c02131145002c154014201403105050801007401c0c0900d1740ca0404509078010310200380328000402c8010880e015000100d4049000c40c0c40101064000e40c12034001c6000150400c80e0108620182c00c0d15441111042c1504102c080064680684a4801c8061304003040380d0044000c01041030040203a000c0d00d00440d41500c80724101d40394802c3c50302c020b400860410ba40400d050f075000419100c808011402158180c014550744d15000c035058a03418000352140b4051035100710503c000c5000454005180c0f0520b140203030010401e401d069042688036000000d24100000709503c507207500060810210361140b0b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 433394631 1250 433393381 433393391
    0x709050307030302060a020f0706090b04050c0a0303090b03090102041d16030606210612060b040c021207151104080f010e0615090c040e0709060905030304120602090d061a04 76
    0x441415281c0800e0300c03008001d42c2c02a00403880744403958000c2d18540c1d512010320b9003441c01c2501c904090301d46690b800c2e5094a0720f80c080c017040c02424003d42280300026565107a00c0740c9542d900501441240c421014040300c0031001c9000580d0a4042758010700d04803c1ca05245400e0701c20380402c0107401e84003030003500c40041110080e03d0190040c0b07000c80360b69071100c0c10010781c9081c0300b401400820913885003c540d200404107a1401000032100100c1c01418006450102141440102e5901c0d0440c00c05541c0402c03440243d9440081c1195581603101c103d101c4207401c50307040c20000e00309091010b95280301c040740104868000107040210701055000034090303e4441c1c2c20a41d21080160b503440c400e1130b2450f80c26070f650b0810740d880940121904814500d06555044195400007058403440000380c03525200300b064590006076078000d840124080c3d450300e0314009440c840700c04503c50060440d600401d4216990b6110392a00d0781042d0050340038822070035840c01c0342a0801c901c9055502c1140b0300 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 433395881 1250 433394631 433394639
    0x51506040909050a292d06010314071d03060411060f300f0c160c05190e0a05160f021507020601170f030406050304080f16060b0f030703060b0102070e010803030709 72
    0x60528204084503c00d580586c00d0051550070342542c030004c0115061688070045014440b1081104610032011552000c80107142c5215040802e20801c0003e48242e011400340004149460315403c0040f10842e61180d03660f02003407612015000e20f80b1000820710400e82040d4078030944100076400e04903611900d5403103a0351050301c81d441c010240c4000301410310600100d0030580e0015415108c03175008644403401181c1d40e20002c1c641c1160780c0044440309085c0f08040141c4064009200d4110031060820b001600e4130003505010a22805c581604100074143e400b50703814000e0120944031703898400362080a03e00484041d5071104203110f441100c43c4109902c1200c90030108040740d107083c052014510b41442c0c88012905034101420580e00c1d0f8000b040840301d40c9007142d004142c4048007204802c160310b62400c2000440340c81204050040304d10b0b00080d01c0650f008140c4006596100c180081d0329041080100c0c41c12086800901707000c02d8100c00803400d5400040554403852aa0ba2103004080e15 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 433397131 1250 433395881 433395901
    0x3020309102f0102040b131d01060813060b030d182114030f0c010911040207150c0516030c050c01020c0306070503070e06180103051506040909050a29 66
    0x8003004840082c80618440c0400070002a20342034801d110320005814991030300e4441d030903940108a50b021352880d018003044031000c0c1600018466000740c15072002503140030800f51001c440184608051524817203603000300700d500c5d40061000200074080314012140d0080c080c2c001b10941c1c901900e0841201c0c000503e10609c90400c00d0060780d00e0b203034503454210503502e203c4071740a10809400940814054421100031103400b03000000031100000c1000b5070307075007003490391030551496150107580100104408111001084070154501c407600003034550f80300800711014002d240e00c030415608500c4c504810300d0780c000b1014600c00d004005850500e0404c3c40160307a142c00c864002078142d0400350000d040680110040c580c8401a400c040c18071284d100006284c030780c0700c2d00207480280c038034000b0043c465a16100ea40c1d80004510030132800080040005480340c02144521240540c032101e003c810400e06200003103185602c40305520030b201100124400a14450150055030000100044c0c81022 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 433398381 1250 433397131 433397147
    0x1110a0201022d09060c010207050a1b090510061d062115360a14100303091701110d0506011707080402040c110d030e010b0d0c050402130b0301030302030910 69
    0x200e0a5420f501d04510340c000d101454004200710074071958248065004104144441c101d07080c0328002700c84003919031000383c00030b0f10301c0c035003011003818509010031051440742805a4266071290130200b00f08012020a44c0039094180c4201d600400c0c00b00d465942103280400e0050384100c401c01001490392141030705c101d0004402401603000f100095545c11a0f00c0c4200325499032492106014190074850b1143d038075080c030968101e0b032426907450300c02c100d014048040302d411403461007072406118910703180109080c0c410b00501c0c1d0780c81050700019080c20000d50010703000441d00d06810792160580c00b0f00e800100002c98000740461194001408818142004d042c41904191154501030b21942c0a0000808403c5425001d11403000985043c0301c2c0c04101ca2601c0713950b07560f004110500c40300701d81c03030a41f002088424011101c1010b44000581c40805260a990040d0f60041c0c40c3c1010b04102502d22620340e116003015000000003106165001c8010300d40d014003070303405000c5402e541004a882039 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 433399631 1250 433398381 433398457
    0x1a0103110307030506030a0c142115180f0102040306050601020325030507020409060c0306050607020901031b031707060c080c030601080408091309050f0114071101110a020102 77
    0x40d40400005401c54000c0c1c1c441a0001c0024089a80d0001c0550314038000d0324068001c1c2c071043c46010111541450a41c3d046030007484070511903842001d6140c40716903284056413845105082400c00500724198000308851a0001c80c000c03a0042d4440c600328900030342c8180020b40303000d1b013000c0c009007040d4000000c030b03024080c000e40204000e0342c1c289500002554002d20803130030130204022040160780c2d18019881142c0c0034007c006008411460084c003141c000ea03012a001e110280581d00161765001f00050450fa013000b030350070942091000b500035006140e00028050401040104074807841349025145c0984202d000300400003c40d84154cc002404940c1c1d01107032401040002e442c0d5210310450360f00076101d044d51a04017260180003c0030013061440034007049035500074803010b01c0390800012840d410742c80d00030404c8000d1948003044d0b00e00024240d06c18400c1c2030300820030307098096115400901180f900f0715202d100d65480280070f0b5115200244540c080702090400072909000e0350b400d51 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 433400881 1250 433399631 433399661
    0xe03011d070f050901061b020a0b03090601060206190b0a050a0e010e0603010209150702042007061407091211060a051c111602130f0605120708150402060714011a0103 73
    0x10340c0c40c1c01b4007252103400c90001400da01403121501d9005803145c0350f03018007034a405ca00f07103074407490080d140a2420030164000821940440240b1480000340025007590410341d0b2001f15190010b040402e840c01000c1d880280c100d130a1210000304010342850890580710301e4000c0d508541c0750b803002c05003030303000e84a030481d0302c040b020041581e120381610003801d50301c1c8003900c00700d4030f080c02841c480601d011514a0f80300c00c040008420040113680d00c42c100c100031203400749122038102014001d000170170a0003a08000c0d504100aa814440004410005c0c00310081000359100c8c2d04090080054208101e0141050320810020780c0e4018030b0b004407444104c07030140c0c880c1000000d055071924107006031406c0e03030401c4500040080e1078030240a6040748000c2c160002c2101703883d15003440400d4000c00e114030341c01c1d00414801c0c041d00d100810b1144850500d20b540784c100d5111800054007074494840010304403520020440041641034100040302d408050780c41d0002c2991800641c00d0741c041901c03100039 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 433402131 1250 433400881 433400899
    0x6090f07050120011401030507090f02070c0504110c0a050313080a02090415020403080c0703021503010f0501050304020f0d03270308031314060f190b010507060c0e03011d070f05 78
    0x64001011500348030f000520011a001d40282103110a029081c0c00035181c5404c404004c0c040000240a03413445c1d0007104408600d001025121503420718054014544030700e07160114440842214070a494040c9041c205507604003009141803540c03a4080c0e14085544240a60002024807002c1185014a90083c0c0300e210207070340d607940d81103814000c40070449a841d4280408400301b01010040d102c1c0c807141100a03c40542140100140d00d110b00213800440c40d02000140542911007810208481007802c000b61247c03540d1000a00040d6618a196048211840d48506142d4060310001807440c0c1044002108440034511076020042400040c009030002c00215022400b05030440001702d0041201444a0708507012640c01c195041d110b645444000d0700601029001b414000580002d03000c030200b2002c41400c001034072038001c510020b0511a550811458001e0140040b42c0d0b88650080081281c034456000f4014907880d09501003090f480b40c003001040180d020f20000d170540e800240104a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 433403381 1250 433402131 433402157
    0x60a060f0309141911060f0a0804061121010509070e0d140d0206010e0108030909040821070507030e03070302011e211a03070303050906070f05060906090f070501 71
    0x1c06041110300407100300c000d00844041c402001d101014840200d21000c141102c080c1c14220076030319545524602c10001003080131807441000084400b800964144008156075906000c0002e10b40f034a402110b140700000e15892001400c461450390860382c10560f0000d0342c07244c0a0200142e812110000454040d0121800138903203015103252640c41607280c209031481540c1024140b0400d90350b044090f80c40103005001050b490401d180c05000c1c40340003581480780c44800038074098030150010b40049000900326001102e900d0014255000302707078500c41e01e410580e40c018940d0780050010380009035034001c11a0207140104240045a40507906d980e05c7c0b625000c0c2006071000717034403030f42c3e03081c440101c00c4801c4d00803201000001040448100040c1d01d01180009040c0c400c44403061440781d000107105100198011044d5818664242ca0598070748003d0301c0c01c1e501081d042035001d80b15108440410910b03e0001890610654151090b100c60343c0404544d030382d413020617000c2c280c082030300518404 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 433404631 1250 433403381 433403387
    0x6040303050c0f01060308040b1c0c02010b03070839310b060304061112040c0303091d07050d06080610061808101112090a05120f0304020d02030c060409060509060a060f 74
    0x148841003082042241e218803690402c54103600bc035540580d440d8410b100044c581409007000030003001014051a800c103e00c2125501061a21401f11000e2244601101c1d00607040040c07d814010702010143c0d0b21250203854410010f041d1b040304a41c0f02c041c110b84da00c003517010700c0c4050b0f130010b0121411503c440c1ea0f10005049161342031032031280184200009a00040c01140c025400344841098803030650070010a401c440313800c444106a504454060254140c0a000341d01c01c0d1545801c0b601c07004201c041d00050710346544512007a20070340341170000e81e881c040f42d100c045520356140c0884070108510380d9141ca041d54810240301ea0881c41d000f500030005900003045403140c0107007030383c41c1c00d5036600c2c0402020380036a42250307c4d621441e100e03c1080404c01c2414210305c2c44080d41420041c403c901200d1600c0300a00003402400707040103c404640b0f040004060711140100102d880310346801414000342194803d251150700705601040140c1814821f00c01641d00640d24070f640103070303506026 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 433405881 1250 433404631 433404637
    0x2070b0703051c020340020303040902040905060316150509151602010206060405090d0e060f030705181008040219230117060907081506040303050c0f01060308040b 72
    0x154180074042003141c02c0710518039080743c4244081000143c40b0300301256920500301c8002945c503807a5002c64808030340e011090000c4c074540d2119401c100078211152012a0641c0165070003030326070a00125000c5000802034102034402e02081d000c9560402c1400c0450130800460b109246849182c01440d040040c40360380105103041e805000d6071000c0b901b03105100403d41c00031102c0104420880383c200c00f19a070603c0381726002002200d0a000768182600f109407136901d08101030040c8120706088050540b00c12080c0e5080010340c090b90303074403031400000181075503000510b0001c0010300602d9040480c90400881c64000b02c055481c44895915a0b003802684401d050004100640140303000a061036180319a098060411041080c082d071101d0004d800303841c1d943c400040c042c8103801008810b40f507035164103070310440c5441d2a205c26202d900f4240c104031710300c11685800001c001001303c00d141e0401c0c0106180100003046804050b1002006800c0701c250b400300a2441030100001c0100e00000030107 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 433407131 1250 433405881 433405883
    0x2032506120b13020a030c110d0f030905150105010f02030c2a030105070f090f1208130f0b031806090601060f0e0301092306073e011a1002070b07 64
    0x2411001220004014001c4415000d40b101d03000540d1700c0718a030741805003a21f0319803142003031210401c0c4264007944038030042e0b03e11010440850404070401c1c2c801d42008140d2504042070b41e2410840b03c40403000001c00740070302c40c00f080802240180040c80041240e0b4aa03a5950152002c02100300c2101c2040c01740007450b881420048031100c520340c1c0c0a02c155806a01c0a031540000c00803003040c0035000c02c8444d4000180f410582d68100309805019a11111450703005488079560400900c0c0c40039400955000b01c1654010442c0200d5011140001103028031605021000fa102010250036550300c01110812075a8011a004100c280d01946603044519107900382041050804404a0708403902140305843d0354521403052001c0c200710503810200b410310000502200c0c90700381e00c0545564500601d090210500d030708900c02135941c00e822010bd006419084842140007e0b00081c00380005001400e24041343e0b9802d84010303c0c0c1180788070242c175616006000f21034580f1560000d01d411000c4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 433408381 1250 433407131 433407167
    0xc050f0a0e07022a03060c0a030204030804060e040f0608210c1209151905030c070c0306050a0c0306150c1511041a040506030a0510030b09010902032506 67
    0x4804912071420080c142d100d101035030b00400742c16880e01e08038094218100c9071000640d0030008141d019803004200c003603020740300d0340c405569404c0c4c062089000384101da2001e012400c001c280403503402d0740011004803d41040302e060080310748003000300c1c003159210310074a04140e02440520f60180b8440c05808800100f0100d903604246c00d600e8154200307551825040344054000841c5c81c000d140c500d120941e4003001110050130070600e2001041c5010f170a104031010700c28044000780d000102c80080702c0710558844a07101e14540c0c0c2c1d140c00c001a140a45203141458140030700194000d10901c11541240d902c0d407c0300400d61004502901e040c45100c8081d195025000010368490282c0c2c0215854841e032001e085660300d241000c0388003a40b240d0010041c6660b420002080261384442c1526002802d890000a11381c40701c5045580642480d4401056500700030100410300c1010342c004200c0c503000b64165501c40c40c07028141030504940c00170301240c04074000414009a4402c80c481c1d1080f04c6440 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 433409631 1250 433408381 433408399
    0x40902040204062601080c0616050a060504111e0607020d0f0c03020a080111041401031b110f07080d030c2307150504020a0311130905030a0305130c050f 67
    0x60045030580c0d015410040103e10190304208241d0030b01c40065200c1181460348000d294100180c3d20789035001d68291a128000c040350613030348140c81746198014160300004a461682e00c500c2c040000d00030456007920541310049801d4401c1c244080914402c2443c1900303d401d41d18007904000050300b0402069070810039200740e07031300040c0340030703501d545e00c2c500400e05030f50320614500c100700b802149604500070740d0b4105400101060741280c1528250382c05034800950079100c1d00c0c0103c00034130102c10f05805030605160192740c619007040340c00c1c082e030150381c0596962584008c074003035403071003148a002c1d455031110004240c014400e50147e910000d240c60000c841c02164a8160303004150f1892008002c44006248810024410f6101803245543d08092045250a800081c0b4000241c44040c12503500d10342d80503290f80c0c541412130700d1380c88442c104108001050503c2552074020116020101346424040b4400f4030303c041004511503417017003689400d5414070007800151144090015002a400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 433410881 1250 433409631 433409633
    0x6040b0a06180e0c0d050a080f0706241401082a0406020105190e1914071d0105012c03010204090f09030f090609030b0603100213030309140a090b0409 66
    0x40b038000e0a0280c2d0008002c901003002450540c142420f649206125110006400f00058404104021156002608591a0204049106a80c0c0b04440300208000d16000a011180c400d842003101002502c9595800d03482d00e90200e68040c1d0496020386000c5040203001034080a0340140342940e181c548900b0310851044a10030300440c0e0400d400c4580541d44442c10011060502c1e1070507000803040600a1056681045850390ac5103815070b091a0b1080009811106200f4003800d10040e00c6540021107480c19070302d150080000f00807120b1082c0d905008000080c1540c4640d138100d15040690b009035004403941e03048002d81485078160030360903540030f0200065a907603901c1030080407800100d000c14241800d1a0044c10300380311100d0380061003004981400782d00d5003c0099410749600c05034950141d00c138400002d18010040000421480c00007540c41e40000c0070318010403c80344241ca44401c0f10340c50340c1014241c40410782e03903680c2228038000c0402c10072215401030004148040c0001034843d140d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 433412131 1250 433410881 433410899
    0xc210c060a0909230f0109180210050c212a07050d0f020307030b160f050904020706090206070c061403130305091801091d010203090604020f010519021b06090306040b0a06 75
    0x411a542030300100c0717450041085c04d43d640150341f00c0c0705060080e066042290350004180e25070080501003003080c0850b85c106030113000c0000c2e40c1000c202c52802c0840359103280350409594041d0a40d0100c10400d003035015540d0680100900c070010061001d8814281004c0900c5240d001c600b40c02e070780a90031100c1d44005038600b0b011203005980100b9500a01e40382180b500b43c5030007c020a1030081000500b801c440f4a40d000d03068640d02c840455002d81c0d12140c03814580041d10348101c0c040e40c41030001aa080401843c0c604500444140782c54404001400003a200650700045030b0004019440098140020b44600700500c0d50250041502c052a5990102440400c0e001d0700001c00241e69006010b0b000c0000c0c006882907140c41740029480c43c5012410103071651405007000380240c00e0408041340320382c0550103840f049900c1c800000f4010342400e0b80203641d000080e05200c180c44001c00701c08041d00b4120704481c441e01000e40245010740f550340d500c11940400a14504405944540c04610501 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 433413381 1250 433412131 433412201
    0x1602100e0604020109150f120603080c030c01150b03040615081020160803280605090c04030201021510080304080c09101211030c210c060a0909 63
    0x2a0001807501e403400e88000b6206030080c0c0c00140302c0c0e04000700c01c84030407a884428079510600780d10348800300350b070311507001d00140c0001d41000f42425804240300c00d8154000024100c4005403200034012090b060500c601100107a0040d00020f400c01c200180202d2103a403c0a4080d900701442d8148179a500c00242d0f04200c04628500403160f181c00c5100c0603014003000d42c400f4401c0c03800b12585410080080706508500d1010018429200400000d10401c01c0d5400034004440300d016088000404904c10002030059010b0075120f507a038030010a1074865802e0646094a6040e001401030503486104030340a81c90080120a0028400c400421340c0c14090001c4e00c0104100401000b0b41c498900c10070824101c01024014022a484070030003800c21030b181d642d6005600200c1d040b840345040d41c04079081100002d80d00e50401c4400c446842c0ca40303000700c0440901110f0340e040c0c50084007945c0400ca010311640020600180c000320f0180090035103680a0791040d15a1381e0800c0d01d28082c80d0744200c1c420 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 433414631 1250 433413381 433413401
    0x604030c152309010c0e010c02041b0908011401030f0f050a170c010e01020309070b030901180b0403020c01170601030b06120703050702160503070308030c130f14010e0306160210 78
    0x4400d0110300440b4910074500389070028072100c02801a416507840041889250b091400e0401c20701c416480d0a648540d0f02c114414029180b440c0a00c40d200f02c0c001c0c00705d48071480b54940c03641c030b01a60030f0328540e10f1000e990305890380819242d00c00c441c1c0c7c2d1540012944448010360b0a4011545080c000500c1c2210490400c03803044051520f481c4c603c03a000742101c4a0744819403c43c0d00400410840e4140814007d068400a4604a071039481d0031961a004016100e24285040d10038070001040c81a19104103200f1846603003200e100c001d00a00445e8429030850350b1005016000c004290258000c3d00706440020003d40301500300200e6000200e40403105685400c00300e543d82c024407910b540c0c1400031308405002112581c02e2a8075000109544020512000d0000c48010000c684400040021201482094604016601e440c0c0d10242c50364051807040100300440e040e103d40b1a94010804540045070007805007410765a0340c1d00b80d0a0b070315803944405e001c60141e08101c051139003052041680f14 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 433415881 1250 433414631 433414661
    0x309010f0e0606042405060a09080703080d05010b0901080103152003090c01050301030c0b2a011509150e0a020c060106020a0b0a060e060d082b05010e090604030c15 72
    0x142046404d1000f156100284885044401e18425000c50301c031110680c2190740030388207590b8484c045441290700b4006c6810080307441c061108008140503000700138000352141c214040240da41d070380c0d0024045204104525010030340038001000814078a0720401c3e0325000e12400030070900140080364004000c6000003000c0300c0404000c1c0f128607a41002180302c0e81c0401c3c03c001e85554110f88030040010081e00c030362010309400007407201d80c10140203020481080a643c0130106000d200e05014081c200b02c0e0a5072800c5040c110000603055014010f540c01c0b25004144050700f03d08000c40d144101000602c0b100003e0f408000e603400b10401009454002c01c1c5c0e65014040251591900e481d50f000090039142515041c000140b121318448001c4903042001103400d0b01c10400d440c42e00000600594070a00c0c2d20301034082440340e0400d601554280300c2611410104240c0e82ca0b5003240b420810183e980000c00d034807400000d000070307000310000408180035070000600c0090445203a81a20031100e005a00d03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 433417131 1250 433415881 433415893
    0x20123090105070f0c1202120c010e0609030307090302040b0301180b0702060112031b031205010603020a11010c30020706090b2512020f0408032212080309010f0e 71
    0x52480c00b0b101c1c040c0c200780c2900d018140f5000555000704440005031000d170141901c801d00011450007042000000c0389400a0103403146c1690070124001c00070500c41244a000329000103410300d901000701d034450140b030b8444c000c003e1b046d034080c00020301c5010f408030703010340d80d50368108041048030403402c1041e4401c02d0650514600312100170705100c8182e01c000c501d00170700d0201c0e4000903004440e9060402c60070803076004401903801c0480724044080381c1d4110580c907007400852659459001000c0681550320b4000703800245041c1c0302d08031448500c4100004031101a08c075114041142c2c2c00e1f000f219100c40348140c158004202108982c000300088070030560b5002040200414902c0785503000034994241080311503111002d604440255041c7e82c05c010340411940755a00c7d5981c161035034240741030000c0b900c51342c94500c0c040c0d0f030b64000115108064a800c1c0c01d003030144c5d2109035080c203a85200341e020581072841e543d003070169000540204955500d0f0480302020304c903288103c0010a15000041c00703 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 433418381 1250 433417131 433417141
    0xe070c0c33140403080a030b090a1a3703080d0506210d2601030f030215090304090b010e100e0109170c0d0f0219030308010603051510020123 62
    0x28000070000103401030050300d41c2102c2020305031200741c80440390400141607a4204c1e20a084005151000c2c0c010b0707011601c14280460450a5400010302c02c1d82000600c4a070b1000c00c08011820b81500012104009640005000180121008030b1912a069814901d141e100c0e40e9504a98201d601c003000c0f01070359081000081e151940022007070503110094107280d090001c0515858142c0625104140100030003603107400004603501035594624009800d40a5840c1e00c0c002802c1c0c000d03e041507005120b000c20b0b0041100e00d00240d0f5000d414410010752400380b621f800b4001a041c0080028144101c00104020984070845126941d0b8415621151b06010010002d002d4818030342024110f40301c0541c8000040c000010011038900040703c540010501c0791500110084401c42c0094006107500301100b80d1000003410142545d21031786a120140c0c1e281e800441c1199000c0b2041c1128004050844c03a20b1705081080c0c40300b4080920010600340d01c01c91000907819180003e0250304510300e01004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 433419631 1250 433418381 433418459
    0xa0902040503120a031d160504061409040c0906140306011a0703080c0d0509030a0f030b010203070308040f17070312150302190305070b0a14040e0c0d0204030b07080601080a05010e070c0c 82
    0x4028123001c07602040410b091010b064002c1d00c0184640d8041d03442d000108041c0205c2c03141460080080003070074071030240c0382ca1300710070407152000f00f09001e44104000450281501d400da0405640e00942580c02c1c02002d031011156442e003e040b100d04c000c4100072b0228861a54000d03180300d101071000035607590001402c01020458030060080c101458124107503e02e03030b030210480d04107941601d004000da40f07550506d01c14484a0501c002c0201150204400c03c01d8419009032030f009000b034480006864840c01d1180503a0000528824241c88000044c030051a14818070105c00700c0c501c03031942140da1240d0301c46150080329000390701c803080d001c01d43c114400c2d80000d0f010520083c3c0c902c12400c051401b46241d1130824060404040c2410100b29200c103a1400c0d41074800864000215200904100350040c0500006407001070004038400c00160318681030380180c0e412203180304491021aaa41c0030b046401a81d0fa810480e100c02a150000450060b000313080d5091440510148000c0b00c8403511030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 433420881 1250 433419631 433419673
    0x206071a0907080d031509060f0e130209040f031701030b43022a0406050301020a1d010509030604081b0706090927060b0a0902040503120a031d 63
    0x40030071984034200a00c004400490051242c85840c1008518100f02032460004480075030800d200f0103213042c50025004c0d58040d41001221906a02c20b505912007090840301c1d4100c411003e900030404101050025030380c1d00b403460049009180151800d95803840f010b400e00000c0c1e009442c644280d00c28405000d10581240098420f8202c03208150181e40010040c201580700f020b05e4a19165510080118028099507440740c80c0e0070704070a1414510400000034009004105000d40c1c5021000300306401d05108403407440000b9101c0201c004040844003000c01f080d052500d0400000780891001c2ea10204842c9020707922651040780c50b8024201d00c13608410003d44500301d0380e4003075a01001410341108107041501d10603007020549221003901c00f10061032140d01000703401030340c450b00c20900800d5440885040412526800e0140d41c40c254441030307001c2e50007402e5054012501100b40d016642c001881c420720a0705010420088040c2e80c0040c45083d003940049a400001032402c0c13441c0e6000103 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 433422131 1250 433420881 433420891
    0x40b031005040513150506061c1a0109140f220501080606010c02010801060e1503090604051204050f0603060a030503070503120f070903030c03020f07061701050d0b041e0206071a 78
    0x1213882101807903252038004000042480c0c41c10b550301c1010403040d446040c00c4560700503102c01d83d45004c01416007078034020100940d00402d40400440c0b00d44803507101b20320b00f20458200c0304a0050100b15070003005601718106000e90740c41207252000c0b0480091102400381440b0b80c0081c001100d40c90400b0041c10300c003004007031504102c0217042e84801030782c00c80f11240c15030743d59140400850140a01244414101c040c100d89562400b004116280400264141c0f00c1c0d032250090751900c511489240f02e0754041e600450368021011681450389080082c0035661081004000e02040c1c2e03629140c0b9800d682c40740902340c5160700001801c003400002c40410300d400c201414501a03182c600610010000010307400300400b001029a0a881418401c0002c1a104410300080c3c840072581c450b4041c280e10b000384039550420421400004e411f2821360f000020301600301e61806690f59480e43c0311180c1d040c1e84d00100b500d840554078aa1701584802000c0c02c0c0703017841055011150b560b0100800da20240c0104 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 433423381 1250 433422131 433422151
    0x3127020f040204081519090c03110a060e010c06020d05040b011a0304030203090405090a0506010f06200a0206130902030a0203040b0f06030a060b010c151a010203030c040e0c040b0310050405 83
    0x8820084e20300001040707076030074040413140e002c20f40b10040b920303a0746c000d005002a142400c00710902d080c0714108002c50100c900c580e403085496030100052001c0300300f15100d114013041c018aa03860340d6502404402c1d45542c4100f10040c6410449800c100859005443c1952401115401400404441c11140c8071140022400314103510300341d90000c0da2842110840c40c0110344a0380862102c82042004000c11940107050ba200c1c0d607103800540100f0030007403052500042c060440b681c40c3d00021244074120300e10280c050030101c40c442e000c0c441d140d400101c004101c050300d84000184801940301441c0209161038000d60350742890b0510581090006d000c4202e8284028240101035400040306400c0300d9110710045244101c01c0c005803112076a80102400c400200c1d0804600c2c9506035200080307001100d943d400845448500499507404100d4544003104420082480450100c2e1000ca50201440340c5007450a80c44071003414080e001540c400c80300743d0b89940c06025501d040d000c1c031540600303004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 433424631 1250 433423381 433423387
    0x705070312032307200d030b03010b0406080c0f01050f030a1521110f100302270604060c1104061502010e01020a091e1508040b063127020f0402 63
    0x3411444011502070310721418841c008100b00d000310002050f44141551708020744009030a40c000141c00740a0075250a4403951030074072100e011b480c1c50310411055401444c0106841003100d001d0000452b03030405038505020041c4010b5410442d908021441601d00c81c5000c5038032450341c0b41c40d070f840071850b401031400c0707030b406001d0a00d0203c2e2403440c003424070303802a10306440e41c02c2d00b0020827400609048115042990601c178041166019001400d40503125005001206802c00002e80c51400081d86264080001c10081141a200380c100d401441c0c02203079420a203142c260000b400b204c1965010842150400c651014031a4081c0300721036522242000940c0b5005e0313150001444108a401002400c000710510754410340400040840603210503201e04c5601008000054204241140c0880d08191784000044032421700c2d20046a0090a1210080780c00c0c940c07460749100c0f400100e012440480c0c2d00c940002500e0038950315200030080000500404101d5030041c8031441c0410040785014074010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 433425881 1250 433424631 433424681
    0x20306011205120a050a0c03030603060e03120609360105010312230301090c09092409020f070f02031903121404150b030a0f081b060702150705070507031203 69
    0x2040840f5011b524030b14017403241004e1464160020072003600003410b1149401d56220304040000000c000360140d1104295255a8003000c0144140c021691200349000407901100c401c0b00d903c64010030004403803010b6851031450500309003110000d9009075015035000c03e01880150b00b1400d450860340741036101d80b42881c1d00c044a12614407040c4521000f0307030740d12920700e045144220042000790080e0341051041550040b80e00c1054100c4200d072070b80707c80d00201c00103004c40e103510031100071015851100d802c0c0f00094445001207d8402c40c1681c160045042c400c1c050603c041598001a2080d110b2400350300c044840d001c11544042e886401340c401d43c60a001c0450b000000c1c02d6444850f0801c0891015103550200307080c07084c0404c00a189100380c045402c208484074000d40500340700b0002c81000b001d5088440d40e138404041d01c406026030070039000d8405400c0700b456129408003080c2845072609036a50b840e1403516445034800e807a02e246298103281c1d51a80b5020f443c10314102039208115480038 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 433427131 1250 433425881 433425887
    0x14120405090601030b22020f03090304050a050118090522030f0206090c03060105060d1b0509031c050304060509030405120105090706020d1e020c0d030816030213090513020306011205120a 82
    0x1b4106802c42d0032a840d034000400d0940d90f0b01110461403242807040c0e1a82440c80c0c1007540da400501905224110001002c1442c0d4802c8900a003402d40102481c1d40b030a00c0c000d511402408050910418505044103038108120044104017805100c0d5890302e00c102c0103101d00904201000d4800040340d040110342401c641c3d40003801506650040380c00d83da45010503c8807070010120282d80d0340810021345615612141c21801405009100342c085d51501c030ba91403000c07103880b00c060708114003003601400414081900c0f035106661144d90682101d150a40f41c00000b41803150b000a2141c1da69100c100300201c620060042400425044c0003c056141d07400c20043c000010b0580ba234803002c0b804400c0818400d10800054041c07440140c4100400451400d0080c500002101c190b000c122100a129103014800d108030b4488200701c403402c4c45070310b0511118101421010303015200e05a07181031000003503a03040c4a964002d1202d441d200c0c4911000e89445401e000506840e0a4416001d200b002125a0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 433428381 1250 433427131 433427149
    0xd08010e100303032c0d0f0e10050912190c0e01060507140c060f3a0905010f060e1e07080403110f0115140a0315020714120405090601030b 61
    0xf9250401044400303100c0440c80c0300d4100045071031800e0508070011440303003d010614000a40103035130303507001400c00440181c840303003c2c240f580c0e40c1100341400643c400c64480c0c4080c1052001c02820011444000510759141400000410a45d442b0a0558100f00911680150700030a80340814a0b540c4d8507201c40500f0500906e00c000d0271020465401190b400d80a00c9040089007000f40301944035004000818a280c000b0200038000c01014011082c18210900c159103c0c5030807212400110341c080c00910018116504048a003992038200541e410003c500400c07000d00481000c0840718903091300a1030340c800c1c7c2d120301e21659500031024032044030f0340003000a51190301400c2120001440c0c1d00b05900c0e1814607000c80341c85500c0c201d07000c8003540741005004201c54070b0790a40b20200320404c04005c00e0300c0300740c030008020110204080c0351000b0039401038071120b402035209030006606000c003141064a0b810170880d42e8000045c045c03241c0c2c507003a400160810400c2c030b401c0003c51000004983c01803 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 433429631 1250 433428381 433428383
    0x40203030405150d06030b062e03020d29030d1b02101202030f010906050a050a36050f0117060708061c031706040207120e030a0b01080d08010e1003 65
    0x1228024005010514404907441e040160804100c030070ba07203080440c901da07c01d41d8840d00c00d0400b8403665900c1010302203031005c010300300c210002040740707102e409800070f504c40481c2001050b110080d040111030a80d0301d980201030001c4c003045296413032404050800300c0310348114081c0401003161801c12000f0310b00015072541d05035a186914813515a05980000d001074081030603d0000003006030448000b00e00b581240d21000c030501c012911081001103c041d00c2c003441d03400840910040002c203013041d0b20b11b0b0318000c2c2442c070600304001103880010404038054100000546034018040c4150301e21001034010420905880c0d4a056000d1a20751208000f403c0c8104000d240307804942c0c140d481d036a90007400300540500350384917a1945409080c440080315403c040d0700c000c40001d40385040ca4000c881d4110351065825800f1801840240e403100404c55265806200d0710307014000007400e500c45a07001e804108001c2c0300c0d1510b840001440b04005811900540c89000140300c040080c07038031030006503 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 433430881 1250 433429631 433429639
    0x10306020c19150b06040b0a0806041d0319020705010e0103020a270e18062a0708032e051e0607062013050d1a070f0e09040203030405 59
    0x8207010314103140b4100da4032000c8103500d5900c455140402c800724900d020706004404007800003032aa20f0400c002401588a0201421420088806454410001c250381700c840104002114592a0095000c0030403d688901c105d40c00000c403076483d1440725500010000051006000071810840000c01071010506018103054001c1603285100d80140b40d1100305400817058001d40503080503484d0745280700e610406541881c3c490224240300e11b0042c0e010010f4200c50300031305081e1120034410031403608420000c029541440be000e0a031048903002440402d0043d9a11034803030030111601b116101101d800e0b075400c071820f800704840344401803e40d03000300d940c102d8039507005004100b41da050494001c9409a8808000078842c0100941584040c00403400c002c0e40d40c4003150b00c00104400303841414101c4046400b200c0d81000a880c0c1004030141d1641300344081e0b00300b400030707148071901e00109a0303405000c200a00303214410541d0001c0b80c0350703211f80c00700c0300c556403030400e900840d4480c45140900303030103 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 433432131 1250 433430881 433430887
    0x619030b1e0307090203151f03060801051b090102151009060519091a0301110d203009150603070e060405060415031b0905150d0201110a08030a06080102040b0301030602 74
    0x5101c1f20f100e042c80c0c00c01800b07450380b84a01c010320401c800c240820b08015021034501000401c003080144609031280c1716504c110213064243c11020480c5402c8035147c41d046101d1010020a4a50840086401490845030400245041212100035513840344c1001c0c1c0107058000305c004020705000e0047d82105d000880002c0c801d030008465201c18040c904001e5015801c0001128101c00c644005110b2104202810460308200700d00240403030b20740350100d0a034039030180310740340d5440d41a01d1404a0b43c50301c13204820048d41032080c8400e10403000c54a146164221409144081101e4601180d00410842c05803c05a042c048110014200905050700859a800014006031140e600005e012000c01c0b1802c0c0c0c03031036502d2400c52400c0b803401404000880303030844001242d2905000b00d5028940f052501512590204c00b031040e000c80c9a2070980c100700c1e0480081100c814107105001e2050701a00c4081e030f0700d1404400c0a815510280c0c040e40f440d82c81044104684c604250649056951052002d66 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 433433381 1250 433432131 433432141
    0x50a020c120106270c0f020a1217010305101a010215090703061d0106080703030f1d0604090207030e0604080d140c060106050a031406010e010e0619030b1e0307090203 73
    0xc01030107240c04c8052031100503051050107030701c00c500071404031100400c103000c01c1d40c400004403486038076084043c0c0545d0043ca040da00051300e903c0101003146203854000503060398010107034001c402c280d00644068000440740d130b462070350601403450040b42c84d0100004400f6281c000035615040b81094002d129440c40206011079400e100f06130081d5008502403200400003509000320024408614100e9864003400245000020410100b26a0561565007908841160540d11401c2c0300c1104207080c00305c00d8440d0220380d942805040603101c11440140c6424042c0f4000d441c0d12481003c6510910080c402000340c144001545041d000705032912051003800b8001503111070044a10306403241c0503c00010a4069020700500301141040c2c4c0c0c14450036460304010041c00d00151040c50020b51540b09a403125405a103000c800510301030304540c5410800500f60b40400b41c5d0040000000c3d80b125180c4000e445c051800c15916041c07010110074901c0303004006039030f4038441d2040f17090498001c40000c0c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 433434631 1250 433433381 433433383
    0x40b1603230702061b0d05070c06061401140c0601031415010e0412030c0e1203040306020706090b16020a020907031b020f060c090a030807110303040b1306050a020c12 73
    0x255042104003000e0354071103446030041e106841200c403000140b103500c0014a9040d076014102c0b9107a241c0c03010041c074106002c52030720003400e00101804140701c0884072030000282d19100d04402403001d030900c1c2e80a040e00900052107003200c00c514506005080c0320300600c90101150f000e04490340060147e0003000840b142c0c81c208031082d050302141e0503c100c00000d004100807501d40c0300f14418520081700d0028405c0541c100c1d51444000c100003491a0184056800c1007803402c20000003d8003100c1c203245c0e5035951b000599104c3c810441c0c038951503034410010030407140600741d04186403013411000c224081e0002036035002003100292080400d0004506e41500030344c018001c0048080480103086000d15020b984ea00300450100700912516000400b1056120141c2c4c0b00400002e00840c2021329603141d0340003503041410207403140c1c1c01111181c50140d808000800051000d0070231940ca40d48075105075044445c003540000e007030000400c030402d0340c43d50201d4814501035081300c0744444800f50984807 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 433435881 1250 433434631 433434641
    0x201020a0f0809010e04090b0604090201020705040c030209090105030c150d110c0f0616090b13080115080f0c0d021e0a140a150e0d03050c03070f0515040b1603 70
    0x10308060100c100690030300061400803c4480003e80b40d2a46682c581c405101c2201c1d0f000c10007a01503080d801c04078401c0d01e4580c00c1548800d005104580d1080c1d07d403030020341215004c0c4150004250300040c3c0b2205828a0b01d071080c018038044001d0a40782d00604040307900b1454006000d0407000b00042c0c030142002844e0301000c5100d680d580c1050b101e140e503500c0b15a42e01c9989039484803500c40c4100048200000901e4600300c621155140e1130003514140d0103a241d0342060380415a80d004154002c10914002d02c22800451542d074185499640341c02c00c2070341481d54840d004004d0340c1119a0007c0382c1d4031020b419144c4d046c0d055402c03440c1c0710003410b4940c4841a0010b21954401101c00b00025640c12500c0094444c07c1e0444007844c242d543c5541d212103070315495406401084010303800122501e08010444c104a0180c10103c0c40c18941040007070440d484454111000246070f606423080c08010042703502c1c00f000c003036501401d6041540700d14050302802005a00e450b0701c44012940c041c0c2c071907082 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 433437131 1250 433435881 433435883
    0x3021e01200a0f030f0221160f06140f0a0c1d01050c060a021c020c070618080a0c0611060f0414030f070c0905070804031b0c1d01031e110d0201020a 65
    0x7011800f00d02d94a0000d008180c0c0100001c0140720310f143c202002d0b03030b413a0b1000725015092400345160025a080101c519103043c0016a01111041c00c803401007000d0307000320012881c00c40c00d0321340d0b18984800301c0a80940c018010700d144c10f1914210f484515002505070401c482c481400c0d00102c06441c00484441c810b051035622341d070140b0000d0040421958000d481e0758001c0d8180e40e100405089500b0742280a1f461084201e076100c0c80b42048280d0052186048c0300300107110847c40c65072210316480c43c0c00d0001c581200d0700103240c44200f002032790015001d859a1003c078007500d0203080000740500c10032009080941070760908080100c1c0c2e41c004004a940090384001c8260311070306682000764441040b44203440402e42800b0007e0049031003144981d1040346e042d2901c028001583c120b09054403100c100460b80d400e011040801c10ba40c80030080302555030816103035070096040d403034000c6640aca1100400c01c11080110034800091104410300d00340903044d100110020100e0004031304d04006040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 433438381 1250 433437131 433437143
    0x708061522081908120403090b0705060402040c0527191214150f040503130b180f10030203091905160510080a0902120607020703021e01200a 62
    0x81207081c03200342081c402044404070302c203940e0142e0181c100e050141031042d00040c14002c0801a54407444214010542c0090180c82d1018903142c641c8091030301d55000001c19030301032b40901c04000441c0740070300641454412a107003090904504035007882042810f4011030140d4940c07500e00859580b91041c200c41c500c010b1030500200700d070b50b4035440765000702614015601040400102080b804000500106009500103101010344d5a451294010200944102c030640000c0000c44e1035058100c1554000e400c20364005541e81459818444000d03000c10320b118040c0400e107640c011142d0360745c0c024581c00d4140d03007070140e81c903510400c03c2d5080456601d416a62940c0b030141480500c040040d040c103101d440c862180368819194000c001d0341c1492082d01800242c0b2842c0020960000c80d0080300c08248046c00c141c90442c041654141407203001c5a40000592120b84100154035010408005451035100e107440c1207201032000900407248401a03000442428a5910007070900b007007800999070300300d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 433439631 1250 433438381 433438417
    0x403050610050d3201360c120807120504050117010305030d0908070203011d0f0c10120e0d0e1507021008040c08060a2c10050a021b0c0102010501080607080615 70
    0x10031401503401c3e400c4000c01d1b44144c0014809a1948216016500243c010300c030380d00d80314034018580000c0c040c00001104c0c46042404480009440e6900b800d02c503402c0340c1c48039510743e410440010040588001c202d82240b011100402c0815004001c64282400724080842d10309101d007044800f40c460000000d40541c43c000311041d91510507d121403c00d0359641c15940740403d88201d01d50b5031900c40c2c29841e801140c4a1143e20164040c2c1056141c001180b84003050b1020381e50303c400d0410741c03041c4211000c900000522480c6160610020505005500b0b110f824002d072500418180880300d0108014044403c0100c1d0500850880c000020b1604904803581071812000c2c10b0058103924401c126036201d80c8645100e0703d0040050680d005250b10700502410301405007400c050310740a880d9004042c0e00700190100e41000348801c000b0100080000c080d003403c00d200080c00c444051340445141c0e00800e050000442e0300c4a05643c100b03404030748100038040d08404d003d016104000100044084103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 433440881 1250 433439631 433439651
    0x61e06070503041509062f010c030c12113a020d050f060609041a03030a050405030c04230406180b1014130e0c060403050610050d3201 59
    0x10043c801e40380c442005024651504009a0721150360340100e00101c0d010002c000d840b1400b000c8041103205002c02c0181072035800100303481c00c44690076600f40000391201510100703903410206004050400342000c2041d00d80c0141101003d020350505e094100c0c04003e503029018011951030009011014a005025583d40d9134680096112904803103000e824140051441c10810303042a10070500a01001d00e0683c3c42d10803c00200580e0003a007184200700080251192030401c0a0310300c0c03540507101c80f40d569040c0401c0615004104c030035584510b09188554a900c003009403c2600701301031201c0101c01c2d81310382c604040581881c0c004c1101d12460782510700c05000010b000340303010b02c03034003034807000c28503220303003941d90421401740c8181d4000741c4000d91051003010b075900c90300ca120841c40588090883c0f0000041032a405030740240d40c142c3c001e10502c007204400c1d080c8200205412548000b10044641d03903044070901842110068501d407000301406e008003810721040f43c0f03403240020022a018 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 433442131 1250 433440881 433440883
    0x30906090303090a0f14060301060e060306010c050d09090f150612060b0703080a0c1e0f020c1203041d060a060c2a0f05060c030d0e030c030301080c1e09061e060705 72
    0x1152180280304980d4924186035810947c003100e05031109907940d404003051000038040a9440507040b241004400014000070940900c0203102c0712800340d85402d185490040304100741c40d03103800311116140c5081c0b40090340d13000e0881c45001b19201400c02c01489102c0120707000003801780b680101483c070b60020720001055440503446101c2c1c881c5a400300101c00701c5d00c40840b023505103000307241e05880406009454071405548a00c082800b20300c100c80c051528000420581c1e001100c1442c003e0703101007400e106142031106500c110013421500c03e452490f10380001400701840d480b91000380100100c3d0403051001000f1519100e0816096041800090900d0002544610f220300d03c503001d03c62402045900d0709000326111407086000550602c0c68403c00d10008103078210703800e12076100810000340d885101f4000365000703004030006400d4013032a4105101c246445114070081c080c29550781d01801da03840e00490381e045402520b6420b80c505400769000e1038620020105640542d02050180030448 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 433443381 1250 433442131 433442159
    0x90918150f040201140306030c0616062a14040e0a0e01181203060b22050d050102120609131209170c0a0504230403031b0c1205030702030906090303090a 67
    0x8401c0c0d9405049031114072151740580800c2d03c05950540084802c01d515180c44c00c080c1c004230b001c2d103d0034030703904c0880d40e100021181003010043c13011b020000f80343c00e040c1c20380c4140f004150b46030074103002100c17400751140c01501c100d005000318108440040354240d09158070000b00e240310400200022502c8441755072280681110840703803054148120040c141c8a4081ca204403048488091f040c03210404851050700d1070f481c0f0034202c3c24815500010340c1d642c3e501c030521203903001e10001039481138503280705110840000c143d6401900c22105002080d60801c02c11075881d60008189003c4580a45044400e40b1950780804859590a6a0620041c001099580500c00c0894400d55103a540d03509120030740e406410286040742141508803010801800c000c0d81c41807007840c00080003100f0700500d184403101403c481000980001000c000c0101100341140700f51000e045c494110300e80340c0002582c0b03201d01c038085401420003040d248680c5d24104255507140390020318090f555078903140c40040402d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 433444631 1250 433443381 433443383
    0x10605220608090715050708090d05030f07110a06050f07022227050a030c06060b030f0402040c18120305040506070b0603120a05033c070f05090918150f04 68
    0x20113032820010b00c00b6607000e07910326281125280e41e8241240b54a801420750004001070790840c81c818500000a0810301c0108894007601c0000758440180342410b004600400b83c123940130f01b800d03120520084d60420240c90386109400b040607030359500c44c80440d010010707002c566100c1591a20354041d00d100c80f900311381d44004805100d040310032594000740c1c03011200b0341e2014000341c0048e02a54042485800140c0f031281c02032001180095484080001651040320300703900000100040c001185042d0043c1c0f00342c03503094603001d11050141a4021040141440b4000043e112407031010304140c040e900f41c2c0c008000003002c880d101c0d00c880c2004400d4600031248a0f2003800741550f20700c0c0c000340b007000340d0b4103416890340c840d411950b40c2491aa0071044800052480030001c500070301e080b60701003d0351040c2081d2004181002d05101d000075144802c90a00390f01880000c7c0320b82a550b03219100e205a00070b180c80c05140a440030340a14605113001007841d0b0a00a4481d0200030380746500d004128062 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 433445881 1250 433444631 433444633
    0x50a05060f010e1c050f070306021b0321191107030905061204151e06060201050a02120a02030717090c01180e060d0206131e080d020601060522060809 66
    0x100341d00c2401161203040c458034a0341c1c0b0042c40b1030212a43c00305a2003501c8011720810072a004000e44440351803070502d40ea4030490311103070002101d0010154003081e08a005220314001c50400080c0741e40151101d410150380312120070448005010b2481c00306050300c002c004802c00308080c1c07040c9140351040368860242034000c034200240020b0a81482e00860341c5560308103c1d40d1301039864a80d5043ca0040f0781c000c0c2e07255016101c514207841c0f0a200903010b1031051043d072000804034a0900064203461004203401c9899105228161003080700405035981310042c40f0340180d50356a180001c0e5080c008070710740c0380440100041000158203000803681f00405003603e03181e4401140040412400d6224001d00c0071000c010030102d00a4105100ca809041d840200054181407066990380d01c50360307565006106a64222040580d003441011000000d080402d000e0001e003a403500c800b960340c41c41880b61404001c0d00141c920007030404038590302c441e06003e041c000210350b524030b00100140d40c10b40e001e20342 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 433447131 1250 433445881 433445899
    0x50606030a080d0926070b0a060803300c0c07050f0d0201030507020a02040515042a05030a061220030106060f0e2106100803090f0402090d0204050a0506 67
    0x20500e00052001c00c1c1950003400180b4000702d100048014080141085a580c0101e00c00030700c1d2640500301382a01404100ba007542c0710b01482c02e0400710b2160150000b8452460171605000c446804070440d5401703417007050002104158002404000007001582946004806051005c5086454024007070308400c3c8045410080c0c07508108540d04c0210810f00d5800b000d40054640154041c0d0841ca500c6441d6006440401c4440d4001c98141c41046a00c08444070b246000300070075141a100310108030740c0e6080d000019120030301d030b20840c100c1002c03108000d00502000180300c1d42201e402400c040c015681280088100d6442d00100c42144039a5001585101d031750701356401c0c18140b1440003110000c5e6250000c0c10006c0d4009d5900082401e0001e82120800140d940307203000100d0500c01c1410a0002054185440e4644d00c3c0b038900c040e0041c800c0d507002003000349503130354402e5a8034034120f00c00c0b1001030740d512148001424038800d040000350454203001c01c0292042a962215100c1e44c810368070405 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 433448381 1250 433447131 433447141
    0x9051f15080d08190e0105040308060102190b01061416030302031009090f03030e0f0a0b10060504030c150c06240902160b070512090a1b05090a0e0102250506 69
    0x901c0350b100c0050710700081d041100088602d01d20400c4080c4051210400181a9581403241360941d0011a410b0f408190702e1800e000d080c0d6410071903000700214240c90450461b4050b6203038042d03400e041c8110410007095030030340500401400b00b160060381400c11030411410081c80c01034041e4008541d581040b00d1851800a042001d601410b551564005c0582003659619641030340188020014507015200d14414499118410001b4503034044c06031008142c9803400a0446c0c440c1034143d0000c0c13003008010b02c010000281c09030100300c20380b00c00c41425605142000c0c012207040c3c0a181001d0300362800d1401200200c0c2c400005085042024140b5074500c40c0c44480e44c80c01c1c0c0c0301d84009415010002408000401c000450300768221040e49000740c58040c1419900f2400c3c04192000394140e0010081c5500f0071001214400303000415603c80c090441c0380400040385242c000b040103c22646822811800b11420340c111110709900d80022001c00048c0788004800c0302c540c120886280c424400031903 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 433449631 1250 433448381 433448383
    0x15020f0c060c0307030c0606091404060609020a0c0605040510050a0b0f01050408210712120b040b090f040c0b0406030b030c09090c0d08070f0303020a02060a0e060a09051f1508 77
    0x41d041c0d6150b03a006510b03107600c9940455440c1c0b90104c0664030380790340304000309000085d8000c2010303d41260325440d69600741401c01c88101e964503400400124810402682003e0308240d0014100340c010400140c1550b031420030038100344502d07406040c81442c1c441007201c0c00c515903000c1802c1c075100b550030440404505005484a202c2d50184e13414a40c45810200c0811a0145640c04581040381c55507090200c02d40d9804210b10350300354603d02080766461a058140c180b403103903c2200104450a0060280c0000855001e20014105660004000c0001018854807a814a000300111030b64559282d6490304020010210440c0040c40b0340234a03d030408152030310411702802014804046d02c07054002c2d008010030001c2a0100700c40e108130902403032012501d40e5200d0b051550207500c01696030503248a000781442c000408c1800d0013490051004410f07103000804035804520144c0004044040d030502d6840d007480c0d00900784401508800100c50624150464020303200c0d01320412112a845d54582 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 433450881 1250 433449631 433449637
    0x708030103060e120f0c0f030403080a02300703020a0b100f06140a0e0a030b010905040308060306070e010e01021011040302090702030315060a0327020906041413020a15020f0c06 78
    0x13160307680c80500c00c00d00100f5409004200d00a95002100c1d40c080c010a03010341582c0242e8404e50703076072201003009080c003178041c408075804010f0150005441c0a980d41382e00c1002840007041030000401160f03002c10140200f014a032101d8020200c0c408600d0150007480c01c00845000740c0c2030814001100040440c0a8070031000f0108035080011709001d01000d00710b07049161030020702d900c01c2000400201041101e881c4501a003010fa030b0114141ca0300381005089600042c0400b4040d41c841c808110180e54071042e05600d2903c2440c05001c00164540100d10b083d414440c600c4501d80761880080f481000308004100b103034406c0d07402c0300b400e80c3c400c42d00f13903124041200c004507426402c0e0f480fa055841c0c000c00400c0c81c0126400c0002d0602c040002d82c8181c0382030301200d41c9008058110034429454503080282c2d0080e02240c0a00c86c04000d440100c040703030000f0384180300c50002495500c04654502482c4030182000302c091500c0114010402581c489100c00c00d02c1040c0a90b803200b100500b410011 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 433452131 1250 433450881 433450903
    0x18050405120c0c042a09060f09080c010f05041d01050907230306011e020f011a1c14030309030a1101111c0f050c0705070b120121080708030103060e 65
    0x5000f000301400244005802000541c8400d0040b540c5a0310210110b9103901c664900c050b660090303018181403018107050300c030740461024050081e83c00c1100e520001070001c84941c0038604110320540f00502507805d805260081c6c480c5100451100e4400610342c04524102e40303044a04c440542ca44e140241c42c0d02440000c85030380b82d0b486a00b48107600d071090b00215006403040c0b4105840000b54284040d041c4001407a40005030412107203008c82003000d0041d100c0020600e000c559900744550002440e050200d5609012400350408130000e2000f140210440d0b001641c055075903a00d01000076984070b0303001c209000003042d071404501010aa0504c0b0719969030351851041440c00d240031070250215860050703550b010b0341d21102c010900c0c0e9501d000c4c8074003902d882111140c0b240d036030b07241441c2840c0c181d8200e80c900000500032202115403803440d2a04580c020010f03841d8080b445007001c8105006841c01500482c2c000031418204481e0b200190304903402104100a03450b95a00e0301c2c1c0d00c0d441281e01c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 433453237 1106 433452131 433452133
    0xd0905010806220e0f0a0f0c080a030912021c0b011505120105060c0a050115031e0201080f0907120605090114040c140a18050405120c 59
    0x4290011401c940c80383c0288820000b445840d0781e440072141e40540c481d410580e14000a10046061002003025100c00d4500d0781402c903003e02014004507401100480001401134002c19094002070707066440300d414a207000ea03007042c400203602080e64000e0400102d41e003e1410140a981c04521038040c00c041e80d032504044003d00010100940b003401000c10601c0c0518242c0a01141541d2041381c070240c845808500d641d02e068a0f40e000208150f00e880054200c11040e294040701f101e100741001502081c1c54848003c01e02800c100007400300f21b014000c5200440e0300380310117620101080450f41c0c0103a0b00c00d450003113040746200549460b03a440c0180100d1407006e001d040800d25405107203040904180e50340c038480c480c1503c1940903820140395038200680e5100380c4100240078641d0400601600c0340f0307400000340400d881c12070f218801c00d11004106000a8141c0c2c0300000508 = true := by decide +kernel

theorem cover : BRFrame.Cov 433273381 433453237 := by
  have h0 := BRFrame.cov_init 433273381
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 433273381 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 433273381 ≤ n) (h2 : n < 433453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
