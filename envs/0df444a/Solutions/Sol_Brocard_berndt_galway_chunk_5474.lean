-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5474
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:58:47.125995+00:00
-- url     : https://prove2.me/submissions/3293ee08-cd07-4cde-a9a0-6a7e8fe14294

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 984352517 ≤ n < 984532374 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 984353767 1250 984352517 984352529
    0x60302090118080a2f0d0305070c2c0c0f09030c0604030516230f01120e0c1908070302060c10060b0d0b0f010804151404121e0504060302090a03060e011401 68
    0x804414805c0080d6a610020b490031510614401001130105030041c0261070419411080380000b456075111152108096018000030340703030558609041d1032048003242e0380200e0341c540d44103003022441840200325912100b4bc40394144201e00d00288140d80d0000100090351250300a4000c448245002248218241d0002d000150034420306100881200c68013881c2c2c40c01c2260050564441000180d6030f8603400d14803ea2000e0400c13800d21182d543c00603024074103e03403d54409400c0c02808514402013040c0703005c0d440058029a6040015142002c041c00e0712260881c02c0d00d0a40c81d00320880c0d41100d880d0350000c03140510104158580b140e6601c51400458400d0380c1410304101050300003082103c000300024005954050060344010880c1e0105c6061218001611020308050811940d0104003ea0200020707803020f54404404c0308001c59040101101d840c0c41d400c00f8100f180940280d0403d001c0345d508411100c00c0013001c1400d034080c90f100c840f484400002c0d00040c544e9850003200050301300b8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 984355017 1250 984353767 984353813
    0x70e0408041a0c060619030b09060906070903020109170106170606010f05030408030a0504050304090204122003030406030c051201031b14010c0602180306100f06090f060302090118080a 81
    0x40c41d006000441c02943c441001c885d141410440020800c6c20301c01550070250418032039004104445e01c00190306402001c40c0b4013251242d54030468100c5070100303980002400074040000402c5034169502a1008020030306002203003154a030a41c85160070600c01c084a01e035848a000c1c4529940c11100d281440f00d511b25200b41385240c00c0d114074655200203441c500340305544000140034414213006850240070110402d55841e940c90000401079801c40c001070301e0200c551020001c0801c1c40561a02488001502543c10b151601509400411500c2081018014204110011004000c460b40e001e14420f0b070400d41d000907040030300950114185c002c01c1c0c0b01541801c100079540e03080540090b046a12480240c0c0d2008201c0c0303441840d0301c0c205032454140c81842c05100c00c01594030061030584443c040c1d43c1030125034031101160300701340078803400c041e40c3c688840c1030110621a07002001d00d9001814680701c1510030f8980c40380364004c40c1d4801030140e00003188090800806c540100d4140c8a95111 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 984356267 1250 984355017 984355027
    0x10219081b090d0212011e0609060305060415140712140606160213020a050304051005040305300708090f0f030f0a1814010305090d080a050603070e0408041a 69
    0x120700590b00c41c82001c00e119200e090007580c1196034540080c031894125000a1154040000030781d44031280100d00c084116041c0600803d20b02c500e881400101d035006001420107880300d0f1210018580502500b482040d21085c401d031262401d000e2650040b1225540c94040d00104603503003007240c2d40d09200030000303025007061040c195283d00070303100e59200078584203245030728901c00650f58402800015025900100d5040c802c243c2020155101c1c5014030f0a40e1404117a038100c041c102d036400c50703005010410034071040781050041e00c4812210004040b2103614105140340101003004222041c00026507840708216800c0000c0c4240c80e00504240028100710300d40440c101e8480c01644480e00c2906400300304101c505100f45130b0124660501e02050130683d4a5403404005880344c1c200315130100b4105404169440b10006d00b4981c08685a5a031101f15101c580419000e0900234003c69410700c2800b40c00b0070b0300e100c0c0e8140c817402544a03051255440786030003070720847ca02800315104040441444 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 984357517 1250 984356267 984356311
    0x1704150e030316080c0f010e0604020a060207060c0b1b0706092109050d0303020f0f070515010608060f0f041d1605180613020d0b13021314060c01021908 67
    0x10035190440d4044402074403990075607503180c1b80c243c2141c0c50382ea0075030814020514000010a80c41c0c0164001e4410801c000d407100c40076a600c02c80341c0700300780000e03135601c0c2c07914042400e03000f8054201c107180c6103500014240a450b842207811103401a50032940d01c8820004204928020606001c508405660000e9950740060f240c01094030540d0b004800c05a58402010711a82c102c812261002c280147c80b54500e03582c040c003a801c4240c045840303110b0f502125200120b00790380d06048844660701c00c0065510745090040986082410a41042d22244004159903513030207011880d842151442c8030199205c2281d0740f41440410f407001001601e0402841661a0101201840c084101c0071184680b02d8070007141c02c145070ba00c2011306003440032403114100411a0046001e608080300d410012080c0c0c1c0181000701d10800300010741c04480c18004001076100b80b84c8400314004000c0816080440c2d15100e9400d81e404100c3c0c1c1c065005240c010610000d0304054040c4c0c000388124001d0390b04201d191 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 984358767 1250 984357517 984357547
    0x130f05010c110d02090103080304030f05091c020409050316060f09020d0b0730050601090b0421080711150c03042102030d08010521060606071704150e0303 68
    0x700c06030198030040070030815600ca03a58188002640130f0a0f0345165a034906251a80e40c0007940c0c00c500094085890240301c81c801c80c00d54803a51001043d0b0000e0000c4580e2000740c0011560049800945807458000030810610244c04c4a506c1c5201c3e01c1010720781890f040b000c98441001c3d0b9840c1c1880d0020420240e182c4000d10080c1070380c05143c6014540b03603074005881c0c02000c2d56082500309017401d080e0300c00e00d140118492801c041d0b0681031001da2150340066806a07054050407600d07560610003040381480710162000e1035440f151b45800e50f54460344031000c0c0ea92100c80305483c010414084581c060030300a501000300201d0f0300c00315007030071444285141ca0744940c0c4125004002c840c941240c21409010a00180036401000c07180802400d141c0500100024031a8500c100180ca807017500355844140389005e9900d102001e030000d41c0d1484100801600110400d0701c0c0303003030b0b03001e001640d200140005201600112508914241c40080001c046070305001485000b03070804d01c03541c5205a1350b8 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 984360017 1250 984358767 984358787
    0x106181805101a1b010b150307050f070524010b2b1e060b090102061614070602030406060605282106051c03091a070611130f0501 57
    0x1905001c034141d100d4908000700036401d0b40100034020b010351031910403091410010405550b07a100c41c1c4811011400419088881404025800900000a0341c04a40617071004590214460804070300700300b03654165410b00d4120140489107a400301c52412620141d00d612255800d842a40045280d814020040080e000750a06d901000010300441050781850145440241d420110700700b11421a541440d501e07601068200d0a0083c5084004640174150300215201400181c00806903511601280d0138175101d0455000204424005000c3e03034183c800c4002c000301d40c060040541c0b24145030400d00111282ca502070f00a0240410104501c65202040740c070b490001c008039441601c907180003e880c0b4402c230129020002c4018201588085182d6200320203031041a10405425000e41e0030129903c4215040903020402125080218080815180c04c08021445490381458000d55608050351416102181d81500200d822803182034100c00860080c44106018101107207401d00103480c1d540c6c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 984361267 1250 984360017 984360059
    0xf0509090a112106090105251103190c20010e09060a0806071206050f0a1710051f0b0f1b0c10080a0f06030b061c05071502060906100512010f1103010618 67
    0x503150300c001072818000d96500104c2c280722940741d050b0300d0712f00a2800c5030700042210201c0305502050510210070004080a00041e1110361102d0307544020007040140040c07215a00270f404140114500406205550203036580340c84500c412018401080309454050700a03c1c007440d40001103104607520905018101c801030900e508070380718002d0045080540312022021130500f004240800d030011428080031000c00310035030f10511034481004808922421500c07844450703061000e21001d10f0141a19201d01545208031038904400c200860002c103200d04e482030225500c4420045d03401800e0040700301c0700860130020800310781103540b11001c80a0141c44039000307144c07141c0d6078921100020000a40caa420004403120565582456020740d000c01c0b40c40e00041c007400c40420b09044001a80700d00541d50380d00080d42c45070510f803d00032070f060103410000c003640d02c0c0c08441240203e40d10401303081840743c01d4207503034135030401c04040c000d031182c050400e0224184010400030070864030103409213a61 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 984362517 1250 984361267 984361277
    0x12030506010f110c09042303090f150c120a0f021c23131401050c030904110f0c01060e07021b04020a170c040f0509090a11210609010525 60
    0x400003c94625188400e910150889940400d1200f4817810701603010004000c840d41008181002c081030ba02e0340582542180c0200048180648a1a010244e01c00200c8500100c0b8105952a0f006a26100e81003080350301000c3c00080e441c0695074041c000459240c8179000030890343c101c0e0f44a016007111041c140c0340401c00699001c00c00d006050111460380c070410319005803100c590181c1880480418030840480105110ba814490b50203142610481032900d0055070816030030030240406000704040c110310f0301408022403110722841c000605040c00884000090036824003106401e4800081c1186055500c803c10101408204170303042841a0f0f02a5070158450782000c1c0c060f140b64007143c0ca0081225144001c001d002e10401003c0d000725003030342c0c210401079941d03041070000c1200c0598030090140c0107050800041020420a4031034860040d2102800c2000022103079040285540c8103040d81e00540140106041e090180c15000600e0b807142002c41c001c98800301e00d202d0303185030403441400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 984363767 1250 984362517 984362537
    0x70f18060e072d020f061b1903060e011e140f040b06070602071b0f030309050d0f02030102030a020a1116054f0b060f0904061a0712030506010f 63
    0x554100c030060142062049900e000b49001d07501940760380701c100d45140c0c17910030500050140001e907075171105d0800380603507102d241c010000d2034044280040300050301070507220140001c01d0f054200031305000b0031180c044210683d05000c1c400c80c500c140c5501c100001d02d50360081ca0555901c6c02e14101c5641170455001906100d000c1c00301c2c48a0251620250901e8808191b140030f003e01c40c150a0803030106107480c1d42d03000742c0ba40b803c80e98245d02404042e002030700c1d0b8201400241400701004480501548a000d0380980c260300003070981e031080300c2c9004030503004148190f0780c1e80c1113420b02e0041d202407405080215174408000c000030400f03205007841500c1141200801d0803248407095000c15144821500885580546040d05a5002a030242c4c04080858020320046940b080c1000000005c0c42d05180120362001c800c50394100c072a035154402d90705c50000034081106d142c100a9650100c0016480381114144694039469052102c402c0c1030031f040030080c4680c0e1025404924803041d00301101c82c1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 984365017 1250 984363767 984363797
    0x819090f0b090706020f0f060703020a050903010906060f0603063506071d0d03021e030d0e0c0a080d050306130b030a0c091b0c0611070203070f18060e07 67
    0x2003911035001500c001d034484244588060041100800d9401c10b408441c200344032009001e03982c0d44880c4200c0c0300c42d0411030204203c507100744c0003002c990507285072032407c03d0070400010b800c4139074007002100c11941e034980800c003650701681b0490081800e17080800c03103107180005031100c1d58400c4c00d14000d01301807a000c07610300751030203102d61880d106504111406840c0000c00500005480c5071607011018070440c42e02e00e20f103800740f40c1d00c1712254964080c0c54041c107581465126150300d00824201c40c0010312007a451142035102d1503030091446002400c80089901c03d21568401d2600301d44c02e41d4103c0c004504280e600802101e8011300103031100001e40503032428020080210344400e540c140104054101800011400c20055540e181e004008448545014010030f2004105a8001c0768504c1c00c0b0401055050b40708444000f400b1002902d400e14660000342010b007030b03802480043d018190305021103014811810008420040d08002c89818910201c52906000b0000c0c0304028901b0754003044 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 984366267 1250 984365017 984365033
    0x3203130312150924030804031e0302030a1d120601090b060f030c0306040b040e010f1401140f18010b03040303140c0412150509150f04080a11011b0e10081909 69
    0x1c1140084c07601800c3c80d0300e9150044e05503019110645103d168032100c034000345180c2d80f001c00ea80d036240d00110b10300013003c9000c0d01c4035805001d40070000f958100601d0007940741d511401000092950262003598184189e82084682ca5074080303005500a000003043c91020101701c91708006201030040c2c0744d94480780050081e00580224640003801c000080411280c150041d030030f100c803c40c5040c40762114600c20020500024402d035010351090019140d000c2c24100c0c1c1340400c41d0030107002500e40c0e00644100c2007a2980a90004120140001c100014140d15208043c5860329201034a06942031100c080c00c0280618001d642c800145180c2c2c00041100b4902000f0070350100303d805001602d010404036413192540860460007291000020b42401c3e10315044a00c540d0b44800f006041c10714054040710301d03d10b500051110396682d12100c4800071102e10390a01c0304111552a001101c001109201410802c02848400d001150090251843c2402003645000414010009602c80c0c2800c001c95 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 984367517 1250 984366267 984366311
    0x131208031b040510090806070c020f010c0f0803010e1f0b0a050318010524040605101107030c03050309151e0915130f06020d32031303121509 62
    0x40d004a104e48400401d98200700180e003103c17003040a5132810340d102801510160310030b1800a601080501c03d40c1103941c01008111170b01405241c03865010106a95050080c0e40300703801510042010008011105c01000103010207020307102100c80059240020741d00c0107001d80c1c28080e0038084048000b0385400150003007a0f5002030307640d0007030150303080012041e070103d03206169400c20440242514901800e00f8014001200c5000d80710741d0300351246940846940c20150b840003154003400b078001021404800c0c3c90030280d40500d0213181ea626000c000c003d8964019156840780f2075043c000451661401d82c41c80240345400c040d25656908c0aa000540109401900c0d11001e400070135070f24a140f070000d90f0070303044d280c06001c99983d11f85c46510580c1d0315440520508000b9501d140d0303641c2c0700918030345810342c90440d560f08803148250003510341d00d00f13410031500502c17442d0340c0b001c02909055021204078017414803041c080000320320303003100070250b030050380600c92403261500c0134003e171022000a158 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 984368767 1250 984367517 984367519
    0x121110050f07150b01090807030807061d010b01020d32041a041706041e0804050607050309040b0f030c09180d050a0305101d090a05030c03131208031b0405 68
    0xd40d200101d01c0c0c000c00f0340c540c821a0800b000c1c41c2031520300e6254090700f5034105a9030070500500b541455580c840d0f61a61003503000b10340154907a0380303041000d80c0071402c01c1c0d60780d400d010012891049410009280c4070740301c1c940d48200000582d8030081d010003112424080d03d038065a400c08400030308410186481940d005615610a0344054aa05071000001e402925001c881c201080181a80020b540312400c1d20050050025034911250907980b800c0401711191289454500703260781c1c0c0001401e03070b40010718291041d400008007031036146428440c00e64401401c6810460b03400d05a400709596100c0d071640140600101e2011400310340c10750380141c1c0d00024140840c4c010f81a50040100a600803a0034034002c6410940450b0301d000c3c044203400c00b03580c8505a9602c0d139090030300c3c00807090800907210007864051580c1c00d0002c00c40500050044241c08001560ba03001341c25030000c413010160f0b00c82c106919020400100050708a800c80703800c00440c4468803a14800441d40030494415580b0107 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 984370017 1250 984368767 984368797
    0x203030a230412200c030c09010f1203090b03151819090303090b0103080712030e030702100e181b0f090609031e010f0c030203090c09090c09040b01080712111005 71
    0x410074040d4005810300001c08117070151800c260107c8240a00e8200038000c3c02070404c600001403000301c04a10044940902030714103c5002a45c031090400e0b0ba40c020f580418181d0002e03580c1c10000c0c2000512084100b542203180c41c2e040c544900d000250540c04982c500e0f8080d120b50a0809241c030980094a40e2a08080300c26010b5a491030500a642c2c003c1404a0f11000300200b03104809000e481400e00441141005e90f1510032950300300080100046c60b00014841c0103a028140c0b500ca2a101800380b407510300c3c10b0181e41c188042c02040d0380c0392183c00c0c41d0412404029201c00a0030640503600480802d85400d500d4481e00c030002800c0103140c1d0004030302d00c3e407039209a01e8208415000729036079603000c40081103860850f030001c17401d84c402180d444c56164401c894035492414030102c40d5506c03801080036034003121000f01c001442179806490641e0800c65040c0144849001445030790300a001c3c0b2100c8480321740045d035904030403074005001c4c103100d0301e4590807440a80340214100c0b82194038686e90 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 984371267 1250 984370017 984370067
    0xc03090a080a200103110f0d050702070f0e0c0d05090d020c040c0504124d010c021005250b060919021606020a050c0c151e070609030203030a230412 65
    0x1b2000d40d030010010b594108d4104004182d56600100e002d00a42d840640c41d15865400c02c1ca08001400d0050000c0d41701e40c0d010046010440346520a903409902500098113031070700d6a0074000c0c40c000c0d0300545107200e00d140c140d10001d42078104048404480c9007115010581000f07080040b441c0500f801c42e11005205076910002e68400d004560352941d218600c1d612007400b4008071601110010700b10f0902040540ca00240546442003c1b259034811900d011890309882d94003050141d4241c010072800300300ca20303040a0400c0607501526901000551781101a0f140120000d0750000f20304004a80342507001070701403c02d1380502e000d800c800750084803d65a85586440c000c103075605c10042c01c0740c0350060307280b856442c1c40d0600710800c2140552072414100880d001c0d018680d070304048694006544100300f1000000e000d4050040c525001b9000340d6180e113401121802a02d4480f1031141c4480b1000810035080d642c0c6235401900315170841d103c440c0c66030b031201301500c95400621551011100b8484 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 984372517 1250 984371267 984371287
    0xf111c08040c0f0506090415210c090213120c050a030b0609090606012a1703010e0f090d030e100e1e0f0a0f03050f0c03090a080a20010311 61
    0x2210307001c0ca1041d444105440e40e01ca15242480e0b5150141c0c039070185082100e180240340c2600400007514506080c0b41d90155140035202e0040102c110000314000b036400c000c004e200c08100564000c140b03584040d03242910441d000d0324140894012409000c04801000040c000c1512410002d084041c21703a0301f8290f100c1c02d203c480c41008951442c861080302c80025a10070020415a0182c101038540094582d504000882c0502c1301d15444075040404464440203d00c100c0220500700c0d400c5002ca60740c1e9410324500054129004000d000042580018005c1c1c01c080002c01010408847c80d000070b03900d00c051205410030750500d84a1104034204444d90140c600081412020055003140000200c00341c4e03040d05441c0e4018180e20078031a08440c40d0704000c01c1801d00315920091103490308614040c1c5805134451542c12020030a0604e51004c2025441c1c1d04124001c1c03000b40100790002d0252588503650b15001c2103030031403060207104112841c2c04131079000c2c0c0c000c165a09001400d036900d90403207039 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 984373767 1250 984372517 984372527
    0x501060503012421150e060307060f1e030e0607180504090213020d020417071a072001030b04110315060306060f2a0a03021c0f111c 58
    0x8040c040514144145201000c1c0c803e20015032004855102c2c0100c07512094442c501c2813005035600760309a500ca822a04102210841e403102a105441c1264014144581410301c0c01b0b03601d801040c01d11a00c51082ca11082d0030210064501d941e10304e40d08030501003180d04801500b1142c155403042e00c03588040c4404950008030080c900c0f4090741c06881c3e13170b95640040000f601c1c0d1303400b0065007001050243d550856102c3c3c00070000c0340001c2c031015146c540d0f50a00c550cc3d800c40c1d803454441c40d07040050223011702c010a00710031031030724068003486052010703d4544c43d9640b08140c1e14090400300700009180c80c1c1c0d000303800c400700080000300304010a030003028580403154003c5901403981000394a810701070785040826a40200d00203000340d4280150700051140c0741e4011110b01d03401100c46030641c10a6041d001c3d040d1401d601220213059034140625001c0c0c50704140341e46031140d01801000d0010800c0d405200e800460695140c90344040e101c020205050515055014042c40341e00d40b481c24940f0b401c4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 984375017 1250 984373767 984373769
    0x30705070902070f0b18060a0606050f0c1603081803071a03150a150e0303070317221410360b0903250c0e150307091a060304170705030d050106050301 66
    0x544166116503039000458070849281e402b589010490a10292403021090005813403a6005441103a6442c2c110079901c44c040c241c2948100c515503000511040c0f82c42c1041c3e00440c603400f064004152407410b180d14445510003070118070710f00b2a0b000c40000e9444040340c40c002160b010251219400076220b5000301d454581a00111010a1803207048000c40e0800000b01d841c11a01950741049181c2c0040701152004406450411440146501480d543c0d03030b1582d015200178403403100b08888031001c4105070f0a0a002d0426400418546940000c0400940c880403012060840301c1030340c5000030010403245000c1c2d60801428025402041201da6040003006109410002182030903001c0310700381d600404075000c4401010602084020004400c611403500d070080e0b09011010030540710040402e1030441c2603404150100d0304c5e000071501c850000305440038042c02c00d86c0c09070b02e58505501c450b04415110042510f00410000705034060000603c159150107103800000c1c401c55a41d100024120b40003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 984376267 1250 984375017 984375061
    0x60c080a0b01020c03031e0c030d0f0e01200a03020f031801111c051017010902090a020f0319140703050f060607031205072003030414030705070902070f0b 68
    0x905190001d56600000710000c500e00000c4c001e42c038001034801840d145212462a641e00303410244505501c0d020701b40302908081c0315103940080e41e96420b1107584c3c01d6400d40050760300640d14042d4410758209088149e00400c008503410a943d40b050810f080f0001d10401c0c42c1035503008804010b01c104941c18040034048811450001c3c440702540150211661050444440c03114500304081003101e0b42603004660701c808a410031f1001b66640b4800e07110480440c003110500359660303a4140c02145000340c5801d070004072a00c021410001d0100a0a0081c030003e006030303135031300a00305141d002c1c0b85c16600812400384181c001029282880350f00a009080259580104185460002841b500340101500d0b0310a815035941448803500c500e80c10001d20011303126004004462081d180240c030b0030012603104200341303c015580c0c0d00e450f04008140c60715480284480c0c3e0410400c840c0800c0d00000e440c4141c60040000590300c0d50b031031400d10205103141e07200030807200742c40c010030021801d880600c40c503841d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 984377517 1250 984376267 984376271
    0x18051305011503140f25051207050405150c010f02070f11150403020415030605010f080111070c05060f0c07171b030d0c1505391c0207060c080a 63
    0x30301010150144c440c0c070403d00c03685001c3c3c400026002844201c4686e00140ea9a4050380c40c102204c0030381c440040c541c4501c001044c2c000a080b010020031600d50303917006040745001d50070542031600281202030000c9581c40d801b080419074010a00080d4003c6012a0007142c2c119030f284600c0c600a0350342c00c40c01d0803d844401100e2405140c0d410003460040c0b1510f10030001d107107070508560070400140113406503d64003080824000c40040d15a00c01d0764064440f40703c003809880c3c900b06031542550000324211008440a0050f040080c0e00303041e0602c15030700112015525111071041d00d00060090f00410703481e52040e01400101c41481582c46070f03c01e040b140a03503140858800c407601022400c554856010392090b0341c0074803598030981f24001c2c001d1065080c1032014140c18110000e130381c002e55400c0400300e40440c0445d010704c2c00900e030703076901c25086064400101d075014040d8030502402c1118071112641c0072941030061556030454130b40c240d100c102007201001001c0c3c010481181112101d8200d4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 984378767 1250 984377517 984377549
    0x60323030d0c0c12050306131107021005130b090a06030b2b02100329120a05011a090114010c080403140106090501050d0203070308090301150806041b060804031805130501 75
    0x1407258003103034464480544031115580c4807102180003060300c04101003424100b80b110070010799442069980040701039841c9030724ed240e444011408d07064030b03600c082c030070300f01c01c011240d082d4035601419002c903502c40c1000184180c050f00428400c0307400300c5242102d280d100c11290100400442583c520900030707224158403a00c015800d900322244201c405400e05400c8600c0c3c848415214046056060b01030400040a110460102e10700a5100c00803a0380c0c6e5101c203403401aa001c0c00422020f904d00441c0c2d0f03180954500b02c1c140c3d001442d1040b00030f040007482200700e0180081e0400310f60040d42d00c500c0c42c003920b07680c2c2e0100d58002c00090050340744250070000001154548030840e55075185d0000c02030650a03185039108013103948640000c0d40c16540340c4000461600301c11803e14001c2403040050185407a0a1400da0301000424a40181c0b215000030184409503014070829031290b49424060442c0194402881c6c2c84202944040e030700440c1c0c5545d45807a500d454200a04945d100702001600e0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 984380017 1250 984378767 984378803
    0xe0a0b03010e07090c090b072102030405040609021206010807081305030906030f0601202a030601031a07170708040c0b030108010c09120305030f130503030109091401060323030d0c0c 80
    0x43d22030008d014140740440741c40b24205010054125130b0800103401141c0c5400c0d0741e50b011034181d1369581d00405c0300f2540495800000b540d0240c9041d40600246001112480e1409004c0d20990010b814035944a0851050408022041040b15000e070401440d403030300e0745014104468012030454041d40000e10019691301c1c194409107401c24074094550190a00e240b1030700342200404414043c001d1014000340501d10661024080b40307010314000c2d01000310a4809a00070342d078190000d40b401081210481c01c80c5803506900018a411401620f0105402d480e1030030681d440c580300703030046110f14100100000700c030901540290b0180f00c458455410499480a8103614050188000782c0451420400607000c0e40640d10a1030f4010035040303c290b036000c0c06403030b0185181c00c2600800310301640d400304035050124a490540d0351500201c028132003141107940746041c100d000c0740f40c03400d09540c48045d07104420090041c0d850304241200d00300300d64022044002d040500311501a5007c000c2440402c0300 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 984381267 1250 984380017 984380039
    0x403061508250915050d060501380703031d0105010f17030a050702010207030605040f0201030b04050907050618040e10061a030c0d1b0c02040c02070e0a0b03010e07090c09 75
    0xc5103090003110311002d4900340ca6100a045041011200d14800715008900c07541c660a10889081c0a068000b07080d41c10b0442c24585c0e0b072120400c44107004c115044102141c018800d48650008100c41c00b00d4440c120742c60150b0281500036503030200040300c0f10b0b043d02c0030f0394150b000798101c1d424030484084599a4000c45c0b500a40300150125064004200070402a0701900042190b1403043c4100c4852a6894850008480080c1d4044070702102c030403885401d42d80d06005a82d0307804002c54040207203086c0308120994038010f921856003e11000b043c4080150f0f1420030700c0100317003000f030028060a51071000b407548030004100d2861041749011030101f841228030304550580c0000b240200c0c5103817a1641e11041c50741116540a0b4030585508140ca01400500c1ca05030181e882c1d43c0310540c2c203006034410801900c5c90003000004650180b00304010308034170304210b01d0700400810f0000803a80904808a030160094900400b8684558680000d4880c110ba002c209240f2055540d0803455440b4a25040 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 984382517 1250 984381267 984381313
    0x516082107050a0903111c1b06051804090201270302090c040509040f05010207140d111606050f0903370b06061c1b0306080106030305041503020403061508 68
    0x40000c03c480810320001ba088100c10704a000010300c849000f4803058510744c06000f10250403a405040030a29440200908404501030301c05410520f080209200300c50b402d456080c0c03000d610a544508291042d64014010440032a00c04851103d12014000b480062601144000c90040340d00c0000101d0071081d030005c0d90161500101168907688581e203403081340f21000c0c40f05642c2950308100110010b0400300000742803015060203405114003c100c050a5003100842c5440ca5400242031003c0031790003002c0c0f034000d880e09410305580700c003402202464140680e40e41507400d40309400c400000d5000315801c420b44a01031743c561002c4d2840000012003c45034201c001040d884032200810385525140e0060020602184050006020508800e41c161412002683c803181391503003680740350717541c0b40c040c4002410030036000740035040c55582c2c01071503449144200c40d602c080a441d00c2d02418031070380403500255003010083c400e0908248031203e544000d4452508030740700d0000c4104081582c0f1075210 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 984383767 1250 984382517 984382537
    0x30f070507030212070c1403062205010b0a090203180309010207050d020105271003060b0a0302090a080610092d0c0306030b010801050a051f06051608210705 69
    0x1291110081a6025001114100d0950284003480315040302d105018001361070082a41c041554030f00081d442c01c0403800120789010b5040b0070204001c410710a0034110148000c45c3d800c003c1e5040d5401c15900426914220a510400300500064802d80703d80180d0700130103078810001100c034103101401c1d030380344501221175002d40c00440301048980782040d4600e0b4580d0041c10058604000d02c0d481200207140100715400c000d41001120a0f0b07418590000480400d040c1000c102283c1068040c3e40b00c1e0141041010405800050510841e1035100c41c0b0001402140e08981807030030241807001261150340111104245040d080e81840c2072515100c480014089481134805880482e03001d02910403c601003060689902d000000140322010850090500030b00004550074003089103415510301130000c0200803050b08019102c0c0c00b1001005080301c001381803603036980340200004c1107444549a0301030107070030001c00c00b00e50190f10316080005044603004042e03440d030b407400d40599442c00b03030751044 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 984385017 1250 984383767 984383791
    0x4150e04020907170f04120c0201020a0b0a061e05130506100c240e010501090b01050a050c100e03070203063706050d05070f060f0f210c05180603 64
    0x4140541003403051590085024a441e0752840030404213910b06590a0f80d40032402c00c00d41741000b0a000342800361010700c1d441807521074000e1426400003941c9455020010f4140200040468100c1450368002402070451040c280001e08100444103410021440703443c0c0540300c480c0ca028070610381482624400d49004000a08160260f40d08030349003803010004555419a425100090607184050818966006400407800456114500382034460692143d40041e00300000242107030b80020588084000078074056441d0b88000040d181303030030180d09402c46040d1600840d8501001e0201c001d1684500030780171281542c84e25075282041480700c024002c02c5c0039060485041c0603000a0800c4040c0c1e00800010681e5911440084ca00c0350000b10108d441d40d000032400c10525401c0c1001c4001011a030034090072054810354041c1119603070a4540c0100100b40884500040c1c41d094030941d904080c440400c01c1c00e0750240054485d0384941c01c80ca4074090302007404017840c40c02c0000c6922800004581c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 984386267 1250 984385017 984385021
    0xd050313050a05160f090c05040b070501151d090610050d0305070b0a06030510050103030804030804031e1101110403050a020f0a1a0301300b092a04150e 67
    0x52410030308511504451034001c1c84801400305008102d000090000405100903580c6031007850100b2500641c0440182d0b8140100349445607041400c1c1ea0855007180b80060703403213005282090040c0b010103124105260901008151a0a0f4100e24804503080503405c80395600e40c08426540c4820450309400401c04400d814059409c00d061011120781c42420f000d400c1c10b0302a40e131507100120442e0810f401c95a90305041050010410400e1000241900100080c1d41103850050918000500107414001840c003c00c042601c00e0217800a0094100e0228440c0c0c020182c0040c0a1700c10808990115820100b04451030034001e0112000c1f0380e8400c0040c100d14a486e424410840e075803802990703228140e40c40004d42c1e001c10101c0484440c4014426659a60602646100944175096090700701d0302003004880d8200384000c40c2c0082c40d90811070040713075a59810354035413911142d0050720303042401c071110a4442e100c551b40702000782c1d0720484049c07004041900000c003d904192081c81c840301c0a40340 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 984387517 1250 984386267 984386281
    0xb0301060327022110140405010b060c030702040207020d0605040f150605130f020f030c1228050907080d0302030a05150a090e0102041a0a020606010905060703200a0f0309080d0503 79
    0x24000e91400007a410b41310050398170000c5400302c4080480c17290a00c40b4070010001042001c4c8a080b41c011401c541c018104100090083d50300c0c094118001d0045074005508003e6603552000e1303009040c0c0c0309200717001d10311b49031900d00f044401c2070808035840240000c4203814168140598802e4840140c41044180d103039000314030103064018140c0181701da08001c004144600d0034000c4d485401c1c180e03461540c0c3d030503040b1030001c01200284000b127000c80c0310408042d900905240405843c0303182201152507110468294205070295100c0003451040641030411203815030051841080480d800304019500c58a5420305c041020418aa0110010300b080c0b282c40040d500c0311240d0513181c0300050030581c4074040120f800c0c0103034240780e5100002044d0080310550401040307502441c00c3ca000d80056107003201103030003401a418020188810341c0d24034601c960070f00305004049a6094212020603409003000744c1c803680f005905a00081e4100c40c040344066002a4601e03080030700d582c403d8a1952100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 984388767 1250 984387517 984387559
    0x7051b0d0512040602070b100f0906050f100201060e0703060305100c050f0705120a0804150603021e220212070e101b21031d0a06020a090b030106032702 67
    0x6004544c896401c0c0180302c0410040341c14248245006081e0001150170403104842c40030441c0e010300e0500d0305203075080c0801c0d19607244e04400502c060310301c07515983c8500c1040e4003400440c0c10248900c9404170401074500d525030070040440b401801074994417010103804400b40c8c3c10107030072030001c02c42c2080034400c9030705090010b041960007442901c1612603040c2d1642240e0f400124103000180c2124203000c00d0101109030303500600814041040350501e580c1c04076240c11b8030000f00a00b134400350000000251031f00e020920181d00c0d0402c0d00611503070498540c0000b0340100c4030b0304c03078000d03c01400200308078042c1d51020f002c110000d2081c84e942d03070543e0381291003d03401c0900d09046112103021600150021101c0300c1360400c610000c0000074002d550050481f40300d60500140702c3d0042a082124a50110303440204541105025170345400f455170584200c54507034040302d1050000800042c00540c5584109101d409002d01d81c0280c10002108180070b29552802952100c6c0a00d032000d0711072502 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 984390017 1250 984388767 984388771
    0x30c030408070f0b04030c0c060809060f09032a3d0204150f03050c0a090e06040905030703030917180f012616080c0f18040507051b0d0512 61
    0x350700c03401040c0c0d051340d4a08001503810b460840c0405d01d03200b8158200510b004003600070701034a00e000c0b8180d14000641c15070f1080b000c2c00b4110b65041c1c0001203030904d07000340b0031035902c1040c0068a40814004407100c42111018407902c030b080d405103154403000302507507c901c08030700201c1550b050b1030206081060b140300341e940c6100955040d401c100000f040e0109131402820142c960b1107503c03030145c0601000e002d540d402000469504410410384d2081900250440c00382c1c5c1075140d24442540c0c0e01c90102d0000d0000c80310103051072102045013010180d00da00810f06880c483d44038040381d590040c40c424168011440703001201556001e047d8298205581b010750408030500d054a207000105407100380d203400e0b601440703822088074000c020703800360505a04100074040d440c001031a440d024407001524040c1c0308100d8418200000c0c5c001d82a112002094510b1200038010003050800075805001d0b640004c40050341c007040010f54184803c00442e0142e0102c2054652a240c85ca00480603070050340c1c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 984391267 1250 984390017 984390023
    0x12090c01080115090f12050f0c060d0e0f0a05061506190815121b1c0f05030c060a0606020d090602033403020109021302090a050d050a05011a0f030102030c03040807 72
    0x4c944000150010510494402403409052204500d40309041240c00e111520910034040d0f403000244c004203840d810119030001c8041c1c00f001481c032251800140c1084882e081618451080740b01540921402051160040d0154130f116001461081c00744030080c001c84e09466200102d500c81c003205140a410740960098120300030040003810301c0005494911804044101c0b641f0002d0310b40c0c200d20064021480102d400c65880c1410601c1c1014030404403d00e402c02010f00824140c0c0900b017280030010b4076240da000c04103540c207524000510303800070b000c107100b01401845080704000c410350261940340152501d40c0e018601d400100a020003032411144084111303000720840030001b242c140a000c1d00c90382d00c658004201c045c3c950041203104440482c8240302648100304007100c90b40c0712515202110002d4842106006150600c1410921201000380c215420300d540000110321a1704050384111707007129500b00614400f0141403c0340011189903048820402c08200881c0c000b0020b0241c03d44 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 984392517 1250 984391267 984391277
    0x3180d050a200f0304050f0a1a0c0703060504050d1b030212130915151106070c060225170406080109050603070f030503040501120e0a0228030812090c01080115 70
    0x1100c0740310549440090303815150f641e0008201881240707041c56103010b0a100c2107540442980c24028604104841850020500d030342c009500c0c400e1030300c00d015010042d60031030420442c61405040064903041641918400070303840c00450b20302801403540c0441c2103034040d40146400e01040384501c1079940102c221400e4103030702c140005490080c900400d1006481111301660301894031850043c0d8640c65203440c0140311000003904009440003a006510100600e03024030114160b049c220003e00c070342110581780f4944401c504c8400d21a2601400c0808d21070b41c0c40c01c8003000e84003e0540d81e8000ca010f40c60014000c540100642101c58000d47e40240d80242540d03101ba64514100400590383c0e80704462580000c2010042583c0282c8188401d596000d424031561900010154a591a030700b4000d100d99001e46900480a607001040300c81c1c1c42d0341c040e54415113601c1b0304140500340c1040c81e0840000709401c000585040c00440c40a03041030041e15030b0301c0301c1d9003820503550044141840b0841004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 984393767 1250 984392517 984392567
    0x1e09100b040b070c170d0804030302040e0414060603011505011115040b0f070c080405060d0f060612110a080105090a0e010609020a0324120606080f010203180d050a 72
    0x10280300c000300001e001c0050860f59071401450042200d990680c410303c0340740c1c001c90f880c60080d18042040741405000c1c0c6083d130300366900c0389001d13002400750740c00200c4134113140c1c8100820003075214074106540301e100c012543c01d44c0d500d0040500340c07282c201c8040d0705150321440801095010741e0344140118152010780d2002d1640c14440803080c0c0045400387c0780d4916a0041c0510942070700c0c55650025010305d4100140f80c0142c941d41028481c070303c94a130140c01c00040c02400207840c0d07486110780c0288030b0070520a5956480300104104050902134948914007001605902120b0040381c4045229882c1d401e210ba08e0b00080113a0200003c140d41c903940c2e00d074510740314591000e00c00c3c00c025007141440181c907039040d62801811290301c000e001901090980b12150301c0b00f0180c00c60790444050316900104084940f0b0407501804c0c4036441441a4480e41410b508405011340143d8850007035200040b02c507400d1821495621180c020800d40414020000d02d145180315004518031320341095049051b071 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 984395017 1250 984393767 984393779
    0x10c08030a050f092a0d02030d050316080f07080c07050d180b2d16050a0b0603070f050f0619021507091815030503030403030501141e0910 61
    0xd50046030396041640da20000c100755420301058482d0040c2d900c0f0010401c01200302c403a850800402100c4030340448444000450a549a02000d00341c0369000e019a8940d1108600c09056500242ca141d9000710042064200440c4035510032071103400060f06659498681100560700720310090714050342c40b0320030003d40001c2082005814020030030380d654030074941c001d5403840d04650510741002d200608104042c0b500111704c240381d42e0407080300000741011003a60ba25040340382d00c200b803095034458400c00940803e101c40840c01b41041401070002c1c2680355100c0381050340382c5146015038001d001e4109418032580c01c001502203004107000e4241440e1803035500c554111307a00b150118900582c003102c140e80030800c8050006801c08001d0800c8041d40c1e081c020340b803030290300242e1302d4010540d50300980052406043c03100030045420800362503413410a4140100648002d01800041038180014200d060800141e41c480126611078020300d4258104200f01c1d0061024000c001644401c280210b01 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 984396267 1250 984395017 984395033
    0x91c0f0c2304020c060402100905033c07030b0a0902090133020a03210501060807020f0a020a0501031a120a061b0903020d08130b092814010c 62
    0x16114802100e00c4a0a4598590041d00e00d0841d500d40607034014007034003800d02070014290b0f40203641192211821240d010048512800e00e034080c5515201d55128400400018100102c0342c03011001c1950b807849909403407002c4416a405008295408424104082070035910200d4102030301250200b01100c05400265550344203030803075030140c0305054070409940000c04050b4180103070410810f0120303807083c5003e900d0f03096082015041c410094041c090740c100302c2444030f41e42c0c0c4001e0010400355841e108014800e100c1100d810016101d501c4030754182100006080140300c1d401010303088940c1c1480011070141c00740c40c1e800052002071032100011a0741d00c58800d980392001c480100308001660030040b083d1020007542001342c815034020290f940c0e034010400c2d01a80d13010342d000001c607241403030040e00503c0760380c2001d240d039420200e0204640c1d5142008115030741048603624607a007a011000c0c07601055419140b40100c140803010442107205403000c0f02d0400f014108042004c07035070f8551880c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 984397517 1250 984396267 984396269
    0x2918060711100f0606020c0909030f0901020c131d06092107021e0f0906060301060c051006260309010c170903070b0d0c110c090a0b0d0f17091c0f0c 65
    0x4902c6441e01c0051180d65410032503201d00340d1f41247d02182c0c03402c04032001600c80c42144101070042c0030010304005c46900130411080d500300040c0261031b50000171503444000303103030401c8000c140300c072209100407c1c0c1a000441c00d01034000b610241602c4c4499241c6903181701c040c1424030448020522a05016944440001c04078903100324038507801d01c0e109820081c0f04420700c1842132140c08a50180401a141c070001d5a0641e01c00e4100403052070315131700f095481d082c140200052124100f040204220714410351132001c409004405505564850103002d13100e000354820b81d40003c800c000020049402240302c0e829060366004507500c2d00c4d00040101e0b0400009400c11014100c00090714003200915101c8e0703142c00d2040e0700d0040c1e240d041741120144c0b10094200c604c2d100d5588000030448103c50f43c2c0c0084404e200007401030080d440c1514080400410b04030080c5c4410510154404a0810700c408072030400c84018202e42d103001030200c2d015240500c0ea00c00785e59141202038000002003082d12000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 984398767 1250 984397517 984397541
    0x524091903150b12010c05040b07020d05030304050a2121150f0302030c040213180b0603011202041416111203091b030102040f050f030109291806071110 67
    0x481d40f100d4a2040c032094814244100d1501c0c1e02d030a000f040c4a5030700000703880a40744208141590f0720a1030002401000c0d10700385c003500902001060004102c0c000800c001410300c10400300a044151016401c0582d504042c1d40380032800c00b4083c9a8070058040314043c0d6103216060008115842c50088940c0219a8216107841d50301f40405105510b020484844001002c440640c50702192000550054680784929041441c000e0814220703282c0f1034010405000020b01080d403a503030b48181a800740c00050b40141e00542c500450340d4860000d51001034814660000c452403421a1850100d130142c0d00400040e1081c080c0d000d50300211140100154040c0f1480d100410510300000ca003c41c0800e60600441c1c0b00c2d0388108004c01c424911030354807800302c2d8011901d0300e9400c010355020a015101d00da500406654188041c02e85400d0070600d01401441c0c8840164041d41d81c003140d40d20080c1454001040c1c0c0d91004000a80703691056040042566560058560b1011540000703000e40d40014101 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 984400017 1250 984398767 984398771
    0x2010f0f1d0304150f030e031206010e0a03080a0507030216030305092b02151201090509010f20031e0901021b010b0d030f17040606052409190315 64
    0x41c0d081003104628030010012214082d40c40c0034070302032100100c84201181d02050100c0c2500c3e500606019a202140e21072060060304c0d51443c582211088003c02121004d010405a0801c404503042c03e009400582e40d0010819161a039103000543d0550002c520480452041e60b00c0c021455615081e08002075110341c80300e9885440c0001000681c10f01e014414480b40d000007007885100d41c4d821078100d2031070b40648050f00d0002e1060411551441132085450b40e400c810000042c1d55231441d8055803040290f40700800295000d03d0341902074804400500320f0507090ba01e0345040c0310650b0b9005641182c101d4000f014010850400942d250750201d4400640da50702084510364801038a07400c030b00c2c10007210002c01120b4148c000242032820002d40c003804102890680c41c6c891070041040850380031b0f03031119211551a05140c100c019003000d00600e4000c404590403107001c40e00580141420b01c1d000c0b218142030008010030b20641041074a070282c01400e00b14030020116000e0140d1200c098000100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 984401267 1250 984400017 984400031
    0x10504050606010203070317060402040e100501020c030708100216170d05010608061807020c06161202011e0e100c0815151c1d0601031101051201120302010f0f 70
    0x3000741000c1000b40442e055410030040000001e52051150f404204881680f480d1500c6400200c0d00034082c68000d02141c1132030900348180d0466206a981c1100d0302682107981861041003815244c14091051000690242e03c007400b180880390003500100c3c2e250410881c60381481d407079041030b22500c54121040e040c00020344a0301c1d040a03010307884c0540b80c2400c0c000200d04022001c070304401c03108070156005114a40124407554420310010501c500020034031526052842c0900b01d04500c1160b00b1203418103880022904c09006004641d040c18103050050108003c01d40d00c900a085400000340c024007580310042400f050504c030b4082c84410590b40c0000300c0c0f402840701420750b400364003850310400050300d1a404103040e0310100e4000350411802e40301c071500c0a051081c00ba00a102441c44440e42c84031904426200020f99181202d005094020582c0242401541e1901c20403030100c101880301c0e4014011810401c54584080d4468400040c04250a45034282140c0d0403d0444c010301d91500300c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 984402517 1250 984401267 984401273
    0x1201091a0c030114041d1c080f060f0d0512300c0d150302030d08040c06080c0d05041a150414130f030c140c01030f020c0601030201050921010504 64
    0x640d114101030040d615550400c03407040410000c4d03003480c61069031103c503031841400a1841c2c030b000c402e0060044800e800101d0301c00350302d00c114150201d400222600c00040001501c04801c0e4007410010b88076a820107400b40c02c1c0410142d03540d0301a40d8034403940e100070012140c11030090607e070b4810703024030340c40c2c005d089010b081ca19445030100308858840401d00041c1e0303003024101c56400e240c0d0000060a541074a124500040303180e072020758903000c0c04d50006019501704025034401c511172009003641c948c50369000d580510003a145d0000c481c0d0705000180c0d0140301a804190401e0107880000d40c0744880c3e00f001ca046007802c03208944510580c1904051504050160629126120000203602c0c0b400341c0340141081c1e000c010280c20313481e018107803009141c010ba04030a0140c3d0030000700f0b0625928508038594030b1021511f554000391404179040e66210140c82526403910144d805404980d03c0c0d0b400455241c0c10102d00541d001000c1034107903c015548140201c0c070110060004103051900781 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 984403767 1250 984402517 984402563
    0x21f091511100e160e04050c0d03050304150204080a0c1703270d0b09070317030c03040314160f05060a062939120f030402120109 57
    0x95122414001c0d2081c1c1941d040c1e4010440d4207140b5802c0000250105a02d038516207850803038a525015040d41301c00c04100101500d101c5031159000b041101d1003d684881484002c010043e005400982e0a0001c240001c884080c0300c002d00300000c80140c2800d4030352500300d00f03004007018112402c0c1850313102040300c3c0b1007a1030520840b0341c594000e507080c0044d080c5071000c03000750304141d141c1400000d0140c00640d5603242c2210001038100310100b105250212400399546018081603c0310b5009409100b140014141240c4c07242e1200d4400c9801c43d1030b540d84c02c0e500c90201301c4004401e098280610f200880c0403c200e007604134000e00440e02c00f00c019003000341c240764020700364207141401c0c00c03000e02840030080003140d007208214490864508004110038403500409581018145441110030f80e0310504c205100c080c04900308010940021700c6030a59a40c104d4401440009802441601c8420b0a03002c091640f0a0016149010701e0740301c8030907142120000c3c1c500f01d514460410402400d80114 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 984405017 1250 984403767 984403799
    0x1050720191a090604080d080a0b0a050105090409030e09090706030b040204050a06120f0906020a0e0907020714030a0f051f0209010c020f01050c100501080c06030103021c021f09 78
    0x2024220010b040078039400107980c0c100902d550388500001c0c031120036100c100480b0002c040f08020740d010000101c00042c0152410365180c1590760404240121500e41482300703208840d81615020318000b00d440030b200141185140035410711a880242c00b049840350300c2820701c503a90480180180c54208840502250300ba1303039000f0f000e103206210511094850700822010f4640c2410300c800c010034000300c1130001d401100b901c1e00c81c2c10304103400d000c20083c40350081c0a4640d40c40d1204904200810140079034400201c1381c4a006138030040b010002d4140d07007021000c00b41d90140983c0c840074019101c01d0f104095080084485500a501d01d1030200c880128141981100c140c065140c0804880005c00904010a002c2e201e54004a00c00d04640e0280007126007000c84c20050b2802e00751035a001800030b020074401c0381002d0048032010902440c00f03100b100e0580354014072100c00c11000e4488242080300303495049070044000b03400008034440f503510001c0d46803c0d555480300b8080c20944800c20716075403 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 984406267 1250 984405017 984405049
    0x303034203070e0c04171015030b0c07020108010306051003050609030901110f030a180801240f230607020a1413050c120903040b0c2401060f050901050720 68
    0x128074180100388040004580480c5c029040c0504140c401017242c41c10447d000b410392800e503241020030007003051180c80c1c0504403400341040050b1551a444220795520680800a001600780f40040c0001580c45e4130954004001080c0e0100712600e9a48040c5030940903501c0700000d90000c11105120740e8040462501203038620060940c08080c00c410320b035a03012303da01e00d00520402e215121348a07940c44590100500b800e03002840b020005051000403121400003450344001c603c8404541c0348040c03900d6104444010100300d02d074803030100b0042210010603d400c1c0d4020010040b06000d070741c0303122080d005801800200790707450b8003501c10422960054035031801c40c1400c1104200500e02e035401600d514030700f04030b5032840070b0b929001d145046200390342159011110100d03d43c620b456000400403901c0e41580180d135000750072032089485a8600f40700d600001600d01c8007040c665840350380a4800103406051080c00c180c095512241c4840c000c18a4070103440030090880c0b175038908100100d40082c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 984407517 1250 984406267 984406289
    0x108061b1b030c1608012a1d09040609030e01051303030525050d020709050403090311010e0a0b09040501170d2a080705011b0e240d050412030b030303420307 69
    0xc211080c1142c500130b02901d081c88429210301101c0c0306015850308d210a00240601014500762600d03074000d1038204011780024009405000c0f540d4043d8080380d003080501084100403610b19902160207a000700e8a0401420380b84e020314044840c1c0505e0154400e01c244060403c0302d984081c0203180500d50341c0032240c0941040140070110b0f030001000d800b1b40741c0010040030001c0c41c1d000160b40340588050650340201e00140c0016084030340c0c4c0007a181c1d6110407142403280b83d80e500d0384a100d000f424000311b031081d08203c4164020314019558071400d00a5030300c00c40070151400d240d42500ba140500c00f6103048c0c00000e0800c0030490700b8801c0725480d14a181e104440d0101c240070080c400d01201d0034041c01003140c040c1c40e0705250f055000010000e29028540756841c105218980302030f0500395400c848040d011710048203c140280500c100c20302e8094025411992095101c2401a45488100018600c0b030007003c1c090f00004150707820050758140da030058000c01201131624010040d404001449 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 984408767 1250 984407517 984407561
    0xa031107060e060912060a020307171605090a17070e0a15180f020c0a0b18100c030b03010905070f050a061209030509180108061b1b030c160801 63
    0x6070071015039104030000f907a0041c0c0341c90416010440d2607022030600e084e64840d0340104203d11201e40c0041d0302c2000c3e40d6941e0720051654102284031030005480200e21094442e1f2014665407040c00a055400001000b06a001e642d8205090f024031078055151181d0b080500d05000c405030701381071203401400c01c0c001040641c407003000d00c036402c244030700580001c416203806101300121079811804404404c420300715940c00021001c03964030a15180221400c01c401d40c006112038510150500e07a802c030780c03030250400405600c0c0040c01807500710402801d055840c0704400c141c0d00c0901c01c0301c90040c8110024880c0c0c0d4102038000003a41c0c11540a07501c141460a02031224551043c0d4002070942903180201c0c02e807500e0b2178207507414081c0c048060381090341800c1d908041d170700e0103c102c1d04a0340b1040c1910b0f4242c954081c0d600c114035a0181c22540c11804110402c1c00350703160142d400c14405014150f074200302a4803001c6007852010b0b0680c02c00340004960500c0704400070301c01c1043d0769204035075650f412 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 984410017 1250 984408767 984408779
    0x6050a03050a1203150807030506011202031009020d1202370b0a1d07150518010c020a09020408030c1b010c0b100302030601030b040312060303090510020304080f0a031107 75
    0xa0044101c0c014120f000105451644502135009080d20541401e5104002612002499640e0909100030348441c41001c1c00040c03500c11140c448086603401038040c003003d10b00e940780314002d02540581280c0000c4240c0d000c0c0c0129600300343c0b2182c01c850544c00740c0040402c900c018035419001c200c4803100034800780d440100480e030340d510b804010343c3c4c4011080d1b20b65940c030140000414001c102c1d05804018800c038424109030200f0b00d4010740d040c800c05d000b0791410718401152903004501034a0110b61180d22020303c60b40c0a00c461444040c4020129101035884441000580e0410341c007004042c2d0000c2424251b5100500401c4840f80540300241c041521210009080b121420400391200744410041490f89480b006040c004d5600031f0202c4003e541d4a20700355012240459060b8002030400480e03030b0500045000da5400c481d0107131b0754004440c1c20141002078581e0225110b009612040000240100c010b0004132030294000c405402c800a080c10042c08400c02205541603e40002400f4410 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 984411267 1250 984410017 984410023
    0xd02120406030f020405040f09030215060f15222c07030504021801150809010203040c0b0f04030204150303020609030c070938040b010201020c0a02040b03010b12030d06050a0305 78
    0x1c8841c0c6190108000c0001c0c030b0a04020b1145400803608242051a04003040e0410713000340d8503840c8254202c41940b4440940e070aa221790603101c2503840000103400040929102c2500540d043e200b001c010b05e002c842018106048845a002c185001221801040041c40209581c00e801e250a00d6400401000c4c103450003035200001d0614080c035a48501080964540e10609031494400c2c220290565840da2848400d15040410500010390b444000900c02d00060081c1c07400303a80d101c4212407210f41070200700380003504a9000921b1407807041c04008056512409050103a01200d6440c00850342581030003400e06400500c03208003070f8810813100c00540b0300010109c0440314079800009102c00009003030459903e0a40454086500440d10301c000c00e1982e829900c20b08108660810000081c000168240e004181015123030307800c0010400051304081e0014521b1600080000980301c3c194800a20940e0300050a00c0c45540045454940d081c031501c9aa0083d200456495818915507641c00303039 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 984412517 1250 984411267 984411269
    0x50d0906050f043b06030606120a0209071202041206050a290604091e0b0406060f030e0309100c11010c0b1612020316021b06190207080a03030b030d021204 68
    0x82080341803e031503a0301a40b0700210740c514100c0200326040f1a01c4c03030b0003040585040e14030b6482401800d011038603074030705501d81c0b255842045024020300e401e0340d020040d00c020000c040809000454840f00381044041c8002c1028040b030240809450b0028144041180c0c0001c2c881d200c0742d40341000807100c0000c900c40c8a010b403510f10780c0d6180022940408110f65005031780c8508000e5060904086010384088034050410388014020007022040404100a5858605c102001b0039141660003000e079101e900815480c06542c811079140c00983d10125041025202d82400024000d10385041000010a500e002d000c10901e0310760403d000d5074698a003007010182031603403170600100618410710f000350700d045500c5200035070031901d9142501403413040e1180b4140e5000180545248000d13107043c2400c0f0031400c45000380005017442c80001038044040f2100b92014254442d01a0016242d031040128600c0c0c188280c0d80450801340301d00c1418038118013125000150340003292040e19081c02442a28 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 984413767 1250 984412517 984412529
    0x30e0f0f0a0501140126010902130c0e010f080c0c1c0807120c0203040e15090702061915170304031b180504210c020d061a060a1704060b0d050d0906050f04 68
    0x581d00d61440031b02ea0040c07508a4000703420030b40e0200d0284002c113030f0740c1c4140303150070b05515000c0c0629464001140e204000c21010f401045014020a6040c0c0c410005400c03180e00306411200224606850010788504801050340020300010410100581c010303810304049034140d0042c80032544140c0061b44a0003103004138921a4001c000284e0741303508050141a40e060064000340c8282820840207444920856440c0e540c2d070700c52040d00d0781d0400d80b440b48002d480d58a00c0c000c0c500a0800c490b0041d00100f808014259100034800400842c403071240030440c4508a1500ea202e492900d40a580b010702030351a10750701d0f24640010040031070b280c4003101e02c0040c164103400c2500c6425080503110300b51012400780d000507404104104102d629400044100c8400840382c0e090383c1c041d0200045446440d562000003242040d64a180c20885003600da001445240d020800460007404a0400c03062024151a80da01c064010005260001000c00203071200345400303490001e5652070800503220764403400c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 984415017 1250 984413767 984413819
    0x1d10180203100c020f3f1602120a030e090a140a0c03060501051614010e030d15080c0a0b0705010b0d060209040e0601050607020d050a0501020f04171c030e0f0f0a05011401 75
    0x81d0010a41b0104030014007552241d440301c44000094000d400c84c03920032406500601120810f1000c001085515a42c0c156103150805000600780b0020100140c0240012620398180c0031a01c901a44042d11440c4c1110000401c2285c4034002015261107a02150600c5010003103091242c10210307580d6030342600301d41045801d001440005005040003140300b0003030301000c14180004145a00025804100c0500846d200c07512980b0150f15400c81c402103541c0221881020403080c0510005081c0c06400b8100008a50514001080340510044030440d8926800658030305039182c50b1103562010300546006050365810900403502034410303800c0191080881c94500420802c003000100c14103540b0400a640b60700f0034501b1003000ba00540100745040010020b080d1801c00c00103101500d007001c0300640b440410105906030020a070081c0082a14051005079400d1001d08008404050030100020711235420542045400c440c02c0380884000c03a00b28070010001e40d240842c2b050100e141850203 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 984416267 1250 984415017 984415093
    0x20f030109020a0908061914060328061506022e090f0807080301180903050a2d0203130504020c0a240504050a061d10180203100c020f 59
    0x200307990308501980081900d02c1800c0030040d08100c2c9400030b0010112010040c423400182e01d00da14061201183c1140d019440381940f079008000165101d036031150070151142c1101c0003510ae2005480b0500500941c12a0840c2c00300182d55041104a482960040d0b810f40f03011001440c3e801c0c0c1c0c0c2c2451036074262468a40c000321051021403980005c100740d001c1c10f181e0307440d101407900503100e400900c43c28143c242c16039040c0c00103108500898826030fa165035594544900510181d0322070410240d40f5001c850581301c1302c0500c008030219141400c0300c2e900290b40341c042c0d12108040030001a048070b400390b801840780403a00c0000040c20b00340729900c010828441c02c02c60012141042d4184480c1c0d282034180030070712060010210758000650f00a0b8010b10401240450179040e11010040001c000d5010b06c640d040c0005669001d581c20300170608015000d100705400181c6040482d664030f2a0a6980e1003c03401019010401040c100c0b0b41c0030054040764800307401c3e04003079611103244856800d1034402 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 984417517 1250 984416267 984416287
    0x8090a050604081317010b120609030702011d0603131b06090b0a17070c020906011b0b07020106050d031e080702060403080c13080616050906090f030a0210180504020f03010902 77
    0x110030030107002c1d02c1c030030ba0118160121031710b4044c1c820317080d800d030040c0000223016000681c0402c080303201d0f1100e08025450a4455070044400d10303655607038011050317016040700c109a0b03503020066004245a03a00300100d8a158100495220b00881015400342c200c1081008501c1c0c00003410012103501051083d00d070600320b402070320210a921409003100080d60100150503410040e022001402500d040c0100c0d5140c400642c0d0741300d0403924042c0ca00000740e1045000800d44031065911102c5440040703001651100400c1d81c030f000400b01140400c00c500080c0700d903545090389031a65080305240049513400c01c007201030b450f1340000d84041e0400415100241c5d48020503411900c202071038103406244c941d6542445a1221815164081285040c64122450390700c12400c1c0c03280f0380f100804051411480702d04100d09142c0704003084d60513009040881003d0781d00c0c0c0c1c08140c2e0303100580e120781101d402c80840c0840002400d4009a01c030381e1051051003110312500003030700e06451220200517621403140d1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 984418767 1250 984417517 984417547
    0x405090d090b04140108311202032502011413031103061303050304110303070f1b05011e02010b090108010219020f0613051501080d020c0a1d18070608060108090a05060408 75
    0xd02d52030911101c1c444807000c8149074450564864010001e08e9201c1001c0c0b402245c4030320441e03038010003815072041219070010b02030607110900c1d07105041c0380d42244600250000c40b07130001c9403c890410010202013042c000d2261070b0320601c2c0c40c11400b502c40c5185c0302440800b1142040c0380901040004400502000506c0440e4210900300030110b90310740e000e514001807050105001100d02c0068207003603007a0079030282282000d545d0161500307a130640c0c1e0404292200e115022681003159200c5004840c262200d00e5200d02078204840050b9503004e5941c00b0f01045104800110115441800c42180400010400c1741d00300001d00c003c62140c102900305680341c070080400350760040c400790000203509c07140010f4441070001a80c09440481c0849002c0001400c0075120b841c3c032405800001d8403031903001d1503d003503000010140c0c000f820081221504c1c41c18480e50072400105d400102444042d41e000b00700d950307229160344001d02c4109840c2d80c9103a111580980020b01c890000300c2c40f2601d0030140 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 984420017 1250 984418767 984418801
    0x1609080a1103120408030306010e0d050a080a120609060518010608130c0302030d020d09120f15020408030715110702030a0f02060d150f0f0303020601060f020307020405090d090b04140108 82
    0x41c20f005922503403646000c5880b948103507201c60124140c19080a828140001c3c074515668114000c1c1002c0701d032585500c03003994000c0100c50100b003104150301c080443e151181c4000381000d10000039071a800e040500c8007811814030340a50110210300100196035200c201141e100b0000b52500050f020301e4508420101d50300c3e080254140109112a400300da40020314a00403030682c0d43d6984032943c0d43c40e00c0030031110356003409800340d0f8a9a03545004620004960b1070910300320803005140a640300041400c42e003081c03070201c482200010700c0c4020b50405006440d9600f03020706000c3d10303000c1d281d130000b6581c100000004201801c048011425507481105a4201d0303071125200b1b000300b4a642070311140e120028044c120020b0500c1c01c002c289001c4401152050f00c1d41500108400d9007095029035a0b1500051100b0852108215120042c3c880b4041c050207200c099008205510154001420840850301300d0100b176170050004001400800341030411034503080c00c0030030198440e811440d040340c00d0307 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 984421267 1250 984420017 984420043
    0x10204121e06061409101401050c0a1a04050d0e0d1b050a08100e0a11010809031903020301170d052203020301180b0f06011706061902061609080a1103 66
    0x203866000145452002d40380d070b1394514116002d0180341d844c850000e07003000381c5005e082e02040111000c41c0300c550240000307000302c01504017280c1041503150f0380c6d1440e46c0a13640c854440d03840039005100400404001e42000450a414140007013074011020810b14212000042c00780344018002c2100e41008030319840203460090f01d07a5204589031034866540c0d1000c5400b00404500d401c140d2059030001084100364994848110300b04902d000c801112840c2001e00301408a020420660f014040903651107040b20316243c901588944c504407202e42e081d0744500850b0400d0b04084210082c0c60350040c12a21314a0400700600c500440c000850800d01c2c1150700000e40644c43d000d90075a0032541c800842200c81d204075200c1d8182c1d0745021282030142402d44d00f10b0301041d1500510b2140d007100c441120f41c00b410207030840c0d0a100e12100b481031080060804c4c0740c05078001106000304284d07030070005c50100e15141800f42c65a0325240d1540e070344440482c0007500280c02c645481d40680c0e4140040007035546 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 984422517 1250 984421267 984421271
    0x6070309260d150f080118081c0c021c020610180207051504020a061701060c030c08030f01031101091428080303070e0f130509101404050f010204121e06 67
    0x2804001c00740d1090303020300030310404403104d400000b02d00c45c0500408843d1480040c01300d00000c802c1d40d60360419000400103100316030700d03040b2600d948a024424000700081e558010038150099110785803000520a14040841d0051030401448013800e0300300c24100c032000c441c9c13034545541442c4250000e008120000785030340a9490000c000700c0141003214003445c022201038249555401d802c1c2ca20380c141c44c402c09612510780e40100140742c0510383e0b10401c14080e0410b06218807281c0e031502243d03071045540703a200380c01d81801171080c8a81e03081601e01c0c910084c20810900303805d11070307280c14421501d144584503030088229880461201411305500225240032903502030307101d11200752282c0040794032000044111340141303054a00050f00c1c4094440243c0540e45004030368180c48040c0900034002d1034103200340144803100d0b0100d8802c105495800301a03211940c241884c0c841e040c500440c0343c020b0756a00600040c0a07003c001809084090782c886552801d0001e00395500d06207218029000e042d0038 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 984423767 1250 984422517 984422531
    0x320904020f010c0c121b090c090b0705121912021821010203040b09010c020a030e060706090503040609050117010303021509070320100f050a0c06140c0c06070309260d 73
    0xd114800070000015071b1056216603880b06080c0048030b41c24540e50340003500804c81003140061840081070094024016910041c840d42d83e5100c4a5000034076050140c48440d0429404d203510500b1000000000c1c88250300d40002c081020910b40364030500e003413186035031080e01c1240b600011001011008000c00940d280d107060304104500e5030088030741850650800100e071102070300c0400c8084600741c1c1611500c229030340b05410300c1119003145204a03100380d51281e1000c00b04404001500042070326969a404035030030300000601d8000380d502501e1803521202e00510010b900820385618040040141150a40c0c44861881c6000d00660007d45080b250304400c940301c2804100003070485c2c1040d1048140480402d200b190851401e0b040000000d200303202c80e950107031240c8981d400c4d041c0075030703008110708a010703020250304903042d550060b40da0000207104003030650a00a190340100035080c10011550152510014184116900022404010300c900082007510060700c4280e001090200711039 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 984425017 1250 984423767 984423773
    0x1505220209030604030c1b030c060302030718080d20150c070c030b010645090e07090605100206070e1f11060117120c07320904020f010c0c12 62
    0x110600010347d4007081040501c0e00004041c0c4960313044030380c00301c4100d00131071401c84114002d4001401410030400500740b00e00c0310f16a00410200644042c10140032090384004c1d010b0305200040d03408899807003414401d42c03218640461201040d04c0b44060581e415070328011002200e100d42c000c000c2440a19110110a1141d2100f880c0d058640310346841c01c4c042d0b001594140343c035041c03d42d140d0003c180540380000c2140e1040d0719000440c01c002c442c2c00c40c16142d0f011f8000b901c000d0700400d150360380324000402991509000302401044107540000c0141c00744040251500d100500400038404840b03800300d2252651110521861080424180070204100000b0000342d01201207521601c111000402c1030621540d6040d076400480d4020402d00354001c44084541e0003084c82100503008000c40065840540c600d02c19a00003601200d582c1a000e00c540040540d03100c041c0b8034020041d41c020440140c0b030382c03000b142110509003401100c405891504840c01c007055000201040c3d2082240410 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 984426267 1250 984425017 984425027
    0x901080f010c0309110d0311120315060906040608130b13020306070206060307120203010e06160908061608150a060c050c1f080406020d0c12150522020903060403 71
    0x1940e00150000c0c041c0103006502107080d0742e00070300c000e4060907854507014031a203085810740742d0952180c02d107003803000d004810041c140074018031000382d00b10002041180301c000c3c1005418070b04030104c1d159414801100080380c843c0c0601c1c0a560305100403032011881c9003500c00301c12043c80d58051111039091a207080001540e6454410480c001d109180c00f1036504c50003c0b600b94440e0001500401800b403a0180803c1003400c80801642c01d0355880d1022842c180040c0302d80c038030580c1803903590501030150b101c0080951b1032a84c8501e105411240901c5134038407101003085980e054030728004604e6252003610707030118010409550741c0308200900c0082c5541e049400300200500800030b95080500d00c2c0e042c000c440ca568841d0400d08440025140c2549000d42d01c129007180c000c400040c1450501c04115048440c494401c034089565201c40a10083c00360040c10f8461340c0b11081752035003500c0e1a000c981e03146005d941500780e201004c4603c002c0282140d05030f13a02d0600080807243c260805041c0601 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 984427517 1250 984426267 984426283
    0x70b030c0f0d150e0f0c09040f0209190824010506180301090525030206030a02030414010911040e15011518120b01331b0605071b0f0204090809090108 66
    0x601c80b071213030002240d003240c1201032445154552289031400400204010041c4118882d218000c2d138240441001c54a030000032904501c8481400040c440c101003c0c1445c20401c2102c06461644601400802080302140c081c1101c805036a00b5840c0d81d0410072107140c0b6034241e0110713901903280020362000d001d40040c900d11708950700f00680e0660741da0741041c2c800940d05804065000030007000802c2c0d403980b0560055600502806c207034500c14514140460950350001c005031204041c0d5070f40801c1da898640705c0c0300341a0003203c000f071040307420b80e9640400c041f0701446040c0b80d0580b00720307900e40b40c64050741001740d10b100c00b9640802899141c000030900d0000801080e03407040c01681c00482c5d15008054004106071401d4400000c0c0561403083e8411011558803000030041e000080e545080c4001000703070002403017240e002c103143c0751041000344400701c2e003103001d206c8051420514020500050508007c15010317180400c0030005030500348071a200d00881c880c0c0200709000001a900b00c0458440d07 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 984428767 1250 984427517 984427529
    0xc02061005030a0b13020409080307110c06160f0528050c04020304031205060319050604030f08100504020f040b0403230705090a2a03020912070b030c0f0d15 69
    0x40303a44035002e060707a58507103200080c50154040040b0340c840800c2802c40c58901d1000780b02043e0028a42d075217518a40065640d000422890011900d05401c288034103190080c040d81d405081009090324001d0203a81868003400c451448420700e0203004050268200c50740f800801e28981e0b0b4062403803000c010341c00c0e40e02541c0174001c4c282d01a86c0c51401c2c0c021207010315010354545041100b02c4031588014003014014550620030038685564402d120307442d5042d140d0041c40546101c0c50030381000740103442869443c004205180c020000d075030320110080e00544000351001600c0b54100741a00302284900c0e080581c2010020400004100d408a5641c0402984160f482c0000c1d0b09003400311342d154960702030300d5070201e1036000040c0c3c41410381d444207203100051244c0b6450110034035469800c01c48400d603004c00007900000e49039401d04000454110031000f20005048451a0010600c020301010341460340110b00080e8200185c0c3c640c10507684400a10360080200544036001c0c0300300c01003c2e00c116 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 984430017 1250 984428767 984428791
    0x1205091f0203010e06060f280e03120d090c1a04050a06080105060304141f06050f0901080d05030403090b0a0c0c05040b0f010e0103110403060501170a0312090c090c0206 74
    0xd6000c800c03541c02901c1c101d805540c9aa80c0f03a49a42080020a4020880000c8000b500340607040c2c10a0b02d118541a04588403840c8500d102c24207030005180040c403108450190b481141c8a004c0c2c0640f242c100c501544035000001000c034103900c0c0000460300313513a04c0341c2c035110309982085a0000c3e0a10080041b00c504980782030001356901802c6c4c8041d402407240c3c5030b0000b814400980415000d5000452a85005007510400720380c4104150213120064110b4103400d40d141024070640c1018900c124040310100d6050400e0740c5014501d50343d8443c90420306040240101c0420f04060042060401416403140c0050303c0d0141240d00600346140c1460a403603504180d5800102d03400e1502c9000312014001e03040450201d503580056a01190034a101c60401d6511003030110403c0c8003030007403c059446500045143e5140102a101d103001c00c4401d4003031a00440800c2c400030750000110b8001503a45407011610010324100020440c026501c00c000c03050402222490080c0e0101f04103128007002c03061 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 984431267 1250 984430017 984430063
    0x2090108090604050c1003021b010f0f060503121809010306151406090d031b030e0a09060b04091e02030708091501081e07030210020a05060a02090916120509 69
    0x842ea80705415a40a0555000803e9040d500c0c1080c00c000e121100346410054600004800b180258074000480b00b12140d56039140a01c0001d168081c003800342025282c03e0013040d04040002c0c0d1106d0f1010402d00c001c1800244451300107140c03a8100741c02c20401007210b5415070b0740b41400000390401003188810081d501c4004138604e000c2e40e8000400b4000500010705180c4110244280125003007001d4090110401004e0607485000c01c54070140d03071083d0740b443c48082040042c070908946130341004444074200304040c4211000c0d1015182100d0300010041a0b91565101444200144821140805000004110b11140c00103a064000c280782001c81e01001905003106140ca00203000f0f946190b0081904842418007c20300040d803c0000001e1740c40c0785030b595000034448542c0b105281c025800c01c0c0400002d0220074045c483d80000c01260951401410300005400168000c0c49030f40341c0703821a2000c0300078a01c00c00c002c022520700a0000c21030341c20800051aa43e0035086007455003c000a18 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 984432517 1250 984431267 984431281
    0x30504092007110301060509070507170c0d14071208090f2802030f0d1e020102130603050403020a1b09110702102304060306090e01090210230d02090108 67
    0x2100104240502581c0740c1000440e90729a00500041d020703507949503495100100341c5550303000406001d00e4076038840503524a6607180a0100060312900c2c0302003c0c0c03003880030318100030003c9207400445c0c42d1741c40c01c44442c5803029038807200c41c040d1800c007900d407491101c460800f04c3c0d0801c589902403407a80c0100d540070703045c0750b010550381c0030468030003107003009000a0704020410991010380302d40d1000302591500c0c992010600d190241c0064201c002411040c0c0c10310f40780e0b00c00602406c031880300340b00030361030801d040703903000316a11203481040c007015506c400142c1414828000001d04640c05440b1023003000c22105041c0c1c5101c114000d000c1c5091500383e500000d420018100c519440e4007030a402c0c401d02d061401603a501c00403c211090084400c00c0700414000c0c000d00400c040c01c4182c400107105414050050304562005480c8541603160561300000742e41c0f0087d041020420500c2e000030b440c84c0c416006035544d070500391070f25503001c030218142d03003007601c80e40103000307291403c0e40c80b458250340d601 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 984433767 1250 984432517 984432551
    0x3030e01021c0b030c131505030703030c02010f03060e090f07060f0804140a05030c0a060c0e0315060a080106080c031002040f03030f0e0d061505031c0810030506010303050409 77
    0xc080c64014a41d82c0c00d001d4034960305a00704075142d90f00241030791100841000400d0400015104201c0d1003a900c2c10300c100801c1100107103070081c25003039001b00301e9a030079135070054941c03812410040e0500c05c3c03519000c03001d54880d4026101070040784d8032060b480d0501c54072599856184001c840510f0041c001c0205085229008058558125549009031a2034580b10194032051403c2d0004881c040c40c1d02c0780d0080740e030030801003904c071042c84000c06034201d407414200c044420b0024020304000201e20002d00380e17640010b5440203003004c0c1c481491152100c2001424100d0385034041402035080040016080f007010611984608042c0c05076041d50380d20f401c2081c1244035138007502c000c4d208281410310100b8410100c2240c8850b890504078082080540010f0108042032030846a0350744500640c907150b071011503070342c00406059000300103103030340c40c00c810500c0c0301d0300414842000901c4001409540503a04010015034110b03056981e9940c5a081c01022580b00d400740c0d269031030800002070001034100d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 984435017 1250 984433767 984433777
    0x1e02040f0c05041e030f0f0b0a09080d0b01020c12010207060f05070504061404030206030c09031507080117100507050909010614031504020705060f01090c03060312050a0504030c080a03030e0102 85
    0x60390342c0703803902e8105280f1285402c181c0350605528100040084000b9016001000804e401035001c1000c01c822480d0a00040000401c8402c0007410503205000003034948003a40c04c2e01414410200b410404840100d1500c0345a01c083e5510410142e90080f10710810343c0200503250003800c0c00d000c003182420b81c420a80c1d50588100b80014403c0204002040c4a01184030b003d0500c48022850f1955940000d00c20360000d81d22340c107402c1c0c000605550103150402072280d802c41c0d01c0c2c001c04c485150250002d01420380c14440d00321840007031002c00c2022a014401250f03964006e10042144e401d180c03400421039089110000c0c0104810000411311600840b5200c1103a00b054480b6441c6580b500c003100821510074403000d81141c1c00380803c000040c03060024600c10542e42c2a0308500c3d6140510f901d0641e1015a5507105061410300309002052140014a140c94403506200c0c0e0b03614003a02007200d0511a40d0300152454480d00e402142a00c0d0103e64070090350f000743d070240008000800b0b214200d00c12 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 984436267 1250 984435017 984435041
    0x6301908070602030c0f04060905090610200f0312060103050105031516030e010903030f0f1e02030c0903100605031507020d0c080c070315050a090213020d091e02040f 73
    0x24054480002d000380c0055900003132403940582018100d030700841442d0407541141022071100042031040e402c1840365a64007000841c1c110b4a02000014041c1054101941b500c1c0b10141400c030861031040200070110b15442d0a00803240d507406842d440480400c400d0b070f1250700203410704c00001014a0000340a03100241c9030080781619881c1d20240c4600321380041c0c00c450616490320100750740c4000a1295200c2e0744d0003610040b855594829501d4111041c06440a44203464646211110040c486810404400f001d9005940752910100b1200d0ba0186c00d440a0b494030400445421042454004208030b807000d400706e030f0b41149288065010f100c0300702c4582e40141d01c0f02c4048030302c84e84544000c24060740240e00b041c3c0f40a0030118803605004850300140c41400f120800c1081c603010b03501c94607911003c000d0080180d440c15500142119a0b00c0c0041c0000d01c1c5c000c12005583d03845c0340c5c08003001c56802040300200e0903481c4140c03240d004416406038800ea01d00504510818800e0268600c0a0f107 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 984437517 1250 984436267 984436283
    0x150a0303051b010b06030910050106082211092d060f101806020d1209120804060b0d0c080105090708070506070602070b070c050709020f030f063019 65
    0x114541004076200b8602614402c903641321511281e2a0319800002c0d070140c150b010103056101440443c110944006034081d104111012080141680103400c0c10f03c02d018006490b12001403444c1010344244032101c21081c0d00c942a40709001c52240780a105400302010054044a6100a0300c022680750108954580c4c02020350810804145064030541c0d450005504006103402400c465a00c146241030b000032001d81e0100714548041c540005007106420302c2294284500c03000c035595069240515411031042c0100300700071508000c1c0035044000360b540b01030300b000e465080e241070007400c5041520500029500c4d01000c02d01100c401324440c1c080c1c80c4901c1c01000000d20701410300907140d04c03030a41526036075030902c04080002c0d107040032180684607540d586a403401c180d04107507050120030703801041c10703e1042000700d0842102e0000d607640322480c11070124059450101142c0d80f503911502c00003950900d1554101d141800241c4001101407007070031100401a2000c0c060450fa00150019229803 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 984438767 1250 984437517 984437527
    0x219030c050d020301090b040b07301d0f010213050409120e0607080409060e010e010e0106030b01170702071809030801260a140114010e13030e100503150a030305 71
    0x1042c0010b0080e4140d201900000304190b158880500303c0400391804c039080c03c107810038002e1069110310103010b0880841c1005d00c200310114402c1c1900c410800d4541c3c0c50944885030b141c0c03102200c8001c0081c942c1c4d01c0301541d10558407101c4c00d9000350300c61800100c13840b9824038003042e50b040910504d03840301e9202180462801d2841c0040d94003620145e0307038550114040142d0310006500740c01400040c00450340124180d82451041244058142c00054003240130100410040381c0c0402840e04603102402d0005240c203129004071200401c000d09000840d2103d0700f40310305031b40e00284002c1218810700d51010070403160f14502060b52001400900001d04450040c460883c0b11802d4100034260104c40e110703465290552281040b1138200300751403a01a00f642c9200b41e071420301550346400c5003281030780d44540c140605400d801c0d502170181c0c4400c00f0130020301c3d010180120b02800c507d100003031807044420304c0c034440103050354802c40c0c0d001e01107409992501000d051000d040426a07070f060702e0b07980c241 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 984440017 1250 984438767 984438769
    0x605070b0a0b0a0f08060606070209040308070c020a18050606090d1704410a0b1b061f0e0601080f0c040906060507030305100e130c0f09090219030c05 66
    0x1450300600505081e0740e452020030314903920b2041d00c0000f8186141075440c0180b6081181e400c21400034441030180c0c00030030107a03006079a880c001641c000c1d171504003801592512141102c85c0300c4c6074140203400a03070704900850704c0b100145c02d000389215644c80500c043c0c3e86000a00029000b0b00b1100e40e044220216520001080c00d0100301d900d071000c0e0801c40c00d0950f1014040785842c88849529900a200c0b4109103da881343c802540c5580007005c1c4d18000c011441c03002c50072041c82d41c40384202110000c41e110f414103040b400e0181c0b140c9072401c21143c080c04e107039003a503c1c519501c0012480c003c403040310005440100300b116610031101615200c4107551043c5980c80c001000070007566101c0c800300004540d03080c00e88100b4000c0c015550b81d982d29001d040c60050121030001c1d10403680c45c143c0e1842000010b5604a5243e402000e8481026500200d882d080030003c0031604822546010584046625541070740705287c094001c440c1b41c0c080e00724006094000020381c0c0409031441901d00410f100b5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 984441267 1250 984440017 984440033
    0x80304140d052a03040902090a0902071a180703030e10020f0c15040b19091707180b040617011b090312110a11150405030a06090f0f0312050c0301060507 67
    0x400050701d0b00b00303400b0380201d20601c0c20345c1d0054224050780350340031800c1d180a003030401111016146008086181640507181c810060001a01440c80d0190742c100040d420341d1100081d281c030450120464001c04c2c1c5900e00580140c0700400c203103000d448036040c4042054400100f042e0b15a02d69405016400841004d000002041d00030240d0b100c401004005804100c0d04010009031410180080c181d0030007d500800c41e6000b0340c07200d01007a01d0104502d00c007081c0450004115603000c1052820703061100c01502c050040e5505c0f15911915001c000a201101080000e010050040080050b600409040d00031080078581e580001b03901c1d00002d00000c2c0e0829035541e130180311400d00c02022030000101a140448240301260100c0c5d4416011040781088881417184801404242d400d04c3d042002007590b5250b89080034020646947c403c506000300f0200b90b0881c207411400d603401050035420060401092482c090035040c1c580000542000c0d0b0b6201664161913007a81c0c0c0500c0c00e05d40da01c817114 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 984442517 1250 984441267 984441307
    0xd03022113020a09020c0615010215060a150905090a0207120f02120f190305010b0f0f0f0a0507050610050d02040507141801033204110904080304140d05 67
    0x803258280e604030304050703999950307900020044c40130091ba0b00d0f40d140a0b0581032000c00b07868402c00c40da00c1c0110021a030b0f000305551044034001c0ca4031000c260384403000a51802e036543e0100f83c915000b0002d1411f41a1702c255084c080c1c88042c0c600c1c42c04e07520b60802440032840794001c00341c20760001c001d60303148851040c110000300c1c105520454101042c851800c4100b64403c4034800d0a200002031205c1c07000070003c58909121607903060070040c0d50b25007010320100e80710742207100b0880b0900140915000e587c0406030780c0c52522510119031544c0b16058040c04a41c041d0105a45501c50900051081d80408454000782d500141800c00f00c0c0403541d0074007019244c042c1c0307640c0901c00507103d125502c0800790060610310f006801c00780e0f03240d00310600260071148504e0601d01c503c0d1040f00100a00e402420140620311120f186507812a5201e04000d9500710501c5517180d409103c84050100b07010011002d03500072405103100019442c2e144100c103a4071b600302600380d0f0114000348580c0220904405140b6 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 984443767 1250 984442517 984442531
    0x15130303210204090b0906090106080106050705030f0315010801090e0a0311150c0306121c1808012406020a020f010509031608030703110304030c09020d020405120606030d030221 78
    0xa081408a18a000b660015041501d6103591aa4010303030034902694a16004103050300c803000513504003023000703080d548140213038014810002600000c01504004450060051401080d12030500248500c8041000303440c15000840c0d903400420510001d11405041058003801004a1684c0d40d038142d071441920f4400162a0181402900d80c9000b9249000c2c41004078043c1e5554134a010810048070b01c1c44100181c4403607100c00102c0310004906551000c20031494200740c01001c45a1009100040d1180c000072070f5035090410303880442d44200046101071840755428620140c035500102e0b600c076400800039500202c802c03103c5c030865010704c0050a54550103010382d04407001d028107105212900e94482803490b07000184400503d42c0c843d642020032070b0b100000d1031400b851502c6260052100d40545251542c3c0010f8030820404158112001000081c1800e00001c140c844140d0700c03518100c1f0424024025a140c011206120f8402c452803060300301300e180b45c040b0402c11200e2004c04010948 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 984445017 1250 984443767 984443807
    0xc0a020705010f09050607060c0f0507030804080d110a020102070501060605090303030a1a0a080c03010c210e0c04111201050a050112092d110d020607060515040c0e15130303 76
    0x80b172252108402000c0341405941b004c91000100c01c030003014011440b80f0741040010034040d034800680d01174001d070f40045e00a1000703510703410600f170018002e203a200d0701c0b0300282c100025070700d00143e0190060714500f07001e6002040981e80e43c41c0151000c0c1320b940005641a0803c10000e5140340c40360f030040b0382e0000340c0101c04a40d00c3c5d101d004240394404035082864140e00c0503844d08000c0c6800d02880320400010702d00307410390100c0700e00a07a50b0901d213030104540107900c451041c00b030142d0401040c03002200040061141030f05205011001d54400b920508041408000100e811b05110300a40211807060b500e040440310450078500060913811412255a80c2c0903010305001c0d840510340c24440055450207050608151404a00b05400f50503514000c00500d298200581d49402c165158039130810700100d181d03070312540302c1c220034000e114017594403900e882c00d134400e0b20368820f081d0360701c800c001d9a18100c0c000358116104014015502d82811000110f0010b100003407040100c0e010549000d408 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 984446267 1250 984445017 984445019
    0x612090609050d090306050105030a03080417070204050c070308160203030601120207020a0f050a06030b030d0e1f020d020705030703020d080703050f1c05011d06010e01020f01110306090c0a020705010f09 89
    0xd940d0905a0050300000004d4407004240300f841014483c550042070100c004140e003014a540240a214000f00083c10301e034001d1030302010300d85282d0211400264024800c1126141c025a000604d801c4224160000380109000070701c05070180144092000311500111304690790100115140a03a0301100c150740398090041c4030050300c0b1065641b014003a40030b05094030341d083c0420b101000807180c1c003950030541003002c020f6003a100403600125107025843c100c0d0703c0d2906400441e03889035810305210100744840500225140c3d0114070001d1241d091390985400c00c1d5035804150341da00441c000a0340c0300c40c40841c07140000311044000c11809204e0704095007001400441c0e48010b4106200320745034070440c80c81d0807050361302922a5501422804840d03172007903020111010007503500149003d040c0542c90010300300c5030780200440c41e020319042d03000784410480f50300c40036400c0e0000d84485001e00a02800708095a00302015503041c0e43d120b81c001d140b0a842d003001195032404046045041c4003c1081c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 984447517 1250 984446267 984446273
    0x70c1b0305100203040201270909020a0b03040516080c090a0515190609091406040902060418090506070c080a0e0a180203090d08100b03041b1d010b03010612090609 72
    0x10b0440c0c400380000e00140c42c1d00d0f260002500850258554407501c0d00100280c04200b514604803906039010b81100082c102c5651001c180c038594a07402401e401840841000100b100015440340c40600d4400786109080d0303103a00c140c0c1c1c1d46104042300c62f480281940080c44180c065480b40c2d40c041202031021440d101303014041601407080314443e4850194006040c005640c100b0784000041150400030081c424090310403944121010b001300c0d124540720403201d07043d5528141603c025104000f010340d00040715803219801011880f0341115203001c1c4500040318907000b020401d42482d0003400072442c0219048084070250303003031000307254060110031012030b80c5540c0e859800d090000080340107a49040008429260088000e1700c40108140f4104005055100841d824102e9444a41407500c0340c0b26498041094a010b021001c01c00305850400900082c64045056811218900700c20080c0d803203245008981c8824021403020440c1c0c140340381204501d0380c0c48001c5140c003d0b10300280009840d5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 984448767 1250 984447517 984447523
    0x2b0204090c1a19020303070c030c030306080d0302090f030304051c06090803070504091505031002070c032108010b0306010503040f1b030c1a1e09010c1502031e070c1b0305 75
    0x2d00550714401c004a030580f0304580107001040c10300a103000850842c600740030001c4c00c84c802818002c02304031035030b0120030803d03000340c011401602ca034100361244801e1041e070040007500644402c83c440e498081c3c842071542404001c80f425540081c0080340b812800c5400d50628282400046070702560b1400ca80d004a01e41401071409030b5a81d640f40da40d00c2d860f00003084140c500b8a10b218226034017001c400c115a40e000907201010301c205e14009a1102814101600d0811050f0f00180150701103108025078080c24405038224035500d910740160301d90325980f800c3c049000071280a40800c00800126000c15120204600c000b0302c0f0b810040ca10300d0000044101e551000d50007100c02c41c4505030f080c000340044029006818100d600c5050808414401c0007607110001c41388040b04400c00540b007180d03644203e049081d03280d00440104410301c25036660a0003903000711002624141c825909103190080b11070301c10f0085056544400c0e01428540310285207100c185e41d00420503840c2040000021014 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 984450017 1250 984448767 984448799
    0xc13030305091810060f1116290d02280206070e0d0818030316030503010306060b070b040b0901020d09140c011806121104142b0204090c 60
    0x303591000d4035001ca0206101120300d5105540000034403200c20400312482201440301103d4040c9010b007a0382d420608190785060b03448071a818036000d0301c502405034a044100c844221442d40010950340301c400c8000c21024600018801d4200c10100240700c48806240c000d40340103040800303200b200500340b4000022103a00c031102800942c200c10100031106401000f000400001500d41c3e2848140564030312055200d68a41d40f803400d030280151454603142002030700e40c00722001269142325442da00f806889078209100c01c65402e402d04402113940154001542e40c0309901009012083e01c03159202604c5100c0206080b07420341d4240a0800011041d00520100c24040c580c11504114003003c10742c1008040c0403510306100d03003c3c45030461350300780841c84070403a8114500004400c40100058014260800b180f609040c004107020800309100c4501045200c0c003201c031404444a010300000340600c0604149204507000c0c030064016080c560450120035100780000f400091f00e962983c0501840307 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 984451267 1250 984450017 984450023
    0xb0a032a2303010c0507152012071b02010309050a0204050109020901031d06160c0b01260a0b060d020607120306051003020405030c010c02060c060106050c0c0a0e0406050c1303 77
    0xc01241001c222250420340300410150024003d40e800124080c00f28451424000c0000c1d0000d81e042e00342c0c8005038005090050303943e2901c4000c06114041d410103400c9041c0540b10001d0341c07000300e00601e000d041103100701c1c0314922054410782c4440c0c00540c02881000c3c4107540b11700035400c020006030380e144206400780408001c01a00c0c1d0700c0070800102110100054440c040f0780c110a0500c840c100041c880d0b6200541c0d484085003c26800000c4580c0d100c01306d40100917030108000032810018000f0301c8900003610079030703c00310030f480035803415600d03c00c152024002074109000b0481908000d038087c03e40300e002070000c1d441d2402d6070f982c0c030742992110304100001a584210034010303460301c120741098861051805500381400c00300000c0d103850711000e03010b061124180d5003504545450040d0341c00c000669003518401d60b516540a00a940214190b20081c0039200076103e00e45044081d86c81640c2e20340b20307085c4540d540c969408006007800740100d000b0180511000300b0580c000aa100080c40c8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 984452517 1250 984451267 984451289
    0x21005010f1401031103060d1a040825031d0301062414030903090906132c162d0b04061205061c0311011406130b0a032a 53
    0x45030410200c100b10895011034105401c010017590030b18940c0007681d030014021a5050840d490070f141c6070f4501b055500d00d50302c0c0756060108010074071030114040c0c020042c058a104a450b0320012a0341d0546914080080110740c0810040c0c2d42d0003521b8811600941c0082d00001d4410389512030240811500490f01d0001040c030081540050784c07001481034910044502e25045081c0b100d01680c4034010300703d895008101520000308190f80d00d1070484170b64400300000300841d0703250580e04424840107900005011001d0420f480d980c1c8800108860158451441c0c520399505100d00380c410b00c902e01582c601d002c88000214200304c0c0000c1c081e40014084404283d503540e1030701c00c0c0a00081c4900600d14001884e21381081b401d921101c103030810400c86031004ca070480300c8524054519042c101c017024165881d06168402d206060807565001d4a07085500c0c04901152103147d0059814000030b540d08003a05140400004181c1040040c49413001104044034822001c0303102844025a48450030700c103 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 984453767 1250 984452517 984452519
    0x30d05041703090721060501150824010e27010e070c0807020910030b0702030c010506041b110703080d1b02160b130e011511210703021005010f 63
    0x14039120440303207544615825504514001c001c09480b0311052003008042080c58985e42d02e071464000440c0c031007642c440070400655031542001141600703c1800da502062908010a11110401c80102006d06080c022449100056001180d010004d80c980c142c206040d845442c00c10540c1c0074403074407611a00c060b010490342c5494420036285c04041d00503410f01c601424108041009002101c0c1202d4065039400c9041e1117004403002d821010317601c05888440b911060000d0386a004c4020201d042420009004176100c2c0802c0100b00c800b0440d503c40360b22074503100026828000c0024034003030103040c000e07200e0403540e035102c10390640c0c0a01d00c040c50301c90f035501c610090550a900041c2041c00248010084c05038200c2525801d0401030288400c3c0600c0030550406180c42819100007400c0c1c03141da101915607480d44203049501f403512034a404108202e40300310445400181d410044000b4154001c80790040c50358440340d65210003810380450244805000d54800207014240c028118005405801 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 984455017 1250 984453767 984453773
    0x20133171009111017130f020d0602130b03060603071b0501290a080c090601200a02010f181a04050619110607020d0509060c0d0903050129040e0109050d0801090c030c0c0b04060e030d0504 82
    0xf00d07180c224080380dc0040c070603c012a1540416070760302203003a04160144440303810f0002c20b10a84400002d180b50f00344542001c0c10109500301c0222010303d8040090800138200411100841600034044903034000e090b2480d0a10340300d01050780040042c10b181c000610243c090394560380a8104046960340f00003450011035905c0150070220001528140050658008200d10408058455441c0282d1821044c3d460518840220b40081000414241d943d80410800c4060000603a41c43d00110700c3c500c20100c5c00c0e500204010f4411003569004d00341308400b000b070079030b034a800188809401c410240b00c1c09240c95010440407887c2192602c0d002e00f244c2c91450440d0941c0d100c100126011140c04070850510ba080c032510140340901100c2c041013541701d00e080b980c01008074a001604a21540070156003a130b0300003040506980d0051410300010f40070802c140d003511043c4108000081c0d00020b4203000c102c50424694105100d444082001810712800901d0b6800000380300401c259900c0c240410 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 984456267 1250 984455017 984455047
    0xc0f1516051b01050a0e0102030d1508100209010206010b030a020d020d0f050c19050714010507110705040902090408091201020a020133171009111017130f020d0602 72
    0x965034044030810382d000386850000b4010302503149844280441e1b0106c000c081d078000d0059034003030000308030100b00303000000d107049003292000c0c82540414011100302c2c4060281d1070003101c0302e500040e0000d2515900e0a0200d6015900c02020110078582c248011080e4076080c0c001840e1942d000d440c041243c81212408100700c91002c0c01d46000d4400c100545040c980c01c5a2008820403540d060dea41c642c1d85030704149012003554240540554a003904109499800c18a40b9608001d21411500b100c2d441344280004c40b219400c01a6005c0210303800039000407030260040c20520405011504800c074203460a909903008000c0100c0581d45900d1140b00d80c0144072a42154035041480000340b0840e016010302002d03143d8010b030291000d008045000c2550200014000326107060001c01603072485040190481c08100c12081c03251001d100e01408480c41100c1e401010400e04100841603160800c0d03020003802c10b84811036800e40c03084030500c003590b82c00c455401541e01440b0050703510141c840507852 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 984457517 1250 984456267 984456283
    0x201080a050103200f0909070609120c0506031503120319020301051018030507030b07030524011803020301050f090115120b2e080d020705030c0f151605 67
    0x5440d01c1c2200410200c2d0075403000410240b0780d201201199400900443c1042d01e42120040d0400e0602041c0400340d02c0028008080369030659030403050a0300c03070710039000803030742c00b03002602c45280d180b000c0c002860031800441e000b0f20008100b5084003400c1001c030b414081f440404004011010003001642c0210b040390003880d4070094000c41c690740c104070000e1200b010742044a010042081111401c9200311a00d182c050f541040446520941e00d00d4040001e54089514600190802d030200381c40a030a00c400e0803e40301841c84151184507a480111010b2071b9807880503280c1d840a10000000d62030a02c1150701600c80011104014a0a20003036030030b440303610314514890f021039042040801036440c0407040c20b035805030344010140c42d03182203031000c9000402d52074410304d014407409486442009180c0d0445602c03409946c0c001c1164501a61603440c070340714442c0c140c0c004c00146403551400d4142e04d5450300d4018000450411820796410b56a0405c803c2a48d0403410800c00400744801082601 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 984458767 1250 984457517 984457531
    0x41104092a09061b0204180f060c0305061e040f180c12020303030103060f0f0c0c0203060f0c0d110c010e0a03030f1e0509011407020a20061e0408031204020108 70
    0xa4202c070b2030031600815408141407048608116200d030345045541d00d80080f100610000304c950300100140c14000502e94a9280c00c503086c41c0b0b0440d030032040d14028007401e1302c10759004000540c40340d0403000088110130280412580266652006840000507204103070101c0b0092904074400e20b20341ca4200b15010301500050320140703241c0060710040c2d600004513410b5943c401b001181e5040c8440e10312029140012942c242c09041134010b40e201d0390310005500c81c2c2c0340228200d40054440d140b002e0740c0c2c2c1005407140d09500e9000c0007080e0745100c10307820546140da9a404541e240004896445c0d08498591460f11141d40220480c0d00c18564107005601c42045503000810040c82319050301440105880c80c440c124076110000508610400e6010401015444202d0300d61441d0a82000b0f481da503a440b82142c1c00c000c0e480010700c2c1e8000360a00000402e402601d2103207000001030b00102d07014208802140901020000414075440500c043c140c0703040d100c020b03a0018181480007616204c4018040 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 984460017 1250 984458767 984458777
    0x406020c01020705030f1f02160b07080a0501051302090105040e1815130327141905030607050c0f0a030203180613050f01030222030303060b0c0c041104092a 69
    0x101440076404107900d011041031860540b00c00314141c07d264040e00420005411349604a0500340c00d001521880500c5031100e40d4421240c6c1e540c044100c402c48000303000f2290000c14030500310186035441e40c020000c040050501c6403d00d661800c40c1e8104000848085081c00e0320301840540d003640421008070402e102501035005032401440030140005120303009010085550210a1b54410502c0d0380144038400f03000d10300d1610703190a208444004440d01007030003a004004004400c2a2008040080d10340050140007251110f901c00c4134503404c24a03141d8440e0189a22100c0910820482050441d200c0d40265840f05000008030000510070f0302241e010b000304020340aa404241c41801c000e54400301c66030807080b400e180040b0024000e01c98030300c1601d511185080700c41d03c910905201280d1007030340c0501c07929480340d603540c00e180640124000650b007c1c00441c2500d01d01178101c108810740c900d00141c102035842d0556000e850100e8080642d01380c1c88400c21503011030398962a0f404500c0c1f4100 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 984461267 1250 984460017 984460033
    0x60c020316080703091d040c090e100e03040b0c01050601022b0c080f070501090c1208030a020d0b0402070b070f02211303020301090804141504290406020c0102070503 73
    0x741c0c0300e20048207001048440d001982408241c018003005011340f500507040c0900c2e203050008805161000d07507040e00c0402e040c0c400000c00d802180641c00000a10001800e40301c00c900c819980900403410700c80c4054001403101040250312003002d00303181024240082000d00f01040064141040c00c44614041507030324a950700e921a00180021103420300340340c0744d083e032892410071401d18010541c0400d0000c00010300d007424060b05400c11741000c0d000e00c0120f11080c1e42c0d26507508085841400c01842c24105100044948ad400d601402e02024060404500c0b2001540014100c3e403114400300c5201e10490300b4404456070100c04e000800042c1d00007040c44903256001000000091011500622030014042101600b81d006081c01164080c009000700f0300e0724500903590742c0090040b0004109003000052151500304034811207204142071030f80c80c0c1350800318110000120304200c039801c0c0280c071085c104d121004c01d000344010104d42d40504070415506000a04040d036652200d8425400071070 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 984462517 1250 984461267 984461287
    0xb0405010312050304050f010e0307022e05070c0305060c04030b13030503131703090d1d1f0201091704060f051809180d0306050406080d0804030806011812060c0203 72
    0x28140064040c2c50409644995892038002e150403010a40d0340c80a5003040d4001c0c5e01d000c0c001000d418828400c4800e0b80e0b4068041c02c0300c4404488004c640392507000840d020400c3d40b80144020304016010341d210149017522601c03128900304c1e00351341903a02000700050800501100c922881c2d0814944404d0050008403518001e00d1800040d00020b5114040c000f041c0401418090142c4205000180b083e100e18103d0005511141040c00120208002d0000000d82c14242491b1800c07400340144801d10f15146050103444911940340320409544d41c44507030f0404900c1401c1c00100d011000390806590318100480200381c405000d24420500c8014003a620380f10120b01c40c500c4c6e004600395225441a560300180b000c80504084503180e0340d0107143e0f841e0050030340c5074100205840c8140d50902501e5030303c0e11219070303502c0c8103000c0c0300c00125a00041800240705260403a0042014584107000350308090307001d80310384059131158000aaa141603241004214054500600d1050000c0c5d41442c416207 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 984463767 1250 984462517 984462533
    0x5c030c0108070e0301020d05010b0702040c090e0a02033111100509310f0b100206040b07120c08160c0f240203090a0c081609020d061a030a0b04050103 66
    0x740042c0284014400c074258580c40960549140c20100c80c0b060000b540c0da200414440d61000006034000c0b400c01036103010060091482c84100c800e40025501c0e140d4842d07800c40300a410280030002c29215404805c20340c082e90244d45020080e0510526000130128074005003c00c140d11480f40c0a0400608085981d80d000003d84440d044143c81800320030b1007484030301c4c40700800c0d208a2164254a500c0003040100c040d80005504101c0d00000c1100e003c202e020400e00b180d441c2e156900580c090000034001600c0e80080541015a500b40780e1400300400140070281c035459426100040e0101042043c2d07a030803009005111300da18181182c890b8000d44400807402000e030402350081d01c1c04084210102020b1b050610007200c80201191203080840b01c050b2100d40c1c3d0803041d1504078a040e0081400d20b0085021202000001c440c5124030b4900390401019401c00079504000a54814001844802c2915600b01800d07501c0350710340d80d07490000003c90440320b403158900d001d54a05401400012f00007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 984465017 1250 984463767 984463771
    0x60f220c110304060e190e090f060f0408090d0b0c070506060d05030403030c11040216030e090f0711100e1510030305030a090f3005075c030c0108 64
    0x13900c3c01218018058010600103c154044016194508040052810f40542c41e45005079040c80507200b0f0307034900000855440009642c020038118000000c2800240818010200001d026200f2800e091864a6008001c401141c44803414a4005104801c00074180150396120b07004440303a4000b4140c07a2202d564034080c0f800003c05000c8120444024800078480000303180c0c00c010419541c9140300d10740d03051780689542c0200d000c5210030300c000c402481c0c0303462428032501c04140900e10a0341c032000100d8255110004030030160003a4007000c80e24900381d021303150582e11034100a00c924100500303a000c082c14020112504000002018000a503206048a403c402d0700300c80421200030b2800c2040400d256600020503101c2c290801e1201041c1e003041048150340382501c0c0040c0200d15003c252200c0c0310f012001066800320555440100340401e18001e041e4400901c40750030481f8400c030030159003d0480140041910f111483c001001e41015904103a103415005402070049000020305003040c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 984466267 1250 984465017 984465029
    0x30b0f0a0b0f0714030409020d060e060112050a09020402031005120a1212240303200606120a02060301090510060f0203092e180e0c0f03060f220c110304 67
    0x11004180091148509491044c050a40e0faa0325540c015550013035000c104010080d40c104040010303000341403080584102d006031114a500000d0108500003002c009103803c080f6990b550f4080d001d601c031480510301c158180b084400d140c5007024100b141c001a80e03000c01c0020341c400404035002a80340f110705149030b540ea0600c549039440c9181c00001512464280130101002e001903008240c05400019044a0081e00e0320a000e034a6108141c2001c0c003002c208083c40d900c480c000c240241480d02c0c1200910a10310140c40c00340c0216030000e20640d2081c1e00014100e034031081441002036802c110600140464108481c00c80701010000c0d440b07000e43d200007441071076042c28611121300801c2602c5072100d0510b1030402a2881050b01910300d0755068030031100b10f0001035010504151422400d401802140200c0b410a0700c00440080320ba400142002c0d0002d5500e120100a5111600014286482c0d542c541c2c401c0188124002c040b01c00e100c40104c1004880194440a04004422035080d604 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 984467517 1250 984466267 984466297
    0x1503070c06051e090a03030e030f040512100213080105011211012303010b121303020309101b0b0a05070e1e03030c0d030b100203030f0106050304050a0210030b0f0a0b 73
    0x65003000005865203c841c0c15901d0401001c10080e164034007240342040c69220780c6082112016110081d5503a00030440408044d40702080f041c4404d10b0603115118201c02c03c80111034868140b80e10420903600003003461a880700c6415400c0c02008001c0c01128054404040d26000c4c10225032120000ca4180c050980d05100c110740c10100c00f20102c031450425109080005a40d179692110618510781c46a8144a02c110f00513010581d0340c04541c0d82e00310003a07010b900035410585104104854090348006050500440c070b04400c20722200d54152031009070044031301010f00c0c0380038404c80c003c0e280000c4c20901001240f0546500d00c0ea00d2104d0b02603d0300c0f060740011024003940000c00e146224100390316000e4842c501c5071003031a581c1034021615030341e019903510320b099140602c16030362404203031150140014a01c00500035540300c1e030040c0d81c0c0076000b4000c869090b002d41d0049517025000d01d0f10040001d445401c05c807000c1c244403455004c41c1506031000a805031404050003094060440d039221542 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 984468767 1250 984467517 984467521
    0xd03022109030919080c0105040503060c09210c1318030e04141f0608090c09070302041d0609060f030a080a1806020f01060b0301050f010e1215061503070c0605 70
    0x1c08104203841200380081d26252002962200018a064992050501038440c0030001c200c00e51259050742d0882c1c8001c1d00034111919218902200d0740c0044a410740c0014800004003540f58224a005401d400440301818444052a040c40414405c41070319080c0c10342401c8041004003400c800c4100b0003038052619210450480000a01070240340c1c2d815031036080301a00f4000050300d460300f04c070501400c50a41c80081a0b940d002a140c01400302c1e00f000303954000440f45502ca086c11004180c1c0320b219031500500c0c054450722041840519004008040480d5904002c9182003400703840d0780110302110805240c0800c0d00000356500d6412000070000701010500ea2040781c007032080100f000f9801c102d420401521640000c0d0f0380d2210380d03000c025541c28882e00240054841c030841c0c1c1600c40140015601c680040019a0f800880580311600410380c2284154158818068800d091a028801c80e02e2418110100604200100d103601e8080708100203110460303070091404050b90307510140100c0e0039 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 984470017 1250 984468767 984468781
    0x13150f05092211030f0609070831151a1309060615050c06131128080717010c021905010e101d0601030c171009050106080d030221 57
    0x3040c0b040504580c2e05107510400081030318005140304240041070304103103544010030450041310968030200802c0c1140c011070110131080e1500e140c03280c508080c01b10440c0b881d01104101c3c012215099505e48001c0d02041403070b1103103014000c81041d00007045032918a0380030018451704c10605110004035500d601800800180d034000b0070082045038a5641050030300440039110f54800780442000d0b0050800103122401c0c200605100c1d90f81050706030400452400922507000b1348044418481d48041c10740c9c8004110007401040640098009401050310b843c04e807940c040b6540444501590400a070303c0755042c0c0c0052003880d00d04010310348003040785039410540d006182c0d210003c4c1481c06103003495480c0442c5900259071000c02c003005084c80d0f100811250791201c900f800f004040e04580041006403a01c50344164503c6c0b0304440035150421f407981039404c1140e101803811200d9035101e040c2080400000e11040b036429800341402d500d003906005a420711420010b0051240050800220755a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 984471267 1250 984470017 984470059
    0x606030c13020d0612050c030d080421120c110d020a05100b0607061107030806061e0a02010f0612030807320d0213080601060f0e04090f050313150f0509 67
    0x6051000c0c0507115085181411b030b85521555000038003c0c8a20381807451110f05c501c404900c43d41c1c01c00c20250880c680142007041e0204154084801c00c00580c00c92081580c6620035022902d140d82c64114130741d030025202c00d0800c054800c4070019504012040c40c0407e00c0403030140c440f001c00840008125034102c0005006000d041e50162405262200c0450040810401030022070700a40794010256201c0080154074841c1079900038940e0321111a81c904400369001030103140b501d600012481c4216051003000326612030b4000420480110030321414075802c52101c13500200e0034a85084580d03819030101e80740340324079261480c0c010031200e42c0c000c00200c0c0c0b0065406805000006542d10601c1104400b00c6800500460745240214000042d9082c05907501880494161700e801c2c10f03109014041100624404c1030948403d046626900c00207542400108038110f0103103071308100705042864400080d0100c9800d4410710038881c4507a403025400400340d4005010480380120740500c43e01030061 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 984472517 1250 984471267 984471269
    0x2390f1f05090a05150105010e0a05030a021003061802041d0601020a0b060402120702100c0203160f02040603020303120a0509010510050415080d0302120f010518131203020306030606030c13020d06 86
    0x650080710b80c042c1d200c1c0a0104961b04030b44007641c44064007481a010849140082e2040e507906030301c10005040141001e0002c0a86459103080020b1129a1580d00440c0c0394030300051103c03515400a018060b078005800c00c0200d00240390044d005501d81000041d5440030710090103418030713000c98002507076039840d0340440314800703071540d014962030034144006507590400c1e2018484442c284220710f00350381d20010a940110007800d0390f01141a02c1500e0b502e08000d14110141c1e003107a1a00c90100247e2010801003d00c2c0b8004c5803070781c10701e240ca061703600101d410140c500d1030140d041005200304072220745111f4096482c11a070015400010030900003058840ea8051101401190451281140c03d81d018211078200071780d1500d0103903150b45010b05003203001d0180f2980860b40c0b10b500d1003409071040f07410383e00100a010b0481c84404e5600e9810040b0780011111000a80010821045081c180459500404250000c200c98020000040c00030401d1080c4e40010300c1e8041074030000d900040d00448 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 984473767 1250 984472517 984472523
    0x20c0a09330e0a0e0a230a11060a0c060e061008010905030f0a180f15050f03070f0c0803130c090c0e0f0d0c080a0b130f020402390f1f05090a 62
    0x80c581d24051810110f9000c00c8801da8482c102c0b21208008041801f00d0450034407079102c840d40e103065030300e14204912a08404165020003a01500d5040003a501c0d20a00100c405c4030802011185403079041d03020507400680164180781d040519040000700c0001c10b481b01040d800010503204d901c82d40381120350060f003410044500c02c90000c000b03810420310f020750b802e8031a080d4480ca94040340304e1003034036070b44243c4000a5110380208001004284a02c1c0d803410a00c6c02840e18003002c02c903944410245400541d00030141000c41d8500c40200700100240f40e00503d5022028801480b2020016014500d0365200a0042007559a200c4040c2d8404060ba58040d1303114002d10f1641361100000e0380e60700848102141d200170300d00003056101000300d501c103110662049184000c15103d03824400a9000a160032840c0031040352030040d5043c1907441898007e8142d901d041c4081035900741a8900144106c0c1300076542c0024011049110549601c4c3c142e100c90600c01042544400d005da600c0c08041c05009 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 984475017 1250 984473767 984473773
    0x402090a0f0f0906240506070305040b1329090120011a13050f070309060f0501060c2a030605100308220509070507060b01020c0a09330e0a0e 62
    0x10360344100a5406041c0d40f600070b079002c001928203024000004003045400c0201da9440300010040c0b8903010000f091305600ca4541203050643d039041c0c51443d17400104012683c031056138028040d21400300e1481204a17900755400c140b1260896200c50144104000e03141000107032100c10102c0c0034510526031845004400800c11642c01100248055003540c00d42c604c900d54660304a000c0d0610340c015070f4001c09480320144e00c0ca032200c400c1a00140103240b000c031000c98503080c9020205000f80b0a1a000701599282c142d01414289007100503c4c010b009500c1030041d10b81058110a510303000640243d81d03105100141c0ca498981401c8030400e2558001000c4090004a040307034003103012105003034071182d003200414182d04c0f0f00402150980459040d00010000c1c45004080703072160708848603146041c0180d8002a48442c081041c01e4080d40210f09010b440b84401500d02c050032007070181a85100c540403503603103d401d10383e186403c21813003945030503141040824583c810540c05009090a03402c12 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 984476267 1250 984475017 984475031
    0xf02030a08161403090109150e0304050d06140c030412081510120207081c1e0f230709050102030c0304290711010923120c06040306320402090a0f 64
    0x20043c06401f10500413a81445031120003518128540241e241c86140781703010310f0030217003030906109800360034001c20b13030303685840c0c8110200e00580506894014119500c0310750703072458181001c80040043c079440004100300c1c40100540714041d20540c400c42402100e4010902603111401c0380c11596600710650403c0c800034502c0300704191b96001304a6004110018070922000500140840d000051130f4883c02d0041200c03047d08410039440016204044100026481086c141d400380b030620303000c001c203101c401c10014081601d800c03525442c0100380c00d00c010351809440a4030941c880c001c43c41880c3c0c4c00c02040c401c00038031407039403506c1e02c0c9920342c1040d250742ca640b820f04089a440d94080b4159020460301000410b600003103614100000300e8072204c01052219180034400704e402881c80f08070090140c0c481c070442d0ba650710002000214010f00c00810708402507541c9140c072500800300ca250308105000210481c0c0f1100d04020780c41a01110500e4007603941e054850f001d0a40041014003880c0341ca00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 984477517 1250 984476267 984476281
    0xb030604021b01050402030d2303041703090606010813240b1005070b06100e150c0a030206010503160503060a02131208030a060f050609040e16030507060f02030a08161403 75
    0xc40035104500880c101d4a213848e98050540d590480c0c2404000e8a140c142c0807041266042c0005580203407149030081143c0e802c03c032000505400503100e04074150040c0c002c0c0044c560703000c21810740000c0690942d500081c140d80c0c405540801410b00d28001940d8465001d0f28405c4075032100000d0040902180030003c0c0144005006a003c040121990303510321000c1501810850004201c0505a441d85500080d10904025002007003c030080c44500e0104044120340405000489180344290010b00719541890105400c1088a84520485008820041102d590005420768200c0a01072005030343e0100810900300307007d21500546c00d4105c481520b901001b911000943c40303103000b00020002c1c562548460080da402c00d106091344800c1c00c5c4005000c0d483c15a00c003030412400901210181150003160580003038586d402aa125004400704200c5940c001e405072402c1c1e03500d0300c00341d881e040710032001404480c0c01070000441100007900342102c10b07024003c0748c4080c031080660b1988925040e1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 984478767 1250 984477517 984477521
    0x3061116142b0c050f1014010503190803071103040f08060f1006051c0f140702031323181006020f0330010b03060f01020c09010b030604021b01 63
    0x78860540a104884810807800c8402402095412480300201808018418200d90800c0c0c920b1040d52540998075103410008000c0055410305038005a0206d802d0382c002d03c1041029005920032070107600320801e202c03c810901c0c4400140c0701d030700982c21a22510b44000880710711400d6010509a807000082c04070302405140261821550302c1000c840c4c0c596106d00c4a214021020390320400c3c5456035031001d01900380128058a46005400c00343e40652010309100c1042c2d9081040c103c9100d03a450022816403c0d001c140140c2c0302d4182d00041d40b61218045c4101c54410f101e201d010a400d0a0290103201c0007107410f40c06007454030060840e075030841c4640551042c2001683e030038050542c1c031600000d01c0c5001103810300605548002850a281c400090240080c001c0411003101c4106218002030741501020f1160180501e038170080d4403840c224051103040003840190304d0555100300a0054640c0e5080d003c103065489600d60207480c0d07113031440443c1c0a401140c003444d008031042e003095580e034030b415 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 984480017 1250 984478767 984478793
    0x60a08090708150a230406020a0201021e0a09060503010e0f04020105070501091505010515270a030602070b0c160f061d0105060a0501050a08010b1602040609090212010c0903061116 79
    0x1d10402c2000207170f10401814442c0c440000621080d80c6032000030040344a075406400300f540380740009071803c406480f51040517041c2c1e800c81d030750a840c0494138480321907220707007a2000f40c006401c205180d541443c04441c2811801881200f00c804a40005411640320341c042e0303501c3c0c41d4004002c0c04901c440d46822160441100801110b2616000c000200b501d0310448101c0076002c0c600d07016150000d1044050007507501e9120070506410390380380c2c810306030300d50b816660010b40c00b6190061300c441451401680c201c0c80074044803d0000203004900e003c84c0b03030b03100021800e513014049224940c0b2a10300071000d44904a0500c0b806a074120700d91070340a40640200d8401c1c1c40c00c88400c10402d403030300010340e16030007241403007030000f40198014880c6c2c0040c3e000515900c41002c80c029412281ba900040648000340c1200e814103844000510460402034614003075405810024440021440c0004100f440b8911001c5c2810307031a1400707110912111022100c1c1c03000d4182040e0703441601c13410304484030202 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 984481267 1250 984480017 984480031
    0x1060b1602030d080c1c11030403080405011127030a06061413150e071701032001090803090f060909040f02030d1107151709060108100902060a0809070815 68
    0x181c07400007003d192051940c0b501c280c000a0820342018000c11565810760910840f03200351503079030100725100382240000f86204610a98640c09686403e14019007076030b80c440c0051000300414030050384604c000700c01e030001400b08400d45208402e0400d0009150190900d0040c19462414402143c080d0001445a21903801a00e141100c4048001503e0403602011184103500001c07403002d1200000700040c4907049616483e1803119007010210522a00da002e0348101c40c41034000f950030608807081c0c8041c0603060800d08107600075a05e0010b245440c0d02c96910072601c40e0741d0604190081d59200f42c160365116801500642c0245040c0ca1301140d8451820340036403281c030032800170f040324500c01c6a06018880b50840a4502249450f034201150050348010360b0601c0005124044006d01c084a0144982d440400404165142110050800c0e031550300c09141c0354200903500c8056201e040446a10100c980361500e12030707640300f2400b810401d00350800c201034010f4020b04c0803480030703500c0c0302d13805100 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 984482517 1250 984481267 984481273
    0x6120712092001020a020609100215070206070e03030306010c060b031905070305060609040c2304021306120e060f0414100504020103110405032104050415090509210c01060b160203 79
    0x204482c01640d8484000f08000c0d031100b42004040c0250401e00340c07003204920140101d8603603413111020001c0003541100c1e110b0040e845041000082c4e03502072014183c00b0821303000741d0b24500300000024600022035801624440e10b4040700707426518104000b100b580e20710041d4801d440500d141180c2c503248030307120583d0107101d500d0200b2198545600110b0090740d005616041807440e288200c0007584640390300010408100d00d01024545881c002001da0080c0d41c2d00c0c8451082c28401c015240441c0207448a903814030300900d02c0302d26440010301540002d103590b0b4240b8903549501c0c1400301e042d0400d86601042c0114a0700440e003914940117240514402d0700c090120305100c40e103142d03480c09184107081c0c1c1a840300d400c1301140030103130324108000901808603901d06a2184003040030b03150801d900101916500d1010010800340340324964124440401400751440490051305c45a5076001141d00021000110314200510950014000708003843d002e40e2030f802e800305169040c1c0003070035050b40a40 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 984483767 1250 984482517 984482573
    0x60d0c170303250f0809010603060204031b0b0306100c05070f0f060306090b010c0326101701090b0402091e0c0703121506030b030307020307150207080c0612071209 72
    0x108a80d0140c2e00c1c46106942c031080c00e1546001c0c100c0d4007510151046c0d00da03550321000880410203900052006e14091103c0c400144426158000d40714060b503c414400c140a00501c9156074840094000d007018616182d400700b006400d04605141c100d44c0040004000c150000560354200e003406800ca41c101c0d1802c1155507500c2444605642900070054000b414048101c00000e0050340b070740c10012441d0303542c0c08040c001b551480300c2005041c7c4910545032400c2c4020046070340c94902918403200b6110081c044401c0d9980e0b120207040014200038840c500d42000240c2c1940c3c0d40311240ea204400702038a8016040c010b0060703405520981040d03000844e80e000340f0000c1c00350382c040c440d500c030803000f00003000d40d181c44003c90041c415a00c5084c0d00d40410080100036a80820002e809009440e981c1c80d008026440083c1c6060150303030202c06107800c000f0400d001c03a81e60100340c66041500c4040600982c5d101d20040301c4090114900c00492880c0c085103000340100305591124031441d00d001c02d8648 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 984485017 1250 984483767 984483811
    0x7032f0d092f010903140102221404060f0905090a0602031f0e09070506030c0c030418060f1d0a0920040c030e0304141f0c210503060d0c170303 63
    0x10021580c0ca0382d011035036812040001a004186100707501b242c02e4001410715120611011100842000d800d06000c076541060208408104070341d4200c04084604119071440c0441e02010018148943e2024540d1403000a8814a040c8100c00c040c642c05041159285050411012140c4103960100c100c100da80c100440c4401d0300a00d40c03401440050020040b65281108104980d0b10081042400c81020b000040038040b0400240c00600101d00203a6402da019801c0441102c0159104050300414603108004085583c0107030501003c0c04002411a070360b8468010014140c4e01c41c000745031a101d031340e0800410904d031005135084102280c00340413210801d20300b00d0686190003440140f030303007041004211400100010034820714020313040c0303240589422910854100c81d00400008540011203000c1000003501070202148003140c04a55000a255002040340c00018503644c056423800d039000c01408242d038881c00050940340120113440c4101c0b043d40b61642c00a580148200035030b40220341207 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 984486267 1250 984485017 984485093
    0x60d06061407150504110307030c05040b0d080d091719110706020d08040f0c081f110f0304060605150a1107080c060a0905090103081207032f0d09 64
    0x200c250415801c4848001c0c0e41a214000d013400303842194081d020f568000032586081c00300400a50040c030380051442e10b40802e00c070590352b25202c03941c400d01040c2c41e00c0c00021000000e80710040d0594500086d41c40d42e51610030840d2860b0440041000d0000c100314584240c20141e484408803a40d48081c04d448003020440e584940d54018000940c0010b00b410641c540319048040d801030003005001d280c07078071039100e5801c4511030703030401e40d51908405100071b400c015180301441203d1800c0c8040150441d200c0d440d800714095440f1041250100002250501c296500807030050280200440c2144081c500c0b400195401045504045580c005e110903000030042025030840710310201410392403011500f0805141e0001c1f400c0b01c20711541190103e85034a4001000380a948680300751599001c9110040c0054103008054800b00340c1403104407c501001c0021014022218648608200d500d0211041e402d0150702a0554240d1401d09240184040d4641c10381d2030910280d0345010070141710410a02e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 984487517 1250 984486267 984486277
    0x5030304060507030c0605070e240a051809190b0d050d1b05010e070303031b0210110904150e0105060403050607050d0902100f09080706140d0b060d060614 68
    0x541904140400c1003524007400080c00018801d10702198418030070741d0f0b5002118000c0d1400c000086d22100303020450f0600d006107180b010031000350f80f5100c2c43c4914a408203071240f459140d08012000c070b881070b03116400801d0b2811820f4020030000f49071400148039a049120f443d44141100c2c18401c12020a00b0542d803034000c6582c0240280c4880445007038241d6125441c0841c86005011094145002c201c0070703c948851010900090b042031460760070002c0646480c02c42c840c014000e40308808900a0300061803105c00148080042a408429110015640500500c0c0c0d90001e0500100400050805c81c02e40b01f911240095100c10ba622001032102c61300413404001c100f0b502c030b800403540040c0074a01600c91000ca00e08042a44550380c0d020524008218603000041000c00e100310401c9504000442c01818801005004492034440010700314609a2616940c4003000206941104466001400b02083c090170059642e5044a1008028002c074401d0380001100c980c1d1030458559070700700f201c0d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 984488767 1250 984487517 984487519
    0x1c090302010905240d050108061e04020f040f06080304030507060201050702030409410a150612020f1308100504020904022101110d06050f150d020f041203030f0605 72
    0x1071400c40c10203062040d202d42159000780f21503410310701507200d03013034040040000a40303a10000c1501d5261104151524002408028103240048042039903800d180c0c03400f961094045450002401e030250208000317044074079220800d9401d040e4041a04140000203008580c407403011500340d00e82c0c80200b24200d43c015611500107810420040146080c40d412100c0d0122070781942103106c8081c44002d40140b51055070880c00d000c40620350020660100405680c09103003000180300d032110701c6200210381d141c2c6008140038001c2d42081c143d2140903d9040c0c84091000041a640d10a10100e984852860511803650329100d142d8212003002d220380562400703254050100300c429102c80e420400360884154042c0c9020b001c441d401c02c1007910901500c8401500044110341d80c40004040711300340c5070309400240c02000d600d02000100c1d1114182e16500d403c1c05e2910079200c15143d1b400801030722824a8210030800040f4010850b03c1d24003840300c3d0b003188641c0b0200010301c0d44d048900709403a0b0034480c03e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 984490017 1250 984488767 984488777
    0x6090503072103020f0307060519050f06040f0209030604030801051338090c031608060d02280b031e04331d06010e090322080f1c09030201 61
    0x1d02c070100c1000446860354802c0c016910101c6403032040c42e2944c2c004e04400e032a02515036050184030352106610301c6c0011840b1780e00348030500d8004112007180300060001400b03903036a02141c00714031040342d0607502031041c010180d41003030030503003002044e01400b8080d05200b881e140f1840d06022045200702ca0a140d640754020407d0304580d41c9841e034500440c8210050310705800c0110846540d0003070f2040c4500d104240349a10790070301c089054213100d12030300400c00780018801400090b584090041c04040e03411900c010600300501c51640303070810200d00c0040b20180310700000c42c2440740040558803d407200c0c09a0540072010710140007105030151005402c0540c0b0300026a480c0100e948040f803560042d02803080d44000c0001414101c0708011000c0c1c5141c40c0c0101d0300500c02c0d0781480078034010035404103d18001d0402e03102c03c507140d20615541901401688040c03460403051001c1a03801084040c09403420794280c2b402160305d6400c050f034114440350782c1006800fa12130140c40030500740e94041c0d5503 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 984491267 1250 984490017 984490049
    0x40b15030d022d060a15050312032a04060f0f14070212071e090b03070302010912020a1802180a0b0403030e04062c06011b150b0a0f0609050307 63
    0x190b203078100c801c000600d1281c0d0414012980d0f002081120b94021802d401d0300155903041026a20403004282e00729a120b038000000c2240030b4990041540d1b000301c65501c46000d0307440c543c180c01c60b0488200c02c040c141300340003080000e0087e070400409001e9002c0d64459101140f1010012120301245019000e17071103005105c1003000d4104203002c40001940401200e58558484114040036004480c2d0f0b0ba002c203544030001d000c071244034000c50019600a800415a107400c6a0010b01088030078080e40c00349521907000c840966550003444001844d00c00c002c10b424168030042c0c40080d50001c82d000079907030954580320078241003030480703202120014040c46052a0956a044a000200c071504551040d121a8007040303c29402d0b001488443c00c03101030815102e805810401d60820040044e0b05210404501d0340e8281161803160345096440104401480009061f62000313042022045030020104000412400014080c103410b680f50341d20b6814080e9038030000c050b0303501c2150149061280703200304 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 984492517 1250 984491267 984491293
    0x1509210c0b03070c050f070602010e060709061101060b0a0905100c020f1908120408070e0415090201020102071b08011413030e03101a040509010e1c1106040b15030d02 73
    0x2941d0043c510303140500755080142c41d41450030500030b1180441d50000d180401c4042e409100b276101424043c1c000d000c0c00c1c41c003040c0c06041480c0c58420001441841494442d0300c10080d444240544080c840d0f15441d000080c800a0002100d400744070b01400c45925101c9840380244819519035134000d05503454081003100b440844150915002002070704d001c8007003001c030001e00501d201803410301e034a2a1180d15042c804c5240c44200d03131040040c429200c0030b00c8082060000302440b09466003102088501c403502c0101d0080c480c03028081e282c00280082e54665903070341701c5924100c1c0c6030800280148000c290780300e220000d06a80b0300003030b50008503c060009009040e0303100f0904001b800d650070005107614503020388214103d4140c48640079400e01215203410701c15550802d061310b000f0005030a5888916944121800951188031094a0b8030941c01303101d02240c0750100510002e640f002c7c2868a00022000c009640001030000000104c4070a82000070b1800380e0103405500416071050710701 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 984493767 1250 984492517 984492539
    0x605190603110c0f030d0501050a0e070c0317091006050f0609040507030209060315090c0a020a170c1501090c1814040908180111010c050409050a061509210c 69
    0x1400030103000740c052214400d00320f014015440f08a00040c00303943d43e180c80390079200032a90142c020a1094428030004e100110316008030381d030300c00c0180c1401c4901d00f0003800c0569510b0039411840c9103c040030010042c00c0da40200d205c40320b102c0c980707000344042925542040312400445802c690409018800c0703c60920701500700315000007041c20300605c1d0581e0040130940503401124100d285c01c440b0360100c0382d141000059030340c0c00801d0051032030074100c0c0007800a44510740c0c408041d12010301c41c0c02401e12008500e0480f0b043c90094011103004800c5d550041e00341007000d1041d00c082a242040e50007004d4066600c0c3d50a0a1070b561048415a0421003903200f680078081e41a60006c2e600e5014400103085880241910040c196814a4005060300010440101d0f507080c048564180540c0d101a0b81d00202540c3c00d680039030f03001089a54507c034100c401001e01c1da00c4401c103e42180712048859402841c2c80c020795545090f080e814600d21911842204d10340e80c0000d0003180809010081c1400d10 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 984495017 1250 984493767 984493781
    0x5100f050c0913112b0603111327050c150a0513031a04021c081e120c0909090313060507060915061814281e0605190603 53
    0x42e80f00041d111000c074035420407508024103440e034694802d1044200f000741c0e5a480c0e0303005207001409003c100e0075175603260015400200210b01440c000c4124483e45000d03500000700a00c5007041c00e00764420701000d000610140c0080550391030250f044001070303508081600c0c2d452102403d00b03a46c54030702049011241503111a201040c100d1840300040006200c45004e01422a80720701450300da41058010010307442071050400341c440544917a0400003c0000c000d680c0c01d0b807114050007041941030f850302d480c00e00c102040d042c07145001108002060020001600b0b002400f92900101c3e139031a0f0031001e035a0b1080c00d40c40745010700480d90402c43c4074850f40007804c100d80705600219880289035510700140d0740707104460103400d440e0070040c04040d14901d92402500230314001071003460710180000e040060054104281441401040607180342c61611034014091200c80030003500074a91003801a250301f000ea603d03422800c03c80001340a00d005207449980b500c5c40300c104007032545850400c1e0000d09207 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 984496267 1250 984495017 984495049
    0xa050a060f140c030405101d09130b04050304150f020601090506060d0212060316141002030f030f0f1b031807090e03070204050105060c0a0609060204050d05100f050c09 74
    0x1c1410120080082c07000307052030440c000c00651300c5a042a041203104003620142100300210710442040c4c4581d03200c140316424000759014001510359401c5140007140a40b030250050042070180420828000010070459080b520703420541d05543c20101c640d903980300079860040c0e00001c0103001d404041d034407150704144000d04480c03510074051102018ad0b048602039807282558030040100e2410140034804110204004261450b400e280280109002c111360310341c003a107151a0b410303100c14002c0084410400c4a904155140e01e05251100c2c210380c001c072003a0a40340ea0b40303000704000d18102c1c41c2011041092045260450344c843c030214840f4010545000c055100d0390100207180015071080881d400d00b220051a91121140140400c0c0d9206a01460143d98100302851080c640402c02c00b20440e0b01135004200d04c9410304160010f4040ca4100b9a40007900c0f00340e020800c500016441d121001d400750910074140e0801c00300c4116481100c41c450020010403005031117141a841403030a4170a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 984497517 1250 984496267 984496277
    0x6180c0207051810060806030a06020708070b13111c0f0c05130e0106080d020d1b06020a0806010314060102120901020708060106030c090f05100c05190302030a030b0a050a060f 77
    0x1a0b00c00c00034900d1000d1240301041c66038080c080c401d09810080340c03240940700604080d130300c0d428003001281e42c1d0703120800090282030703021a04c1403c0129960484165540280c100c01ca5818504601030f081c500c500c5041310320854016607030000b800c04a04204411a100440e00d4540e41c1907200d41c00c5000780c0a10403244400340800100e141d0365540b490415403165030200052204a0610341400c46a07a40c221141c0d6030f001c03a541c41c8502d80c0c00540341c0b044181502c0c02848502c258680400b0640d02d0400041649002080080e0039550203400180311380b0090340c0500081c0465001c8607541601661214010303080304032000084001c2c203005011602041c811145000d94541e0341504011007230b04100c0000391a0b01c0e162545541c8103001401074141d9014031803c2d0761a00000840c40c40300c404200c414060626500c000f40303e02444107000da5941d15100c4802c900c45460025241ea005440202c0440e2610069128605021a5040940e007004d44034074078140c03d185040d15005102da82410400c8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 984498767 1250 984497517 984497519
    0x2090a1a090405031b0a02031c0c060905060604050c03040f080313021206100b0c0c2e020703030306080a020918012405090705090108060d06061a0d0e0106180c0207 72
    0x61140c1405030b01c078034060406161101241d03444407140c98008040e03c0c40e40c0e07020140c41000741e500402d810a04240f240040c0c0084060000c058856040158014000c5480d0036150001d104012440a110392001c68007041a036584182480e0300340003c0d900504400e41803510100010351200045401000f00e90008580000590004840c0c030200e210001040d00084c0c02d12130300a06203115a03014207440b0f1662405c090442c0091940d4000484100e4811408103501002030240002040c12803039104400034071100401901a551350210302c07007100001c0c5485000981003034080741102d81540d00901c0a40b4903107070044c008030101e00c03a00c0c001003503559802043c0d8034607610300b5092400d01102c6c40046012843d000800c040404003c0000e010720804010030541c1c2c1c2c1e13220403107a40c40071084407180a03421540c1844802419960040518683c0340c000d025101001d03500941400240008184922a10301206034240d031118410341f030048003c0c0515030a0405103801460140b04144111035400e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 984500017 1250 984498767 984498769
    0x15050a1107050c2412070e0622060f0210051e27030406090b22091d07030803040201050c1606030509060a050f070c030e060705030c0d0c02090a1a 64
    0xd6104a504079500c2c3e20201c0381840342c0c20813408a45820004010200030b402c0d40903002c3c88588902c020b0b4000300310540c1c000403a00c40c001d5040c4018004007800a5072152030070801c0950b060b0066030b41d640c088070015000203400f0b106581140c401c6450741e02812500c2d40d03080c0024044e00010b041301944444007401103094002d405a11449203034180d1a5407160940022400c00701c4c0302c00003103007005800402050014039000211704003107611109a250ba02c000a0b10720000e2010510480904070040f400700046120594104413010070842803d48800d80e03581c51825074a5425200c0145481ca0900000740590301450140286103d07810a8810051403031008000c540340c203400100c00300b9035580070b03c054080104000780d80000071540400090600e00700c40c03007464030010445001c0000110030102010721501540080c0400904919101c5a4514015849410085d1007042ca40324180460140d5803040300703100745441c5c018112100c1c541341c510180025100844481e205100d105441100c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 984501267 1250 984500017 984500051
    0xd05090409061b23090f0102010905010903080117030415080c040b030403030c08060f03100515031c2c190e040f050705061e070c080a0503040e1315050a 67
    0xc02c20b0700c0d001c44803041e650f90043e103c18884c541c0724540d104201c076003024444455040b81d03e400c0080300ca00207503059120040740501005070000b0100e50038160210101760b0000da00b241a140c0c9101d01002000d4012003050b42d0303020724401c404048500c1d03100307d000c0c1d60103500c0c415007155004200c90300e055125100040c5540c41034030101c0c0000c1c2c0d02c11024414035400030500390800411550460702014040001ea6030325122602a0324180d40e03200403400c0110000e480071211034018090703500c107000c80f60f4901c8540c20202c1040000c1444a0074040c00c101e500890052701c00c00070750454004495a03400d10441d40b10310128400045141440801c4000300309141c01e1049114212000c1829458a0000c0c20078226034005ca001d60401c0c4034030300b22240d411044070740a0341074400c080c0d1224183d09050500900641c0804900d01541d5980750601501000400a854a40c5119081340d150751041e000e268003d880c002d45030750390f12021003400c056140c018942142c50103d01041001e08182e080700c0d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 984502517 1250 984501267 984501281
    0x14011b0f0c06120b060405010c060b060904060803041d041a060409210e01090602072c040807031b0308061e120c01020c06030402060714150a05010e180d0509040906 72
    0x2000c03c0b4203a0700b500700d41078140500080300d68140d9015007058500070000c0c10401c058a4004c0c0b5098441040122030b84520058a0810304001e00910000f82d07140b400545aa10502070701e0b82c409140700b00d110027001191002da0066500a070401c0b52410040184805480c01500c019400394a8901c00380102d0341e4034280c240159940104442d4130704404002801c10400385206e41e05108070400c0800450f038001c03400908548158020000300500485042c100462000d55911410325000c2484181700303000000c0e05d4024401e460711140801c00540710b140000109400800203207103e00020000d0912000382041500c0c40038140a801000400250350702c0110100e80105910804400ca05076904210420725040300341c58613460f5082035004a101c0e4030401d9406401c4042003807140c82e102030100070b82d5108010b2161010b190342020440880034000070702c0749038980888600498100c3c801c0c034a1081c902c492803c000d1940000d9440255031030713000040c50707176417059a4001d400c0200d1410f01a1034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 984503767 1250 984502517 984502529
    0xe07180e150102060417070602090301180c0b041211133308060a020c10090f021f17060a0b030c030412020d09090209060403150501080714011b0f0c 65
    0x40200e28003500c8484014041c400a00d04550001091001041540c55003101c444400a4003d544400a00b03013400603118103a0516055840c003050f6041c00348158032966042c2e4401c0440078905642c076090141c4a0140e402a00034815041400b4000144507503c40003090901a1031001c20510038140c40044818440317510001429200e07003803101c88016a462040c42c4960359180310004d0501080e07a55501d0f00628950701ba0f40d0005098051141c20013000c25482c071004000c3c030504d0312900d00703c220300700002000c0b8080c8031a182007000302c1940100c1d007484030f881992162040c80001d129a5205c10001d03040740d401118047c00800c40381511801503100f03510384000c04c0d41d641000e00d440072a02500d120303110210342012011211459004007039404450403602c000d0384039a2540006112351195504c010001d1400911940390003401d900814100e42080702580d1a041d980c1070b000503c044841032081c0003405aa61240d140f0442913074003280540250b250203100441d50b0360783c160091081d0008 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 984505017 1250 984503767 984503789
    0x7050c040b04090f1205040312091a1206010c08160308040b011a040603020310050a0305010b01030b2403041109070c054c06170111040305070e0718 65
    0x11a91410035025040c1001c40956080000d25143d40340c1070048184544014800c090154000da9090f204100b650045c58102c071000722a0300d000f17040a4031002451084103a01c41000031140c0c0e0b46404c1c10165206c0e403540b120459140d40d035030001140d8644000c501200c81050a110541c401442c8201002d54148242c88031117060400c0d003017002d80800141d01010092100300105130081004e98159401c550980c00d01503220f458001400408459940085401800c0000000140001500000f035204020f880400c82c1c201214180403545511800c01100207081800b03810140021000450f44640242400c10480729610001245078000340c1d2510005400b8070818428000f0900081c8dc62038200d40110015081c2410f4000900750003444440c00f9400e54030741e0490b008040302d6480031449100d042040f9840e240e1070a070101c4035120304400c013550718003410900041c2c2510300702c40540e40c00c04c00034103000d4a001401c54404000174005010002680014040b00c1c04240c80c00002e0a03000404d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 984506267 1250 984505017 984505033
    0x109140718050403050405060309330a0b0609120c060a0503010f090605010c0f050109051f060806010b0412080409150302040e01091a100f1409010b0708031303030f020705 75
    0x10110710a41c8420031070100901d00000e20000907000001c48040b1201960b525840f680d803440c010782440c2103021359014403540c018002145da0a05441018074450002e6a036900d80ca0f40b8602c0300c2114008600e458001d00c1c1005401c80390300e4406080301002a00c0c404440c1000004004654142c01003003109010840c0440103000c580721303041c000340103000b010f003080102520f4071000802c0302c4403030b10010b4100040c010b030301801c1c403a080d0000c01d100d50304042207600c074040b44580c40904a902201c0d00010502d01301010641407000b283c19070488a080b0300281c00c1c0b9051445800300030b0390500044500d02410440042d40c421140902010b5441c0c10901c3c041d41851030050209461210804442d40d074500100700700001e021290b010100c114181c026115a070351a440b00c030b04ca100640103102030000e0840e0005d1a8100b0880740710f0030719004c0d0340715007a507646d802079007100f4040e01800408910060000401030801c2e0b501100c41e160082c50080b800c4182e01e0301000403a4004482a00c050b009090 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 984507517 1250 984506267 984506279
    0xc260d020307020118170310050303030403020a0c050f0108160302090319060506330d020715060e01230f0d0b07081b09040b1f0c030908011b030b010201091407 70
    0x228801c05c500306441c4012642c0107658420203044141a1b40c0b014443c2d0102c0030400751031006c0c0928000d003802604030b9a60f8103160034040e564075216503045600003004500410903051000c2e41020000c0d040c0c50346402515000320766002120045600410568280007141a664080010400612203410041c0c20101e00b42440400d07105c0050079203000c1c18020b101700d81c0211412440c200c0c191026600d0a08100100400d0400d074454080300c0d12a050002c41c8400a11100e0b001d1280b085500c02020004641d4030150001c00da402440b440c1c3c0a100e010100460280b0203071018150000020a19041ca0540c0b500142406520403c20751304c0e01c140104001801da000310500b60021040d00c0705241d20212408141001d1003130364002802140c40e103c9c00c0310241c0340d154540094a481c40c4107250340c01c0301c900d40100f14400345402030b8005100325000080024040c45501c00120201c3c1104c1d0f9604503c0c0810b40140aa00030620f0440d03580c2c00441c0081486c154140c21120308040c040c089444c0740c00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 984508767 1250 984507517 984507521
    0x105131a0601050a0c020d02040203011d0f07021c020a0516061211180a2c0112150b060d0e030d0f06290c03040e0f070f0c260d0203070201 61
    0x10030111518040301442100ea81090641e84c15000303078540b00c507000540f407010440d00c44104900a4001e400400041048404411158a000100c940394641c076135540c1141030b9400340c240c0303240d00580c006101c6e0b07800a004514a82f415070349640101c80580d602503484074a00140c803005a5122418090107002503035200d0004007040841040a0100110b41d103003486452240b2003040c0607565510700380d028240c90b903241c0c6a004202c01c00b00c0c21075036a00b94000c007006030b50361564910702021200000c81d0200c03069030b040390080c0e00640d0360688061f01d864020000c1041000850340300d1028441c0e100340006e2402035403080350034000916101c1610030204c1c41920080d46071915294108241807003035025260715440f54a8031120090400c01003404440307000d1265504c2890680000a401301c2c00c800390141140c0150b41c0c5d019440f50139580d002d030031503107000000a141c0005240c0304503240412a8400301a2040326103d030074217605101d042200c40300d9800aa00789821640107c1005841c42e028 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 984510017 1250 984508767 984508793
    0x90c0e01061206050315360a020109050a0b040b0a030204180b1c08180607170901020601060903050316050c0a06020616052104030e040507030902040e01021c020c010905010513 77
    0xb54018880101ba85800080d40030b00140b0580c1d14a007220f074a1228414046a425400414803400311038001c00c01031625110900e550040c1d0216110200008a504101c2c80c0c2508071403010746403c0c2030504000740089107500031550002019024400860800740b0309500c021100b01007000007401205c6401444462242d0020030080303584031000d140302107031075001100c100105050b49501b051495a00150090180b20f50150042001000e007041544000c0000e0984400036002c0fa00186ea0750720b0101d44c00052400000c0250700b081c0708450300d01442061031900f81d80301e201a40d216041c2040816000c6010360f00a10050b0710100a01c2802d5030b50000e458850380e2a880c0141ca004c0b1604015074611484a004850141c1d00400041c00e144c4074488000515400801c18003140c108080002e0140c80020340991040e444e03c0b0121034498014401c40b00d00500c064514102000e416610000941103451062101d549a000e210002003080c0301d824458856601203c10020003814200e40039101 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 984511267 1250 984510017 984510019
    0x206040e100504051923100f14010c060531020a0e0906130f0f06021b161a13170d050a08010e0601020a05120315041a04090c0e0106120605 61
    0x14000c01e04c101d00962a100d031400d0810b031340003c55101d820f00311b00c1071203c100145910381440154144136000785501c0c004811070310100c030080c0b00f4035144c8160340c034828041b41c1e100d8003040039003035140e00261a6400040e480420703556140760101290000300c001c46505000081032100030310380c81c400c615000c0804030140004d038504030300c0c0d403034030598190380c840c0301810040200000809103403c00035400c58003d40781d54411a501d1500c02c1e2498843c029421500e481c1400c21480c41c41c0080d12240040c505032040300d0100380303180b40340c03514034001c03009444482d01d00e60b07400f800c2041d00380407411440d81300e00811240c0c8401c035240142d10805ca05104a40c44003908010040220801455102d0803131410350740a0741000300642c4901c0010b0f40751801c0408010316500500d103070700300c2202d00440950b2082030040c8548507011004020001251548103c01442c40b4410b43d400c0e070141456400340100520030626151495110486600040d001f40c2c0450b000405a40600c0d14515880c0201002817038 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 984512517 1250 984511267 984511271
    0x21b0319080c090d0c0b1201060f081308031504241205070353071a040303090807050d2015040507050409150501060912030e0d0206040e100504 63
    0x708828222241d10800031070320700c914416104e010500c030300305001c44010070350040d1042d9520000b01800801d680240b00d9034002c1007151100d543d10502568115110300414412054141055030f01e0652581003e051380601300900d03030b5010713101e484a12400340001c040c4000c82203220707541290340110903c41d80000091005031624480080d20000e2420256680180d60310740d400700405940d0004240480c2d441e11211613189100042400d45200e80040c101d40d02c5a85850100141c11400764400d860000302800800b408036010228141019a045440783c90042035000560311005043c1d0410300f000d54280c1c10000750310026982010b20b0200701d01c0e50501084c1103000030000161a0345880601c030f04d00c40900b5001500b00201440110b014000040042043c4911414503541c5000800044203070380780351500106403903000d00054401c56603500404048928981d03400c44600c407070b051005800160044803d80141d4901020784090201c1414060a03031428050850320010143e00548c0218 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 984513767 1250 984512517 984512521
    0x409050901112d03010e04030210020c0a060e120a0206010e01052b0204060f080a060b04020301030b1f03060501240c080f0c0a080724052503021b031908 67
    0x142c0340c140c0d841c100a451051076444507624950032a003030100f20a208900300000081080c1c1c4444002500950003036003250700490303142c941141244640c900c42402540031010110005e080c03508802c540c041c20009850121034940307984030103900108007040260300b12500605c40b24004450782801400100d031401c2041c0030164058020700c90401100d600700c000c92040205640707880d0849002054480c042c41102035485131010b84480f801041118280d05092900c022443c4c18001d807030589811640714040c1d6104c10600050300c4200410402412030741c5d101c00004146603111b124000c00c419528000c015001101c00c030310402a00143e0340078003080b0101c000c0418810341c2552410035407c41860713070380e10018403040c2c03a09124190040410b9000a010b80803c00c6c50003520308100c4150710911403143c08a0080d8080d00ca044401c01d80d442c1e091b01d980310072451100f42c5aa54030700c960500528065100d00404c1d90310017070358140c118035400014442d000c1c8011450540c903101c4a031800449038 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 984515017 1250 984513767 984513791
    0x702090c1e2a0c010306090506030d0507050a06090b01170d0905010305070e0d1101030b180a0209040905061006091409040f2d0b07080f060d03020c03070603020409050901 75
    0x400784800803000740c60100304200c0071600046002074600001802803000c070030501d8001d0340c0392101401580000d046c040e00003950502c2c0d000d101c1c0140c80c0140a00420b0040300301c21035450700801d2094a040c4681905d03003000c100e81c1d00c0b501100340d010301c1c1980d8040d0306011241c3d036192592103006a039507008480c03a80840d52b100840006940307003480c021030a83c591038421500b4009142a0329404031180404008005011200790040c00c02a2418801300700c104040040e82c82c0740c220304214640340000001d51100042e40103115404004200082c450200e880b40ba1412400319418028000003c800303000f4180c00c2003207075004100c0850580c4542c548040070070b141510207040203202e4411800c01d441004031200c00c80c1040e0031a60308600040240a40c0c00d04074a6030500b00707440b428036010100c5c1b8150b00ca40d101c24843e2421401c140350b03a8558500340700c0100b02c0302c0000d404600900703441032030301e81c0c040c4940c00040c0040e90340543c4071820000d03948101e6402600d1042c544c0c0c5452001c49030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 984516267 1250 984515017 984515047
    0x9150c070b0711030c0115091b14070807031d1c081b010e0607030e0a0b040f060f06090212010503012c120a050a11011406041a150702090c 61
    0x1185074030000c10078454941c05030a41d1601d003c01980c042501020920304880c0350151301424054007088101c084081c0c0c1c0e004080226040b0b9042000c91400704100304107094029201103c04a941d401c8543ca01003a603124601c0c6500200800c50004002200100b60781190400c0280d1042046841c1c1000300000e4030070100c480f88070500100400070100d80d641c0015040100746440c802120b0091005841a40440d038a418003110340c5404207180034030f6400240c00005800c00d41550107040c04105480325101c8140d140c804000445851f900c0d45001c0c04a5251401080c1c0105044580503850740c40e841c0070541003460581125000b0382c54484003500519500c45044150280d20b000720405400b1211100c2c24621400c0c00d1110b040400941c3c01c85d00c9030b00100401d42c1495580d070300d10108c4502c80b00301e42645d40741c60300c1095942e5884040b0f6a0307480d05522404e542c1118505030500f00c114031002c0713408181c515003034406644006ca400002c1d8104520a503900c0251400502d180030418040022 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 984517517 1250 984516267 984516277
    0x18030f1809061f0e060d0c09150f1d031c0f0e061305060906071a10060e0109050f0103020d05040b011e06050a18030f05210403050c0913020603090609150c 68
    0x104200c1150204e50b0392200c104807040100078034001c0c0140041c21030050b04c00004c511508003410300b441d202c001d00741e12980304400b000d070070750f0b50303c0d038040e10f01c40c40d407c091030740100741c480d494003601c02c034040502d0280c2080d281c803d04503119030a9000401d0030240540481e281f22500804d41006611420310002e07144905449048803426161840311001c55040d0203038410003000c1c161100200361407204a60700346c46c460b49005840d02003040e1140c1c821103224100b02d1002d400f04021880912032460170900340020740c44185401400c0442d00499002560000d0701c06948030000c580060082c4044580300000e682c1c5801d5009100d1881d03e00003c02034412030741d044041007a54071854a001c3d41032013890008542010501000e40c07040d040103615052855021071405a4410b07068800c0860401031f5000c40382c210001c0c20180c1162824400400380091480702c10010111581d001642c4820107180902c0c40c0800a00c41c40c504150302d40d2074030340074080044003058000e04000c403070044031003200c0c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 984518767 1250 984517517 984517579
    0x2060403020d060902060301080f120a2f1905011406011704060f02040b1c060501020d05030a1d030a0207060c0b15120613020114070b18030f180906 65
    0xd04059582c03c0a2004000398200294840000000016050000240103400b10140e10580340144080d0220030ba02e4881c80c00b07590b01090685507415a540350b18422020211418001c0300c00e02c2c48040d809a0404000c0756a0041e450081e031046410312509109510480003040fa518403e410910700290010030301201203484036503400001402c000e1144c2011a2840ca002401d6444540b03681c0f41d4007064010501540d80080d01c01ca00169014141c01683e040384e9040c2c020b808201c415000403580d96000400707003440315880300030190700500c500b00f000c1c003042c83c100c014580303c15900c44000d041041079805042003103079076041c50300410b444211380c0d40c1100000d040c000081c070b201008140c0c81c2e4000f40c0420385a0003448100030340000e4210b0244c07500751003680c40c2c141d00345400214003254007940c0800f806e407421140001b18000c0c00c81c50303101c04100e1550210ba09080c0070600540c80d580c400700800c01c400c0040d604c946080e00f4038116042d048602100d481466000e542601a520f00b0101150 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 984520017 1250 984518767 984518779
    0x306181c0509100c05010216020915060f090a120305030711030301151b020a0314070e090d0507020d080c01021305101d040f060b070506011208090d0206040503010f0c1b0206040302 79
    0xe07001e014020083c1c4d100302d40d0b2040082d52a41d8884204503e1000c00b9103042c0c0c06100c00c4000078120454241c03003504902c5d0001d068600304142510905c64942000e061150008415803003c95000300e4445001c5d456842551000d03a0780c5442d03040105081012808020706600600041c081041107100010400c584c40c0b1b04400d188802040b800c1951070308130000b035000155400b01000384038112001200c4000f4a20846603440e940d01d160700044001241c00300d40c0e0390002a40c85040c00c0c8110018404035000070040c1c180e030007880d201d410481c0e0159207002c420345e50005402001003880218030f8010441226800e00e5045224400f0f0001241c0006449613914014842c03030103030b69207604c01d00d02482d0700d0104100c103c1e00d0307000003d03199103d040144c40d05e1150304000555000125032104002d030b40301d40c0c8030342800c0f5604280000e4255181d4103d901800512010445031000d11035445011061440400d883c2200c03040500310010b0740102c40c1c5000e030100610405a150301003210100c9030705982c6 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 984521267 1250 984520017 984520039
    0x70201032304033b0f151e040e01080c030115080d030f060f081b150f090604030602070f031e0c0803060a05100903120305240d020306181c0509 63
    0x210b4044c50401038004030030b40300800e044218105400320205035042055030180c40c4d0000c1e8808001e40c20708030f81c103240d031080c100b0051003000c4480c00b0103204440c80801006030403d900c5020300140c0c040d00340c226148a60040340e803602c0502d424013032003102c01900d070035441c6aa41402c030081d40b100840b0480e281416218070703001207405466404113000b070016041c00c1074015166914240c5071801141e18403139a00d0348055403c1e5500d071011141c2c1e00d121410b5a42032400d20351145080e481c0c0c02502250394460341c20f001c0000800d4282c002400c0d264031418641441500904d0081c28009503040b009120641d0760f200c0c14030250b006a45940516042555141c0320340d100c2002a018162903040030b03410240300301c0d056a1246c0c0113203104042c0ea00c00e0142c600c103500c00d440210300f00c3e40c2c11140c0140c0290307604c1100410f01c8100c0010426480e0161400c06402c00c9600401d26281c015584515120040b000e40f5408050600c040610766a8140c6400700b52500d04400406600620f0031151007020300c440 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 984522517 1250 984521267 984521297
    0x7080d0c1205130c0905010f05010c050a050d03230c252909010e0c0d030516150f0207050c04051015020606121501090216060e010207020103230403 65
    0x9206111001120382800070349010f045620158016a03800c40b030003107003003801181c1030009014007070581d0f01004021890600e80401100e856441100944003030058000340701c080340c0e060169040d019001d0710046611040031403800203e096030551360903401001c0052015155020044440842c4911002d0705100b20f004003048450480c0c001c000e06140c0c0078510320b01d201400369840e4540217004c649404850f03540801e107500342c960121924407582c01c052895a4075182004d041c0a015002e13188c410300700600d024401403144589002500d64030038424480139240001c0c010b00c004080c11410075414807000b5a62550b0320540243c00b54030407a00c0d040000c4000c00c088561100a107074602103017002040c8400003941f41c120a40d0028000c8158017800501031a0005005000d102102184607540e803901241ca002500a441c80d071503010760000c140c2e0040b51260040342441c5100b01d0006075110360f1440090115894180300c0c4003a603651074a00030912220007a0540c1c01901030a1100d1141d050310 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 984523767 1250 984522517 984522527
    0x2090a1d01020705010f390e041e0b030a0b0406052a09010201140105220b0a0e100504270611210109020f0406030b04090803090610050607080d0c 64
    0x821031580e540c404546001803040540100c0c524110440f0100001c0c80401488121500520b11910541c0d1009022803110102007404060a828230300d01301620700200c1001406441c000b001f80204440210342c548410a0076100300001c0f940210010032f5110b40f039550782c0d100100018400740c81e1666600c0004d00041c1e030f03080001d13600c00c00050321030302d01c40c0d40300c03504140360300044001030040d86090301685d01e1031500035501d8140d0300010702100700c1c032282c1c1e0800e9100441c05c00b890340d203a585880951070b087d25482c2d414005450148103a8240d49083c50795100102e01341c0e80803e20032803d1003150003d000f000814510464848621211345103040d00300a800b518001d008410305010001d031880801030700440903844841d40601c1e02d51143d0307803202300105a01445502c5965460104000c1103243d000760320803140614050310110341301d0f060b901d5060098000311402142a00f00104000758091000c4400c2c0240c0002c603405c0b0704181181d1034081c1d030ba0041c90800401695603a032036010b564020 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 984525017 1250 984523767 984523811
    0x702030c1209120334230a02030304170f01330e010905090105070f02190c0506030408040f1d0609130f120e0a080a030f2309150702090a 60
    0x18007141d0380c0d408419026248550685002d03010310b03203100d03000e44900121440101109401c0b4110b140320f01a0241d032106c0a40002e28241118402c000c0c003c40140c03005d02c0030340000c201c5040c0303910016450500c0d007814010b038a04070701e48992401444200c40710a0f01c801d19011b050701103003003510241c0104004560300c203d401041c40640440b00000303901d1016048940700b01075070700003841251502c074000e496201144005001582180d10300d404422078a02040c120280100c80e403201d920340e43c40124445610544040d1215040000c2c00e0081c075944003032207130007042c462140000000a07998400d0181d0b1014245034070076150080842c41200440d6504140340390000e420341041203441c503110800c44402c0c01000d008c250015914042c51800c001e070300040b84c2070040507100d0030540756001c5030520380798103400c000e11140740c145031010001b0260940d581d1441113100b50b40c6d1103112040010b0301810101914070660100500c20050704e4102609070012150301022605031031161200c4252414 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 984526267 1250 984525017 984525049
    0x901090221090a0317060a050411120c092803061107200f0a050a0e07022419050408180105090319110306070c140c0d0f0b0702030c1209 60
    0x80c0c2400d00c0701035034001c25140800c91103500c604003000392610040005c01c10803074240d13611008041d02007040d0305043d0440c0301c903420300344142840c01d035083c0038410700e030718041c1c6000c3d1440a020540000d50b052901900c4211030100700314455464010001055001150000800840e16048103045504104c4143e44a2a5018030741202c5080c0d801c041c00e130224407404a02d80315014801400c02e007810b01015000070788a020788031131a0107042a508261001c40540207008520a6030241c2032480340b80f1555078088207020022056505000150711845002c0b000840300040c9001d00340300014a4000c100d03203150346070b0001c7c14060031464005880c82c0c01160303501368041c05480e42104100e11506001400c052240e00702200b0000030609155a80e042198903030040703080c08903140041010380c9107182c1980142c1d81107a007030540050102e058000400d00c1100c0d1107070004001c13403c000b2499201580f00c655403000b141020744d0340500d40d59070407215002c6c49102c0c000041850b1a034607112075070029401 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 984527517 1250 984526267 984526327
    0x2090f0a061106010509010b0d0b030a061b1205060616021518010306080c0108010e10080a080406031b020c1302130b090a1401050913021b100e06040209010902 70
    0x7a8641000d000d00b5038500008000c0d008070f800200b61464003a401905a41a0301c2c00f19003080d4401400000602c490b00c2160307450310a440004000503428002c0b074107a182049280c54080040b68806070100206698920782c90707041000700306145c1c0301d0100b503810700c5000c1203081600c2d041c280013040c02c615a18659802d14400000c9010100c0f60001c07645054490a0780d080100c00d6844600a49880a40ca1041d00145255004024442113460303200e411a140c0003030507400b40d980e800e80b54a40030010300100d810b0080458108022509031041d200515400351401c0c03035241c02c0b00381c000e407501603403440e0920600f1810780900c1c0021507681650743c01c80825040c60240e5441d04004c05036034014002c1d0f544035140700c0002142224400c404940c1000060f1107150600c4c5a030020089040421742a29069581c2031080f80300001c0c0ba6038501d11001300c11030181049010066448003600c016203841d1100350b001c0020302c001621209a001c1c1120044000140c841210125010f0542003a081d90010b9034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 984528767 1250 984527517 984527519
    0xf030601030e06090106080f030309300a090f05181b090a093206090712090c050114040b0405060313140304062606130e0a03050c071d0a02090f0a 64
    0x31300541c052401d031034807078049440112030208003d90303a1104a0360b81e0074907005640100b03001c150160308404d011000d0f401040d21503122941514154224034a400005440c20b8003c00078801a035540790060442601c0c05c448041c070101c081e22368060f0151101070600300c0b50980c0e4414002e0f02d01900d102050080a815500303070307600728080c0a84014076001280e480e82a402840d5140e45041d540c880322401d413100c51443d5513500421000000051038101404000881038204440310310450305801e11401600901c0380c1001c000410180c6040414500701004102c00e01440c06482d00351407c59070100c03131459503580c03000d900d4081c4e01c6070000c000700204014600310700b55260101c06003003550a00c2c0c0d50035032014280140c1c1400c0050b50b01e00071110510759004204141403030b1619041801700c8d5075001c0780720241c004045181c8000242c0c1038000880c04030300c0006441e000e0050800a05410400240e614a4009401155a070181a10340750590016a40ca0103031a000713012404584000c00c2c6007451 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 984530017 1250 984528767 984528781
    0x1403012d09060308090a0506091c0213060618091a0d080909071214101203140c010902040f110a08040606030b0406050601020f01112a01020a0e12120f030601030e06 72
    0x2e80140e00001e00c1b41c01000804212410200300341c1d0090340c8000c08558840f14094003c00b0040b0305d002060f60030402e144c088101905c0d6a0040ea030090a141e078481c0820b004016400c0c0d58022a500510300650405c0d920500c0900c031000809034030001295030001e0302005182c05845841082160ba0700005031204110606030481c8054992000c480003c3c45009040f000c0500251021600034a00f440d02443c01d002d490b44804031940315a2090401c19488040c618003454242c000d062142180e84d16500d44400b1820306018a00810480b0207080c4a02c1c0c00881c1500b005016100c000802c003d0303214001000e104554208c80025900301d103c004140c101740c01c06030b0140c00d0482d40280540f0038040c41c403414000510901c42d603090240c40750b50400c001c0350742669030f034240055400071105030300d108003010502c28401000300c0e089079200d00088101078414000f00794200743c0480c0b030680209126600d07400c0e012044a070700c61000c0d00b903a9a04c0d0b4030301005800400b030303040365400d451140b10208000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 984531267 1250 984530017 984530033
    0x140106060207090509060403031a0a1e060c051b06070c0f050a0e04030f2f060f09030a08060d03050d050a1509020a0e3d1403012d090603 60
    0x1610060780c203580c081d41d1181c03049016183c1c107075105040782d0301c00400500403a00c2540715907a903903100c981500d1110401000268000c0d4283c1103603100c1e4440c80029401d070410170881d0700050050f030401600f004c1c03041d00d40f5a11151300e0181c2c55240b4040f1082440c16a40d81001c0301c101542c0850810030b1551640c09145c0c81501030302400b8050302c090003000c542091100005031040380d01d070b5154400360300c10f40700840d02c0303d8900000c50030001c800900900c0702501d100050007503002e9a0000d01c000e1822852a0068031800341c00e050032600100210499503901441096000c041611001c2e07070303002103150031249440f4414200d0036262074901481480d07040c41d0044130642c01e40f81a44140c02c2d40b00e51030340d8224841d885038080401d400c0c00c0c9210841c10a00f0743e0101809084041580c41e40d8114040e9100349409010b04134451030309103291446941140780300801203c2c80c60100e04543c1007800400b509240c2c48511100d80d1441e615050b001c41c1c80c240d116010f0071a00401b44199070b035920304000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 984532374 1107 984531267 984531269
    0x916031a1c060f0c0309021009080d1b080a020607030f0b010903111c03050d050a06030c0e101502070801240302090408040515040608070c051b030703140106 69
    0x102070400c544105402040ca80c0c4022031b62140601c104000507505907288400d2102c0e001c41400803850004440060040318200354442c03450034010000501d000c07840042001c0c0000078000001540452450700031000e80d2001e12281604d45104000e13118810307020f50000c0d00fa10340801c0815010306080c0040317840a40f000e0303040100a41910003108581d0000e40200c1c4001408201c01d15aa00ca4507901c41e8444008008c203a00b59030300c403503185210748100d40d0312400501c080703103004004003110303070003030000f1402d03007008200e400000b0351140143d04c80d08901e540384c04c02400d041c0c11022070800130603034185200c1006074116420024407400240c810b590f2200140804200c0d525040b00100035400509601529980381030802481c142e80104010204030050b290340d40045e20016640c800c861003c55804198040c900209107012016440a4003411381d60010300d88160f01075010750 = true := by decide +kernel

theorem cover : BRFrame.Cov 984352517 984532374 := by
  have h0 := BRFrame.cov_init 984352517
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984352517 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 984352517 ≤ n) (h2 : n < 984532374) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
