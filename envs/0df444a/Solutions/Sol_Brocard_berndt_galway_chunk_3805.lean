-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3805
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:43:17.256298+00:00
-- url     : https://prove2.me/submissions/54d8c203-a4e5-4f15-9605-4083e0eefa43

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 684172661 ≤ n < 684352517 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 684173911 1250 684172661 684172663
    0x11160602010f06210305180306011413050c1e0706020c0a03080a0e2805010e070626130f0807030914010302090f0603090f060906150a0609031704030f050609 69
    0xf400342c000340c010644000c2c000c10025640c010203207001014007a0002d80d0350040c0c52400c480011041e401402c603460741da112041c0b144403481c4503600d21f000e500000700740c44004e015802164031031803e003061030b41048001240c0034030825400045038032440b0f01300a0303800442d4850006000b0741405000400c444841442c004202481c0100780d50412494070010030100507010400300c0d000542441c0b03a10040075081c409111812026000800341e40c80c01c5d1260a5600011400b081114255191850007040c40102d907082e07400b01c9003410500c0d99003000000d82e0005001050b0f004240074002c01c141c50a0a07540b0f40c003495015001c01d5001c00c80103041000360342e05041040d5591402842e056003000414404180c00e4884214940c1c416135000c000034020b4842044217000f40c02c200d808a41c082e00f400068140c888606a80c8900740c505072000c04c2c4d205060010701f0804441c0c0541e900c480d5a859921491001c010702c072818070055104000010201307041c6810900d00900420240207241041c031016 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 684175161 1250 684173911 684173921
    0x30b0601090807030312020f0f0a170901020703232205100c0503160203120d0207020a21151407021f150504050a0603020907080f070c020d0311160602010f 68
    0x122610f030300940003403000135405070545c0002a0003800140c2c8031030300e03160414014010607441c0d08403c40301050b416802c55111208100d0000095000140f644a540d0080c5c282d01c650040500411082841c040c5050b50921007402c0c0410f507004a241414140b8084000b401d00d500444640d1040081c3d00b40524a4070003e071460300402403c1c4010b0501c80e90742c2d580d40740e006075045420032589441c400070554405004400d0b0110100c00d1255580a00071070001c001e400800301a40902800132000c60541000d00d060f055594071598807a540880d140d460b20b045000d0360300544291a100c1c010902d4080352109001d01400d2550007400048408404c0d100e004240d400307403050140c2c10454602c40c540a990401c0c4165281640e0104031f9690b036030303601c1018298a520003904008a581007005c119480401280249100c50490301d044c0c503030980494410040741d6002c1d5201d1071a5a401e03000034081c3d6090241c000302c3c18103850054514400307241d8004c04a44c00070b00540d450b101a014403d0842c45a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 684176411 1250 684175161 684175169
    0xc02060906090a1101030203100302040513210203070b190603030e010201051f060e041803111506061c1e060603060b04031101050c03040b07081903230c07020901030b060109 76
    0xd140090f42610f411100c1e04200710030505041c3d000003c00c20b072044100d00e10000d160054030621a5040140002c00701251056050b41c1c902c41c480d0031800c6d100070304660310400c038440340d005508041d00d0780c6540b1016040a0425050020b608405001c040014021440114000d48500038040c86a01c0003909440000340540c00840070440e96020b2030041c0c6144800740c51b220700e002e18000e107000740820001d043c500b8928400300120700900c0e0405900140030340b9210071a0040d2200d0440d824a094807241095842c203500c040c0600c0103280c4000c8034580761071400c207680c1c400720390302c0c0b009001a500b9002801c800e030032194035181c06008064150246500502070011503900d81803454503010b4442c0008006541040030006900c40c526400f04242c8000d42019140d107a62048186400d81955000280c80f980c03441c07101c2c1c40c00b0385882c004d210f40e581080f1207081c07407006414590309410a440c0d0003040b010005030140326504c00358503111400d0307004c0c51003a40c103080305060480000d0000222a44 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 684177661 1250 684176411 684176413
    0x507291e160f0b070c021f050c1009060c02060f01141f02010903081303201c02100605090705090f1f0309110a1d090319051317120306030f010c0206090609 68
    0x490038005890b80800309111086447d010401408610011501481114004070542c482c40030308840c1400c1580c002003405125020410410b940c0003400e83e1140d80444101041c4044000100030401c50700300d01c3c0c1d042e0761000f40f04000803a1070014040818001c0d10301c100041c0e55031241c1c6406c05402600e09034101001c4510040140450b5400600400b607110090003190107400348210301e40c90401c100301c10846c1d10b031201068030042d044000e50f101144400c510364036090900029160401c00e0940b8040c8078203598182c6440400b0b41409440c40045000e19040480090101a1101c003214001408407081d42c0100d410b60103030800141c0880300c803566034810303a4042c004101e91041c1a00303c407403203050072004d0780c281d41e141c0c900c242c25030099460308c0700ca08040c50362551486910900408411405802627009592105c504414030300000304a80710b144e1050301403030b5822011002542d80301c13000404540c280098418600e0030754130003001c800e0160344140c041c8400e446041c4600b90f403000c0d040c8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 684178911 1250 684177661 684177677
    0x9040524090c0d060906110d1104050a0303030b15041e0807050105120a0608060406050f090604080409110409061401020f0c210c0901030507291e160f0b07 68
    0x284010b4446582c24a980d00c1600100e1002042010304d401105030389400800c1004581c43c80301c4190300c40e45c088403817560042d10f0500d0404558403c3c20550b02918405001c0d0310103181980c0d001c0d0002c100122400d94820102d03a1803502030303080724000b000030704031000c041d0540000d0300c5902240401036800c01205900702060038881c41c0d03070103025140d000220a95040c080d444030030941c40103015a4100c01d0460103800d0800c81031112a0b04007074020300c10041190340b01d0f9507412680381c50b00b8081c0c9004104030b17401c10040001462681140f03820441004510b480d05a60303541501c11604d032544000c8540244401c2e4840310760f010310030111114005009401c416040c030b40010142804003400c102d841c01c10391440108024100480c484428001d014206030756100d0030419510320032131003010a031300065403203401108111030280b8050003580c240e9505144245450141348220700c3c0d0705001c1e400b81408181c1d83d10882c202d6002c401c0703002d2003034110300b81c00d682000425254024200f50134400c7c00303 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 684180161 1250 684178911 684178921
    0x30a1211010c030204120b18010f09020a080d02070302061b0601090f05060105030709030213020f070309090e0c0102070b0d090227010b0c06060409060f060306051006080106140a02070509040524 85
    0x1485132604c1071030b4040c2c1d007e0503e40c1c5a00d4a8541d0b00749000070100558a04404070007181c0306507021142e254000c81e21100703081e03901c4002550b5045001e05100c0180c100403810001400c0490241c1944403d190a484c08070703911080081c03414000364841d0340e000b074a8810000035042c00d8031410743c00130000e01e0311a14500d0641ca0103001040c2e1444001e000c4d19612505d05820507d07a41520a01d605644409070781d400703241001402058280a0b4071000c902d00f60101750032000015040c0c10310481a005030444a00d1f2515549107a042100e40c07002e0261a41c1c4510010303038482aa00c000c00800c0115490403201031f6000307001101058000c80640030041140f0a4160800240d556001000301d0b8042009103461403c00c010700f0004901c0c200140c10100040204503080c0c000702e100351004001858019a502c034101c1e082c02c0d00b8800e410128034020441080f00c01840020302060b01c16004507402036584102003045680c04031016256500903800040030001e29030f2403d2124080441319940c14144 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 684181411 1250 684180161 684180179
    0x1d07031514010b0d020403150e07050307060e06071703011217090d0209191b02060a0b0f0d03180608010509100303020c0f1f0801061101050106020d0509030a1211010c030204 76
    0x206003c0c0c040d0341c1a011a4446000d891601204c0255501251000720f42c0d84011402003c0c02001e81c0e008458050340308040b40d641000544942158995540d4164020132442404030941c0702c1c8105031030308a141281d02004034885001140240500a0410503450306803d01034000c040c803810510103208104410745459031643c482c000d9041c0c0450b54101e460f02c602101d81080b641d0300b9101268941002d10f9162882100d020380c10035001d140c0c09880440d960f0b009928101c40b815240030341c1c081043d070303443d100c2824921001c80e00d080c42803d252400090f8099041c0400c4400d074000c10010b906400140a80d00b0040141a008100d8090b158001c1d41140d802075203a02c80f14500c140036000800c0503134015541c5684400300020250081411001da5443c01022900c0902070080803d000044580d001d240520501d4102c0c0c0480d400713007042d8405054211a42e07481100215450707c05c81c0800800f041c030b1803030018516074007030b1125a090031051000d2400d54900903111010305105010800883c04 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 684182661 1250 684181411 684181451
    0x6041518140108151002100606030605090a111c0204060e120607120605040e100c090e0402010c110907020721110607051203010603090b34031d070315 66
    0x1003400c040c1c0450b80d4a50110b885407084032401540104e00714601c0303083c80d1b00402d0b0304000e02121300040c0b0116454607000d805882440c4a61900824404000b0310504400c0c1d212601802c4407805a6180800441d0070205020050017005815680001c04010340c6402003000c6070051016600021900c0c0d5480c00592200001480c2ca418044100314450b0000d41a0f80020003400000300100510817010329071599580c0010081d00b0024505544085e04500070182c480841c1e0344000b0b900c03000c0c2e8842d8011641c042075801304803a4602145403032800b640d504958180b003085142d00410900d4a464804000d007071071801c507840194400b480c01d00106629038403d511140003038070042da440c0d1241c908031340740401d40700300350b408054027000202e0f400340c0c03541010b04428000c107071045240c0c4400265111400c24003c201650b665003800c200b1280500315031a00703202106080000d5551007640c4070100ca07090040008945070044138041c01004109541044d02c04090003040219059500d4102e40201c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 684183911 1250 684182661 684182699
    0x5240a0e040b0a0602011514060f0901140d09030807030c0906031d07170c06120a050a090b0c0d051e18010f060603020c0f0c0604050607080906041518 66
    0x1812100528140c507240c210030440b080c00b40c40c80c880c1d5035541c1c0001b4020200c1d1200714120107852840081c80000105c014004040700510661600e148c001d03107025a43d03c02c20301941444114800c001c012003103030001d400c01e040c2000000c69014213070700e4020b065007002008501410301c0d10fa80964240c0d4010450b0044c0c5405040c000303800c00c4560030300180c64010384e003100450f109849011500400e01d2006900700c00b004030854807484004010080140078140b5400d80780608103000454400c202c1d041142c2020040400003520301940d01e9075810000100e80c002c68002c0c00080810f5071010310f2062690144c2051041d201c0340b01c4001010361070b4003014046c0042d00c2d0501e480035188180070340c0904400603040d1030402009543da00054040d4104449a492a0180311030680704030102280c01c08520030005c0c07a05107024200030410500d0780107200140c2d0544424089110991a407a000700058800b98071714444810000700020511004d000882003403003030100c8200501d000d059500601780c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 684185161 1250 684183911 684183917
    0x5041401020d12090606331110020d0b0d03091401080c07060c050c070342021602030703050102130b070b0a05040f1a10150503130203031c02030105240a 67
    0x14505003803040107002c580d0455155a111410a8003460507d0042c1a2550800d078503c01140d02140d2015100d603841801c544500d60012482030080340c802d60700403c03252864900010b02003080034042010080b040800700c010540c3c42d00180504000521080c48034407092a1800540c40c10312480c0c003c600075503d000340102e07220051103901e180074000381c81c0741c2e10020088600e80303556401c044201904030f000708107420440300d031418151064030060501c81040c29124600a00090301c80c2c4001f940b2070100c0c0c8411106a80d00e09005a07018030201e0002c5010754005600c4106001c22036801ca4500da100d0021058200a580c1c00900c080ca6035503400702c00207800050780d40d00c0c2e0405a00c00240f110b00284810081d0030b14550120001042501514007030039109400c0d62142c5140042001d14900070004c220203000044007032440e0112400c900b403018065030306240321003c540115122042d56680c08a4000c0014010350030068440c481e21112800d00c100c6542c05940c1c09445c500c10203146a0030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 684186411 1250 684185161 684185171
    0xc0207030206070602160609150e031b0f0d11010e0106060206040605040c0b0c011407032c030705070e0415020304080418060b0c0a0b09150c0703090e01030305041401020d12 76
    0x41c132649074151560800030f403085080040d80d40c80c0a400903d00400d04480d881e481050a0108000c2072241d032100508000c0190710303020040300c94620100a0031000821845100c0506800400030302201d03003001b24a440341e6500391000b0300e5850030741e0101e4085074410703032602c4401c008180e800144141c125410280001d60f039203a84c2441d503000e40e0740382c2000440100010344101000070562200e020010103031490a5140c5071410210706650000680303510300b030902520041707221025107c6560324146501120f00e04070035560de01e41020450341c8220101c100384800c120a00403200e4402d00c0c0c0806114085145140507620380903e80994022aa040f06034640481c1b09042240c2c89034001e4181c0001d8281c503148441c20580da21a0905004c030740b024600400b04e01d2010000a004c401c08541d900c410704c0d540d030350300c000000b103400c01042030381000151600003903a4106445c4060107980a0780e031382580c0341d08140c05c40b00710242d151240c034119070000c0c44800c0340c182d2185030541401d51900022a03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 684187661 1250 684186411 684186413
    0x2070e010b03042d230114151e0a08060103020108091c0f031e1a0a0308161b030326090607111f06090c0206091f0e1507080a0c020703020607 62
    0x202c0400701c00300080c05118070025801c810300f94503140681e65a1030000070700001401c10301c029601300069400003500350642280d030150f4275126214100c000401c3c200d180b19100228001158003045501586550b0070200046c0155680101a40c0e40f10b07194000500c140801d990f240280e440c1450448420400418480350025109800009160003000c1a42480114098171030300104010b1015558482c007280e18007146080c40981981180d402c49111410f012441d44102c03030100031020101c40c0c0d225a404d281c92200c0070070540718040c0d0b01903959442e500c484c501d034202e0009080700c8a40c007a4410a010401e0700b0b000042c6544d448141480c00101d5140c529541d0b919080e0f0081c28841680c848010041051502d80c0c09241113030b045040034070040080010036601c6440655240c0010303002010381a91510189044980a5910361800075041103945501820541a00d0600e48100c030304405104040c2c2c2e20220041d000300041c4001c1194492000d0084c1d0f540c81a440000d01a402c0818450 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 684188911 1250 684187661 684187733
    0x2306100c02031608010b04060b030c0a030204120b0114040e0a0f021201141b0702010f05031e070f02151e150405091f09080405061305030d02070e010b0304 68
    0x604181d400b0b000c556200034030000d60b0074589a00d02802c42250b290410002103407426000d403008442c0d01c0c03520310f4559114502c5003041c80c1e01440e104401d0640030080010354491400ca02c610090289808800310f505104110801c4040180d039240b08a0a203518414007050105208000c2540300120220620b05c610120301035107000d0304403890f08d5103091003d200c0200540c80c1c00780f103002c111800984100d140051408540207480020303000402551a52031280e010b0401140c1000030443e40f5250354280e4102489092000c4841400054100044900c07072501040b813000500d481c02070001a51400444d2280d1104a0801050035081e1000c040b80c0a0100401c51134401071011740280b20a1a1295549503554024010380795552505007504903184010320407059041e0380000c40c1850640b8000030800c55809c1222510044404020700041e030f6541000b0819a4184540142c4807062500b40c03808000a01613102e803408140420400c800580c10f0505944003850301041a81c4d8051052041 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 684190161 1250 684188911 684188927
    0x1801081302030303090a0201091517040c150c0201110d081f0305070305030403021002030301060e0121050a061706010b0307050703090b0a0815011b03030e1f0e01230610 74
    0x30b900340c0800014031036013410104210342824001c4c1c854107030295403040e15080084148240000044600c50f92881c0190f5030341c000c1b90454000c0c3e401603040d5865612606500b15000503407400b0540b000040001c650300104084021383c04c507405866600002c2c58081c18901c0000c02c1440c064117040c140c051040054000b800c041c50b04001124211a02c0745080c40c2e0702d6100c1d010a91048440658045a00d1720002c12a8141e500a64030441c15400d50001511061940420f401c0c213483c54106400380a10a0712405202d05c8800c000840c2151810512054040580748011403070f4100038010312204029108403070304000d540c50090b6450415003012a02058150070800c008070001030195002a88800414012540c01444204002c0458010f54190750607441110900e010504c949010a0007940924280e4100da42a0740507400c00080d10b025480324008804030a03561078112a900302c20034031418005030280c140040003400e40398000d00c9401801000075108195110411401601c50018 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 684191411 1250 684190161 684190163
    0x1270b090d0614070e030a0c0510051207121104050603060f0f0a030803150f01021e0712060e0c0102010b13091a0f0a0c1818110415080a0218010813 65
    0x2c20440380100d8180c54201d41c0060798403a0010740b260311042d01034600032039140c42c8268841081c2c03000310328040511806a0502807040203224081c0302241c0e614028141845c480c030001c0c0d803aa0b05007024507840b40f0444000c1e003180c1c40d00c11014070080c4401e460740d8040301d40080003210340d00c2c007900740100010304d121041400541c00c08003032080007041010078070296005560806d1105121540700301409501280f0342ca01d50b005034404d0203200400003540c9002250015118203a80031b00e0f8450804800c43c45900da8100c0f08076941d00b084107d018070a1120100b100000d00c000c0c070901c016000020300d4000c00201c0340e074440b40e45d040c46000300681d120114100200b4911030148929180e0844003580a040b074000c1d90aa041410b4070306e12510460b107031040d80812511440300300c0e0800c1040a1044660454004c1ca0343c0d544990b0f00d07040c006d120141c001412520569103051100d550b0080030321001401401d42d05c0c1c0180310702e5500d403c424044106481c02841d15180c6559120200801c008810348 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 684192661 1250 684191411 684191423
    0x510020c03040e060402090a0902090d0507060f17010f17030c06010f05040509011407030c170f190b031e0309090408090f030c090105010c14150601270b090d 69
    0xe40c008403000100160044030000c0500701400d503100024030013603101d41d031070413907100200010501005881d135014043d842009080e11503a0601550b501c1c5c84c00526402210215240b0800004401d9020101d601c06a12100c000a0254500000c18109141c0d13070080d484190402a5800955041002503402c820105800c8441a5960382c55003000c4040034041c6d14009d80c00c0c080020071070b03101405000d0611140300341940a50f61620300480081107010030103c10000700c910b47c1400c20004c9015103009183c48211240d05003000741080d030459904800b240085810f1010b103016039a00072034609100c0c80c00c0d181d0300f003001c00780e030b00e0107425846401d8035140d00c070650109200601c111074028041154041d240200005000c03410036984000070b07000c06601107000001030000394441c90041c0c82c0b55100c0c0401942c2483c102403407a0404001d42211901d02c000034040040560344114403444010120240700f080903450031020302c111182e401035407010b50000602c0400c91302c400d0038540c1d002c0c0d0404 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 684193911 1250 684192661 684192667
    0x1502191b021c2013020c0d0e03071a0d0b01020a0f02040515100e1002010b060d020d0902060f0a0914060315010e0d0804031203020f0d09021314040c090608100504051002 74
    0x43e01c80302c0c0c0b243c81c076411140070300210405104c9000d214400c8414688010000740860349210500320750b0046014112501030050700c00000300740ca10703e400300c0c0e0314010900b202d584500c1d1101114046510000d003041c1150710240052001c01e000808580c1d600342c041e6000300381941d40001c51600c20301c8a035500364014403180e10016040d9440b2040182c011002c841480409000440880c00da80083d9400c603404002003202032200c401c294000c1403014049075010940d0310090300000d1490300440c102c444004c5000403100f28541e03109480303102416040c040803c9100701c400108015000050262405041001c003c4000383e00500405c40344100003031040d444905a4075141c0165001444100c914051001030b04001c1d50080c020303220b40800e490b00c2e8504040344115040d015088403c001ea80290b0b00000906a03000580031b0301c0f031000e6107044540170a00703151514041d01c040315800900100d00c0c2000500101d803020031800781c0c2001c280b1003c10507803100d040050805030f006003071603090380c400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 684195161 1250 684193911 684193943
    0x90603020a052802010608030315040e0a06090309080d0923030a021914040501030203150a090c30021f1e0206011707030804030602030703091502191b021c 68
    0x900e2202028500d0f50b0300038800c0c0f5550703022031580d902058502c1400d526280c901d01100c1d0902d903000c0b1a06a00c601d045a10410503610794000315001c0340c0c1c055000404414061081050801050403540020b2401040d5a2300d0309100c0c2402d2054464800c01064030580c8514480c4d07010811203020540007444e1041c51800200038407070f902040c0c440c0c0c68a5410b10b18001d1b40600d040c0c07050504a0b074010703002e0820300c081c41c101200d204100501407045141d0300c400340808031b11004090006414102062200309140100704a41c3c59000340c01c1551460041c079400c40103884d170161160032100e0103a01c000c0607402503081911141c2600041c0401c4114801301c943d4216400142681200d190301c0c945020800d09a0700707243c42c0c1e012404090180302c0200710400000d58654025a0f1158007880c0004000049a03100440d005101d111040400d0300415000020f0b450240800342c1e0f00410704180c2540ea214280b10100115281c03006842907071320705201000402c1d40011051000d44c4152801c10000315 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 684196411 1250 684195161 684195217
    0x5010b1503092a0405070908060a021209031e03101a04030201180b030106050f1b01050403020d0c11040b0409050a0b101211040f021c2a090603020a05 66
    0x40300c00104612900781d1000909a021aa00d446103c1d000c04115a600160003808050800940a981004880d00001801480074008580110701d0a100540da54500c40e110b45108440a800c4c6041c0303400c204610f64401544000d00b08e000c222b4640032540740e5442070f1803102070280d1540510900380c00810b0801085a02038000c0040d60320076212001105010307100d016940003d0f0141c3d00d006c450402c01403041c94050310207440c501e50035001c1d4600c0c0c694180f840412280390030540345103681d160400d0204041d0140490f40341c0368082e14024031601a0358540c220301e04410307036205004603079420340c044254440d80c20003440c0c0e0383c11031300715509800c0c1c91070100c0503480229010410210703448404640083d900000d00c0b90b40d500100d91389a1a00030108000c01000d0145000d201d860b800c1102c2c000c9115410b4900301e8480c0548070008400c550a502d0f00c4454601d9200110306460307402108030501c0e001000d02c02910480d1030010380320b400c104816100d0340303e03c045840c225000e0306c20b88004203103 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 684197661 1250 684196411 684196417
    0x9150412060501030618080d0b04091211010507080603070e060312070f03031107030804060b1801061206080f151305011a0f10080705070f08040e100f0605090d05010b15 74
    0x3c400c0904100e500c8021962861400382440c00030544441042444134242d041d030846129030380d00400008802f035669844056150720354507a103010817101c2c109200f82040038420141d1044460514a0342443e1640c002510f4400d02d0060040d650030b02c2c80403c40d103403002c1100740061110f021343c03150b940b99103041882c0d40c0980940120002414810400302101c0031000b5140710603072644408000b0b48895851602070b10b8036425854101c984907182246441c5001c40f640c1c000c00943e11138440203801041e0940030b560060f00000d00c2584a25000e07038022800081d180200440708925aa0030b850711551803410f01f80000c00942158203004103010001e07a0b00766098600e94044400400c4112000c0600010700d180c0808440856000c50000705030380d00403401000340714894400c001e2190a15501d40450f5049900503104001081003041001c07a801d1350283c01404940c3d2419190701e03d0440c0080c072510030142501c0c02150310210a17800c01c4000d40120302c2101008021034000f4610806130b1507250 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 684198911 1250 684197661 684197663
    0xf0a080909011e05060c0a051609060824060312270409050d030c020a021e010e0a0e13170a030902010801050a03050c1c1a070206011a0915041206050103 67
    0x40c1e850001421118410912040158408414190618200412446410440d4842c1d554003034068003c001900c14488080310050001e082d66455050910a8048824540020005a1284d8107814016810a281084c0c00401c20801501982c4070700200b400c02038041c43c090b0380720038041003040c540d425200125034100b1003407410807450200402003205480a03040c015040da0407058a2035400e07482500100003141d03d50040301e128681c0b55000c21381c0e03012030204000c0d03071201a008007083c5690040040207040c100700c5041e20241e0904910711802e44d000b6012000c040c0c2445600070410030340c401e0003034003420720ba41044c0e100c6001d464082e029080c60f400890010785494004110362900300e0006080c0c9411800800011200c0700c184458102e44001c0003480580d002e410000243e100d0241580f00081c0301c1a29149041400d006860f02c001030b0030500c07501c10707203402a07034092074000f0949904100441e01644401c0001485084a00c41c64002100903990080e2035400d006007600030034102c5e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 684200161 1250 684198911 684198919
    0xa09021309150203010b18031f05251e170a0c02010501091a0603100e161d180703090c170705030c090705031510120f050c04090e0f0a0809 61
    0x100102c1010603049102c240915442030a041c02240c400484440c03402421090240884907004814801107000e413045030400a2066203c02c200b0004140c0d082c41c0d480c4000c148440e868071500e400750040d01c6081ca03110240070110740308440b0000c16115140d681e482c1504004840043c0c2403000b00e25005d03008030208030001d0340c01c07d00001902a854460848104107500001c0c2510500314100203d9500c05404031a21101c41e1001280d203412410700719025040040c2c90807001c442c40113019090140240c40c05c246400d9a0107a0209a04c80f50561000700c05142c486005a03515010194010a260040075000411102002c0354100c94081a40c00039104403080f0b401d40d907554000c05584008074a540c9070040c02500100b0210f500803805135401c030781c0140389034024400090126032110315000d8104001922a500344140702c241c1d1050028000707041d101403040d072810725169280c5114600c98480303410341d0707050007001045040c003040d03407a14615002c5d074070405254289210381ea00314180003481 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 684201411 1250 684200161 684200183
    0xf0d06140a0b0315040b03070f1d010b0711010203120106091d091203060d150c08060607030e13020d1406152d0d150e0108010b180a09021309 62
    0x803840d00d400c200c02158800c2002c0c6280d40c0d40d00110b158040440480355070044c1d00c401210207150780034001074015081d0500c00344d000a1820000d060300d481014030b25004015190010b0115950100c115150b641d0881d10104140c1040c000407407451041400240000c41242c00110f801030340a000442114580d008112048010b50242403202d641960600c4450788003c1100c104203848601450f40700780d0080400002d110591218200091030b0700e01e0300f0541d5696451000ca890300811400d4000d4010340741d081c00c0c0152a9806024003c2c51a90075120350284c0ca803240282031160101c80d03080d694801c041c8034035000c90002401c0f0f1803081c3c03002440781b00114001c0d136081480009641c0e440040000c5a100802e010341c183d4088903204050482d2150100040984030b51796000381040300030706081c444da1032440d2182d52490b841d010380000e035242e4180b00804d8010faa46544541000e05500440c0040fa240c03c2c000c0d80080c64040310080d0000030032080c0400410b416840800964010090015 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 684202661 1250 684201411 684201449
    0x1612030507030b0f04110f0c01060f141c06020f04081e0a0b01330503071107080c06090a1505030a0c0206070c15060b1b250b0f0f0d06 59
    0x641d4040d510703d80e00300505807400d8050f40790030f80200d448454045441d41c50300c466000b0f00003065100d03800c81c5e081607441320803c21805c900300076284000e0a00790900c8040394204000204d4180c07001d4120300c560207000c5400424080c40384d049030621200007403250340d600d0741c4103e60743c1c60719104080714041c1d007000480d1034207408000c503440c0340d01503012142c070704a6803c18150b4089000d49a00c00800b0741e00e402800c80d281e03203585d200d000c50b040490b200d9a45a160206004010400103000d40c1401d8001050802801c50b00064688104a080b40c0440d2180202d03c00301d0703d00000b40d8446102c01800c058009120f50b040700003180520403d003004d00002030b5807042680d44000a95205000981c07580c0303030350040b0782c003841001d018840e003510128020340d407484104959001030312011140c60701c03984d25048000040084c0c80000012280800c0301d44062190010a540d03284039000042e1400600c481d080240d59040340c10080d580c1a0b400c0c0c460100f0101f020081541d40118841104240e648003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 684203911 1250 684202661 684202667
    0xc02070923070f050c0327010f02030315040b19030b09010b0109090905010216080903010f1103070c0212060a1b0e1f0306120506091e0a0201080c1612030507 69
    0x50307020a001d8400d50160316021012280c1040f0419001c040240600000075000001c1c0010421100d928450014418441c402e180400703140600040c14009002c40c48004640c0100a03254808149686c000020310b11130013060141501603205a802030050310380540c3c850b84d003024002642c0c01000034070450740d40c8909180c00c0303404140c44c1134045182940304004254154000420303591146001500305481c0b54000340c4650f003111000c030b0302a44042540100760400344562011060100c0043c0030080e401040003080d84009030802c4108890b404914056407030318039005030039028600c21920a4603000c001c4500405c04201e40e5003842101a01c0c003518148200f940c02154500103045000703a442d0005003240030036103032a10505254480d0702c00103051580700303009a0401e000703001902d03d5140c06900b150030144001c1ea0051002e100510700108103000041050445030b082c20031030181e0302e9000721004180550800d41e0701003030780441c400e8200f00f6001d0007154100d0641c0c409101c1c81d15500c10503 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 684205161 1250 684203911 684203951
    0x40b0a0813030206040b0c04120605090c0a06140702220b041505061b010e01021b060901060f170709060305030a090821030406020906160c06020a151d010c020709 71
    0x42c005a10460100d0049804540903540144014039803619240d59104207802c1001c001a068840ca581c076020005407240034440d40700c942e40c08a4030b00000d5401c202c0d0140150300c801c3c042c7c0308000c1c000304050381191039014a031810b0134109442d41ba401d000c070568042c0503000e0a8100360249040c084406010021303c2c10000959200800c1d96080c800317048100760324680880c98900166480709141e0640301ca0a02c020003103040039001c007850b520790b902c20843c031707205002c0c16044490b8580001040001040c0e4113140c149e43c0381500d003114490100801606d031480d19007080d02c0140c0303840000410041d000002b0b040e456166224030701800e60300c0c0403580c6c595007080e050351943e081c0c08040e0b02d8000303130700001541d1040c4208001400c3c060341c50007150307044d0010080b2105c09000c1c0101d80e418440000d55480c01061180700074040b6070507660714480b0110316080c2c100c01c00c5403510300349892914003a07484440e41c41244002c02a811040c08000d50300d181c10701c11840700b940303060f4441d4050000c00f0300e4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 684206411 1250 684205161 684205163
    0x70f0807120c020114131a1513061d0105040c0807140901120203070305041b0b0a08044206030f020108062106180102070c030303050c0906040b0a0813 66
    0x590344101d40d640341000c024001d0b012419007195079032503665404c0d52a04620b0f03030141c4001c440c0b8030000e034054601803007961401e01c0d014400e03020071030800106261404000d6411041611075010001742000c3c0a0080c1c60305d504003070b0300c48c0415a0340b001d00d070110342e180034101c41046605020094ae201d001361000141501c0e060006203401d4084003101e6010340c0140303040d03035040c50920050107107001d961040380c005039841400292031b601440140440300d54100090039141040b4100c0c0c500d080304034802c0e071140501d42406e024210000500340103002c0861990100c0d840c040704040040410f03c085241c030300c80f8030608402c0e6030011a15181c41c15219100a517a0701c0540c2c4c2d00141c20342c0d00103456048000306a558802ca00b0013041040c00c44595030300a0848082004010505000c1c0610403030310307258001100568070501c13205002c550720450003412281c050a0000b4207444020441c0440c0c0b0400d41c02c40d0700a00001070001d28070740c51000500403e4115664565981c40b070079070b5000700503000701c8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 684207661 1250 684206411 684206417
    0x8060f0607050d180803221a0901140c0105130605010603060f170f120d0501050d080909061c0b10060809070e0a0902130209091f090b0d0503070b070f0807 68
    0x1002c0b070a81d0081c1c113101c805601e48400c80d07400342d54482c6481d18662080e0300f4071112041c40e91400e80300350020503906003d0000048041080c00d4265148283c03402405d2034981000300021003c002c2c0210502100c0d42036440500a008900d44000c01480241e80c0702c4c0304540703581c80e02000080440c4a442244142c0301c10781c0350303440c06901c1d20311044091420b1001c10400c1c0d0107560000e40c2c142e58100500100355420f420981d0315407400c00f82080032104141c0c041801038030f000c623002c00000e03880300c04c4694a050481b5100c02c10b841e1240440c03510300103028083c21202c00100654280000302c1d003000d20800c1044011103005072200d404417880b81040d56038a1007036010940500c10b2034140c0c0c0a0aa120188140c0050300d00b1203500024001c944258140403415400562030100781001d007a4203034800074031a0081c46400d0600a0801e80c68424840c0f4000d40d84d40d450035100396500c50190811582d0401c040b0b03510750801d410405040c0c1003d48540c0041807a02200c41c10f0710b07014003e094402d4071309407 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 684208911 1250 684207661 684207673
    0x307030515090a23070c03050d0609050f010807140607062a05041403010603030822051f05070f090902090103111801081f0e060d060c0e03071202030604022b0308060f060705 76
    0x47d8040d00c580d005400c48001880c2c8035800445c030704400b8421184181012122030700309514200d01d550400030386400016140b00f40321000390080e2690011601d49503808070000425401c0c038951a00c00e112601140041c6c009041804403146038800007800560710010741c2445001741d4601054229811880002c3c0400c1582001911200e42c00038501103410010561384024051640c0396400c00c5400d410751a00414150300074090510740d0f201d400d900100c80d04001590740d8010801401545441c0b091103051034000030303031a030141d1003a081401d82c0303018000217949584000c071a00030700740007030b0a00a0004110000050740303549018000280100f20300c03084400c07203040010710449500001c00c816007003041c1c1d42d83e440c0042c802c2e119291441da920fa56200c1407079000380c101400c090b0540d1180040300c007440f01100141e80c0118945400580c11501da61a18004120440380c2c40c0c000e40c907101068981405030030a064100e800d01f48500300445085a0310501e110070020303e40203910000e415a4008 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 684210161 1250 684208911 684208913
    0xf0e0f0907050903030415120608060402132706020d11070305040b07020105190c020319051002180d030206040201030f06120b04080c01020c011d060c0307030515090a23070c 76
    0x10300000d0140002c05000c5c2c0e8034094403003400f00c810b0300c1450513110016500815814501000c1e11a20002e0601032025140c0d5040039000508121445e060100300155070741c42c03080003201400107440c11011140140400c4507504d04004000750400c2c4c04171790141d42015507081094000d80c0485280a0b85511600d007481c0c1011420101034100d684200d040c80410014001c05880200c280c1700000b5203580d0b4035201d44c3d010300c14141000e10851030383c01c81d240d48103034000000c6c0300803070100c5004020620060702c0d0460103895100d021403550b801900100c5510400301495404500c0510440c002c1c2c8087c0b04840c090010a030072100184102e00c200b1079400c0705100000c085151740c50700540146615070620f6100000107007242d00c404506907031a9034803011005a244544800480103803080d02400c254908208852a1448001c100302c04141c0d0721400110182e080b07903540c00700c40300c028001134403601d4a010220000c059141e207030000c03101440c1e10751081044039100240301f284940d551000303c00c0c2c1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 684211411 1250 684210161 684210167
    0x819050f010b013009061d0f0d0804050a020a03030503220201050d020703031410030b0c0f2b06062c01021c0e040c030203040317040209040209071e0f0e0f0907 70
    0x34507a8540f440c1952458030200703019150007010003042c0190070001c4c42e62807c00c06500344041c41104080180c1101800681060011480c0c000841d40c0d4100400c4c955900d00d08241041090a03000303601c03050384200030042c50b03800800345102d030074124100003218880e14400b0301c6004c40940000e0001d05c0130841c61705401d1042d005041d010f03202c0d090128140210000e80c14070303180700300c50f5014a00121182001405222207000760024140c1491b1443c00a0588103000d0910542894a409403111586c68031604881505242e01405900081004548503800140740041101c00ca12641c104c01c403890550580d82d681084040c0720503002000c08080c2c52941d64200310000020805000c0002e03205a990340341d07070041d186004c02d40d80d00160340e440d0602c4c01621040d040d80c42c1d0307021703180074004000058540500040d0415011900c4201598460f40219001c130312968182c00204d400c441d004040c075230403284100c512030298944600194400b014403621745086800d180c1d001d180c0202154182d80 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 684212661 1250 684211411 684211457
    0x503010e280807141c0e18040803060409020d060207110109060e010804060f060915050306071b20130b0f040e030f0a0e03030301030b0613020306090708100819050f010b01 75
    0x10b08801170f00d1150074610007030601a0000d054440200c4c50039459039001c0d20b0440c500e036102040e0b20a8090642c146521490350b036010003040c80d409540d84410701c030155614200c0f041c0c4d52503400181550b45409500d00b01c3d91040925060601003500120007040b094010700840c0c0360040107a54450240d0794585034000034101240305401615540d40d0042107074044c50042100b1000c0803007078041d08034a8401403603e0000010428030802c5038190f141c0030008980d401786200345070003114042000340c440030022003002040c105540d1102e05c919200d1591500781d001586400011102b0510010262041c4002c0c3ca01c20140345ea41d54108001c0c03c40c4081d0010081c1202169525111400100c0f10000c039203107600a0300180d8004001b0301c2008954500340158211a100d500415421801d1110119050700b4019080d81c0038000003000040d44844514002801000183c040364030f494030000c0c40c0b41c0021090b08003036482c3d028500d440041d0040c14042c0c0002d562060359038681d10090641100f000d00303 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 684213911 1250 684212661 684212693
    0x1003110f090a0911090d170d0905070512120705030f031807150207091503081308011109180a0b0402191e020a020904150c0908100b280503010e280807 66
    0x107048006040707413046a18000d000c19134210080049d02030b0440c1001c9141c0130355680201d20800e180a2032060b4900301041c00441c4c0d1041d80070040c1c881e4228a07000d0f080d40a5010f00f202c0420740032080040c1c440b010120824580030100039135182a03102c40c00120b5611044001001681c0244000c11680c4010385c0800050f1800c2c42d403051106071255545070140d0301c0203500b4803d401c40c060f024400c2a07030a01c038032422014965640c03850302140c40003282d48101d442401c0f005544131703c400076a0b1061b0300c0e00144940303030006004640e626400c0070340ea00031007015106207001400b204809a81e83c000350a1103030b002d11040d0001e04c07072600d5030b608201c05440020402c0702d5081c11035040d0707510b5900350701411001d10b949865031500c4e2030a1403440340c503200890005000c601d003070140445c010340f18606a4444140f5030030114046d48801d014500b00002c4e80e501c0250190318050000403041008a100310325440402008440307800b0301c00002c070070522824000383c4610f104118420004030710341d0481d0703030b20 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 684215161 1250 684213911 684213923
    0xe0c0a0306090c031d03040513020d0f0e0d26131406010f050909010c080f06030102070503041503060e0903030106181d0907060314061003110f090a0911090d 69
    0x19440701c00803802d50b5682031a07600443d4841214a601d07003110170a000007500c620004600302403400001603510b5403648404c40d155907000903112501d5100d90485100000160418068207101e00320f9265120f1b040381d040c00020b461000940019038080c03030669040c448501b500305141d2a0009401071202440e070003250009040d200d49410301509210150081c84c6001103905130618100c140101c0200041106110f64903115007100002c0c0c1106035039800ca551b2401c4d4804540d60200461300a12503143c028182e03100100300003820750a0182039001c0100d169500740041661010141300140c000d480b0350029800510040c44002d01c242e4140550301803c0082425090340d40ea44060000c40d84c010a03640b14a06004104c043c40c020072500000b40620700c1c040141070300000b50050010720141c000341c41020180080c0c070540c0e10a8201c564600c0d51500600d42c0c1d0492041040ea040e407020340b846000304000c120000d4084414800e02c490044c00310a8540b80c480100308026501c0c11032001240c070303 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 684216411 1250 684215161 684215171
    0xc1403030714060105042a03090213060b0405030f07180527030309012703051309020406050304030e1c03051c02031504050a090c0302010f0207121a0703060e0c0a03 72
    0x4180501400b0b12078007860005000039505100c140020b4426880000c040c0c0410441c1d4843d4043c503164281d000c0481c5441c001552a40c2c500c0002ea0308406400054001c0e4242034000c5802c0c42e88030002e05c100e940880440714a40c144840090300c1d03207c9446442016103845607a1284070f061031300400c0e84484844403034032100c1d4441400e20500f0b940c0280445d00750f80088100142c40300300344505440008111058511400101d90480d00c2c41140000101000000704254595502400c0c0c048003515001c5002d40d2199211903000340740d0742080724294000703042c8440f00d245604043c40c2d070f014843c90780750207074444411a85080c0c0e0942d0041180e56981c00c1400f40700702c1080354903c003450081602c00e4600c2c400100d000104001c1e031710080c1c1130040b518540200940000c8182d1002002c0302c0c1e081c00c19020390140d04000340d0804005500403e00c0d85e010105000800c0044001842440b803c19440102c9441d000403c80498481c0e000703008a071412a80840d031508022070161498075414900425 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 684217661 1250 684216411 684216413
    0x4150c021c0510060807061407060203070c030f2105060d0507060f2c040b01020a05010501061e18030201030209032a030d050a020a030302090d050d0215090a0c14030307 74
    0xc200300340d8020241ca0380440400c007009424411903201d4032002d40e050020b2810440b0700ca480381418468030042c0210101c001400c0300040c825280c0050304100c08544925182101038003180100200300c00156416896030201c6004007400d84020070a50110b08070980f8880c100c1c0000d1202404403030344141c807001c1e92000560200944406000995203500c07803031041ca20090300d07682144440100da030041d520011030805c02e0a0000000f10000c4030080b6982c1209070050381464040307400038000d9401c3c100085901d503040b103400004134182801000417110f030540d045031040d0385131080b09500f42460b0010005503100390080d2401034002400d80d80320803181c2d8826105d0300c0da040390703298800c03c04601100203450103002c3c030007094001d41401850030744030f444000e44408031008002c1c00d165010034981169114600c00f1501d4a52103801c40d22545581d4001941e161555141d03200d00718403031070001d02540004034002d85100d82c042c3e02007080034208151100d601c060a14441d4141c0b01c02c0c40060 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 684218911 1250 684217661 684217669
    0x51311012d02070810061a0721050901081003050a0f150c02060a0605030303010b040b031302120c10020f030a270b070b010819060216140d030e1204150c02 68
    0x7103081010780003040f0240c606005142400c1e42134020114607032500004002d02c1410040102104079549003060746e0303402500d0032103002802032049818411410401084481e0440010034070030400740c968000581d16841a030325000c1d0f03503000c01000354210041540019a00120740f4803d81e200e414115010600c0c1e41c007190807a58100b04101c0180c0c01403060040c541d64510680e405844254081c0d0310750741c10201051401d20480c4150b0810300400000034050b0f407500843c0440296000700a112402003088801c1d0b0784011011880f44110541c0400003211800055201d0803440484051800c0030f9901d0f4080d9284204242c40b0001054090500c01102c2400341c1524054868094000e0719400c6070308000d4072000f0140c000c52400d40c801502c4109400d00e00d010036990542c0088003690b14105110415510308800c5001846202c0d0b0710103000c141030022880c101c0c01c00700c0f51790401210034105812907440c030742440c02c1e40080104120070f00100304400c80110804446040c444014040303607000c5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 684220161 1250 684218911 684218987
    0x4150207050f161e0645050906030a03020601090c0504050301050903280e06160c0b04051201090f0209070c080403050a20010e0f030a0b1905131101 65
    0x30029040110240040e414600b01e014580112002c2403003100c1c181702010b0900c202038030a20583d4042154050350201d00b0043d5181ea0480c10b00112134103030801a1003801c00d031180c0c081d01e8490b14111000401d0350130000340c90304c85190582e0080800d03034a00322420000340f084032414004c20100300008200c0b62400d00420b800f44416100030746e50f4a00d000215184460700160b046c4108494401d0981c3c6941d01000a10000600711442952000f82009614003c1d00214000301408015400090041c02600c042d10841d001514142400e5001c01c0c1040d00300d17401c1d0314004000c2d50000c1418005030a003400c03c964804150704100303e408446d904c41c6842500a0350080310658482d056100800c981507000384030500039a100c050702e8108000020708040b0000c10014001c0505031205c00003654100581c801484c2c10400c42d0b030880c00e189030141c65405001004607080d034204408510b00070342d49600c0724005504029030181c69243c540044401001c41e0911042c00e106034882107814031004504 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 684221411 1250 684220161 684220183
    0x904090b10030501050f0114010807050c1903020d17040602090a030206030c070c0e0f1306060506180307060513030b0402042a03050c0903030f1b03040e0a0506060304150207050f 78
    0x15481c0d04500d1407600c282554401000004403400010042102400c0b40842040c00b01c0242498081d03666640401c80e003d00030030755804998413620705000802d030031040c0569410340c06942aa007031042e5210090722000d00680c1000001c0803030303000081c0030810703e40c00f600108030002d0500c440680c1d02c1c1c00040183e0420355020360701c0c100001d211030401001c1400740300100820700c80d1345403e1030700c0c041000c00360000034071800f1a0032034003c141e410000340c0e52051002d0040144590788449801140509908171150001d00a03c51010007242d200d0207901515580180303401401031203030071544e540b0703000c400141c0b080707801940b0341c0310040054130501032802c0d0302c0076502c2e00043e0000352113100a0507a02c2c0541140c000301c10400407003c1c1510301000321145402040855035541d40c03c2c40041c0444060f020078400940000300780400c4801c413001d80369015050101003800703a51201010030903140b009541c0208001090204640e06800d01d40203461a203004006840794a507c46039614140503075110 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 684222661 1250 684221411 684221431
    0xe0c1002070f0509011d06180709090608190807110904031e030b030c060a0c0812011d090d0c030c0c0305060108120c0d0c050a060204080303060901090c0903080904090b 74
    0x181480100200c80590004040860359213030316505d4210080d50398000c3c07600b81c0022268031400120301d42c8075000352407800f004200001c3d4440c5090040108012490b000304007190381002e00002d40304c04005200a46071324418016012049a41d0754008560300a80c421218041340c81d1102100c2c0d9140100c46104c3c501940f40c5483c0340f481040c180450300d60020400c4107061900b0201e1045440000340d5200311001500e10310b0780c840d509442035070fa0200108006040b0400014035000750301141043d181280e40e10110b503c442c2d81031403402a041a001c07200740c1c59a81c0041c50103d10070788901c0c0e01c140c1d40f602900701461020400e485001010300190020b03a6540c0c07121004102c920030400081542190048110f130801903122003550b220506c01030381070704200b0407505800500c0410321034521859840302d011503407280d0f81c10b85a91660021184107108144000002582c1350840c0070342071b4801c105d035556000c001e0960b03643c0c180541003040d40355081541d84100e03e00103040309510500036a1521 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 684223911 1250 684222661 684222673
    0x120c0105010311090405060109021b071404061211040903030612050c030f03131406091c02031902010215100906061211120403030e031201030f03080a1505040e0c1002 73
    0x20606121149a40b83e080f4040c2032540d0805c404903001140603419240c2200015a0b00c0b0140c3c48041b44500c009079008c0110302410400040520348000d0300500707541e0558040c000241e5450000425055801000c2c100e8084080c03442d1940c0342903400011580d00c0b90400003801c43c0c883c0c41e00d4003400e840007001c844030f9015241000d25450b0400c02c080f103a405005c000c503d800b030051805801184a4480c4030404d103281c80d028101035131031506031010f5850140000c0103400030020494030700b9455001c00d0b4000d010700c1201c8200b9804005000304a40d8040e0024200d440007419040b40d001c900070104d12500b01a0740002c102240e90340030740c0000740065503442501e10501d030f104c0c108079003c1030000740403c0700422141d0fa54441035007405501a41504002030708403600140103003140f00301840700849200950010041110030824002114007079900d51480b40c1e14002c11100b00c443d12018030300d12070044034080155280c5904802c2d98030320442c0550b004011514080f03030002d001c0044640242c0c1143c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 684225161 1250 684223911 684223913
    0x1020a0f12031a0f0121050c180906010f0c0f081308012412171b011407021e0a020303070506070f1e050306220b040c0507021f02120c01050103 63
    0x16003d02044069010505001048900009411040d03d1007400303061000141124200b030b507240c18070320715201da940c5091025140c400340d10f40c0641d00c5603408007200c40741d000d105000c81c103200620620410041c0c6425401c0d140e540d1f03040d50100718021044030319040440c079250008000c0c4015100003188201100c501c00e00b8041c84600b524907191007211480e180701c042e010303014007241a036400c4400b60304040e00a4241800c00c0307075412000191400201100003402d0380b036031003483c00400301e9540c2d0500821100c00900e644100110050b142d9400582c40340c5011010101c41c00101212070703040004640b00700c42d85501003070640d0001d990550305a000a0108103003180c00c1180703404464040e1a00321707480490a9440a070341c0301403101d00410410044001005922010454070324826000410312040e0f420250382c0e8042d00c6600c005602030760600040c0011240180155160b4a034010420030340d0300a5040320206034010007800c24218400c81c41d0040719114040020400704002d800040703440d46c15 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 684226411 1250 684225161 684225167
    0x80402010332060f0103051005090c0f041206050a0510030204050601030e010e0f0105010602120f1312060504021005160807020f06030106091a0304230309120a020418150b01020a0f12 80
    0x1943c003040f17041c10300304010000948030b52401c03101603840c02caa8010740c41d16101da44014034010007880080b120380024001c0341068100642c82041442030300306001c1940c418210000f516801c3e5501010001079040610041c90140c00180c0c0c0080180b40c0012100003452465082d581c94902d0f000903500480d070184075810f02030050502403eaa0700003032a50a628454414081c81120341014031100d0104a2040e800c800f4640e1000401c66001c1502c00c1c082c0c1030602a000b4503066a04074402c0400e0108400000e0048040c0c8020000c48502408101000d0f11411003503031003c20221307488218950240070795550400034502038507082c0d458618203424441840c6250410150381c5610703c6040c010000017840c400c02503d60b2510503080848114402c09000307165010f00700b0700036441081c1303c40003007080a00090405010340220741c18088400d1480a9411301c000b01400a0032282c0600d00c05141d16105401c008030045041c411035100d0303c0152a206001c01c04c5100840301b80b52202e2014040642c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 684227661 1250 684226411 684226429
    0x8030906010b070302030a0804060b130c0923060c0c1503090105062d0a030c17060a0c0e0108040c18020301181a011b0c0b070c080106030308040201033206 68
    0xc110b008441c606550368030069564043e81f117591003040321040c0082d042125a801c01c0d45102c1c0080d00724903403803c54080300005032084442c100b0014010384000640c0762094500007246100100d03454140b01010001d001079540511100301a600c144101d24103d42c940c180c1006c0741c4095180c0c182e88904100340000e0a440002d010b840c4102000c413052054807500398080c03003d0056650300684058500008100304a00300d42c4041d18504004100007907400c0140e0000306d2520030705083c4c6500d5074a80e180d1104a445407062b1500160b14902c40c601c20354012804035401c2070090310626a41a5520600c4800d04c503150003640c00c45801100403c414092040c5140452946000c14402404030040701d03200f558012044904000700096013000954001c410300740300d1034002100124444c1c40e81c0c02001c081e03004203411103460841000c005150308061184405070b81d4140d0702c51a10740c07601c3e00118094603000410b0480f8020b00d400724400307221580b00329961003c0065030720205140107005c2161043c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 684228911 1250 684227661 684227669
    0x1506050306040f15081e210903010905010e03480307050316032a06051b070b07020c09090706080615070f020a05060a0210110c061305060109021602040903050c0106030803090601 78
    0xa170041801461107803047c80300d000c40c0541034840e82d481e00840d000003800b4200d244800b40c16540b0704100740d583c50b84040028075891624408021440c40382c2020f188081448410941803251005400d9555000034004c800d68510002d049074241556170315282c0c11a4400381c0c42240c000d100340c41c101c04141d0024209401038460003650f5404480000d198100c03051440ea00500c41035603080010f0b411101014228103000d000d07410340c0d846045500d00041404401e07101d00f000b41c40b5000c03080d13400340741c0800064402c2c420800a020710070f00e011400d848201000c1c1040d6840010a01920400d2603404060500c43c3e0051200ea4019400e03801070002c1c04140350030241c05070f04100400c00c003080e0005244e18080c87d101a00049000ca080d13008e0009010741140c6050380d02444042c024104985c64400318258054070956141e40d0760f0340c000d4030803442607a0b001d8141a147d43c10510251925a00a0702034a0180c140a481c3c028081091421201c2075082240e51200100501070000c0c004c029041c058 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 684230161 1250 684228911 684228913
    0x106080907050f0f04050705040f1214010912110c090702060a0f0c020a020105181809010f0219050a09030c0620010212041707050d050a02011506050306040f15081e 72
    0x403d07010000c6001e00c19101e00a600503500c074030220f44090304c60001c07980101411101101000c0c0c07161035002c80050b01640642d03002c0340482e4003000070700301882030300680c95114512a920f801d1020090760425900c0902d40480c3c055000301544640b1082d10551140e10183d02800692806012560407118a00740c540fa22a10b1b018144e0403068000400f04501602401e119444280c1d102c51b9480c007003210444580c10070440c03140146411006c02c111405a101e0100074022a402c104100c0124018800418518501c0c480000c854a00442c01002c04452515000c0e80d96a12500c0f01051a00b00354131110000c0c8005058100440800b04a1f081c051f1055000390b01e400e035108030b00d407c0404041e00180201951301070310307119000480110b031740d01e80d44102035074820b074001d9901616503040058240099400d040170600000241c1c501c000590700d01c0c2d2900c50541e1544000c3c040140601c40100e00005e60300d500503040300001075407240050440b0300003810304040000825451000081c100d110b1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 684231411 1250 684230161 684230179
    0x22030314191b050f0f070c091509110f030402010e030d020c03250e09030c06010b1c150b130801150303020706080114011b0b0a140612060f100509010608090705 70
    0x640f5481001c0310300910094140585030115030044240e10300c1210340007403022000d00b4001075010100d4000186082c014640b00103c655911100c03810b03101c0c1d070500f14403d20010043e0700e0030008420040c2d0303042401850b080c42e045050001082ca004c1c1702032100c1c3c001da88030340c48400b0325113410001c0d64040d40240e9425481c540034081c0d4846509040d000390402580214006140b030f6104105544910030b8040032207109582d01e00101885a0040c045044400300682840d02c142140e809442c0075058610484400c10b071600d0039000c2c070b0b50030081d080740344900f81c0400060010700c2405207900c5d0001c0c0c03400e81003011f4a13528000c0e240c2505a4002d0080c460b09100400400b0301020940424020a00780490446022041210001c04202c0001d29620302c1c41d060000c211a80d500c4101c2c113550200701c540258940310200004d0400c040d40d840c55030782c800070005201c03801800516802102041402c005940c03282c0019802da20709821003c009100c00d000c010014104102a20040c1800d4445001d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 684232661 1250 684231411 684231461
    0x9050d1b1e0905041a04080301060201050601030b0d060c0e0303070b0a050901050105030a290a0504061113120206041d04060501050406030b041410021305090c032203031419 76
    0xc210400e100c0c1102e8980d655001600b03000c2c226218215501110f6095401ea190070718013518075400038011100150f203800c0010314030b1350107803003260401540249803a034188959034400024200041070241004410b4110285a442c20006042ea00c0d2007502004900c0ca010b10384402120710080c103580480e818000100f0180d20041035001c05a904011180b4000829468001500380200c40d100009410107082008542d150b0340042e000f0340c82040c0600c03002100c1e5100040138011060204021080c06104006800141000d00c44051014041e9818180d4880036410304254035004208981c07090f0b03040008011007072007030901403c411038007007100b10b0458942605400005000501481c107a0303038010800c940c2000032000300c0e004500250750711414110400d201c1c01c202c0c0700e014018540400421014002d40d02500d201c1c85100000401c0c48c0680000748244400307242e819004e040c0c0c0c4440c0684070540038200984074000040d40c65051180d98031071402203032104804e10342d1141d80695240 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 684233911 1250 684232661 684232709
    0xc2a1707091406090f13080304030c1b03030e0f0409050102030a06030c08010509030d0c050d0e0705040f0204080c1009030507030602130b03090c0907091706100e010b0904050709050d1b 81
    0x25800070072095004a465490071b03500d03100380300902e202408140d0003004006c10154850b54811805100d0045007041201245e61002031510a000003808250840b010914a003081510301040000081002c1442e01003070715400d00321b9100742c0b403514855031202000e00521110030031180041c00540001c1040c0e01c2c0030b5031815203a000d0bc1180c0000240c40d5030159196034410025500c0c4c10782d202c0400c10807148110310302a07480809100301ca000f68104440b010651801c1d00c240c0301140e010300040c0c540c6124280810840458141810050009030030000c00480d8041140c440594803445005a99101400003101401c1c81075200b002e4140c400c00030011070f424081091301d040f580070b40d200d0401d030302c0b002d2041d00c81d56802c5e00991a00c3c103848424801408001421038000c018014403001450380380c1041019017602402840802a41045481c0303560810f64081a803006051030107000098035800011414580007034142c2d03001c0c100e0340d104c1219503101107451000b42440d2100c5e8107a1207403e0122 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 684235161 1250 684233911 684233929
    0x7050a150c060912031a030a1a060a030c0b03340e2101021b0705092a0703030f150524090d030207090b010c2a1707091406 54
    0x100080109840075502040b1080e041281060391286054641e404034070001070082c06240d61180c01c01620100e00042d40c01c001c034241545d42e4010a018074400a10300841810320b03805840c1c00c2c0c0100700381c000040810380b00b500c1c80019145020400303030b880c1030224140301c018107541c075500798a81c1d00c808600c2a01c00880500d90100c0c0075402d26400d1060540e00049490300040d0200b007100345001640c40103002c045d80100f0000f422848000fa8900300e201e0443c4d0703590354034003d950700402960040342c1c103641d028141300d00c0101c01208444c41c10f01d4050307040b88581c201d01802c9010946440880d00100d103a80540c2a05064002c101050245004000740c05441510781d203980410500404c50b5041001348111a6501c0c0c01a0284190b000070b850000d654003118031482600515000200d04150b1041c032509180a4010741c9500c141d030206030600d0702080c008032005800701c1c41c1c1000000c0c2c07820145100d007200e03107200020740b20840c6016801c405545a4400c29220703800c41e0000c0003280c0d640d154032 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 684236411 1250 684235161 684235199
    0x110111040509060a0302130c110615280f06020607021f09080702060f030f01140d03320a03141012020a0b070f03030f052502030403080309010b0307050a 67
    0x206110b15201c540114043c00041c0d00081c1d00000e00809602d50001c0d641c0041810034059601d0b01c41d00100107148548601084d1044003ca16080c04e003031400c3e1529070015041561035818802e8284040c0815501855040c1c0c4003180b80580d00104000b0150107116076544080c2900140800007281c1c0c841400c040110b02000e842c1035500d00385101448960070941701226030203449183d0b80c01c03420805404541088501e2a404d81414001140080d0751601c0c42540204c0a031415000c01005e0781c0903542e200220040c0d540c1d11030080310501d00d002001130154850000c000c1ca040d0307a40c0300120005e0513640061940300c110007002060060640314040018100c42e240c0703600980d215098400510a0711075503120381c55103807001c140030040c0401c190821038098800d490400c401c3e11a4035841041e154101c51050707440c07001210342c41c001024510b0078403a0b010741e071060340c3c6429213035526441681c10039200100c03140c0d50382900c42c2c101d0401701b004030040c3c04216000f02e20310b4588040c0d9000760b6070b00d4403 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 684237661 1250 684236411 684236419
    0x1b0105030c070c1205010e07080d030f0902041407110109020a0e07050f0a05220323031b03180901180c030b040207080c071a07030e030f070608071101110405 69
    0x2a806a020409598007103a201c81843c140a0781e0b64201d140a0900741d0b410788041d4605000381e4100c20002400400300c52682c000b41c9406506104242c0091803022076034001c032912004100f0043c0c1d1507100e03142d484071007020344440d60300300010000c2070011304a01c02082070b8500110f4201594071030f9510002c039140c0101501c41c0380c3c0c8045003100e160007110b0001d00054404610403480300d800c080a8040a5600303c40312001648401940b124051507110180c00500203980c111600c04455180030081351440b0708a03803804036040a0751068074110f00710080315030070208480c61005860426441c2c890002c07101c10941d5410100c003032103501c500b01003400c0f2640c1d40765502c5003c14007036003100002140c0203000719101d400d14204031165610913444100703a030050907070120f150311808a80e018031022607100c2a04000050390107950041518000c81d50510a2210581540d081008543c001e001c1c03a42d20442d141c2014000a0001e40343c114141c402a41000e01489601504105407400c0720340481e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 684238911 1250 684237661 684237667
    0xc170f01180509011401121202010507090b071406010f091404110d050c0d0b1f0810020a021e0c030f0f0c0904020619030203010f080a080712120213060305091b0105 72
    0x203e40c80c01000221201c1024002c078000004d44107505489035002240210b00010300082800002c81c203d44045590001080345820140100c87e802d1002c1c202c82c92142803d803907440e40b203000300340c81e000c000d9004078a084200b03181070046e1102d070b0080381190300e50b418546480f41426550301c1250b40c081042c49000f1214440c1000134400c01f00890006110013901c0d0a2034080c00d800d0442113581d085074003014043c18850058515000786080400719141580640641d6841140c1c40000e54442d0304c881d42148544c1c1d42401ca00c0210300107035100e2100e20b00040c00600500703020b02d4101511031000340309507013040b20507040740300300401d40040004044840b0030382c03540c0d5407001504c40c1c00794915400f014180c0cbc0d003078050510f806500442c162190084a0560305550b005c80c41d5603020140401445078406010382e0000032142500000b00401c241801d80a004154034544101d030080355011421422004041102e240c051080070341106040000c6c000400d0403038440040000c41c0054941041800 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 684240161 1250 684238911 684238921
    0x6040e19080c120f0a301a0613090605060703050f0d0e03030f010f1202060d0b04062310050315010e0301020904022a0a0c0e07120c170f011805 63
    0x140a1a4200000d242c40b03642c83d202c143e00d4004c05a042079110501145190251400951140e5805181a400042c3d4a2405070041c3c0c60a000340c800b064055038141a008400304043d9140005814041c520345c0c8035000304c40c90803880c9005d40301c0541c000b60040c60200103040c00309600c001240c40040340c0813000c0e40e82d845072a4165005001000582c01c9a01022042c01805400c070282c460482c0c498a480560f03880d22414902081c81411000a40c001420449403240c0f1140b03400042d04c0718401480000d03d955258064000700d8200b03010308010582420094440e0728100e003c088040c0c040b4900541545400030f0f0604195014092060610a05054020240c0d50940403114481c0000d841035407941c0d03022007244ac003a400f000703140d6883c540316804844185400039040707401e26041100d211402e0720304100e403501c0701c0c4042c1480f001c0041040d032050f40707200340740144052409507031340e440d501c040d01861034065804c0240100901c0f042041c01000f588111503040c9840c1e5512a800282d96214 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 684241411 1250 684240161 684240163
    0x15060d020f0706022107020f0d0c050c09090a061803050f090f1201020c1b060910020f0313050123180409060603030503040515010302150c031c0506040e19080c 70
    0x1405000503c01c500000d60000407560303056140c03548074010505900c0d00c0c1c8500409070707110000c0704400c51465000e907420144c800c0c0b01d024070040c010b00940944117070f044d001d40458000c41c1d007100c00c903013503501403e581c07410802280b10b03288200414100c40d5100000940c5d0040c40391107001c1900050780300c007284485c8265182e00b213000a52400404201c80c87c20485100c138081e40201ca4130944e20b0003042d1403418101e804800b12070004800402c8280b40c80c64080400060b0189541c1e41c10840c03107000e445128048080008003660f00b02c0e161081c0c540d0785881c00041218103040b050440c04c555018024074241d50b528141e6003803c03401c00c0001c0c08920748101080c000c05040e40d0191400e810700c8000802d060300a00151300841c0030741c090718010b08100300b556450071000e1100a42144e00803403002c84d10300485028110381c0800d1000d8030301e4408000ca600141d041d1800c0449902e541d10810300042c2e180031f210350100d0700319420185c142c001d20381c1c0300460810a242005000c0e01000a003201008034 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 684242661 1250 684241411 684241417
    0x61c0501020c0610080c01052a0a081c050c2a1f05040201020c09090304060509060c060a0b0307060c1505060414040f02040501050603010806180c031f0515060d020f 72
    0x42500890f180ba180443e0700b41307074010840c4a07041d81802041c0d103c03480f55115400b100d6008411410311621a00100d122482c0b091003596002c03054040c0c410b031003000824600003424103181c02c10184508541400030341d0115940585018280b100401ca15140d06020000307809051240407102c07019018142c014500300000b090781001140b0362029400c0c407400c029030045025030300030703130854481d01c3d07204040c01000d04058424055951040c4002c10003a84100010302c01114041c002905111180c00b10310b150070001d5a03c1c46220b07441e00003095a9040c00c10459000340b80f2450601c01ba0009600c0d05140c400c1c01d0315004c020380c2c0c0c0700d900041c56a11a43c0000d50070f43e0b40644040d407185824103062800e800b41c500200d2141d41460000512881c108043d02e040c0d51501000d00141e440d420324108480310888041e00072030044440007034507594103000703620201040000b200e0810701c04901200c2120001000340d64608140e0594102c10344404007660380c071514401c1d0040c0d46d400c44000000c0140 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 684243911 1250 684242661 684242677
    0x5040308130507050a0806090609070303050f1e0f0a02060603060705091e280b04050a06050706060504021603081003030206130f150f0b01030501030201081314030a2105061c050102 79
    0x17085480c400580c2d0080081c107544141000401d40e102900c0340341d085a1034004074400640010004e0021102c50040341004060f10510390b010892030000e40d10210085420544078000c8280c00400c944008a80511010b07138080c0c3c1c02c5000d401ca41c540250b01418070700480e50f00038058141401243c11201700178150b8100d010b0000c00e000e908902111846d820009444500d070420020320b4000a2000100000d850940350b001300ba40540394144a001c613000d402c522001d444051300c80c1c0c40040c170f0741ca4a200034084581e5008809a0320303c11400c015002c3e00300500407500348250500d0420110350301081464200c41855030740014403206080c40d68250780e09043c007404c080c1c5030304c40d001c0f6a120940e00103e80c0d851850b42c00d1100741e01140040d8201e400912019002c501544000303502c0f4000d464200d0201442401c80300003a0046d500400d00d540c020100c0322010030320f06c0406440004a00e0072007002a8545903092081e450800041090071410301c1ea4840300c2104c1b03801320010480c0039015540f483d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 684245161 1250 684243911 684243919
    0x105071812170c01150f05010f030c0e0409050c01020d0809030301050607051e012003100501141b06070e03074a1609080714010905061602040501090504030813050705 73
    0x30b5100070900c64002c0c6045c99640600750009000010a0a14840e00340100e40b01615503038044d4003240002d07405002c094103102c0c00c211080409101c02da880340b140d600c0c41e9008000a2590403000000a8901380a854043d02401b566408010095000000b00c0741904c9003600d1803170300e400b11481d106180120100c000c004260040d0b001c2c900420301503000036200007001035003040307080034100c03905101c0c0720503141c08a20b00100c9005025a5015100c908007445504102d1460000041e20301440b031000d001e08202035810036002d00c150552c4c04000400c014008401500c2502d00d080b905442c69811a202524182d40d4070702c10700c8400340d56041500d480510b03410300c1602074102540c0005d141104480301071140101201c43d869884c030450a100948541c64000c110203401e11220610086074070010904005805c4000324a9485030005001e403412081412614a059071042005641c016005100810700c5c040c200b10100b903001c038000742c000c0103445a04400b21482d080041c00e03c00c01e90403480d00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 684246411 1250 684245161 684245167
    0x312010803030f0a020a1209080c101505030106050306070f030204030606080a1a01080d080a111611091e13120c02090604050115050c0f060414010507181217 69
    0x140d400c080011440344448440c0e111080d42ea483d141001c034011010107800040d0031401c1d0660342440396001d281d0560181d0760107401c104030712030100d261681c02c0d00700075000ca40341c80c40d10f03451500b82042c0c9405171508038001c1c01031a0800c0080790765040024009001c101d140013045075114081d60495000e5601b05800b440119200c400e0269151803441080300e07001c02c00401e0241c00b0610072019416250300d04041c01502c1c004c0c420840348131002500c265100ea0355110a0402c40031002c004000e42203850103400307400300c800e01b000c5240155050b6107601401d201810440190349603c50102119510300d1444015200c001c201c40300030800010043c15062a405012106500810300d00502c1d48202c9200d070150f6941130500c4103442080c801d44c00342c424040d0203110031500840c041e141c11400401200e02014251400c86d1505200b958180c400c035891034030410701108280510b580c060b01600b841c0c9010001c427404032007055168410b0070851075138038100344104600402c403180070035014880345803 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 684247661 1250 684246411 684246419
    0x50901030f081b1506030607210903210605030f0303011d040302010b0406083030070513092d020f040e06120a1203051e042001021204090b0102031201 66
    0x18603130741552124030034410180059407d51142821a5440d00c1c00941c809000841e0032064000e800c0d80b1904800b070181c8410040c40010402542020039841e410300460400d15140170315040c400000001071160304104014000445040201034a05041d45903500300c2c2d940c1d600b4100d00600749081525401030a001000400410020b150106540c44481320000c2c036000d000c1c000070031080103003c40e4644000b4400c482194100d00414088540120b00110b0b41c41c0b911510507109060854000d8086000811b5582405100141250183c02c0c99001000001b100d40c80112406c9040800041d262100d10101e140b940c1d0580c050f10301c03100844c2140f47e1129152000032002001c1250494050940700d820b01d10b80110004141030107030780100c041407812034540401c4000d00b20092004c0e54800342d1b400703c051000c58815060348918012040340e8070a50344001c091000d00f120195090443d0301203000e0440d803800c0b5208980c216070703528900045a114060050341140901400c00c1a203c6404000003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 684248911 1250 684247661 684247693
    0x905151806040b1c0b0307050109030b070c0203191e21020313080a0623040618021017100f230d080d0b03030a080f070c12020304060207050901030f081b 67
    0x8060b4413003180144120760001c000c1c9a0360f254036108103800500f00000420100301107003080b6420901038580a80c400a243c0c0100303140a000584202e0001d400006140500140701c40d40303228041c00d001e1258100c40c564803050002e2045030210b50403408204800c20f1058001c0040b69143d00044114001c082d070b40e40009511004020400c5d200c0d141040bc990428140c000c172800c035520304208220545403642d440d004001c08800340d0240c0300c0c026841014001d0380e140100d40303a0048465842081c0d404400441036820000504080c1400611440a1150706120700e61032040c1c44800e2030000225445440d0a40c00e03803800c41c3d2050b00324610480420034404500c0c0240b05101811000b480554251001d00d540c0c3d10401510b000081d05070004101c41c10015a50150030800e140b4240310ba00601c1c0d22030754890100c00314131501680c80058100a40707034041c0702c0540101802c41d6490f009624645a60315410441d40000700b4500e00020040c2290380e550b00d11030303c9500104101c80700041022070034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 684250161 1250 684248911 684248947
    0x191409010b0f03010905070b070602040515030403031415010f02280203210f0703030f150503120408100c09151205060303190f0203040306050a020301060905151806040b 74
    0x1060040102ca04040c4042c241401610740c1c850f07001000f0b1005a19040107a8016040942c0c225112902040001800c0c1c2d110380d4495586845000d05e1503680c1040c0c0344c0601103c840707915282c0300018117000c1100c00d40c40c00007914000c0200f0b08000ba44c03d486040300300e0030702400c1d02c15401880101c1401c016445407000c0003800c03442c402d4044500030001d0000701480d5510080a006100e542081002c4c548000d410241c140306120f17003008900d1480180301e003c03c1c4ea20845403141c180521350700411031480c0802520a0341c01500403580d1a0a08200c211a101c3c00100d030501806501e9514aa0a0300d100b0b4815070001c10300341180d00108c01c420314004000c0001e005958209a0070300f000311f08140340100881d08030003072030490f02d040311040b00c0003502c034980c141c00a4000c2d40024040040400d29502075075200301002e030170050f940c5d0f040800280001c0d119400481c011207a021604014440c5001200d41c040c0054101c07034455003940e4006000c1e48982e4014824000d00450007003501c500400030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 684251411 1250 684250161 684250181
    0x601030506090607080f0114040204080f0105060f0402042102031e0c01120528180807140601051507170a0f1103031017010b0d08130605070b19140901 66
    0xb0f950040e101c129007101c0c401030075a2080490344042004010035625120380d0300d410940a031025080542c2c9140050400c00c58190b40c1d642070351280104051850083c4140c50080400c58085040c6814181808400241e00000b2102c500340301003010103564080019141b40c44803142100100090300890503240d4030b941d04154085510920a244132a41c0e50068034480d003c2c0100f59600854410144149503506461088007240d6400000c3c82c417042c10b62134030300014040c1c1c3d20b45a03201818505100030000403104c2e058641c1090005000c0d1b6030702d150b010b00300c142580000b00d807070700c0c0c040c02c000100c030688200800112000045e4410342e25080340c01820035408984450021101640596880384011107001c000c9041c1000180207034191907140d0348010079007500015854005102180180c280c031a03040d50041070200300f00098030442d12520001c0d21385071402d1803c1000c650703200b01f0081b0340134101d40020b21001184421120f40d950214001c2038903d0101c4c6030508006242034000c04c09a08 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 684252661 1250 684251411 684251413
    0x3090e0a23100807060203040501080c0a0e0d1e0b180706120f090c0e010e0106050a050a1b02090103260c0a1103030417010b0a060201090b070e12060103050609 70
    0x800200d240c0e629214000e00380400003450040007850040d06541c410000709114982c100b0709901240840c01000343c1405050250011507886041a001420000008280e4a03024004204181ea4140c0c004a83c6051003402d8075251045d0016107004480c0b00650070f4409001d4480000e01002d01a0000105000394014420700421144002c591034848a6500076240410703d600034194400d9500c3d401114005844000040c0c9840d952b602d101092880b9880403002c0c010b40d0303005001c03000c450081b0314014000d1303042c480e1625030f003444003400b02d0140000c480d0600c00c1aa844507031640100520424003039000b00740d5402c940e140e1518001c160125443c81307140705041d007441420714240108403007424907610010000d030412075035207401c01c0c45282d10a54050106001c0000c055000031080c0c055a5030707590000c0303881d440305424807101ca806030340f04608583c142800c01005c21000d514081e0804c1147c5445c075016844907001c9035a07006c400ca903840007881040000001d000b00811081e010703114002c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 684253911 1250 684252661 684252689
    0x190203091f0e0105030c090a120201030605011704170f130f15090512010e0303040f050c1519090503100f0b010e0907030207022209020f030f030d020309070e040309 72
    0x404074100402058a403500842c207180c004510a41c0500042e550210710b014002c0d141140b01404a200ca44443e8410f00500c0543c0c004d030000c6603098021400039050170b180285030351001ca5007600356800007410160000c9480d66076103482402d51011500349100307042c0c03000d0380c8032420065000161210f110b440d029038440c1c0b0001c5282c2c68492500085002c2c50350b5007441d2141803808000718007000080d414410341d614002503901000074000303544102c0c001ccc001c2000d0f20940341800d82c14034040040c3c1610a40850054038031204440054510008048800c5400b205103000250303110286600840d0307141c80742e0b88802d181c0310b0081e04800080911035000384840d10181c0010b6401d0724640400711313403000c034a000088409110f540a07040140c00280200881e00c00b00003a0f4550441c140218540903031117000ca402541403010b00c0003200201940100039441907a02002d841303000c0d0714016440340b5000004170750680010010700c00a0f007401d00d800b100f281050715002e09401040e215001a401005c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 684255161 1250 684253911 684253939
    0xd0206090c0102030406030b06071e0c050108010b030a0b0d0b01120c0504060803070318030c1401030515031e0c04050c1b01090302060109021b0d0f020c06091507050319020309 77
    0x30a680c0c90704901030700258107241c2010002d034043c10030545400c1e0000003d00101c4042542c8010798140c000c04090580010400c07070403d540d1a02c130580225051003803403001040350a2908003200da0000381060002448a03800e40002c11340310071240f026246640d0b0f040003288103140d000c003691046100360300d10561240c0e21024003007070760b040e2307c14810117420500c11003011a024809501e2407510140825804a460b51360f41106100c10f03400069a030031528a6440b42960540700e46500146580f004c2080c5000080000f940c540700b4130602c3c0c003541401e40b50720f500792204120b581447c4e20000d00078407042c6084600f00c07041e03400201030003084802c505005d81452006105442d0840e4242c0d01500680e800c0940c0c11010358044070b0075040d050b914004503a12100d050000c0e14030341203680d03070f01c1101c10446a4028a0041c4c10400c00b4480c441c204000c0e0303662f07501c442d09400e2a805200c072541c3c0794241400c005045000351000f03040b643c2c4d02003001800701540400201040501100c01502c0d110307a1b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 684256411 1250 684255161 684255163
    0x11b0f0906080408070206072402092805040e0114130b060105030103050723060a03090501060506160f03050c0706031b21090c08150a0f1806050402060d05090d020609 73
    0x1503c000d80980002c00c02c6201500305640282030040c041c480d200c0400c440040c4010141c208051034504066000c07612062a250180c000800f204500e0b0302d40c002c50b5030345528020707a5606485410300c9281d07511080e8071505029000b40c01c1d01075401240f40f86602c0c0800d20003103404011802203491020481c0001c80d5503010744152410390f500130004000302410899032140403086481c060102d0110490a2030141e65094014100000d8555000c0b8151a841c5011420b6401d15004a4401c000034821000d9845d07002e901d644456400030b0b21140d1118650038142c80b24418034441d184036000d052004514070b0340540182e483e0f45a04844288102c0c1007080c11688120445403c1a00c034544c3d92010320081c4140c2c0081c401d59004256819901d90740b0000c4600e0145a02c03030b041c844500044c208406949248100c0c160fa000d05031081c440c40c0c02483e080c5030001000705009116507555000b2030155260001a6911f500c915641003040d8108843c9450780c41d019446a80018400d050000c1c4402c08 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 684257661 1250 684256411 684256427
    0x20417010f06060503070c0c030b01180b0f0d060f06361103070e1203040f061e020616030e0d0903120e090606090d1704050a092c011b0f0906 62
    0xe44c0d0760030708540311044222410b688220007902d11801c41d0380b010010801c0d040145000b41000443c08801c96039509030401550602d0300303024495000c00c503c0040903203500e0961b051982d84442c1c0028204d0010517400020321894100351844101c1c01d003c000d14820084e0030f080d52407540011001c42d59030b042d007682c00344c0d0400300f41a85400c9040c408540640d014546203090020020008051f40c04464002c518542081d4001e02d11002c18400c00c0081d550400540505407404444200c10200301c02d1010b55905000f400d01c54140d50182c460740b11140c400cac2c0c003801500c1c2c80701040e10f80b0a1030001004140d0b040c240010f58803000990b03600c2d0401401118140f4a1510142c403c5c041991100100109a004482c0c09034002c2100c030040e03000030f0312003003544650360031036200540c40b075003840c0c14440a41d8164105858151411085041c143c1101801d01f80001c1d00c0f1081e42c0080000d00015801b606108607490481d425030142204841e812254200361640340d1f40c2d607001650354645085034048 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 684258911 1250 684257661 684257669
    0x4603080c040605180607020409051e0c061b03070c0303020106030c05040920010c050312011508010602060a1a03030711190308121005090106170f0708160e04020417010f06 75
    0x341040002901c0741844018140130400300500f81c6081c10101e401041c196000ba8000700c540350442910390788020819074400c08490905801440c8070b142d540d0201e502c520403140905840e200d241e00d4103c43c04003c10455040643c026030010780c4a56918007e40600440e000840d00740e0100080468507003801c0c81100380d070030f41042c84640d10100c2007021010084400300414100450703010711b0750124000700000d007403000038030f5400d00207580f501c680e00b482e4007640800d0301c0801081000401201d80d001178400e8002c044105c0c0002c450140d0b01c2c2600c0100d43d07000040d9018000400e00805012201201c519200d0f0142c0e615006081c290101c0408a01035003c0140121000d100011094130b284403819800404803d09052268550f00025811102680f0980c00200b8600d008031f00c3d040d04d0103150380c20601d14004081541010301c006408540300800b0a68a0410b40d4048900903200f10b100180161000c0c00441d40c1d241c80741d49020015481d901103814542c24601c540c0b403180b00d039114035000c076 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 684260161 1250 684258911 684258917
    0x3020a020d081005180a050a0b0a1a040329010b0f041a0c0316030e090609070509011e030e1203010b041205010204031a040b090f4603080c0406 63
    0x41001c100d09075001d040207045511100c050a50118280e1682c031800002030260006413411441c120300032106480000f054080001c2c10441c40b40541e444451000341524000d9450480c0440c418500e29140d0103161320107400800341803a100040c0c0f01f10070406400c05c4c8428404003041c1c0c0c07100384801c002c0c1316190f04061654000c100420100d05556288040115090070152412009109003890740c0c1005103402010420021345904241e00300ca9804d8218a00380d5071000140f60403000910410380c000c0c03070300040c07003000540000355030710440ea403401c3c164003240c407191503845803d4020001e042699405841e441070030010720201003d0000d0340d04841466040e04e24190a00750f40d0038004820b00c104440640d002e0201000107101c0314001d40b81c100300c540e180242c40ca4141010001d0042c05428190150000030144128100c00701e140406983c2000005400e00c050702c408106103452600ca500c010030500366004540051015a42e441e54000d6480e001c1e1622201c21440322442913210346004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 684261411 1250 684260161 684260173
    0xf0c0112020d0207080d0c170f010612020702092706040b07050705150108011a040e070302011b02040e07030605181009030306080105040b01030b01061403061306080703031e03020a02 80
    0x10025a600144140e40042d0005810150303d5a542c44154001d01c1c401c2e1209500c0300d0380d10920f00da01c030f02000c11980c1c0e00081e0180c80c1c00c04194824042806000c0c4504000050705c2c0100c410340c10790112150a94050100b030582d25103510b01400e020100c01c00b540ba48004040c0c100c0345040001a20340c00b403030304005002131039101d0071020f0303803554002c44080f9014091800e00803050100e410019009144d9140007159610b00f109641010300764000c1100d0aca0b524000340e6080441c03002030088c00b520760a0070088095956010044400c0c80103c000030740c0142045880702c1209400f05043c0120791203640284a6a00c66800c022000090000100c00300d611030794000c01c1c0d0044582064402c60300901380002c5141d19001d6041c00d4403011a0103548980f46600100100300c840c80990b8010000c510307001c5807200c0c14080224480c80040c1581b4031900f03034440c004406400755071068005200f01412240b049a6901d0050070140c640140840c0108490588101c460302900848040030308070303406000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 684262661 1250 684261411 684261437
    0x1c060f0618140a12080a0216060509130b100e1207080607080a061802090a1a0d02210712060e01050f0904031e020f0610031716061d0f0c01 61
    0x4900210b40c200035a005880210020b04500b99980d082d44440c01481c0c41d80c1c2d6020780d0b19002c1d141c03180c0e61444415001456100304101640b00040e2102114100c821020722403805410402a0568461080c0c2c840c50094075550580e070080c4130003484001c1a00d41c802c17180d10f60201c2c1503c500140c41024040d40000b8005580345102d001201d5200000890004005440e2165041d005105c507031495001c40e40002c40b100607240005585000300f1410406000080711601c900b01c650207000715450140b600440c4141664100c000904081005201c814000c6d10301030800a001c0340000301c04003413041c175200001c12045054000d40341a502e0241c44528560484000d001c8500f0700104245d041050070580c2ca10b510704e1000e082d0b03071400620340c001e154500307030182c0c0d8070304292015180c1d160b260300d15403080001800301d00f85003416808901c0c41548514001407008201d032814078005201da882c008a12858940c0071000044507103446044071484820b0280e25039803404031040e060701140b00c260a0744 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 684263911 1250 684262661 684262679
    0xb03010e09120316080a0c02031e09030607080417120103030c1a27070515090a180213141f02280506091605040b04021c060f0618 57
    0x1508031054038202c0c0c803038408904403241c080e00155800c0c1d4222001c0031180c144e603a4414945600300c012100e04100f80404c1000180d40ca03c04c1403105100c8007400200c03807034a000682d0589150740340160a885861825400040005208550407504000c05c0c14408501520380e00680315002d2404842101590841c4c8041d5121070040300112000e015210000070082210036200c0c0c050320380e41369408030000c0c070340b0000040c10090908420056002074001c110380d41d240030042010513890410319541e45440310100703200c04110b8102d0202413148906515884500703030300404864920b510040d0350281c44440905020b090041075a50001c10301132090074400b00704250011032521401210260444540300e0490000703441515200704000e4a0a41d050200c148000d59208501d14050328025140c1c82d14180004494020640610b9403007803141b10607101c42d8101d03000350b0710340e02c403c20001d2070918400c0081d014501401c0c0c48030182d10b82c0084c400c0e00841e03820100ba9000c207682c12a090605040c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 684265161 1250 684263911 684263939
    0x50a150803340303050a1a0306040206030c070816021503010b030a0e1c0203030406060909080304031103040909110a35100e0706021203010501080103120909020d060f050405010b0301 80
    0x8600140000c9804101c40d0038000b08210191081c0c902080c0c40c80c140306008111101d9440c1070700410480d4502c440181e60205203954001d50488070281c0f652107000d00c210781d90040050041030000001101c10030780f113407944807002032407007102c401e100040b9814060348903000c01e115104e0104001e0003c50305006032900700c4101d914104045a80640e100c03d1001090840c1c0c00707464026070400000d1205100d414041d4001400702c1d020203114104640d60750100c1840000c00140030091441001e03503001c4000e0003114010f000a541c240a0301c400c90900b22864420321010601c142c0c180f21000421620090204100036a05042456450098000b0804001c1b0b0b4034061940d81c00740d45e40d00c13841c090052203924038000665008000107400c05601a24240f058040b0714001003003423004012680c1d004002314192a8045520010010b510005641414958012000c1c090020464142c09100c0d6030000003200c19100200703150b160703500c040c8401c9410a006102c1b80010030001481144581800 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 684266411 1250 684265161 684265207
    0x604150c14070902070c120b010620070308090102060a0509060a02160c060504030b0a18021002011d01330b03101d010509150d02010e120709050a150803 67
    0x425946401014029410b0800d20341191514550124101c418000c1804005015200030503000c51646100e4440340304c0300d241440360104105034000ca04802011503d103850900c40b0798000c030f480d05500ea00d0000140c0d003007160030900511171200000c66040450103414010b46207403014017076588078001c2c0d110180d8808401083c151408034110070000341d07110b41c25002800c82c2d40d1165261411840c1240040001400301e450103410551312a41890003641000c80450341140c1040b05c2320f40d00319099000d046403d4400c4100b6220002c0141c0d100c071306400030280365002c58a201c855401c0000050034a600c00280c030315000380324890900c05c10039100019074002c2c4031900a180d02c0c650b0707070111712ba0600c00003e07540c0120540d44d0040080d03050415041c0c0c4c0043c48141034a19070700b4480c002c1100300d1074003007010f8108102880814104d072038406685480380c1500080d60a102e4490103c0e0015100c152010404d0625200000b00040c0c001c50000b002d031000307003024614040c810010001c0d03400c0d41c020 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 684267661 1250 684266411 684266423
    0xb06090f0f0a180207020a051504060c15050405011401090621050106170a0c05040b01120b0a12111801030309171e060928031b082101050604150c 64
    0x400824504040d050000f00041c20500140ea00c1000344140a807010442e40320701d02540c0c2000010750401030720401e4605584440c94242d0103011581002018042041c6804144500d803c040c0005d105041d001340341004031000d05c80c0d030103999030030b01081207552038031640100070488010a50030050f08010300c10220300a50000c5078290300c0d0302d12101520903110305007a90381d203c5060002000451000c82d00204412982004030408c524000b815108200756841410f55944007330007066941c6802c00d00c058015008100d060720494540700311201010b425540c41a545600d0700e14640d140822810f05036503060b540c0210b1a071404031103a11900b080341d8000a24040e804440601da25062030940042a140004018900b018040c0909110680000e1509a00e60b00354503520400c5400381c61048640c14640804144c041c0725600019809050700105921000504019802d1420042070000c0103042041c0b40345991307990400403d84103502c10800c55110041c5400d01c07003405518a00c50140c000c03c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 684268911 1250 684267661 684267679
    0x60e06011d0a030c0b0d06090203010e040809120d050c011107030522080303041514010b1e1e13090e0c100e04050c0a0f090b03040f1a010602060103060b06090f0f 71
    0x15403990040d085980118141c54000703e1b01500080b4980104401400e05079811803071035042ca014041c07804001400548000c10000e03088980b5151041d05050b07807413080d01990751040340e05000a15039440346105c0e17a095800c0c0030005a10010f16001c94507104da064644a1900a00740c25800c44804554550868103101c05000924184140000c6100c0d038400e040365014005034440440855462180a0310542d8015005200855064080350407002c4440011400001042e220412905c1240c40c800c601c1c1003c3e0040c0446c00a600015000c0518080f1800703900e192074180101c00c0760300105000700b031130340400b084c0c0d0040d0400300e540c07108084091820b0742c03986210324003180030349d2000c0d01c2d41025480c000451540d0140c1c4aa09140445401d2a2100d0a9403500c2400740302804003800103020301114001100400c070401070904151480044489600c0da540c3c40083c0d01c54000b480207485072801d03c0781c0100540b070010300712161843c00406414110302c4040030b00118014400b0841c2d0010038035 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 684270161 1250 684268911 684268913
    0x30605010912062d021b011a01050c030405060d09050f0a03080604090c03060507020703030f1701180b0a080303011e050d121202121e1e0405070522060e06011d0a03 72
    0x40070007030130b4000300210007603510240c280c80d078166040c0c800c1840e042c992520042c1283c09205203070000c0340e501c092a10a40383d8110384e0300d0504521a43e40a2a40040002000d08140600f1740060505500030707402d940045251000c0903484800424004000842080000e2600e00c0c240e4494814035004403099904240c5a60b84d400456005a41d2500543d009140420070598801c418031204071103445d0040c1c007404081a041e8a102c2e041c054041c160b00d0310403e061300103906900c541d04449005101100c6150764049940c3c41341c0c420f014021a10074640e80b0031503d103540d122440210b801c060300c05610400070351500c0040da012054158100000a0700e03210040700c85001034094466210300390700032424010b00d10740d448244910502041c40301c40c401c00030340404d0854203ca00080120508100759224078100303017040255000f40c1e40c1304202007100402110310340c0b000151500c1c45202041b05030f4032100043e282da002152010300141c880e40000009044490004085450103003125040d141c413 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 684271411 1250 684270161 684270221
    0x30f0e0406090905060709050121090f080a030e03180609040902040501080f060f0f130c030f030f2303150a030501111c020702031903020f1c03060501091206 69
    0x3603074460b0044640702c0c0683d1007485400d10586800000909052507a286003900207051002c02c80761069a40410038080c516003c1140c20091641340d1258035103140d000e0f42c0c9001040ca4002c21a80c40c0000c3c50114100f200d08800030454512029100c404244040302504010b803035400f1100c4c2c0d580203034480c10082c00589903802014003801f200300140031940018008103185c050014000c1442c85904410b210f807001034119101e8000b403100031040c0500b005410702c03a20504541d80300800342c09881d01c46070b050561001d900b00c0c0d40919076a6005090904201030020000c14400a10302c00d902000483d1401e0105008003540c040c0c0a40031103440c1d41c0ea41c4409003102c60803c044403c0a200050301d8105290b0048030001d0121049421410111700d40c004c640d54240301521548001c40e144251814140200f000c040c030065943c00316401485483d003100391403007040d1a013034042400c21001040960254205c802658207000c011440c1e109039448a0300035282440c0c200c02245c1c0c0c0304600d44414a4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 684272661 1250 684271411 684271421
    0x909050c12150301151404090b06040e120c030307080c0c1c021608010515010c0f0f151a1504210c12050c0120030d0e0c0307120b0c090607030f0e04 65
    0x290740c01c03e0340d1841e4601b240b005490200c40f074105210340e141c100ca04c0300082c035038511660400f800f65000549184030140040c64550046e680381110403001c9001800004000021071285001342d441c000700351110000380da0140520850a14070343c110a8109050100c01c9800ca080c5450300d104980500b41020101c425548007070b0070100aa0f5114010800a004901c10006001400f13203001640d004540d192200102840d2200811000c00440a40107000003107010b0b402c0e0281c081010407610003d0901d07042e004407038004d0b035030080750003003050809011080103540031180b40303608400085101c5074290f00005400f000856554601d000b021402d448038040c40003655100d60000c0969416030000940f500720b414407400036008400000c0c1c403200002005a42e0000c0320742c440484e1041c0c04030640c60809000c3c4c50b9a03901841002000580c0b40ca90803c0c185000b0b01030208400c05848a034542c0205100300340e00c19401c84010006030000038817490401c101c40300c1d40d1902448e0544000006001d0710 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 684273911 1250 684272661 684272681
    0x41e09020918060127080607090602100504060b1206040c08030a0507140a06110d0e030412020402281d030d020c01050c01020f1b1902210709020309010c0909050c12150301 75
    0x31440c1000340301b410000c20965130030140c6070500a040d1444d180c002551100000740e28000b554540e0081010041241c0003d5403c0100425901803004000031045d910481100c007580e500400c44400110b100d00131088a0901380d155a81507d80191506e0391351544031169164802131240b100d40b0804240030384140800e91070a02481a03070f5200b10300744001500d4609003160015041000100050340410450718903556040e02d01603146d00d4a1420401e50540040400c840496074a00a540903070340480d401c0811080030800c0d40510b0344010602d03544181c00c0e801c01c00507a00426041c0d20540c0580d0181c0f56200e03020300094903040c0f5100009113076401491001c1201080421030a42c080018480e24525806881d1a01488005a00029038881d05840c04041800c40c5001103012040e050140002a15901d0002d40d40c0c1c1c2810442203000b4000148484000f540019000c5405c2919000d068002c920742c034501400c01c00000c0280e142c8070000740c40150042c031400d01103078160720b0070b0080183c00d03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 684275161 1250 684273911 684273977
    0x30d020c030405150c0601090c020c22060605040302100c2103050414062a04090203101715070f05071e0309080c0102060103060e12041e090209180601 66
    0x5610f0203090003489203410003074081086040c032401c54403440c0000d9281c1115640000403070100c4141005034203240c403032241941c1040c604042441030b043c00742009507451107404000c110f50355135040c04030303000e010b9030100960204048800007100c40c4038900c0d40a40a000d0410007038060003c80e02503241d0702140d424103010039206c408003c2031040c08000c8118041c40380c0040c20f001d19105501c80000f03144e44206501041500340f0380c061a104d640291405060404800c40d03490038001480c60228513580b181030340d00c0500c0f4420704090b00c00441d0700c01c0944062404800340b82c1b1070308016190b000b1170040240400c0f8003800303420080703041a5410b10510795250065034011140b0f00707004106140d0343d0050f051550007001c0400d01a64001011030447c3d40081d0002407070445000c030b031810000700d1021002c00400100b0041a000d0280252001c07818481042c40c91340da954915a0b4243c0c05002c203c168880028100b1070164200b0b060303401d500035414540b0070010080c0b010010fa41d103d00041da00e90b0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 684276411 1250 684275161 684275167
    0x70b010807090b0315070e060d02030108010f0c1d010c0c06050c01050c2703070f0b030a060f0608060d240c020736060503010504110102061b090d0203030d020c03 71
    0xc4030500040000c1c00c140c14080c8032054090f00403903a5042e54401d0043c12458800002d071030188030b143c0c101c201e0400205040d0752030304032240e0000690420300407142c0651800c01f203101042a039100303140449803680c0716521503800c114000083c44203d0800c05060140d80e04c03545001607800759444020300107a440f15505c1c2c0340c04400c12821240000d110303040155081240b602d0765040142c21aa10a0700e18880310b101c1142c45001c2420144113510001c410410b14002050740350784500690f201d08841c1c1d6081148690b14100300480700c0407403040d00042599074022454504040070514105030042031426407220316200e4200b14039440b0703441020095078a401460300b01c3d038180107000045c285003031480d41001b05a0207440302c0300c0d885140000c450f031618038480b002c003803c2d800150041c10020001c100f2464136003008491034500d40411801401080002030303100031011b85c0780a540d0310743d020080c144903642c0e00f84025249000b5040c5d90511090000380e40c41c03240c5000403c4640307500406592 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 684277661 1250 684276411 684276419
    0x40204030b0a0c081506070312050f0115080103170f070c090614060708090603040c080d050d050c031521010504083a02090d0b040302150c0405030a020f0a0b070b01 72
    0x111510b2680300410400d02c6424170811110380c5400d0650303c2002c0360000c1c0c0c0d035801c80ca401c0c0d03044803507244c0c100c02036400e15003045407000d240d001c4941215807105c3c0b40814907803005001c8461580900006002551041d095103092111030090008601c02d907951a1400b00b450b00c1e001c8800c10b5552041440c030f03490354070921014200ea00c00407154039040c4c41c2079041040ca0b640d0258607020b2000000e018103400700000741417159039940301004214a800343e070f1406400042c014441c3c3d001412001109061a0109a8800c802c1c01203900c00d5a02c114440c80110b00c14040200408621844000805881c0c00d6800401c800b031050b40d0003184918181c0e80c0e10408494100068850398488050075480410540f030200424440c5004046010390016599020180010800510940d024102c0c40554040204050300041e294403403461400b2910341e0b5a0722091310703003c1c0384603c0c011250103400c00c0480308018146040450ba0904008140e0f60040d82c84d82001d000c0c03034022250507074002540e480108 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 684278911 1250 684277661 684277681
    0x506060112060b1c02040e090a020f10020604030c020a0b040b1c0207030801030311010f0c030b0f240c0c062b060f0312030608033601210b040204030b 66
    0x3540356100340d1041c00000c0c6008101c140700d025040c115594810042518040100554106c030b005d8500005806907504050141980d1070410400490194501e5800300343c0380e1074001d20344401d42915900904495407240d17000c440e4030050090498001c0c0d001000882d007000d0170701c080d00c050140c9000454403000c542003103a0262110044541c100e42c410401000425070140c4180d056070f8041c00e03e011a07100039500a8010400340018400017440d2891400c0842d905130013054400c041241d4090040ca18201080700c084417042040d0302054605603403d440c07441d01805002e0b624065004d07102c00e5115400415030b154484e070700822161141000b04071100c0c1100c4041e41d441e14100d2410401241401560011154280030103001d0b071180142d00c400f890701ca034002c1c074084c110380c13010b0b00c0c0c8941c1035403100f40300703840d1001e0381c195849848405800d2480040105c2240c000701651074640c0c801d22460b90007005802400341d0800c240d02c82c0300c00040c035110790004000031031140c0c1030074510f0f1501d21000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 684280161 1250 684278911 684278927
    0x423011e0c18080c15120c0417060106020303160908060403050721120b04020910050408071202060a0813050604051006080c030a08090a0e0108070501020f03120112110d05060601 78
    0x1607850120340c407401d111a410010b2052104181900e45c03924040300d600c4840c0640c019003005582d0041444208044400103074090001c5808107210301c56010b214214140c1c940c0c60900561005920900026003904000d11391202c0c01031003070408242c9181c80e4404a824840211019008503400066800c00c001c0d001040146480100c641c0406044a02a005091114030919010407981300c4000c503c141d51960304171806140300030309103254a0301d103031030140203500035108800103402003242c00207260041b445400d5400394020656443c1281100c1c05035030000015010800f03540d080e4100310002030f020040d43e40154000c00047c0b40c0c031140416450140c03411a080603c040d0809000394255850002e01a20304ca035001080702e1311451440c0105190071766a6025200e049440ca0001520f000701180b900d056036000c1c0c0c25100c99040e54106143d580c4198041c825003076600000402400850b42c05000740a03101e0342251650040d140300044c0d0112001074103680300d400403020301811390703046955 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 684281411 1250 684280161 684280187
    0x23070e030307050c18240a090510051c080904240303020303091624030e0a03050c0c03060615031005120c1f0c0303020903100e060f0703050423011e0c 66
    0x8006014541800c5184290300054551b400010801d1030b8040b482c1da03140740c900c0c081c2a00c603800300001c0c6003843c41c40e4526413680c403455008140c0c03020740c152500c4030545070002031500050f0300c3e450a40300070207000003001c421f1201500810144500208450301c0440c0308001c502a5004503101d05000300d036182007648801d695035803902248030820000710554401b000642d400c1c00d03401040c2515010030303000b40050204410b5180203244100302090340101c06444440341d00012101c042c0e8040c03003450368401d8161203256200d03141c814041c441003020342c002c0d548101000c181c01e42003990741d4081505c0d5090b103d4180b00d15007008001c0072450a2146140c28140c001c209890341c4072486c1c00c3d026000c144804005010990000b914044070340741003050400030014400100180090102d0664a824040d0340c2c404607100c030480410141c0c0d2007030098038042c903000304c4801c00396200300ea0424042014a04c1c0442c0554840c122000c000c003030b1092141d204111810007081031940c540e0028107075010001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 684282661 1250 684281411 684281449
    0x2603040f03110301091101080901060503070b1218210c0613061a10032408030703114b2416030504050a0b01090c080a23070e030307050c 60
    0x3031541c085146c00189040542c070a0920031200e4460300310a84c0900308036003041d03402d0320030000c002590181032030040695900c0c0503282000c3c1d0b1119503084a10b604104c081c0b407459841590b03200941c440b10045803e0000d81400204d140c095210106814040200d03059280c10032050300710400d00500e8080c0c0c9100c0c0304010204119940c0c0c0200045002c281c542035001007556401102020008044014810b021059400310130542d4a0103480c0e500da0010f1811000541c01240b444d40d1100001a140c403075a2000e8081400c03e40102c12980405080c0031200340210304601c101d45039000c801140340441e80c08500036041c43da11510300921074055101c0c03070505c490b02400030498109100c600b94040b181e44d618000c21144c4440c24000c3ca03106070340c540505901d40c84000000c0600f81a404030b0406046500c550000343e840400341b0084500e00c003006c901141034018945400f440a036203040d4444442e0406a0f01490809c01107851a00302c9881150705a00c025406012454001290542469400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 684283911 1250 684282661 684282671
    0x607032307231309020901020f0a030c15060b13050f1801030204020304030c1e060501060c0302030a03050606160b06090a0905070b1606091109010503162603040f03110301 75
    0x20303070003400c03101401d03228100d031900c182c14a0310810101c0100da581d0f8503000c040425a9441d044803030020362194100301c0c094070480444003d80e00020840344100d6416444d40c2d5004042a11500250300781020052a1607130f45040118802c400320001c1c01085910038903080c040f40c00d1030184102d04251010300b600c182032480b2140345e0b4088020074181940d50544025883e03444602c0c0980303803c4802c0034002c212001c0f92410f44001034590b441c00700c0d40b0b8001e200c01c0c42079903a1010141e58066140c0b0005d00160070230072810b598a8003982001d504100c2c09410245420b00c05070403071074074400039602141c0e4100914113101c07840c90580c5503c1d40003c4100010003001000e0b80e500e5550f04020310a00141d2803001c1900c03031010003c542000460303608203000340017442c91407400c5002312400041d018451001c800021603035040014610200d00c43c0480c9034000343d410000e0b800d00d41c02200c2075950b907140501ca04041500d600784003410003054080c608900590542c030381a0b5081c10030300803d07800380e8904 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 684285161 1250 684283911 684283921
    0x9010b0d0f08160f0b071b0308090f030f0c0c1f120b0607120219230f0109030f08091902100e042a170103020f0105040806070323 57
    0x440c089030322101d0903948400c0340c81c0504250103094480040c4201c1225814144010903918064952255440420554441030145d407400d200918000c010b00d1034940c040000703801201416081080c0200300c62400744065802440c50303000c1000841a2540400d05000c10a000c102ca08000003044414123400b922044a802c01d04c08200c404004120b10148032144007881a401034410500140c440ca0f580c184605061040c43c25401c2000014410401418424040c0c4941c2a002e1a4031240c00e03e42403040c00f0320b24220190804503088240540850160142824440c40c0d080601c2511941e4909500d5000580b0b240e500400c44a12a004120444141c22a07580c014558560441e105800043c0d1650100c0b20401c020112940103807800c1c3d0b2522144000502c40a4400d00604007601c2e08990000304603000da00c030072007034000c50840c00c005000510700a2405540319a0600d04035041ca9540c51165140071405d41e10b40002c0703540ca401c0d0780b008410b500b03405030401100c003450840d98241 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 684286411 1250 684285161 684285169
    0x15050102150f04140105101a130e0a06051804020102010c1103251e0b131e0f0c06031a0d050d0c060219031a09060d11030313140909010b 60
    0x300092492540c900018040202c0d4100d1800f802184d4002000710b4a407101c2d07800407540d034a00175403000c291001440c0510b440c0550854401d581e511b0603103448640f9100c001c0391400d101801e21112180c036110080361507281c4000d11001700e000c1303100458150505000290840d144440e03840c04220048250b1007a5040005c00c4074403c00e481d09081c41e12552168800b4194404400000e1400c1e028540500c560009200c0e03c00d00b5500400200c80141c4a060105030421000440180044183c1c044204000689428624060302a100d10101c15100e03a60782c2200b004c3c0e81d0401e10100756600802501d1580e4204000ca01c2403080e1551a101c00d0300fa01c40513500c50071142400b0801580010800404c2126015694654000e24104085202c48200a4043c00388141401d05921030080746820718582000101d0083d080134240103082507181e115007224801c0744182039054407042000490030910045e102000b81044018184c80703400600030000d8100020741802801d13070401922140c00c1e40c4d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 684287661 1250 684286411 684286453
    0xc021207031e2d060c030209010c020906060d020f19030c09090b15040f06020f07050604060c0f0b010905061f09050d060f020301170d0206040305041715070315050102 73
    0x80782d403500d078100149a10700b40e410003511100455080280012241c1140201800c1d07000051140c50140300802c0c0302c040c114224001c988603140000c50a0b003500015084c1007440640140c0060641494281c1485680060341e00450200c090f81d00001000c052446061605403034803005450144501c00f11001c0c000e05c01d11050041c90100b5640c0c40700c1d80b815555120134603030704208480280f81c071282e6940440100180ca481010054001c40d44003034820840440c000096a40003000386040c10b081c404211001c103100c607000c5400e44001404c5502085030340e803d050013011051408615032070b03c41c081c0085108a040c0310195041d50002e402d880503044904041582d500742d0f1b0401c0400d00504140d009044107903146205684000008240200700400c803440740b02c5184121024016055000c1f6076502085802400041042c802071145102481c150104845a0301c2250406111369071003615030407081e588400880d41c0c1d0201d0041920010302c1301f80c01010309001910030391681c5080e24404071 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 684288911 1250 684287661 684287693
    0xe0c07020a05100e0301110d14190203070908152707090f0908031609061404090c0909020c010c080c0406080c090102150106050403150c0c03030c0912030c02120703 72
    0x2101200021440038490101c0c4c4001050044c024064140740e00074504096101050351314450342040d074541d0740110300340c080500600404403001c28444200c2c00c1b0340020742020b0100d504100807203500041074081007009a4441070f092468556904009107210301c03100c0321040c10144c0c0444510200c0d03184501203a03020480e6080c02d0003051041800d0b141d10010b01181400a00c01c04022003809a19140451307030f00400384141c0c4900303201e03d1321110151020425207000200c403d00800c8180400c4030740760030003080b0401e0341c149103800caa11526004107a03040100d4034060390b075652842c814141e900c02d01c0c07150851003115860307250034100300000707040440040c041010342000107000038040c1d00c200038891a200c2e80d40c44140c09542c4982c0010b200f5806480151400081c10b00d46601681240c440d0b503840c00c1c4079845261480e03005660507070140422840c80020b200d03019000092034032051900010a40c80703943c03600c41c0c500c554410815401790040c1461401e03441010107000048408010302a11 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 684290161 1250 684288911 684288919
    0x6050105070f1e06050901060b0c0703120c0b0f060f010f02030a08040f080403080a0e0103140f0405160821090d03201e0d03050412110102090d0c0e0c07020a05 70
    0x104030641495003000b4485083d110880221201c00010301c61240e11081c024005400207112041c1c2d60a4410395500668040845a4001080400c00600d65207101c181c1e00146007400c3c22540419280c940800c1e008641d1590404d40e41303c100f0800c0d02d821202000304039400d0030a140707001001c410003540d90148540c584107100314880407800740050196000e03038950340b00016580c0c817034a80c80c141c080c541240d50610003080e0348070f900031080d40c006e01601e0780001c24000030a040e0780d079145140d0304022021348255194010a240148000e10060311007018065140040c503410700101038019101c4048099003d46080902211a41c1c4c0c0d203040c881035156425182450b02c2e82100c0d4000c041101079000e24000911a810b80900450410070481800e03540c904141d96205144176010b9043c0c0b50100c8005040140600701495081d01031611514034040380340006041c80d01000100e500d03003010503070a50b1800c4180c0400c02a00010030392555110030000005403e00d25070350301190002e1303014000c6501c9 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 684291411 1250 684290161 684290183
    0x225060f0309060c030606140f070308060105130324113004152904020d02040806040807020a06170103022403100302040506150d1805030d0516030605010507 69
    0xc40c601c66000032100e103401c1a000c00502084004c050020045032040300d020401000050009004c10001d80b400028003d00300d91500040342c0d41102c03a144010031035418081d050180900600700036100380301541c8030b1020f81c0035580c10346140f0200c42e100c14150781c960f54281032a28401c681c0c1e1005030f940c42413800301c07411482c1850014111001744441c4907049241070880420041c030211410100d204903402d20104201c10b10300040c0a0380c400c0c40c10784a400b812800d0300c204d4041c10140d0003024841d80b1032a0050401c4d81314559a070070b2a8043c3e40070b0742e0300c4401181c0c050551401d558072800130266820800550807259603889821581444064404d0f14240c1c8184551035003080c4510700b07940c0003400706580c1d2030065401410032045020680c095860100013131001e041c28880f803002094400d64071410140102416030240204062207a03282d101241c5d241c000170000c00c00303045000103260010130207152580860b40300d10200900030742018200402040540d802c0001c940c00070742c01c203511803a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 684292661 1250 684291411 684291437
    0x411040c051b070503030c0607090b04030f0b0703021e0d0506030c01020a0b090115060221030613050c0f210f061c1a150906061206130e030316022506 66
    0x1c1001041d5101303581502001810141542c2d010440c2c40c03244c961900c400d154142c82d19980e44070360083d0700000380040b20304150301340802d04480026900040313078034003d0325219041040c200c102207801c2020083d000041219101051103020700c0c1d511040641c020500d03a008100002d41e512030961b030107014a298030340498400b45003900a0100701c402c0040b035000c0642d40741c800035a101c480e4241005074400003810403680060540c1142d020742030044c201c4107140d081314207480040c84060a00794843d003040014000c400b030308a0240c00340e19105114061035a00351001030034100e00c0140460f60701c2c19103000f002103554070b003452408400103440007039401703909030301d02503c5400b034286549241082c80010010b800034000104000907605423000c0d620340c1c50315810700229002e0070000f02c0d21801c10390300041160401a90706c1214200c480c101003a400b2180282500315030094918146061000c20503e0400340c04200580da4240e003001c05002c0882052410003060f10240030310400c000f85031381128 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 684293911 1250 684292661 684292663
    0xc050102070203070608390d2003101208040e0402042009130509030f0a020709060e0411091510030e1c080709080a0602090402040e0a050411040c051b 66
    0x1803400742e4080c0072592032540300d41c4043c107070200445022151803c0d110400c0b0f000202400b1205140c05c15010740308228007c50341500841c0c00030078081c0e020301d0f510403c45504039480d4984c0707854400c01c85007481e0b5a09044010040071010f40c1c00413140c00094400c0c120004100004407400c4a00c150010100d0392550f20000f005804d0200e00341688000480c900d070008a4000c3c000c0c4600c0104036003101400c4003407442081070f20f108961182d107079042440a503060300301d0040201001e00032441076802c000c5d01c82ea2100f00f101c0594109240b0800781000704001c001c0400c5407020311030011103050800d4540500c00c0100c800e022005213010300141d0b045000d400d80250003824103070418409655050b079489015507401400e020440d800109003402103108c460203440d1050660b1080405010100300540b152030103540840c4016400640c204130000322524243c0019001d007001c4040070405003007500f01004a81d5a00200301d2250340750100c00681d41d50448215a00290b0000c190900c02e1100c102c12 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 684295161 1250 684293911 684293917
    0x51504060f2001050a05070305061e060a020313080307050c0103020301030b1f05041802090a050f040803090c090c0c010c02031c0e1207080a0921031107170a11040209030d0c050102 79
    0x10b00707a29800c10041c0483e2000c650040c610a031140c1d80d00704056a2a442045015028a45410110701c42201e4030849418040c0061101c9142c600441345421f04160681c9407071348840d0700103c440c0e000810a082003001c00d100ca01003034407013441c0c150b0071541103840705a48954040c001540c460300001346070703c4c40c1107140d10010043ca80200100700504110350540603100020008034800d00c40c6500294040c50103100c2c1500508034020003064950741c50b038500740f2a920103480e00030039119043c0941225501e0200140c4030301c641510480d2a182c44044d40390035152072018007810754200b80035210900106a02d100500100300c2008151031010213019170502442d03400000d881d405c009440018807201d0401481403001d96554140e20a0b80d035081c0c1050240d44201040d1204050190716012904c00c0d0001c2005450350004d49560075915407a035074909100050200e101c1e00141440030500040503041c03020302c801500c05619152913180000c3e00d8100721414101400020ba09940a0003402d5043d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 684296411 1250 684295161 684295217
    0x50a110a05070b04170102180d030522062613080408070f0e16020a0f140607020d1d030c010302071b1212030b46051504060f 55
    0x542d0000d544805003261158003078020305840305c0c07242060700300800c01482200d40f01300d0424400040d0000c08010810883e403100d0342079003008014400549034404003240380d03085400482d00952640d10341007019100d00ca080080c660004a41c407040720403040c3d4484650f0b8405205410301c3d024190b40c1c0382078105400f4507002014244100c001c08625161004070320340030744015056001040d940d1041c20608060300910000068004221050001c0d01005030070040e944a4078403103021800318220b02d40341041c11540b48006070b105004641c00700350086841c5406946002440d202c005e400d5011079610f82c91381c00124100340d8001140342c14000c0041c800009000300040007402666a00b510664545c071f611003d0f103050480c4100101c00600a10604400382805010340e02450240322035010082460b042c48100d81d01040814450500755500e00c141c200c98000384c0c0000301c0d050006204505c2c032046219022840304200904c4100d800802130036040241749810100e17011001c2c030740b440e21020740701 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 684297661 1250 684296411 684296413
    0x1101210509010506040b190608250e0a0f140613050909150a02071a1503010e0714061309020a14040305060403030b0406120f0f050a0c06090e07050a110a05 68
    0xc2880032085041d008580107401c01c0780c041c40b21000320410400e0500b016452410100080e510402185002e28a41a481949a50100400e0300e40e8808000010b07036100d502c40002d440f4101442051030800c8a0801600ca040d1802008030700f0810075811a22198040ca8030079180031a000480c2048400300300302400000e440c012441c20191403140d41c40d0980d14100407030300300c100e00143c3c46203010f109480358a6044551564055207080303d400c811440940f01500003001a48c0999054409024150398604480024a221442c20b0551110341c2010905603203d0f0030304000742c9403c2c0340c0904000341030350586400140e0b2808140819500d40c02039101c0c418001e00040380000c01e01c000401c413244118040d032010700202200c0c100308800c462150140f00204a00440c04a0108071140080590f0610404801c688224545c90300b51525901030021036034181c60a0091100700e0f03200800380000d050411100c2214100410040c5c41406015060020001121030280c42800c0802c900031213103401030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 684298911 1250 684297661 684297671
    0x9013e071d0406060815010506070203010e12071401020a0804080d27051015060e011b06051b090108010306090812070e030c030a020d0320030a02010522110121 70
    0xc011155104040ba42900c201d45416000141d00c007020412580000200c41e140c50180c2c24481003002a030032460059030559070b213490500400c0400c018401c04400d411030540e0312142d251811038400000b03400074080760390042c8145007a094005001e60f41150340645000c0d00c4031007040f4144010840d40f990661104869440821240041489030303480f81e024200ba524201101e80c0c54000342c035860b4000580d070194880c0100141403103120340403000304d0145824002c00e200070119080001100d034041d284255144140403100d640c000b000340c1c040c078420045504000d40040081c2c4128070500c00078107910f131101031490400202100b110710307011002d01f2410305400c01d40d20081035507c071003890314084c3c81742e031803101910320b0002100ca05050740208400780400321680c0403038200c209125281106a80611080e01c0c005c000e10140274018619400050149003070304420050704000e1000b012001d11800c981c10220310030360030b40030b8400f400b820718954a60702e0000c4110301c11148121010395610701303 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 684300161 1250 684298911 684298949
    0x60c030d14090a020306060103110d050a0c091d01030f020d02030a0f05070b0705070911040503030a0f020d050c0d0f180e1603020a08011815030809013e07 68
    0x140d40041120740c01032140d0700e2a42c0c0d403041580e03950f00c4160000381d0306a00900c00103041d90700c240c010083c00d22000034200e0402c101080e4500c182c842c1680c14001c4152550350003118030b60320045010082940001a0180d040b03481c0740401100010301002c0c10303980320700c040c58080d504c0c0d20507203140182d0b01a0440b60307900c2d0203040c108000310311440221000e0081100000d0309240640954190b190004080c1120a141c0382c41103008043c0240881000ca0050100081c20707581400540904102522501c3d004900c002c0b00a09001821040c80c00340310042c00f03210a1142c0000e41c10101240034104410490681c000668407244032100c1d42c40008004003001ca60141c40140075406800551100900c03a03050100c00d50590081400340e000080b240c0d401040b0004210b1444518088014400550b50700a01030044151204e07401c191410304000424080c6943c0c0500c15150040340d4001070100103001d10ba84050004402403805030100300b64001c0c00d0010024845240104160700610b20a04d81c1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 684301411 1250 684300161 684300187
    0x80c011107080c06090705150310050901081f050c0f0a030b060d0f05010e060136030b24013009031e050909190222170f060a020306060c03 61
    0x84150302034124024140466400c505c00220340d0250f03600102100b80a140c4482d0140907a0802418901e5254446600182549405414502928407540070b0b00c01444090b01036941c000e0300c0741184039042d280000304800c07024035000740e0302501000a1080d5941d140481c049001c0d1014900d01544584e001900c0034041c00d10b540081a056040001030003d87e0b130715041800e546808482c4140402c0c10818034000c0e101500f46241103880308216074084c0405400361014101445410840b03c0500c2c120600803216a21524108501644030021b07a840c1e41c0980001d00c5000d0b054070f11004941c415100da0014600010502d50031003807620704002d90700301420002c1624017140d60140c2214115601e003100070713125804a4400350b0015001403072546803001d004504107200848190398583c24041c2032288800b4864100c244120204400b104508001c820000c0c1c1000004240290b8411201c00700307041d80204005600c02d000c95001a160341d181d030041401c80c4560800c8a64601002508581e0000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 684302661 1250 684301411 684301417
    0x10b130b0a090506240415030204060e0d151d030c0a1a1612020c0307060905190519020f0a060305150901050d150b10020c12070b07080c01110708 64
    0x411660769211941d51140541200d8058600c0d5400c40d1840040c0e18407032040c0462000b207080100c02c50b03481d26a8400704c40307464110300c140b11400641c000a0421846520038030070040d111044405010498403566801c041c1403403050315098058550f20400505ca12b40080540c400e41ca800c141c0746d4408146000a4a07000d1051003240c0818040104201070034020790740610450426203103600800c1521401d8801007001c000803e90140c080003040d01c0c04c43d05002800d001ca10980c03011481000313516100c1d051a2070441070740f00b801e000c500c2c2200803403000201d1b104c84c3c03032030214006000b41850011802941540690325002408081d00049040c4e0503482544244100303004101c001e114002040704210b028030900d540715405c50001400304952a601418800f103001000514804260214816250104400025070080c01c0d0344005428818080c048011076030015020301420103d245800d07024090000e018030b40c000c60308944500d000d50284001c030244109a5484074014501158258 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 684303911 1250 684302661 684302681
    0x504380d032c010c11060904020c0610090b031908040e09151303080f190c02011e06050a03080f07051615090b0301060c050114250c020a060f02010b13 66
    0xb000c501e80d030360500c802010800c2c801d072030594441c2c64400403910f496802e601408200d80d031180b0b04000150003513440780700404142440601a06043c076145200040d82c0e0702d20b91200706140e00300807090034140c0c0d020078105140c0c11107080ca070b41410300f03d041c5507005000b41d80103414817461300d105111050000051040365240c0005920195a403508400c41c6840c0b0010070050102d514100070680412524081c47d41c0200a0f050b0044c010808142c110280e0342d200c0c41b43c002503556641008204101c01c410b142d40d00704c801370705104280c41e11000c03500c100340c2440050152180810300c80c100b10340c0300d0704986080340c0100490710382070300c480101c0040c103000e07100314a400d8003201048240180038002c40400c81d030130710131994116840c00398180e8030103201020464013956104c2805007281e645140190044103450602c6020344804155105143da07091051401e0140e42d1040c100165560a1400242c8450746010400b03820506c3e02603000d414015992688403010640c842030b41000b83d44a80000303 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 684305161 1250 684303911 684303947
    0x915050408091329120f031903091a091515060c030c1b130e070603180605040c091404080405300c01030f020c1c18090501050a0504380d03 61
    0x1145c441901035a90301030070952080c0941040c401c0a80151140c416041003400e18103012941403400d030f4400342d1620560894902801c0304c042482600c1c0c80401511900100c07003400358a6504240f680228800d81c0f5214161065074001140b04122905000742c440c00700200045035410f4107000341d651000c4121046050040e2500c84e5040004030740ca00402c61028095005415054101002180540b0350440365080c4151501c4441001603403510616110342d000301c1d0150607450502c102038090340d2400b041071061803d49814440456218021201111401c5403040c095109401a2442c4509040110002032410810780c40c0703900da0100e450000d43c0b40998041008441d03140120f42240121185d0400552150001c0c10110312203c02413560240d8070304040700d20000342c2e140044450003540103003080e96180d5004011504140120a0241100321070502000000c1071404a07205105203802ca42440081e10b1807840340c004d400040084040940b0865040386075060280041c08481064100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 684306411 1250 684305161 684305179
    0x90409151b030912030c0e0a180c020d020715030b06030405030a080705041401050702040e0f0706090905150f2d031603030203040b1803100915050408091329 69
    0x70407403080c0f06250701070b0b80c800102d0a0410400208400500f802c03406a0180861100c1c907110603507610070504010020580e10744c2c800042400340e0030075507030048450010f56000600f100c100c0b83d00440c006055507030960b00009080c1c03041c90201d010f4140754a4207901b006000090101b407000200090030f603150f5a480b0314600d6150290129280e101d28400c4501484502100c01d0141d8070a400819907070307000410100304403460304091070034642c406156500c2c03030b84442c074108801c40e0070089a900030309502d02c04000c10b1405042e184440901d04925a03c5181c01c0030394401c46941e00d40101112032040010b05c1180a01142012000c43c04854424030901c585e0318000c503050400d8248000741d952560142d4100307460500301a110f03810504100f454809903503412403454504002c2a251050008000b060307411103070a14140250500769071140b41d034100001c100c0400c85010480f070354a942651802e2900d01804801c00007001e00f9000050340c294142012000e00762100c100c413907000003c03614100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 684307661 1250 684306411 684306461
    0x120903151a150a050c10020a0f110d05030a1e0e100f09050d110a060509060a0e0d020d0f03020d0908031b040e07030207211805120703060209040915 65
    0x301c4400b0b00509540c00e404104145181540705001030310510a00904445070400560b6804080c3c0c0c01015200e0009010070075034035800ca5211410046135041000a41081a03450b04000c1030f81c40002d02c0080c58945a15a881c260501070084101400440d44104011400707100c60907290080d075030801c110f0509024904030340600038820003100691140080040034456a42594001d00100d1480580d0295400c41e0700410f01d0b5004d05071140558202030600340c509000502d00710f83c2c20b8420720030700760302c46032841858a800145c10240000b8500303090407041071402c0114041d00c2030210100780c02c1e007070060071000c0050742c601441c002c244070b40701e54244101418041c00302e80111b10900131110500c4020807600c5000350b00412149014418018407852601a1000311503001100755002944030a0031b1044000e4000c04440500002c8905030085440410215961032060001810180c0d0014402846075119072120600b0b0313a00400c01d214441c01044801300401401c504044542e0504001078 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 684308911 1250 684307661 684307669
    0x105060f0f0f0d0b0406061505040e073504051902030303130c1214061501050706050c04050406080d1e0917120f131401020a120903151a 60
    0x94501400980405004000c541c200540300450950150304201410026004644101640e610560051a010502601d85801004148421a00442081428401880a800c1800d030307450308000e003442e10b230f04180c40304203c1500c44c07000f885108000c05820a81c0c040c070a2003120006114601400545035021181502e281c0c2a855800c4000d515820820024040307001000030001d1003030080d1141070a0f00c1e128401c400d03184c07038484001d60302000341c407000403003803d02000742a6010f011204e8040d030101074500042c10a00911000400603034464000541e03880c655425207008200080040c007620b5642c01055445011022a4000080c484020810700708004009211000700030b5072003208041ca406041c0041000c012185c401c01d014181000c0f00d41c010200144c4404090361411035500c0c041444012010307403642c0e00014400d03501c108095201e80c1c012441900c0103400a000c4800d0b5814903600702e0f03503c180345d0001030104d204c3c81014180c81503654010480002c000c1d40020798142160100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 684310161 1250 684308911 684308929
    0xb0f13060302090a110f03070e03030703030b09090a02030c010e0409050d26010602031806220518090c09040314040f2d03032307050c090f100618090c0f02010506 71
    0x117403103100301006062515000c42e001994404000d1a00501c5801e141e0002801e56200342000e80000c5e4454601030500d01d8100d9440b90800c15603070052030300e00b455601107601c51621031f07021810300c6410840f4224070780700c98000001d410b510100f544e03200601010090112700c0715220321550001d5499000313040300300b0700618505a0b0403e8000b141842d4800329904060840410a40d400c1031040c0141c481071106083c040780d41d81a00300d1407000003803c103014030046070540c0d03a80e01082c2d400702045c003d141c01e011406040c8130708203a4070f0b041290790390308041e5040099060b504a54410000740008c050b10b01c5104403059450700c404120a140b071484034240480081c548103921b40650140c00c1000900941400c01a1400f100d0301c0407410304a010180d1160300281000d81e0b13103400a00c003e02e001e02d1b00601290b4000c0713000d40e60689a0400b0028284011824081c2034280905441700c00d5139030034500380050023401c4459041c0820704031844001d068495090f000c1001d90700740f8020400307a103091195 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 684311411 1250 684310161 684310181
    0x10e0a0807090e12160b04032a02040e0a020114030a060b0c0309130c2007170c0405070203070f060c030209150a020d020d1d0f040e0a03020d0e06030402040b0f13060302090a 76
    0x441c407811010351b161a00c07488800b40044051003400403400100500b0b11100c8480d0b184d010f201c4020084681c010301080d540101281d19442d0005100b01005030303040042c1105500300b00480c0c1e9100c2d82d8030704400c03000340040c1d0804099a403000c03860503107100b0008000d007198a026100c02e004400c1d081d02e0903060b10840e10700700000c1000c0c01d100101491400040000b60080d81e412108032998071f800000e21180f070304c0005d200c181c101c2e158528050806016050b0070000500c0210b245c400d090b02e884c1481e901076a4001c11040c0c5904003065203038481c1e01510312000d8004e285201c0481090803501b01a404100e0001c05801607031181045603002160020880c01d158070b0f540644400d07021225420a410144164001c0c85808801000c5c0c407140714801c0843c41d2400180724242090402030301d403040e080010800c2144069805141d0740760304055a802c5903050b1800308ae1040c10400045100f40e01e4468550030454042003030481e028190000000c50307000382c40351115030b1181c01d020b80c04d403851462 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 684312661 1250 684311411 684311437
    0x3010f05100806010e0307050405090c1807020628050106080f0a0e0606040e0f1015150c0809040b1e0a06080c03040308090f0102071a0c090a05010e0a0807090e12 71
    0xca10b54043c005e0300000e000d000382524003c0391120005800c8a00c1038810f41403035400b004107400c031400c2900c0f600b504058104038500c01c2c0c0c604031400070350359003005040048040c03140f001391000c1121080e17036824640404100303002c8d642e102d0800030042502101c9a0106401040104074009141d01c144c400054070107025090303694981040c400030b0420740600050520500316046c6c4912003d0101c030f03440100c0c02002107004848402c004181081542000400c07255141c04822256000109107640d1a03000601940790100000090300401c98005919040100c2c283d91000100e00110300b032241c40000c0320b01d144031030f8503a403044a1628084402c2d0204000400104000c6401349000d40c1d4894200001c69640f04c00728034403c0d00b03907081228102c0f809200b007441c0c68594882d010b030499100c5000000c050600105c2c000050396000e49100b00b80c140711204005010039142c01110300f014142801c00c0307071031045d80c1d1042d0000501da0490300c1ea10030b000d80f482404010f46118212103c0145a01e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 684313911 1250 684312661 684312677
    0x20406061b020103020c0c090a02090414070f081b1305010f020a030503060f040b060d05010f0e07021b030f0304080a05150103020d12030912020d090f210f021503010f0510 75
    0x19005600a505c0181c5000c428400c3c0c2c03147d00115036a0384a143e2090a00e21800740c0c45580000c203100564001c100c41415a088101c200038801e40c1c8100300d8460040c1d11302d8409680d4842c882c00109184040c0a4004a400c0008030901c50008104501040721002e036107044a0040607070307003240c03990b0810a00500003841080416124685002c106264000050000404000503000151960700c10b001407100240c0b24401000407206061a0700020008070385440c800749042075000391503404904001c040050642d40040c20f40d141000098040c80c0d42c801140c0d41c2d20785400c000c0d5614400e1500c201c446110b82e00d1841e50038210140f685040b01e40c0078001010507407866681e240348a98001e941c1c0101956010901c00bc92440040307100280215000307442d0040b10118000c240e50807580010b02c40303414103201080602d01100514601000c000c902c01103115a501e40312544944010019501c000681d00f4a019580f00b40c0007907040380d03140400e982c609551103044c401310200804440700414105 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 684315161 1250 684313911 684313913
    0x70f1a0702010c05041e0801060e04060c020321130507060c1103031e0f220806150306061908060c090a080d0e0d02180906070e0406030f17041502010504020406061b 72
    0x540151b0040101003410810a5240c3ca401800c4500c10703030001c00070010311018003040c04003911034102c0d0089980b001d5440c00100110a189000d1102080784290564900065410264060712008a548801682d4126540e03600007000301c003803440c0599060f443c800506000345000005c0703900303214040d0201c3c91803806145d804241d54000b0100720030991010084080d07a121007003104031a050030f08200c0c1050030308110f001d600d0500000c003c990087c29480402c15981e500203462503002d07034116607500043c900780c0314104a154240e4014401c0d03203d4030041c0000d000710b0300c004d05007060b015581084040e684049566840c02940c0e08000881c198003910341d41410007410304c0b44098000340c040120b07000b80004604000008483d11000c541291b42400306890b40080e0590740c40c00121020f022060640d2280e01c000c000c2c1c120010324642c09950300c81d00000606082d00c2c02001e0801d255003800d03c0107000030707000c3c10701210228862032420001080075801441890a03550007003811401203030f21 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 684316411 1250 684315161 684315179
    0x90114010302030423030d052206020a0507050109060e0f06011206050a11130614040e0c030702150f0907170c12030f0d0605090a0212070c0602070f1a0702010c0504 72
    0x1014000741d450170151200a1408204030710780d50541c000100003150751f8441c1e03150b14401c4440183c01c080180840403c101040303c541c035069102030780c21001c0165517032000282594a803041010081c219403d00070401b09100319607100044c21401d0400b80c6070240104040705480304002d0290410402c1c02c4040000420000d0384960740c40280b9071b80004130300c140c1c6480c043d11030300700e40060684001000000d11805a1004480055540d40d0600900700390034189455041240145050a0b040010000540c1d252003045100105804040a0445030501c0b0f480341da000c1100f190b42030602c6c440c0603000900310069043c0d40c06070260010140c03565240c0c4104120a1811006801b0303040c1c401488150701d0b050220006100046141500282d518a042d0501c44229001841c66807802d105003e0308103205698503800b54410a42d151403c1c0e01c0b034603454610003e000d403400c0a01244c010320400410850b80901036404d40d04580ca070f409195980c218101e00340c0c0c1c2e13950300400c0042c5080c04204603c205c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 684317661 1250 684316411 684316417
    0x30d0c030e061902010e032104020d0605010b210c0403031b020919110a02030703080709080601060c14060105151e0c1e0c0d03120b04091b05090114010302 68
    0x8420300d04441001d03104000614550000d00c0d07109608460f91500844190302403049000070507054020b54100541c0204011224140d5130740700b80b05203103c070009030031952110710068107141d006c9005c11403541c4502c181540358019a080d000e1905020340d4117907031008030741e400501c103a07682c0c0c42e100d103007074110307507007141d5140c845d204040240020201134801a656010307220311500d0b00e80c50003903c90126441e0704041c2c0d00e149007440e1b05003004005c180710be11303404000c5921140c0c260230b0607002915580360440e8503540b641c3c044e25241c00380300000300c0c0c0325901101440249010380010814160f1201c2c2c0305890300350a10810707502551030122400d00009000c0a05450380011510b00700321449003050410079404420fa0800c0c6400c04900c40382400c903c0c0700d159200c078505030010300d81005541c01040c0b094500140c00f50034812011507640c0c00c0300c511b4000031302c40030000c0c0090100000038039200c08403140048a91411108032040481e036410009030301030498032480c0780ca03c40b1100e00c40064000354 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 684318911 1250 684317661 684317663
    0xb07051e0d0b090708100608040b041b030501090f0309061706090c0c0a121806020c0418080703020705120102280c140303100f0b03040201030e011b09080f0c030d0c 72
    0x41e4580505000541d60103460610071805170311013008511b0300d501241a0f2041c1074004000340643c00c0c081c400030074814144140e0113544454180451102107220003c030984e0307548001e1156091043d1181044411070040070100e01c2500d42900c644c1c1c84400c141c49045840300004006080d1000149c080d2406650340b80c0c00001d8481ca2524204202844078180100c0b004103448424006044410069200d8455000c6c0c0390f5100e01c1203c05801d04800039151046410824400d9031510b107505c41800c40d4010074140c41d51b12074592075a40300719180c0a911080b00d481150322801c11031040750340d0007406000300c035408039115140035041a94203004442c41031813a08020200815090100006601502184004003d40c8001c42e12480c10402c111134041c0140c126070040310b82c480d81045804040c400341c03608036509007008162220000140f42c0104480c00d80020305a0b10f910665408a03007110100041d6030010082d0b4602e10741801445680f0031030030303210b550141d00114418040e03500c0b17103842052003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 684320161 1250 684318911 684318937
    0xe0409021c0506010819020d060504051f0b040f0606022d0105041a060303090a05121219020f0c06033108030f070201140610200304030b07051e 63
    0x1000c41d140e0306a001c01d0800012140ea41c84000140300b0030204000100050000309101200088541d008c1100c0e102c0080c3c0040c01c0c00e03180e40c04541003000922090038003007044200100504800c01e404006406601030550080d450042005080301c07081c0640130136507105400826000ca010506000c01414861030183c501482008500f80004207015190003103002d861740198400e4803d41206500c0b101601441c401c1d881080750410a44507491004200d032000c966461000d000d900b0702a0414404603a0740007156000036140c5000b8840c40d420001c0074800f6402c8568074007400c00035a5403458501e030350581c00802400020080c6100c43e6501403c0c2c0356000481703004002500c0d50b8a1203010382c4008541d0030101100b00324070744440c1010710b40d00000301e01c004c1c42030354001e8440000e8943c001d0310440c014003284589200080c01214002c2c041120f0b8800511f541e2400038190b600c0c0d4203c0e000c11588008181c0206440c18030031010f48800b42000d2840c0d04510614502d0780142e644102a100b01c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 684321411 1250 684320161 684320179
    0x3180321030915020c06010e060f01031d010504030807120905060a09020d0605240f01080408030c22030c0b0a021b150d06090b2b05071212080f0103030e040902 70
    0x3d0621600003004904088001d07858141c011711180c280f210503040080340103020790170044a6500e040006c20014030030300b00000c0c0c03655900c0c16103203d40800f0a05080c42d40c00d0405210030103501010320781c82403209035240000106440710040640b040c4460191650b80403101149900c00143d00000220744010180c420868180d0340320401c0d11000c4035074208040d502c1017644010059220079941c40d1804545070194a11000c3c0043c250810242026220b84400f02c00946410380000444a4140d0008002a0305810200c000184010303180800c958281c3c0801000603444481c4003130341c542d1502c6030080c10b004482d11a492040c1d290038a0315540c000c00f0004c006444100700b000405003805a42c1c0082006400d040c402ca081d940c41d580c00d54016400c1c004aa11880703000464a00031020107040c080d003c0c001400d1162405407180c000a0149280d48104001c110b903c2444c0c0b080e640140d1242e11540d500d90703018000100092001a0210740102d0384241c103407920703511010007248000e1840714 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 684322661 1250 684321411 684321413
    0x90603030903070e09120a0203120a020c0f03040503120705060103031220091228230604030306050409080306061c05090a15051b0d0b180103031803210309 68
    0x4038006140e4000c130b1110395504140a002e03a003d001c0310403000c07080c40b401803400d824040000d6417886200543d003195540c0c040803503081c1d070702034044881c186081011a400c04031082c4080d504e9a006102d82c0c3d10a10074540b0f01c00c0c2000b080c1c41540c02494100028000b82e030319685090314040f685070410321806a85804014034805108429114a40d08103000c9456600038414021402d060036101400c0c0c6d03002d6a04661191081c04005a10303400800c1000900e000c00d240245c400001c2c600c66201da098002845584c490000440610690182e81e0a005c0140d03100c05000c1150450400079001040400000300903003070490017041e44220f1001030544805c82c0880020845030300755030700550741e04a8290340c428010011100c410035050103000704564249580c03815074010000c5003c038101c02010650504c0130748598040040070740d000d002d82110f83d03054406030000d40307400d01044022808094402a41802d16414070059075849402e201d078916058280d580b0a00188001508050726888000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 684323911 1250 684322661 684322663
    0x30c0503090d030f0e010c150c0e040603030206040b0f0103120e12011508010c11030706150305060a020405100c050a1b0302060d0e070b0708090105160f050f06090109030905090603030903 82
    0xb11900b80a5034503005600c0e0308400040c49407290f03a0701a41001a981c0b8004041802ea4540c5901c0098000c800200025403e809852040020200396400707403420100006243d00031034864442c80c815450300109a403900c4046080071020b02001c0c03c49403002202002c841d0050380781d880c040500030b2a84a2228040681d1425180a4441019040c820001c20400300800b401488072a6102d818944446400010100c0d5240115100588415100ca606125602c120080c10000d103802c2001c0c2c0e415032500070000c901039801032080a005042c480130041d012440345a14401d500d81c0440600a000d115403507807510000c1c040071120100440071030010060751074100070403907159140e81c04038042500c4015242002da85511543c1d0f074403010010000012041011910414000d00b85203807101c002420f0703d04131102c0c220005101c121903445007028800e00056014820000c60111001607440401203405d0b601000402004680305020503c050303d080e1114030743c00301001e0300f03c9041002440001e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 684325161 1250 684323911 684323929
    0xa050105100212030c0d0e0709051311151902030301080c01080403020c0f0f03030a0c0c06031407050d06090c0c05010605040204050a090513050618070b0307050301090c03091721060d030c050309 85
    0x84c7c0c00ea81d004403c03c00c40d80c1a140501d65000028460100c54510700307482e4504603010305814a4421812400ca00b551801c0590a03254203142d0041205c1054441c8da030040e59036402070080305114428850300d9a4a903128941c00384c425503060340a03000d98503100d0144400345203841c48495000e402d85c24201d0300e44d1010000b07840103008550360560741080c4e500b40074842440340d80111b0101400d02c3d052014503e8184032140d08686546043d23030f512603400345c14000810b41a04400c00441c02d000e10f0800c840c0d8045084504140900000c1003117076600c1f0100300c2244190710070399411407000e2004000c0c9001561000350702440704103460301c0b00c0e481503940b64204403084808101c9541c0f10350f40700c040c403e41005968083c150715041da03851410014006011800148149070300305440c0c200c41c1d20b6062082d00b041c498540e03c01c80441072a1505600342809401501c400352403001d9000020080707001420240340550750180c407501400d052620b08880d0b0b458000300940f411310040140301582d442d400a9 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 684326411 1250 684325161 684325181
    0x509060c0a1227060f0f031404300207090c171f08120f031e190e07051e0114070807120206070e1212070503030a050105100212030c0d 59
    0x29a10741444020601e20003074071480700d843e0310b0300040c0c0c004d1020035000801154404910708098400594403c8118054420640c1200c0300c0100c51f0280000c21402e42c907401c6c00c115034200003046099055085d6062a00c01c800d0f5000113134030a410801c070003c3c540d4054001d010142c07a0889014506450280024005a6110104c121802850902d000d81d0144420103450054090403204a024034008120300800a80b85884a0f00202054a25007001745112f61490610792185061500b541d010300c82c11200703440030020318101001c03407011900c086103204c01c1e80c80041c03800301c0044802c0b4044003902c200c82c1203581841010700e0300100210051014040311441021034695a0015260010312030f202c0200c08415980000f090060658104840c00340c04141a1902414000f0041e101407426070005510940c010001440d0b01c14040d0110065116695a99043c403199036544203125401520904074801600010345000840b0100c000864025400130130850520321001c0100003102d078030542c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 684327661 1250 684326411 684326417
    0x11211040306060e01080703170c1005040209060d030915030b03060a09061a061912090602040504060510051210030c06050307031a0d060504051203160207150509060c0a12 75
    0x1400308200b01c0d80c1d002c2c0002500016408a9803545454041035461a003404010a049030500c0da0307009030510745080d04d10344a81031003100d2034600032880b003500510080d02c0903800340c150f290009102d07040c915412688c181d416500c142c1e40501e00146c0000d0496114140d10805840b0000c002a568042110783d000d080011800507074880c0f01d01c0c2803c04c13a010108501210092008000c61b20707507034002075501801d200741e010320315510000c1c012946401000e502c005c25034a0f000c1c41c40b0a01c03106501400a0720402e0301d003003148a8580781084400400800c00c0c600084c4104000605000034403007ea8008941e20101c1e4080d84e00d80e5180d840700c0406811840000d2000b0042104c4ca990502030010401c8144143e0342c0f40301c10840c00b0881a0200c0c0c000503107000d44441c041010040100100c4030009155800f0540384c1c18025006204214034481c0712005114224020a2140000004012904154482526101041d420301510360840f0b40d0801190044100400124030f280c1c0c100348007065159 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 684328911 1250 684327661 684327667
    0x807020d151505010c020d05071a0904111905070303060b0a17181009021302030c03100e0910110712051e0405090c09060f04030c051503071706011211 66
    0x2000500c1101c040740d1100010103103480082002c0e0b600304809205d45901611000d0b0749910310b08000d45403844a40c09110515204c40208103030404000150a00b084c088406020f00e20700c0707508540d8580940e42e0080c1404040f2101c81c0c0362036020750014204a8800d00300415020b07920250241c65400980b8404042450030390f0900006280e20f4000e9072120200440810396020060410758035a400045044c03601c0d9110120019903482890b8540c003040001015540d80c40c00d403c240c11560029070b0b100c40c90000355500070860a4a036500c1621882039034000382176090200305030002610b103c2c114815074002c108201070100d83c1c0302803c0083c04603a512403668070b440990f80b04d803401e003807501c80342c1c4604801d01c01880035603188c640c0a50842c84280c038083d201c000c00741c00103409104500d4800000b0000140000820240c0350001080760400c49440c061000a054081010301c8100ca03420006072800e40071f0400c180ca80440706d9042401890044000840070403203104444100c4010300e046a804 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 684330161 1250 684328911 684328943
    0xc010902131806150b0d0c090614030a050a060819290a0c090f0603050105041d0c0d050129030d030e10020901030902061914090a0509040807020d 64
    0x8100140e050040800007030b2060010381c0a5007000300c00043c2043d440e03140140c80c01044520100c06440181c031800d07655905e41403c1e40040181d500e64501040c00207900260541c050524403600d805411080f500d142d980b0001003000f003100800d43c800140c1d0303801c00462810410401c10743c03042c02810302d800182c00319080000d461381c0d4015a910030300d42985281074000964506481e00301e40131100110305100c10050a660890143e0001d1601d0502443d001402c0c40d0305070050750480e02c05a40800c6510780240005820882e0b0342d280c0c15096002444502e02030618040d0806118010400010707203407a0b040c3e282d6403c28813814440072000282e41052400d00c0c00b84a0300400c11a81e00301042481404069280c540100ca01a03098059000c0340a0300a40d00a81050080c4c030790040405540381d1004210301850071150384182d0006110500c50000000004101d842d242c0b80146204080c40c980740c00c01410b000014421280c008041c841240180c6803400081c2d2180d03c030780d01e514010022 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 684331411 1250 684330161 684330169
    0x17010213060c050c030316020d1a07050d050708040f15060504061211190509090a0c0308030f10030206160201090b04032d0308070c0503120108010b0f01021204051c080c010902 77
    0x43c1e2003d07111b5001008441c64150440c82d0b900d9110740d041d20750510b2503c184c00d0403500b400c5c2a1000d50500c400d04c2081090442c0d03c00002d0100c1a0300da10304001549548504070380f810411500140306c400355049101c08952140b0031554012205400072501031f444502003400d65507203500824200c403002c01c0707410030400ba08112144507d0700b0354072003442c044a4460711001d1041c512440b8055121500443c102c030005004d440c07046030708440c03501035456492400c0c940c1a0710466915500b21040303404a8600d26041c60050110707038004040c182041c0046080c0b6407c4a5028030482c1407200040d000160003900c40e014000640c00398681c64088441da1070010843c800e118410350880c1c3c002104800060b40040c1c1c0329800c203e05140c6890001110300d081840e61080c4182100c030209844000a50741c03a05421200312040180e54104600c1031800069946081741d0810300380140c01170006100d1030401492690306840700394031042403d000e43d110364605034000d1f1804c244c2651601c01c83c00c25820 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 684332661 1250 684331411 684331423
    0x6030b0111150a0507121b0f0507050d0503060406032009130503070f06020919140103140105040b030102191220031b0903160e15030717010213060c05 66
    0x1e8080c02404140c44500301d19212007000810745020155608080350880d44510b910210340300c2c1c4602c0402822030503028980124002c46955000100c0e2800d40e588070340e01c19000d5442030346c0d00000504140b034440c801038403d0b400051607d44c00a544010000124045a880d0741c1914001c0465450f15203029040c00340440d402044040c103001c3d80c00d1000c0000b140081169501e03a044810710014211a140c81e20192084481481e03201030b40c00941d01504103583c0208003125000e0071150355800364100190300f529290700303810b50740b600b10000401242c10031340c0212072605001000149000b50f0582d0100300d11a0500c5030b00300199000404418030b0f070503485401343c2c440d4081c3d11450042c0b5601c80e100c21500c802800102c5c003c2e00d0100c910180400f11041e0b0f40b81c1c40004040c1c85100c0040310100074007600d03c4c86041d1420340508003103400c0b07012202c01b54005250103005010340a040c0820350660f080c10020841482d0740c208a42034041007040b015101030710941d035401448840e00e0400e18a011 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 684333911 1250 684332661 684332687
    0x3122a060403030e0f0a1419170c07090f0f0c0318241401060e030a11100c02090901241208031e0703050106020f01060503030a1809060306050403111203010e180706030b01 75
    0x290b4210b420022034000c480004c454038802e081c29a03070381207502b4030320b040011950180507907500344071012200d114190080003c0010b50b400400c40300708405012002c0d1402120340c0d064540c2800c01900115031310040f21581548181c003001842460750162204550351014003050400ea080e0041c0005a031010800c00038001c21001041420b51544540307a0341d020440c490341c4140c2c0110814000790b80140303405900d007500140346100c01c2c030700103412901030040c50350001c0340d181e5038105d403070400d1107080d06020a5071141a5140305800c0b036550745117001d0b80081c00c0c42c14103007007910b0411640181203203018030401082e0b07008110b95141c0000680382811070713405c00842c0e9040445c10b0007c2d88000003959440410b40c80c06a0340c002642c09005041100d1b904003407805814448080248600358101d20b0241c3e10940e82e510010207141d1880783c50710803e2000303007812601000100303c41200c003120550440c06082e0b6222a240e0742d103281038071b0800154000300200351140c8038880c1542e008000c00041c4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 684335161 1250 684333911 684333943
    0xd020607050307090924080c0a0501050f040909020102030c100b0f01020a03171506070615050a150806060d0c230901080a0e0c03122a060403030e0f0a14 67
    0x14100900007510300e050078003c000c5d180c1e603520307412040c00111714000020b2401c21480c1c01e45680c3c440c603800b900c80c00300d41c818a02981c1c48542c00140c9500c200100c83c0d151039040c515030f0529003030540d0f24003d4403c1c40410781c1140300910869502a206020444002c3d603000c4001403200019001d001e000c400c1003510314150f400c0305500b1400710350025080d1617580107886a29031503030360744c040c03010941c0802400942c2100d80402c7d614100f100d943d0100b1840200003525082580e950000c00c41d550101e4025003004a000004000c842070040420541112000700075900300309032400b00b01c0446407100c0e0110300007042501c64080603030040300d076800104800c0c06c000b480c0440c2a000a0034400d000b0744082e88950703490041d019807081c14007518001e9a0000e0560782e00c2c0032410613049071a045035014290380c00d61100c180c108100c1036090050b00d03012101c0601000e03955a1030560080c0302d4402540388a005100f00110303a4181840761891041c4203014180c800d511100040d445c06070100e00380c0d002 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 684336411 1250 684335161 684335167
    0x3090901060302030618371d0304090504060f0905060708060418030e060d1119020606130209030c060307110105090a02010c33060509090105040b22080c0d02060705 72
    0x16154180225601d45002d8412401c50304c0d41060301d030802c4180d490841c1c030f000103201c0701609180b103c0c15003000340d04266420300c480101108c2074810801030840120b51a032040004100110301e80c0c002e141c4c440c1c0100400602c213078601c4d01040682d800144c1c1211550012410030001d1500000712581001d020f480420801c80100241080042a03071b40160032300c1b0243c110400c40347e4511023142d0300d4000940c814401118501900d103119007010701d00300c101550040c41c00302c075140300082040c441d0100509140441c03003541408002984011034986c0c0601075010a0f9240d80c5441000b10701640131581c0c0c4920581072100c01508503440505031900503000000a100542c0c1d00601d80401d658001c9440240441c10758440f423206950903441600540039042c40c04050302c03ca6104004581090f1643c0030030f030b981c1e46d910300c0c22100704890081a500e0117201150411500c2801410003010034070005c000c0411544661a451f00700103c460510352040c2100017210341e0601c501d03500400b6508042d41 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 684337661 1250 684336411 684336421
    0x627150509030709470d060f1b050703020c010804050109060c052a0714010513030b0412020606210c03120c0c060412151404050d180b0405131d0309090106030203 71
    0x2c68030020405c002c0050050324403079071150f0318203100d00c0c200c6074401804c01885801d8055203015103d8600c01400b002c2000c0b40c0d40300101d00520032580103d91560181801e10186c030015100050060000c0c0c817035640c0d4840c00c8000601900c650f007418000e5840e003546030565501040661140521007421000d4480150001d447c0d000440c4426120080807401400f14001c00480c4c0e00d000701f0307600c2d44120108090010620490b0302003a400b03140515011000c1c00082041a681c42e0002d603603d50300451f60707107220f24102d810b9607001840c01708800c0c02d5074420070f000700000780340c50200380601d140c10400082c030040c0d808042100210715001546c00720308242c83c2a0842144030554040545201d4100340345c2030700d0b4202079000925a0001c00310300c000307500302402c0156540882061800114140000780f41130051311260000454401c85500d528140c24481840380d104005421003440d5501c41445040b00c4100208460103014484000d5898030003080400022000690120082c0342c81002849 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 684338911 1250 684337661 684337751
    0x24091521030909180a060e061024050408100e1522080405061605151603090618080a030506010504120807140609070627150509030709 59
    0x2582c442d104452100165070340815000440500c00d004240501581803640108100780c0d00070303910f5040c694201c074116500c0c102c282c40d40004601540180140c4059044001a00c0e007030180349917607903031424504255450001a1900780704031740104903030313450364143c80b5003250070018460540d0702504d20710640d0408100205800250000c00c030356441c0004081003d010205088400034032001d8116980c0d01c0c0903018000141c05110011690b40c02003000c05409241000e12181c086d01c181061074151004124043e0020454180110764840c0c503042d40103a40561181e000740410b015008445d6101d0020b10b0007422510300a20746814814148814003c40000d4000084450303445502c540e5207103400d080c014504084001e540140748642d80422200c440701103000e00c2110140c1d119140020000030360211543c0052240f4103810900000c02c003c12420078511080000709030500920b4002e040000c41d052908517045455516281c030641c0e146030004108082503079008841d020882c42c0304455003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 684340161 1250 684338911 684338917
    0x219080412030e0d151401030314090a030b0408030429010b0f0712050405040e0f0d05090a17011406040c12021e040e18152409152103 59
    0x401d401e10000c0040401d4090042148040c00c001d1441c03ca061303140c030701611040d040c02c845c60400f90400c0c50f0f081c07400b140c2c1421079050781c1c0d060700c40000d40c0c402000c130100190820001c00350f00c0b6131100400000300f5903a0724081c2c0903038082c5034115501c0ca01420000250308003100380b0440361003881010308640d400c4c541810306440a414085964004145941860307014800000e0442d8166500b40c500107a003100c0184112442900c0078004000c01c103a4458989540d4000e44ad501e030070000d10903019078850170040090400c020201e882140c2c403885002958900c0404410b03040e0365501d180c8400c440070b002010340c000e034206c1c0c0030320040d200124010303e4491050840d4001a80125a91040502d2407952141c461000c0c071110340c986940b1101d035030090707006070b42c2681e110401e041c903420561000b044180d030302d0100480c01d04894039807404591551450308041c800c20800c07172000c9510b603174600b91500d0084481040e010240c0c1d1000c801c110301c4001c00c0c400840502100c0c030000b58405008015 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 684341411 1250 684340161 684340169
    0x30a0213180e0a0c030209060d060f0e0f1212180703050f060a0905030901080c09042c0309090c0a0c060c030509151003031209060c120b04021e0a020f01021902190804 73
    0x8441f869803100d00100e0085c000041c001441c450820407101001d540f550b0009185242c0c800450b00d4410800540750348690740d9007020b00000c40100f2a00d510045001751329600800311840610002042d540c500d807c001a98004070740c2a0811850f5144020007009074036080002e41d20100322440150361150740d40d100380d149917410b004100000401c540400c03015914800006007060241d8084810b100c000300b02050446403482d01c04286c0101400c50000030344401410140910186454044041a440e00301500040810102c2080c0400003001f40c06000c12404071790f1404512410900070301382c180380e0740c60f003401510000f410402c000d0b6004441d980017126050b041c100200038418640d035002e00240d12019041a04001700008125801590700c440b240c0c08140400201000700200308c10381c070503882110b48003460048162500486c5030300074140404180112462400c400030039a09a07000b01c0318044404110f4100280c48a1f0103000c1e000101d55510003a000e030303850607030358400c0d54042d9020b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 684342661 1250 684341411 684341419
    0x1501080103030c020f0405130b0f01051507060b061303021807020318180906011809020a05060f072001031805030706090c0f1509150e0105030a0213180e0a0c0302 71
    0x8070308044d500c81142020701e606014000784040d190840e00030f400880c068104617600400c24001030740715814500d455058420007800041405885e800ca20003e42207200d003a80c1d015540ca2041400c1e0399280003c144c4084400955050075103507004010078030b603560119010715091201009192540841120212480b110101e0301540384400440c00c00c81d12088550300000241e4180400701c0400903040381210a55001020880010340380c188c1503581d1071600a4011b03416440a000c0f0b4944072016049820050b54103d0400507252540649007080c0a25070001c98880700d554002541e0500034200c404c203480350310641c0c002d031564030700307540b44038070310024280aa840c58a0410045002070160081c21100c407245982900c5405413907070321022181e200d000c07844140d40005c8001e21b5550420a6034a15120508031040000041d14143d00007805d00640c2c0707508208050140703040000c6003000d40b241134000d2552000c00da038030000300d80c2c400300241c0c1694040d030040e01c0007924007400c8509680e8156 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 684343911 1250 684342661 684342677
    0x308010e091005041110020a120c150504030c0209010807120210140f0a0215041220010e21040305031e090637050d0b0a030507120605150108010303 65
    0x9008a4284003401d440c86001900704004d00017400600043e0b008145003c48003151003102802c41640c1e910120320001702218215254890302e28000d00a0303080e1035014179460580ca50104d00c100c403c80d001103038100d001c200040f54600560600c14880750260480c08001d04100e81010b0084103200c4900e03000030b1140c03001240c01100c0d00e2242c81d00d0704080540c580b0b01070b241d21801031040d68982010345014010f104003641d03000340070b5030204898081c1d03821076a010701400c040d00c0121100f01031114007008024420740d040c4809402403058648004074000a00036070040284407a02000300155645c601c44024001400031400210481d0842c041c00350504001c0407074505038601c64016620120f90056001c00d00103030404540c0d2104c01140d8071140901442c00802c24032041541640d01034400003101441880620a0340c2e5004122044005210084c165544d954140c90f000403500802c801c03444045001007086824020140c0060072050f45080c0f00c510307500020320900d014440642001502 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 684345161 1250 684343911 684343921
    0x3020a050607081b18030105040308010311040b0117061f02030403030306050306070219050c0d060b0f01031109010e1503070201020406020709110306040c0c0b101401020606030a230102131409040308010e 89
    0x501740388143e0701c40c0a4000d00c03a42c901810b018000a0003480281c445200a0000d01c450386428031426102c003005031100c0412101108100d0003249004000c1c039002a01c1c0907410b405990389881e080d10a038035607402590384034294034008003600c00640c0003501a42c00041405180d0380c000c11190500b01200c1040301d0119120309002d80b0b071507803011015421143c2e041c00b4006220280d04402c00d041070551b1140718030803601c00118121510303507032a000f040000340035100c3d440d07120303070103910304004020081840d07502038a0181610740d101b60340c0d0f400540e50005080002a805102403001003410b41410000304180c400c03500203610005154522499841c440500b100340100c84c100c405581103800b43c402440d2007582c040d424030003409034404400038940303c0e43c803d40c800504280b16100c064098022800b465407001d42036080c40c181180b4842c1c100d0105100c011091014141204900c41d901407054900310880c0c000301081c00351103004442d9181080046034200c4d010504540c00380c51001e0465403a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 684346411 1250 684345161 684345187
    0x11802070c090219260103020f0f040f060f061103030f0c0715060608010b040b0715110a021501090c080f060a0b04121707121d0405010303020a050607081b 68
    0x1250421240d080c03001c0340c2d04c0200d0814110494090b5880e4540d070322420700742c85003190b40d09508142060005101c038014801810043c4448580701c074040c1200316070441d048001001e81e000500141c82e03059607920100071546201c2040310080039241812020f5100782013000b074882c40300800700314100c16401301041005104904a42540c0d402441c010a0381e0301c41030ac8000038250910400e400105010008206160b59004030303001c0712400c4c04030526080d5555101000e1030317005101d024070a070360790320480c1c3e03040a444000d100580b51640940315205149500742400501038008182c010303c3e224018081641042d40e83d5040080040d84407039960b14139000413141340041c0c10a00203c02d010400088100e980c0c280c10300000c1c42842070080f80ca0f01c00d01d90398101d001d80e1901810154882c050f04240c1405440c01500303254064111842d1114510041002e5800c2030740200c0040e032050500000f402810300c003e641001c00d83c41c01c0c0440c0d08006c0440c2c0a01414070306801808980000d85c0d041d1500 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 684347661 1250 684346411 684346433
    0x4020f060a030207060f050c041712041706091b011b02041b0201060b400b0702010e030c0328120f140306060304030522030503090f03010501180207 65
    0x1100408080d03403120705010040194000301c90488190307040442600300e02c078171801803074850804c0c3e4a400c4d0503c0d1824a050134102011158190a8003c06000b010380030740b1a00208080c142e44841030b481e145900448510f051801001c2c0001600682c85e403400c2541c0000400e004200d0034a44004d40c3d00000966a41040364088020340c010318090b4039a84410f5078210701034511110390000c12985a445502c10200d20030580383ca002044003805403051b919244441044444100248404080000340c1c24190b1852070703040f03441c0d8194040b07030000866902c1110561620415130140501c130020202090359440d980d04131404411033ba0036080055100f903403601d90b034140c000079021281040e00e8805040c0402c901c940300001401c2121000340301003c01d0440780185005840c0a20719503864a0440c0c0716004901000019088074040c40b0712405010407040182d409200510303590003105c410854481e04018100d030090741490010464845000040b018001c10804051391381c6209180c5101d0b000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 684348911 1250 684347661 684347689
    0x120203061c03021b030a1a180102040f33050c0c0607060c020706080f011a040e10090f0b1c0204060312020705040f021216030e03161a04020907080402 66
    0x8565a9400050583c0002c04030796a038400246024490300c0441407503107520040b034016000394400c10141140c007041003843c40d441456003010408000b5402159400ea80c0903601c020054800284103005e0218800707564450b200101d007a08948034207280b69401036a010114074014803130701044124443e10203201024010300010308407a511035130b620f006001406101c1c00d00c8014460750402080c15401211824001c44015045401030303803030301c0f220062240c8003500c000c8a0300010700c0001030f10441074010b50702a804051861285a0400014104807010315450b4504103013030108034459501d8040da804244001a080c0011010a030b00108020700349c03a520091107144a403094550461780440d17100709503103084078240045504030304501d0a80c000c01046602d41e001610204240901010406035021a00d040c0414a0146005580c0c11500404403400d04050340f803600780c0800642c180c00700034141004036041a1410305801140035020000d1500b000d2010b03520100c0c0035595501c0307400c2d03040d0b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 684350161 1250 684348911 684348949
    0x3040f360b040e07030b0106050c030d1503080409020a0e06090d06091a090304031b0311130609020307020709151d0a060509130b070c02060f18090709180504020112020306 75
    0x300380f00e04480303a41c1c1ca2640b2058901048200000c24400c0c40f40b0b003110000d48104001b03504114400341078000800d0380300001c90303001ca0303201c1c40000024909800b420040003900401a201c154680c0c008d001304090000715481a4410402c5029541d250308000710015040100010f00b9040e07803809a00e02e010004440f03484000c010b007000301000c1c0020081017600e100b41441a8030610f40340301416a031a007808000c061210040c240201410428980e1043ca403200c10081042c594849030002240e20640310400103802180d01480a800180502d020300032051a590b00000e10300200c00e80800c0c1000100e0500300c5080d0040396a88085420250140c58001e000a80e01d040050100314207d0160004036020480d02001400c164007866026842c160050714991400e65100d0812900d030388a0103030201501c11241c8540325903100c4447c0d0178494603168482813206070401f10315194210107840d40a406504241c10400140d0740000c1001c0e80401000001d40c0341d443c0c9100140c210200200c0c07104103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 684351411 1250 684350161 684350171
    0x1e04051f1818060e07090504050d0e061c050912041410020f030d06091b0f0e0a0306050103080904050f0c0405060a14030a090c05040626011401060203040f360b04 71
    0xa2080ca503002004010b130500440304802c0c0e50304080390984008035005800d0782c00011f20044102e004913000015046c00070480b0340340c0ba00303d0282040212074030344185081c03543c41c41001204c20341008000780507074022041e1801c00b4504502c0303031001c250030034550b800b0300c2c81c0d0f0602c4d4a540f8000c01c4040b4010b034003003055907160000845540c00502e00351152400c100d04250601c2035583c0010003164121342d8a5842c403925015101c02035424080b0400095000a2f1a68000000c035605100d900c0c0607600c0703001516550b0440f08204030580e00c014002d4100a06500d040c800e84071900c408407002c0b10415036420b900ca00e2902c90a0342d5018030364010420122000040081c503040c268808503060340300710840c007000ca4892060004030b407068000c00d1b030010104c1e01510350b07504134400645004200d01d00045010000050001079050007070b0b0002025900208051101401200085000d0095111802d0202c01c07100c82443c1d4020a8034444280c48001300c2e4001c90610054104c0c4420b02e4000c0c00500c4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 684352517 1106 684351411 684351413
    0x1020a020d0221010207051b0d0b040f1e0201020114070c080d11121501031401090207031701060504031704030206040b181e04051f1818 60
    0x42e12071030200f1100318181c9010b68541c0030366010700000d0307150011480c003d85004021a10014031003840ea020706c1d199195200c650f2000c42e08961961469100c50078000810002d40002a00142400e140c00002040b00951000194403c2e030082145400c9a03614910010701a00e00c100000c0110b80540c001c10458409010b00e6a111040091641c0745c41d6140d1480380d1000410003001101c0c40204204030311300c1d0142c1d50a0308003c0c2000e000b00300d16440f00c41e100c1001401606000c0d035021951806162042034441c00da05842d014101195840d5400507240e0f40140c0300458689045a81691707200d00c0c01d0041d1011254044d05032070030076040c80d0507219240c1002402c15000c1203550b039106419030760401c482102403042c0030300c508810180000d000560350010200311410040700c0028855561040c071020031294955900034103a290303044030101821940e05016107540e4a0305800d4 = true := by decide +kernel

theorem cover : BRFrame.Cov 684172661 684352517 := by
  have h0 := BRFrame.cov_init 684172661
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684172661 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 684172661 ≤ n) (h2 : n < 684352517) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
