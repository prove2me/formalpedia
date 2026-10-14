-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2706
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:29:47.707721+00:00
-- url     : https://prove2.me/submissions/6195ae6a-3af9-4767-b7b6-57e576740f3e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 486510791 ≤ n < 486690647 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 486512041 1250 486510791 486510799
    0xe0303091e010b0a03081309020a1206080307020f1507080304080304030e010e010203030a150e1e0f0105010918020c0114011703030f0406110c0f0a17070f061109040e070302 76
    0xd480d46114060a0301d410320380b05030b045640601c4c104005440b4500a1103140c0d2401308807407a00d0345801d00e05007a64004014800041d15602c08401c3c10402403184034000c205220040d40b40c13400350340c0426464603d40520034841e032010710f100f06200d0545400c8965166000035065030301e1034185000a030301c0d0402d9409a001502e40900b0548550140e51906804601600254150799504241e4030150860000a0095200041f00016882c452049150040f11a00e030b0100f11302c1e40e035444003080084001c000840f11140000100400e0341c00010703c0341610703202110b042060380507451220203441613450803840b643c60415184001d407002074816050f21b40302e80c0c060214042606035550b8a00043e00d04000000360301c004100007400f81d5120f00f04583e00321001d0750410709600c0b10303141401008546401d503a003004a02404000c1e00e0b42d059010004051915414100b964613862005004c3e00c100400c1e155448480b1004e0300c840c0019079a401e2001801444814200401a5141c40d640e200403401 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 486513291 1250 486512041 486512083
    0x1b0a030305010503030c12210103050a1713060518130b040b0105120a0e011d0d0e1f030c363c030209090309090c0c0705010804060e030309 61
    0x5645404011204203615000c01002c1d600c1c0100b414446c180c2c1315580c8501a00d4220420600908c81c15404a000354015009030030004c00904000c0c0c124107080822819800301003000e0200c00740650001d10942d86540361954072003881c032010b00407591a01c4825981704440320b0300c0c10607001c000c1d000416a00d000f610213010075070a0340c0c01034900b07010301d4200e4003942da90301c4002542c01140350300c01c1070710742d86c00c8002042c5010303118180b103104200c07007551206503041085118402908070008107074031042070700c00405a03410a92300c0102e00b995000035500305078803013114003e82031140040b210303804655110728914003a44800130024040ca12002c0400122042d80024840c00e45890170464003003140c00812064040c0841000b43c080400103061503800c124008005070315000c00c424070907c140340007185e0b1400404108417000000400240741d000b000c0003082003610010602c1070032a4800c0c20850f800c0c1c0c40b24600b0001601c0c0c0c00c4c40b5410103100c080208054800c0028079002446603000103416 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 486514541 1250 486513291 486513299
    0xf0203280f1803080d02040306180506010602070501050a030509071701090b060f01090e04050f06040f021929040506191418090604020d0c09050109051e0409081b0a03030501 76
    0x5444060b202c51415442a800800c0022801c50802482c004212030001480c2940785c2d540d0300115071410702c0540e0400141c20042c001c002041000c1c0380500401d0004049141c600320009003248618103482c0100340e112400b250b0b410f141000400c000e0300c402032007228542141c80e81e41d4003c043c04042a02c404e41c000011481c2400d0444514a0449040c4d4580c001c0c2030620704481c0c0c40003005030007102c9910030141c00c1c080c040030034070001c0e00580c0708460041200a1500400405030041c07003c4203440344a45208002c0300c1002403101101c1d02c1814001c90504192080440d030b14016944410703040b080001e8800380703001c0140e07c268400c0684d5203a146414a1200701c1c5841809103180c0b400f0f580d20b2090742d0300c0b00e500e0041007160f40581c000300301510703268203c200328041c0c1c0c0d00070155002041c0d10b500c00340015030700700101c0c00c00f62000f595510590f00b00e00203c4c4049075280c2007201d000b00c6e510809001400f41480444010301c1e00e4203110021800020070b04c55a6108004041d40000d191000100d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 486515791 1250 486514541 486514547
    0x7020315090d171512030409050a0c03140f06121e1504050c011d040e06010305060703090807020f0114070b06090c0f0712180b07050f0102190f0203280f 67
    0x940380d0003000f003c102281d600d1000b48200544c50f140304e0b5622440c155050b07143e0180800041002d800f4803000860541407902004080c0d803040703443d00c01814200300c04410390012603a105980b18400050008154a1380320104584440d0503c0341d80740c03406400b108421111b0f000c260711804c0c240c00c030304448904034949241c6203910380a0350000e0041e0840d51a5620662203410818041c0909070203000e82c4482003000075003100e20030443e1400a0300614010014448240a40c503803060040c1000d011300d0b045d650b100007191050b80c000910400c1c2c0070f017280001c0d900c00c07140702c00c030001e00c81c0800b03903144c10f9420301d41c01c6104200da260f481641c00c0e01c000f6224042c072200342c611602080111500300191540d07108002c054540c400010080c10801503409102c07590040801000845000340d941c0d030480c2046070428140c04030781070650380100b0205e143c1c10043e02e80c000484c1d005150100110031454012030941c4a0311a010510540d05540c049c0d510740840c0c0e034071002c1e81c01e640329564528050711007a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 486517041 1250 486515791 486515807
    0x1b0302011e02031603032a0e040e030912060f06030a0305033405040302030111120f070201090813080c040c0e0d050a0c031a010b03010e010909060207020315090d 71
    0x24000741d0701818180740c800d14084200c0d601545401074900b044404403036040c079044484001d40c000780d02d801131400415510030b22000c85805100c10240038240410300a030008240300e030744078000d582e60610701c0d5405c081401600e113141c0f8014040c10200200040850303a540066400d002c040d110320020030303100d1800283c2007405d140c0c90b4032540c0c19a82c441c010403151100c407603032a0710840c1c4407a4100c9100d00360401030a03030340081d0b529002c0c1c50700d0860060500710f0b08100c040390141001001840028090b03605007590003004103025444650350800c00f00d01404801030300030480c00c0e01181d108059400c42200400b550101001c82d0b0540c0181c10410080d10030036006038011800d203015804190400300b00c1d21000034018412504038460a0b903800ca10140d807903000351100c0c075050400208001c1030242542c0100f455903034060965050590281c60101c0604c41c0b2500c00da41c0e96403450420401ea011b41794001d400a050b603142650200c9580010348044411000038020092101c1d5901c1c000d40302 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 486518291 1250 486517041 486517043
    0x3050d110c010804060e060901060f0501020307150509030f030c09130b18070513030c05091b04120309030204051005040e0a050a12020102360907082a0409091b03 71
    0x40075070301a0035006450b5401d025000740d950725140d04503085c406000b084540d006000d25000001c08901d000107512000260750003c5045400c10020b038001300d542c4809580441c488810009900d4441c02d20b854074500c21021181361200001c4108011521003c015100659081e01c1c0b00889400d0015035400301d60320151100d5018020701c441002c6624a00005c40e03014219041c0589010229800030140070002d6008881003094504107010b02d007480004150041c100e500070a101094038040b0a1081c000c6001e10603410072030700c0c00f82052510810b04000116000ba01c00c22850400d602030b0340170ba8042d4041c1320301483c03e040e0318040d18040001c2104c419500300d00500b2070440e8907519803910207440b255050856400b400141420b1006590142440500c00040d1410302e540303001d1a4410005800032910034078038402008190b80e08117920640c41888024980c841c80200a580301d101c030080b06607a4410007011501044400c0240c0c0881c4000b40900034a0001d4004d44114038211006804 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 486519541 1250 486518291 486518293
    0x2010503040609140a0b180705030d05090420071127041b0f0f0e040314211303120902030d0804290609070206010b0307050c16060903050d11 62
    0x40024042a8140e005150862141d20040151114403034411703d0404005d0041c1c50024820040c4522603400b081f01a0708600f00501030b0051500e0400060303103a07594440d4501c10b001001416600c0b45d41c1e59030204035420780b0248550200041088090000c0c3c02c1254100c810310344207800c20b606446c280061041304500000c80c4a01d0b0103e044809104400290049482c88a440410101c030b840c00b1494501074441c14040d50141c5142c00512543d14465034066941450010309110120390300690000402004140403076440120905030110f0f4813508070504100e1880e6010b1000c6843d211070540300c0e05029079036510066590010180c1210705003000290b26920a20f0503e4010f07000e6140e441c1d20600422040800c0e10340101c08495015500701c0150010000108000c100e140c410307506a0410a00d20051000e0341c1030805c1c40301c0030701c0068900c0d818424080340c407008107841013068100411041001c1c85000e030307850b0005440c82006020844041c09941c800303107442440350f5035030203928103280 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 486520791 1250 486519541 486519547
    0xf0a050d03020a030b1c0c0e0f070309080c0d03020d0c0908060403181a030105151e0903010f1a030c01110c1519021506100801090e0c090c0c100603020105 68
    0x40d080e07000b03500401c0e80c407090603100d426041c1c3c0c84e03035402d480f041e0f074498910f03038298203082926180903002051b0300100c00c40e0b40000e007803210b00700d09103142e558041c03200d082c009403283c3c01c0d06120443e40a01616407000344101ca005600d10355058000c0c102d20888240240502103200d442a1241442c0b401880400d0f4000400940442e00c501e503e002000e00d03980424103881c2d240c80001552500700e81c2d286200e500000b004006504109401c042507030328801400b42009116800030f000d600407494995014000882c425010f80d81c29806101a9900310388100406003e00901e40f13080f40c40300041e6842806a21000406540901c06151003940301d070002c0c0c0003604400040050f10070800c181c0e080026000d04c20041800d00220b44c8041c243e039250002c0c61124140c0c1c110402111f4010b06070b50003220740ca2110828a40c011ba80399041d9002d03038030041458005803004625240e0024506503010044070180001000c104c07008090340d1480030700b80c4400f007002d050341c130007903c11502c80240010410 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 486522041 1250 486520791 486520813
    0x60b03031215010e1504140904081e1c050f010501050f19030209090a0b04060f080d1101020702091006121107111518090105030105070c020105030a060e0a0e0f0a05 72
    0x12501c05007010070141442102c135201c01c1d0224032082c0500c0040c500c441400601480002603880c0407200031501250146900d00d031550f12400c0e01d009101681c1e01800d48518140e212551389400d503800c9284044c804025400c0034080403020b03105c2600c003e5803400c00c41d800401c042d482201101c030416140e10404e85000100003403c0d51500d850b2001101301582800802400e546003c4600e00804a4070790101c1c40c00070481c2084101c40c8194040001360100d0101040700b08004900798000340c4c00d07804c1030310709051050b1116029100c1c0c0d000003076000f40d1032820005001c80008030b4406443c81540c50b400a0041e404c2c18604840c00d0074801c1043e000180100c0001411030301c0d0070b40740e13120043c04850400000c0f91294056800c44e1030440040c40c105101040f960520580711401800110001c0c0028202044003030920b20300741e41c1c0641005000400104600c00301c0e0003030401031200f449210100d01d44955060010841c1c0400e003032180c040d02880811030b50000400091954214028240319400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 486523291 1250 486522041 486522061
    0x9180f070c1403030a0b03010f0e0c0d0c030c0f06020f0601050a0b0306010c0b16030b0102031c05040c0f031b12030e01080a0b090903090117040b0c090d02030316060b030312 76
    0x78201048800800d0400c00c0d0100007402e10155000300e2100802280c050140420142501d004e0b2034040155854040742945074000002c16240d840801d44075560010382909110030109450741001d0f1042c61883c80010344420703810114012500c3da42d082e9401032000c01c40741c070b484900a02c03409500409104040c08036546407402550480030504120100b1a020713694131005d5001102e0114803943e80100054090ba0140180281ca6800f44082e600c0d200c0d00d40d00500b400501851112401642c0d8000901000024009240500064103280025075074910746200880074071385005100c09454040040e040010b10082078240c0e41c152243c0801c411803a00458230420018803082155803202520001610340f0031180d4002c0380c1c01c2d4040d503950841000003400c0d81400032241c0300004103000410001c42c0709925180e400c841d00014403039517202c818000425864032000040d6040c0000581c900600d21218442500070303200d0740c400d02c200c480b141700b0142c490040500e00098244820002282800 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 486524541 1250 486523291 486523307
    0x7150c05131404021909140117012102060c0606010e06090609010c05011b020a02030d140f09010c0c06080618060d0602090a150c0302011a010c060b031002030c09180f07 74
    0x2c0050710060406907401c410341c9032515559840b0010030008070040c0181d01c075541400e5041c2c5420b08004255000351809c00c0c03043c5c2c00501c141d07182150200e2000600d41e005a5034420390300e070000c060075100d0715004400c6885020a07101e0a0108114120189040c10200d042e00e1003400300504490801202d80300646444a50240888213556541b0b0395603a4810180d00d02420010741340e00030640e40000d84181031038031594008500910007182001010343c0318480449445c0a00500c905450340c40400041e5021654080004d04240c40d0100c081340959102d080184a8141141d4000d03090180f007451140d0300100766034481d00510321313002c888042440c3d42c00400003c1c201400780300c0d030b0655855800030300403070703949810000520202d00c940a05509001e920b004419818007914004200c6001824681c9203a030020020f5496200e025119501805805003070a100c1c00107640d00c1c50302c01c01340582a032010521741d2140142143c000749000d032181a80307200e0f81031528408059102c6c544183d4180d4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 486525791 1250 486524541 486524579
    0x1503020a030b03101a0303070203071214010606080a0f05011401180b0a020607080a140106110c030a050f0d080c0706020f040b07120e0d03140306040b03010207150c0513 74
    0x141c1c40311a00311542e2404c0200d429030503d00400000c6080d69541e072411000c540780405817099009015560150343c0109801049401000080100700d03064503103c001c809002d9101c08081d480c00e07000281042c1c0002c2c4140c4249042d0008000c02c00c070000c086000c80d04280282c0c0001e00e0000d4007001d465008000e000300381d00542a01c0503c0c0c0b40d031000301d440c0703a0340869801001a005942444555038000302c900390011f20311081404050225420021a140144240790400280b40801103180c00c0c1408012a00301c80501602c04e441d80c541880d40d0f403003503104030541c29817084141015110f03110f0444c030780c01500d410440c0e03846c11046441d01300203500641515880030108000001d1400400802054801e10071011100c2e0a80c86002c0609404003021f4100d0042c440303164808002580300c0251012007400c030b4078180e101e031100000301c0d00404240c1801501988005025414040c401c040341c0282929170740144018109400204c4507402151a03000c00948084030520401e031011540c42240 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 486527041 1250 486525791 486525797
    0x3030215162312010b1b0a03020a0f020621010f0f0b1605010209181b030f0f1005060a03050f09031c0203060d06020f090a061d1e03010527071503020a 66
    0x15600f0b4007094100d042130748004c0c250300c000103501c0a02c01032844808880c3e0a81070141401da0b1031610040d4583d01804001420300011004850440d40d9010507a0702c59110300d002c074803035844103040c40b000c0800203025481c841d40d0303400c0000441d260f04003140c90555040c1c580c1203003003130702e0310001541c0c4001e1101c003118a550240010030701c9481d41c0b0032070750600c064440062064240840c07200c1c0308134084800b8540c0c9400410405c9014030390b4042c2c503078101c2d5580e40751858a9480700c40e8000c40d0b00c911740246510603000160a050303542d2641181c0c0c00f50940f626a08a83d40301c2c580e15650364414011020401170074180001c40300480d581c0a1503001c1c1d8050903003ca0400c240d5079407000c0b039000070f4040d020312070b0208040c0c446040a460220261900e400c0200c070140900c0303051100c07155012011031050030030500c0380e01d9030202c0416414000e08060024080c40c205503425076007100b14403280660105004200c0310304440b000611100711805004070741503e2010220440103035001680500c14 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 486528291 1250 486527041 486527047
    0xa1b050106031703010303030b0a030f080325121407020a1515090f05090615040c0c12050903210a03020a0e100e0f12030d091506030302151623 63
    0x4154643d0001002c034509040082d6a5819442c1c0901150304016400b40292640401480080d4004140500ca1904041c006880c2e5603280d4041d01681c00c200240d0740e0042c0c8140c5000c0c489900300400740c06c02c0b00115002c3c04480e81400142030766480c02c482840051744aa0303110340216200207800c0e1120000400c020800644514003085480c2c915403000c0f1030160b0764000030342010003c4c07107032036040284d0340701400513400c00e551490603610442c04028892661550888000f5006482c540384480c1e01226100c1d00102562018210341c00c6104564041d0240355101d10901c12000c1c40c40c03007070b03031511442c032400c202111074201d000f0742200e55103006000b4041800f0b01d00d43c1e9038240c02e14000305c203aa00d00580c2400342d82405541e90325100303042d0013643c480110440040e0040305465100c800b40d20005a8004282080800c0303c1d07482c6905e28165181400c04801c2c158049032494020800b07422060b1a078444980307211111281001a400099141a070042250390560990060307044060407141 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 486529541 1250 486528291 486528293
    0x70501060f050103050f070c080c03040f030b061503160f090503030c0f010b01020f07030204230a050105010807080906061504150302041e0501140306010513060807140a1b05010603 79
    0x108541154000e181e012000780400c008640e4540550b562192407450400d200e82032848018080c41d000010083c10400d02140c00b074032380301040040d14001d0074050451540281c0da070034406448942034484074026800007002c2010a803024003100d000358040c00808620906021041703600c590702c42102d40c02c20418100016140d80c041000d426a60302090142c28841c40320100c0b5400c41e00e0000501e815900014810100f083c4040f03100000c481c7c06403400314502103070407413240c3e00140e0b0441015001c81c0c0c250512509007901d40c046410313070b8400e80752414251241030301615031700f40803a06000700d0750250002a043e0b0070708204a003031284d504209241801d40310040885214000c05d034140000c2e134040b5041011f842010001001000041d032611681424000001c9c0201e03030700006d0b4010b200c40000070409070b901c40d07000c84680d070f24038240c281c860039200c410090180200744d45400024201c2c00310b107815005500e0450300c94055a449016a00d080c04110b0b80a464018009480035580e17084000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 486530791 1250 486529541 486529543
    0x20607020d050c010f030e030417010f050c07030206093702062709041208090a0f080c0607090b180d080a260708010b030408070f1113050603030409110705 68
    0x4684030b100d2000381000b0100e0300c000405003074080f2039981c1010f0a00101104450300402110f0503505480340310007208207801001405810703030b240c000c11b4261405c030400152205550151541a100c1c1c3d0a44400d40c4604204580d21040c030080e40a81082c07491100580710079121120741600e044030420341981c0c22607000168543c00a400e8548021001080c4410f0760000604407164840100d56940e06420103841d80110045044070304401c4c8070b0643c0c007140c8044800c002c0f4a0b0306a501140118140c87e0320325140f120ba8024400b0f8608a04c5850003090340a4000c0d0b03040d43c1560a80c1234014140301c144890589803240310211030390880d10b49000580402c16100052400000d07945030300559100c20003001d4041c014045027054101095030a00000e039521000750390466030030343c50040e26134440f410111b0300c038828108010484010f6010000030845084817072100258100c42106001a10040d900255101100c845515800c204418011074849a02100a203110b041542d400d248486d0ba500f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 486532041 1250 486530791 486530809
    0x8030a0e1f12110c06040b042a1505090f10030605090f060a051c030c02060c01020705010f06080a080301152015060d0b040b07050c01140402150a020a0305030402060702 74
    0x4080022004a410b001d00c902900078607512850380c204003444c101080701c10030346031440580001d118502076030200f0140441c4150b450190203000c1000b56901c110f184100101561510641c3c00080f101ca000d4a107060062040e030351100b50240291090030507440401c401d080c2040556414181c0d03c200c08111a240d05e09124420303900c41c1c09a05d6a4100760b82045180301990b0f1245100c0c1c1014441d00390140144402d4404165243c05c02c038411004502c0024294007a4014104441d8030210300c0c4001c0c000150001164005003450420070151141201c42e02d60042d0b50002d445400d0070001048620115003a83ca4140c0c1c60340307802c4909504040e2210003480c1410544a856485401c00803010a03904482035003018040b40c41041401e41d40c0c0d06c1d0100c20303030001d0001d1b00c202840d8001414050065003102e90b40d540b80f40003006040e82502803c40004030a840581c0111418503001d40980e5900d0103e0b24205140e800401407071849560454044d48024012071700b142d401d100d0344005031200c08403 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 486533291 1250 486532041 486532099
    0x60e011e030621150606170c0d022215020307140111130303030b04090209011205340807060e130b06070f0201170c09060703020f0a03020c0310050108030a0e 69
    0x4100c0f09004142440309000b0075052000801c0340c6021000c200700d6801005103252041560340c001030541d40c0e65150345490050900070408680006402c0c9500c001c02005450144103640c0540076031910b07450b2084401d5018210b000160384100009404500300201146002d802c0c0000460510700c0f01c0040c10039600a043c21907031000e1000d90903c20180c16002e40020700314184c0341000b448a0b140c00240d1248818810b8102e200f810b40d810800317124041c4040901340510210551021520844140d910060110781100782ea4843c2c0000c180070801058400840711107542d88480158103100300700803d13062903201c044840e9211302080c001e0315100060300d00640182045240340d280d030300015140803211404c030444c1c59a81401c200e40081c54109440e880107007503501e030781c40e0070407842c041c1d1400c0c98080381d000c014405d002c07100c030406a00107900040540207400343c4401240310360100085e250300b0300403a807440c3c00c180503615103a0720541d00102c0c803410003005081403000d80002e1030090611168 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 486534541 1250 486533291 486533339
    0x4090f0210200d1d042a0e030102070b010303030e0304080105011e090c08071b0501140a1503030804150204030b0a0b1228050708030c1006060e011e0306 67
    0x401d41d00401c0c1030850301d540c2c825100a064501894800100401651619a0342c0c2521503160714040b61250b600845400c1c01021401c00350458090142103811005050600002e0991680e1910384c1418001d0360080c5920000c0c2c140c1c2ca900b169410713406003520400c0c80b6001d100611000521070402d014860080294086035490722010302c581c0c9906101541120130071038104280c0c00117a9074001c80e21030303022409140141c40c00d071603480c4900d8001d01660303015202b90b00300a0071082210200d0303242c80c0611a600d0080007110304921194000c42c0e89484090089a40070001034003046000b0070704491070303208400044c80d0035129030b656211030000f691103c403c00d903110f4003501c09060503664101c2c0140150020080d01e0704c070035403403040c403080e09214060301200c0c2995407040190800c0a5006040c40b20182c81d218080c0588803a81c0e07960426030309850506042c00090761600448051012202c1a5603541c250075404030301c03c160701007406420003016691840082c10703035103d054000d40520215 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 486535791 1250 486534541 486534557
    0x4021518040b06040e16020f03070b061305060907030216020a0306090201020609010e1b180103031805180406020721020a021306060f1d040603060504061805060604090f0210 76
    0x803050004403020b000c00d6501031407003000240103440e158002c0c1e81d4000202408407142a4030150120700380003d000d0440401c1c4030109502c0100309140c66001d20074001a5044500b28201410300010b6801c1504c4c0b00360407400640200701d00510036001001860742e1021408840c03c21a80810f6115086501c1a907605950b202c90f0821503034103000b095001181f0030001d100e40f29891060340d403070340f155143c0408038041400030096140c4815000604403d000076611071503680d241005021a0780841101420f12158000821306103440d0307241035031200c008064050f441d82d4540d5040000d610141007039a0704519120208060b0204450503d0321498503070161444801c82e2060003000703030f4801401c1d200b0030b050010501106501c6060113019442600d091003519144001c00740291000703507241c0e5000390070074402105024031031300300c03501440c0b0809003000b10014000c03c030001c407001c0c8100248982c016002099032403070113400c002d581c00d0040051081c50700c51540000d5450810b420300901144101c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 486537041 1250 486535791 486535837
    0xc030c241e0c09140f030304060305070f090609051e0a0303020f0f070e040b0c070501021909140904021e06030f04060b0a140d06060b0a0903050622060203040215 71
    0xa01c12041034540c610814007036400c40c0e41c405403ca004034098901e15100c18104002c1c1075441c00885241410080c09032540e594840c04000c0140030100c070840049039829445e00c180e04d01c249c10603c00c41e44155500114141013004103c1c0c4d00c08110003002c5440d000581d09080340c1da079424501d000714440d070028060b06403402d40044c14421105114210f54001500800200000400361580903500c80d1000140341d940e862101703d103001c2e20001070243e40c07001c200d0300441c02142c0e0030080307030240907140d102c1a6650782620711040d403004e04009400c6181d0402046c0181008441c903403c4c200110624070364001030b000460308580048881c1400c40d1000e1060006100305c0c5d12511034100000c3d90441d028604004803020f400102c00282ca000302180b010400c144030040d40900c1c087d0002018860ba100c501d0b40c4001c02d500114002a107aa0103080003103034400443d003c5d14400d28907000700c000e1840402da11190020341005200740e802903007880c007064103c031030f0100510280850398182c5900d2446 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 486538291 1250 486537041 486537071
    0x204140906100b0304140f1b010215041211010f0c0314010504021608030903070f0302030703080f0115050d0f020a0c11040519051003120525030c030c24 67
    0x1420601408550b00000d02c20300a00301d0499901c01d4109004201140304d200005240034112802c004d402d00941e103ca0072140c0c0750000701000b94109a08882e12545e522030303000d900520a480060a22103190104202c050143c00c00d8419261290300005000c0d0908201364161030580d010280080d69030000c08500107903c80c1110701400094508500345005d03044c0c100700180c0c505e0300c003404071030000c00094812041081240d0900307a00603280e0030b060120f0310f0702a540303400c5010220041121400060410050950300c01e040b110044181046d8082c021400e03180c1d0350001c600d00074184d031111070790308112060380010000b151050b81c94910302e003550b0604581e448803075591a4859400d00017441000070194030902c8040c81c0c02c0200080a03100c0f0240c01815200030750004280c051110358090009401401074490319501104c44403540e44104540c8801602c105030040110ba0b14800540210f0303c41c0f0b4211040d40c0c42081107010010381c0200400c610410700c1a0010000e8540d287e0b0ba4101304 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 486539541 1250 486538291 486538303
    0x70e010207090204080a2411091221090604170c1503040203030a031a0a0303030e0706030603020a0b0a140d06030314091f030b0405040501050604060b03010e15040902041409 76
    0x85400214101030800070f5058642408403009012681080364001c0410440030121011a207600010003c50629403010002c036084607271403e1103078400c02d00d0346504580228500c42d08a0302016210341622505940d8506a00423203082e5030003030400c0c840410464003072034107525042c1a450041907000c2a80701002a8038240a1500042d0003081c0300b40001078030000b05488441c42c5600303004c103103844c6044191483c4c0e101145025440082c5501c004240b68150740320342c4804028100751109151502d005806440e01d41c44029003108660400300040560b103400b610b680003003803421211807440c60001080540201314104a8140c2c1d0f03c60070410150020001940c46000718071003400d0101e22000188050b800050140d07c1c0710b401c0c07242c060300b580300784c0c84034441120042c0100098105420031900038101101c42e640202d180804c04156900c10000390b03412110003849510040c0c4e58402c0c0c0200c0303681c10100d05a0070640f949002e0b801666180100c803c1c400074441400b5543c40c0103031400d0700c3d0079 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 486540791 1250 486539541 486539549
    0xc0706080406061211150d06031a130b070806011b0303050406051612020a05040e0c090307060e130e0c18040605060a1a0c120f0304120e060403112710090515010c02010207080303070e010207 83
    0xd4a00c4bd0703104005851601d41c540e100d00300d8200025103035200d200503141d101c5590072031039103038011f101010201901544040d000764010401001643d0385c1500001696a1229400020500c102c04110202120f0703001408080803e01d40303141410350f035502d944a2110141e442c40c061600100e81a0410704041007000001c1c02c003842e10881108103000410902c44402d002041c40c59251082070007010030800142507a0b0030050150300e20740c0c40c2c100844000550695040758113508100104807580ba140c4445403c0c2d5901c0040c07040d200b521010301340440d5104071680da0282c0509000c0c1c0c40d41c911240d014002c030035030b1400d8070350782c0b45498a480c0440d030300003401c00028007421003020078241d221a41620107990384209038102d0145032500040522095000b10180d02150384228030302482c201c00c01c607000360941c8151180440d15060b4000554a0441e280d80001e4131070340c4000e149600c5413a0b090300c42401801940c1000751281402415076004540c42c03008215850300b915020359040002c40b000b0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 486542041 1250 486540791 486540811
    0x3120a050f040b1b04140103060506030108070b0c1f05060405060a0b03060112200403020916051c02120a020309150421050c0706080406061211150d06031a 68
    0x151400c41516284440c1c00340c00076041000c0e1a0019040502d03100640d44200030543c0c0682d10f85035684103900c140c3c1d000c4481e050019080003000112404c02600344ca0507a0a030f440541499410320a8510380d239003004011403440d01c9860420011704d6840214416a10035920307001c03503103242401c103100a50b00090080c0b03008156030310042100c6c00040e02504e403c02802d18010013422030141c8400301811f54081c0010741c40303040040313414100a2120040049034030984a203000c41c4c0d03c41300c2c14012013012a01240201c0e1081043d510002c40031019180540c0000c040103050418085407241c15600854002c1030255000042c440000010000c6840c1c6114a022060207880d00f40d4442045981c0c0b003805592002c0c0301c40a04080c240a04c05441400400d01e00300c0d11455928040204000c0c0c003614203a94151a02c1c002181e100f40c5056100f1031641c012135810311120b0010700740b0042c0c590b411840e0b508820b051002082c44141b0b400348100541c001ca501100c8040078244241c1c0c166800f600c50422 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 486543291 1250 486542041 486542051
    0x209013e0a02090a0f0227040e03120406020904060305010504151505012a0206130e0105040b03030909042906040b031c0804020f0607030203180604050a092c03120a 72
    0x183d480c140c407aa4070500040d00807900002d464140310190241c22950021a066500c0018845042003290710650320215028050307000040209a1070703109401c1c540411012030310002c3d021522540003808030000250000880c550b40791281c40c211001590200c0d0603409660010541d03103c20300803d000006031164507410a032038040064600c0b50384c81c00560a030107440d2403417042c40a81410b00f404035500500780c0d0760f07a00a008074980c01481c05004071110f00140c03100200b16400c0c2807007180542e05c4050001c1d450046030700200b01c129040144100c1e81380103201d8030300c94040076061060145c8241142c20a0a07410484104004e541c070f1081058044c0e03020341c441c54012500b0f100328800041490410300c0064803240080b070104580003908642000c40003858204142d8004010001207a158481e0210b000d00da5003088814441c51007a2039119032506070521084520350b1190490104c1030900d00e0304810030702c8181ca02c1d038500c901000095000800c0019807a940e0450460344000d40700384c2041 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 486544541 1250 486543291 486543293
    0x5010207050405090a0210110708011b05030405010b060a0309020423040f06110f07050d02060408040b1602030a0b07080c03010518040f0b0f15041e0209013e0a 70
    0x150310030192164911858441010070000034051000d01d01154014004000407800c1c40405803020203c880075036020b00c950400040c44a10610900040c5400410b10b02680340c20314500b1142c03030300090401d5034255a114545640c0d9a240340091040d05a40d80f00810808418010481100d8810640c10410440e01203003a82d401c1011010311760065020200382031320040d5041c0500200003910f02601d40003000144101501343c11030160031018400c504503150a0303098001280c4501e0241c600800030700060000744800d03040c0c10040e01c1900d500f200416a14034a9030006458456007082c2039440030000c806005159900c2010b9036840145c0300d40107851540340101286248100607401d04000810034046070410100d44024400e05800c086c50182034201311f1035030455a4002d031088074048220b0900a949400e117409020150b030a20114014000201642d502c080d40c44240018100921946181c0812800398044034004103031901d03072171042c060702c00c00c48010701d00454045040d43c4032110080c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 486545791 1250 486544541 486544543
    0x100e01090b18121906021c02070b07030b0d05030d0e0601060914060a050904091109070309110f060f0c01060e07091512060f14030d0e01200703080c01020c16050102 72
    0x1440b00182a50b005190380b925045090a00ea007900c200e4802c0b00144014906100554000e440141d004071200f0091091190000302244070b8103070003c06400305c55000400c0b0724004c0d84940e40c40d50b000f9040322014000c9a0b2064150340c081d40039030300c0040c0d90b803440c000880300070031819014040078106850194104000095500d0508504910441c000200d4001082c4100151010341401800c14000301c1302a00e007014440144480c0305000b00714120000d16402d00c80e015100b102c0c1d82210031382d9000d041c40018804000f00641d009034114004011300031401200c400100700c47c078103a10000800724142200040c5106000d0045000c0000d80300e814001d10180020f0b820800041d4142080f01c02d0b00820200e014101e154440b064040c508023000a03c170b80740100410410908500f034422030600c84005541c40213991940600080012000070445542405c001102c51a40011030700200c0d0760b5522284954408200301c1c4480e500484e030010060001c01030602804103004400810a080100003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 486547041 1250 486545791 486545827
    0x60705030406020d0b13020a0f08100909110d050708060c07020618010210060603020a02060609011511010b0306040c080d03111806040305060408040e01080c0d060506010509100e01090b 81
    0x501581d500046540c40c407800c4d50b00c60040c000000d4a1140345e0114440c44100a4103c1810200424030844011050038402d821491041018a0400c803040303040c54130708002030040d00c00450700da011008401006030380b111f000b101c40c244034500a0840ca4180104282401c1001e0721006001e04180000c400594815042c0c842d201c1d07001c400c03a070601c01e140e00100c0c94100d41e5804929030350720b81840407070b4999050b0000d01c803801e5143c0845072184c40304424001490001d01c54034000020110002d090f0900c1140c03015004003a40300080380b100c90b600c00003400d00b202540d040303500c129180300400920006000c4c5e0f80f210b40083c1820004640a46005a8103112312000000c0020270484403151942e111025103001d141c1080071034200d40313454a441081383e4824080c290340324203560000904004c00213501c0c05229800340c060610030075a07a56002c05040c005c1d002d00e040c4041406a201c00d52203e1140b1b8030f8824865032010501145140094010003190b000744500440070041c3d01c00101043c988 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 486548291 1250 486547041 486547043
    0x40f2d05010e0d0218040501020c0c01090f030b040821010504060e071d031603080a020f1603080d0906090c17030903191a010e190501030f02040905013201080607050304 74
    0xc09160f1a4441c4005402000035180e4080155100c50034013091120550140c22000e11807000c0340c0344000c01178011343c0ca01a103481034003100c210130201800025010070100707400900c125505070507c00410710f400c0c00003200c06081003007803080702c00420892400d40144801040316509001883c10103010080182d2400b10744140504100c020728119600d08100d080c10360130380b942542c112a9100e01e4580c4095200c0a21500144181c05204103866004280308248540881011021910310394402045403c000c1502c02d65035038a0150030003151642c0100d84005201e02d03560440d2034204110195140100e10900940d40d106005612990300d0014081c0350f01e4000112004c00000a45820b0500091005a485038141c440000195500c1302d0900103000d04900280c082d4003142012410f001c0765400d2102038032002c2640c5481001d42032550207030008602a500208800300c83c0c1c2c6c0210540e450603d9411018101c10704401c0c0e071960b07202400d5001d0440c2001410840c240000014078a002c0980 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 486549541 1250 486548291 486548299
    0xc05010609181209080d02012c0a03110a080c010c1715010804050a0210020a1401200307020703060c0906030e06040809091306140103051b01120e0102040f2d05010e 72
    0x60120903004c0c051034070060610000711402c01a0400c002800303424182d01900d10060342524031a1160f80160510700984005c800030310204600392400c55009038070485144013409101484000f095a0400030f0464005501c004a40c980e943d0500502540c080b030074502c6100d01010600c501c41c4859a81c415144009180c401c0141e1200d0800078100200302038025484650710440314000d540116441c0714050040e81d1034076100860b02940d60030780c2e2000300308120703941d0640b0103203521000c2c0001a5811160920446001c01c2d180c1ea2120122040c58a45402207441e010080040079070601855507500048409007041e4205aa290b80d014050040c0152041c01c80e02d00081c4891000071080540d01e0300000b05200d0045c04110080210714207000c20b40f0700e4055540031220b4240702c00000703903141d40182d45005444070800d104c5030040c041d43d0038828565408120015102e100e00f030180c000380a4090ba28910b51a007001289401c040309900c002e0000d04000040220380c1e0000c0014403510000d817 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 486550791 1250 486549541 486549563
    0x1e0c060a140f0429221d160c0c170a0b0702011505150a080c07061b08070e09061302070c081e16030b0a0219170a0905101109090103030c0501060918 65
    0x205c1c0d00450307600e60760007100b960010405640480711a0702a400c0c01107002c60849030000b204804110b5164500641c0508000c403203200401121040d0180a282100900c0c20b490b03141a440d03803005280f003c103a84940060703441c0c441044039141a452494000e1204841c0360b08068580030480714540119003d50301480342c0d800c002482c1c00e070800d0032196025032007802000501060462207060026800b00b04001500c4400014200da0042401580c000070040c4550516907402003007000720000405074840094082c024100004c0611440390090300c80e950280ca905c0c9a07911741803104400c6020400341030383c011003014456085510794401900d411440d825000d0b0b603084e0300b0502a1040141c09680c040781203c0305036040e0390000342501c010202c104018800e441e082000307801c6c1d40792034034083c010350025800201d058007036038040804203040c600981d00f0729850304005680714500b64802e5001c1b4035025210400c0140070300c10040900300342c4404100246c400d414511700c152a40400070a940130074 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 486552041 1250 486550791 486550837
    0x10306020310030503040305030301030b06220906020c0a0605010509100f0603050703110f090118060504140d02040518071e0b071103120403051e0c060a140f0429 71
    0x1041e00c8000f0f0354000003107954841c1ea91401c1b07962503000748010780765541c070740001c1082440c0c031a0f641088550b41c101c078800c1e1010040f0912000f0002d82e82e04803051542000010a0913605100d800b400c1d0380a40e03000a610b62400301071010481000b0103094001d0a038140c184020044004200241c403407a16000905a41c0c01d8410b90081c0500320789100c1e1088003003480c2d0200d4a01100405071464282e0302c40c0034032440350350050510210341c02040085801400306102d203010010140e1403082c0b00034030030b14030340f02d07250003040440c0e509540b481c2e0001200740981d413000d1400c2040100400000d02812424011400940076403459805030816030440050003509100724115400d01451009040c0c1d075800108941c003174213582c014482120300c0c2c040c204519480404003030320070340c507180018058003548462208028103980018602824840c82104070880c1000e6100030f00862107850a03101c0d82c0e00e080140201c1003110120404202d01411010320000c040818140d9000c0004105450484484 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 486553291 1250 486552041 486552061
    0x10809280807021906030e0106290405040c0e03061303090b03071101150503010f140624040b0d05010512070302040c1211280822080316140406080103060203 69
    0x14500b02075800720355a0300100501c22095a40301c201e400da51804c02c483c2080c07203050350907207140c1d1240032081561440c40074803040b100e404031b1144a500303016043c030b4141c44000080032901070340c00440000d45c4110716402d182c1400c000690f044a0300d8840510320b403003255002092004140079002e01140080003007403409014102c0c403403010300224000d010503441010a900b28070500d10459103c2c1d0b0a0420840740c0555902c90a00c00542144503043c00b6500d15081c04100c0b051071081c059200355200420112201600250002d407034180708a03503546910750500d0b000d070fa00681169100390117902c07201c0d00c0c80e200001d001c021240d06407408905075004034800d4403400a04c1d982d4214050802079800301d4080c95030020114119a0112105112422010803110a505403484400f28045038041040c0020f01c0d000400c0071208102401a1800b05558031405d9420a80d048031f20341c05800030111409400110702d200f020007201c5030508042ca44480200100030605c005040940d0010200e031500f40 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 486554541 1250 486553291 486553297
    0x110303061c060903110d050403080d0c02030c06130b10050306040f05030910050c3f3001050f030a0803100f170f2b020106030c080a020108092808 64
    0x500290304200f500351505002d0030b0807254150160707150051560690390140503034141c9050b240c100308007034100012098407800524031074000d80c2c01d512003845028a03091342002898070403254190003600000e0300303180c03241001e44045c0144d51082205041030000b80c4001981e0386d8000d03080005002d01944504105007544110f07041e85800085540b40807200540000092012040304821503500b070300c031441462201c2e070206c09080010a08152040c44041084038881070050021800d545490360481d0911001d6910b0001d8407031207035030751007102c0b6404120b00d0800d00520007030310021950201c40d4000b070b499800106000300300303002c08004103002500f0002104042c00c4000502c5d580c5c1a12640c996000c01e41042815980340b003070070789154403014041441001c00c6070b449204036603007111a10640035100303051400002c5650f640340c00008204450113460081081c1006003020348194000140306500080c4507120640c404d81044541d2491010050000e00814030481350035006440c120030b1f10301c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 486555791 1250 486554541 486554543
    0xc020904060902060d0c08060a05181b0a0f0e01090e0a020714030c0c1905030c0409110901261204030f1712060406060c020306010b031807090203070f110303061c 71
    0x200c07012515404101181d400201020811f441e06c40c000c2d85e65804202e6000d910703001e025041030400010060100b0400c0d0f42d00d401003940d10044034050b6200c0d01c3c1481d29088545007074001100c11249445a13500680d442c1a411805e103003500206040403c0c00c2600c640c00382190001030380c0021200240301240c0390070280da50407241a699204c4600390300356a252178201185215001002008624041001d860750440d107000e00a072511502940400c8000d0036502820f031808010b96048845507925000350340e000c0c10212150784010703001d921840c0b00c1c02c0c078001d1429030f0f03942c00420407446628400e01034604172907000f520310341421024944002629003001080040d490003103406209289030f02d4206100d060160780401603a562140129403072040240c010750580c0140c001840340b144c5a40080d80c1c071a000d00c100b6002d03100c00d444a070340b50941c964010508030354084248450580d00900607690a1a50f00d0108050490350004507200d21018108511845000241c89810002c641117400f1807 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 486557041 1250 486555791 486555799
    0x70c03111008360c04110c0a08090d050d120c0e010c0f060b03120706050c03460204033e0312070f050d0305071d030304030c0305030d0c090302010c020904060902 71
    0x2c0f051600120354407042c91385018803490620141e00d2041c00c0f03030340c00d403500300082c00028503102c0500d4584102682c0038a01c91a0040342000013240030481c01c2010000c0c0300040e80c0c0c1d1850f02178800401030b00700c0b04404041740810250840242d020382e4850b050440079a040304452410b90410b18100c00189094080130350580a50b2207400c0c040607014025003416402881c050045036580072a0000601c02141d0440c011401e0740309040200c01c09046038001c29410441c000c0c0f1406a0408c052000c1d180414010b03211138000a05004205e45080c0b214614102c440e180c0c610700c14010a01d40305d00302440f04601d995069156500040e987c20880d520401c4504149107036034901c00e0038812251410300c1400d480500c1404503041e1514428810301e44224280d030b491000302441015045030a98400090690520040c0070100204c1c02702801d00b0010b500c184021684d03148800d0211003030b42c030f41c80320304c1040c003103c0300041000d80d821030b0801410580c1104e035441c0c02d41d10344c50054001c041ca0f40b40a500 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 486558291 1250 486557041 486557131
    0x6050109050f1216030c0b19030509010b1e040b030a0305030f1f0f050f150415020a0b09030403050d021f0c120f1514030a0201111002070c03111008 65
    0x3031000300c81da82010340340140d038102c2d1410f8647c0f91108480c80361280e40c040f5010481ca0320741c990782c401e80c0582d8226542400110301918614000740c1c0a1820092410f20400c40c0b0f10032016034500349c40b4900b00030340250090b00d1009850748014141c0c1c04010001e0301d100310f03d4400100c0c2c1041c0076000c2c0765140038102e01800317000c1e2540300c0b000c0640035600a850007451880280c405900d40301320101c40d40408030b42c1d07840c5464186000c4421ba0403c40c048407065110f610b0b03450740050b4212141d03c2c42940810003d40c0c90b2442c506000d0b2510a11107002c1041d034009070000409010ba1000c0211440b08500000c500ca0390710a10880f8444d40ca001424152407404500f620f1200c0150440c100450000302d500f11996190044a112514220a030580c954415180704005500030902c0b0b110190304001920300d0300340d44950701c40990b0300050046602c800c07040700601c1000f1285200401d1104290b0314090b42403036090b800b0342080c8000d00061408130240c0f12143c000068140c16400b0084140b683ca20303 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 486559541 1250 486558291 486558313
    0x30c010c0e090f090604081e040b181e0613080d0306360c050f0c03030910020a02100911061b060106020c0306070513050d050303061306050109050f12 66
    0x700c0004420401ca100e10422004540d10302c000510081c00307038481c0006440c284e10340d0340e0348031040d60088c14444861201c1102143d07010a142010f400108030401546580f1000303600708440d420700310780b40c040c4510080c0a21200c200344841c100000d0540a860250360340f840c1c2c1900303402c80403c650080e0001d220b00c2c0036400485525405c05011503246220102207001c4241d2901360b414101510601c2c05000700503100100306050300240c0020650381032031807a042c1e0711510818075a214136070107900b661001050000880e8100071984121581e150210704001140380e00941300c20561042500c220f86541041003845001c5124030400c1c00000d20055076003a00b0b6014007004000813a80320b207a80198000050b40c603002140c0c4469209005016013056500c0c000180c5540e04401d259086031055000041540d450702d1a092103c11702400065480b483c1200800c2098400c10300d5202107039040c0601004142d07000b40c120800d4401c11104100c00300c4501010550b61484c0060340f0000344501d00c8003c0e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 486560791 1250 486559541 486559547
    0x20c0c0409051c080105030d05031005030625020c010c151b0903170a020a14070909030e031e06221a061f051213020409031d09130212030c010c 63
    0x40f0022203903402c07015808a40240a0322101000d1003120f400d80c100c11440f6005070310031002154480d03002091004449d8840340400c1c5084011078103d2860300311034510b842d4103081a481c803030b500c8003035100078040083c1c2c1d400000c100700880f0b48018104d5aa081421102d00030b10780041044c0c0201d6120300100c0190701c24014029801840269910340504144814020844048505500031500107104141313803691101403c2010300e580b022103025080780400c60700380301e0154a002070300a0707a1703405001c08540f0405041c00d02c3c903a01110800310414081a00700408514250702800d21070388981021f914040c4050302c1108500c0050007041d00c1c203807245600b84407540720f0303000751000d4616411082c10fa44603007003900c1c500c4e40080701094040c00092844160848059445405181b0016071480c455000c1016100d44810482c0803c4146d4803010202c1038104291482c2001141c50343c2d00741c104400000f404065940000e07009801075034581080c2101042102c900d582060000c000f03043e0b800c5001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 486562041 1250 486560791 486560803
    0x50a0602091e0f1c21030605040504020102071502010b0901030b0f070c0809190e10170a0215070602040f0906030b0c040321020718020301081011040603020c0c040905 73
    0x120784039540400c6041d0000b00c2e0070b40700d036603103000207400c0f40c20840b41401000029958000b041039901c8114a000340060764150001c800400310740c0d08031105d01c052a04c09402e44030383d90001030181d03180108000150b84d0000e174810485010324244110448001c0c4d00700e01604a4803c00350b00704000000000c2003002710b540545c46026601034441c81526540f00c2101e40c0322001c800500481418031600342c1601c1c0154514040b8140c40300313020a41561206a00140302007200c2040e80104182402c00c4006448403200ca20160380720040c214618460307000440d00c640f650341d0201c2c1401d01054560030000c1590403070340908001d106403543c280c0d03501110030107032205010840c0d00800701804214604030744810740303064070362046800e81c0000d03014100e0462140c003000e040301144240240001c80320303c080c030700d101ca490307200710056520342c10320707910710f240000251440c1d40c4d80d40341c10241d204190101d01520262022840e000d03a8980c0c4e411680c3e450032001d0001c103030b8031900d810300c0300382042000514 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 486563291 1250 486562041 486562057
    0x804031e0e0f03010507091a090d030f020d0f0c03081317070c1406030127020c07050307121a07050408100f050610080612250f1a09120a050a0602 64
    0x1c02994000d42c0d06142c02e0303e4081d5444008070300085030601c11440c805a14084003490070032200c0c00c0c058140f0020f000d03201030140903408a44d00c1c2d9920743d4800d1707043c041440380c5c10580c288032032240f00030a002016850080000341c01c101000300400e0342a144c0761909403016800102541482140e01035404040d40002011560719120120000c3c40144401141c04503043c010a800c0c04c41c0e10300301c0160340401952086610103c4220f892042e4a10350b4805440380c5001c0500400010341098245490030556412601001c0c2a04105d1400212800c907410308440d910074040c0626295003406a42901607500302e81940d02910360074183c6851a035010904807001e204042c061600d44400380726618001050b02e00007e14001d000800d281000c122012a00c2ca6000440380f00210041400402070384007480da02210240000420040d0720aa80701e502610a003000d641c00e12007155030105a44c4594141e490244190940c0c039002c040c0c0602c0b4078002640c010094130b000400c0c03868070038000d40c00081 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 486564541 1250 486563291 486563299
    0x10605150a1b0f0609020d06060902040906090b0a36320a020a050d02030c09090601020d0e0f1201020c010605011827150b090913080a0804031e0e 64
    0x810142e810300b004081410364100d500003001c00e440d0f45404001c0d005449059030401f03002d01c600310000b0628410a0001c0130444401a01c503030400180d00256441540002da4640c2131191300f0406030340d8009001d040b5521700306441d144a0624035184469141d040b95000706000c540031428561201c1c3d080062030290001002024080d002000c5601110940f032400030b54002c2000a400a11264000c104001d414100b8500302019074110780c0580c0e004a400d03884085010490300c29034200030b19182c1d0012024000b400d0090310560006050300d1560302500e1003002c42e0308580340785486194101e2003444020300203564640c0e000244c0d81c0078296500c202030016000030300390355525041d92848401d8846010101d40a0107a1005038030a80380c41030f0b08907600c1d030b603100c9507010f400314016080401003001410040e02c424030081041083e03500100340d82c0c0440a81901c0c3d00c00608180d08949100c0480e062025a94640c0d0600b100c1c0a0000c403034000000305001081c102883c1c200c06205e4a2850440f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 486565791 1250 486564541 486564557
    0x90d0f120201200703020a03081807060309050114010503061b0f04080105061306080d0c170406180b030c0f130504060807030b0109021305061608030a0f1a030d11010605150a 76
    0x1e40c0030203c0d118100001d0b00581001584c0360010f4882e1001682009410442c201c15a01c0304c1c0342c060811229030721200100741c3d030341405401c0000a0240c61407142d130280004090350315010100c4d0300c0b031000805007600b4501c9102c00e120b240741000c003a94180c11003030000688950300d802d20203008150903945103100310301c1d0b10070040c1c5540b55402034806030703901507000e01491003001e2421354010303d60341d0045030031907071200c0c40f8090b0040007406003009080b0f580d6001c10201c3c5010300300c40076072a03681110100c1c003010020403c0000340d0070b01f11202e0380700c090f10103a90340dc880400010320000c20340106071b01c40c7c18030f007001900030310010b0220150b0b805000c0f11f00480c0d0780c800b0294101d101e0480a003c0c0245501e208000525042c0041c11000f003583c03000685141c403076504c04041e0343c000c5440c5000156642918007103a02d591044202011060084101041174100001c1d40c0d580c070305840c2c0d001c00a1310761100d099903d0a4000c60000c05024040081d162680810300703445801880786200012914 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 486567041 1250 486565791 486565841
    0xf03041104051302060a0c030c12030605010807031401030314130312030c020a121103040e010803031008011808130f031a10030308061512070309020a090c05090d0f120201 75
    0xc3c00d4003104090b030044c000c5160120b0710740181d0300641c071017906506000d02c081c0d032800480c501300710b400400d48076a980041c0c02c1c5d040800241041c01e0207481c090405180072010360b881c48642144505480e09809c20201a03101d01c1c01e100210301c00c2e441002011561604000f041000c82c400724240c020040d203051003d03040001081789d85556000005c0e1130f881960180060440c094104034000c1c040e250240c0c1d1030261203040c0c1000f82d850aa002c600c2c0c65100100b00840c0701031080c0844081d00c0d014000388080c0d06245404901224010340c01341501c078000604078035145440341c9240c01402200c0f4410078036583e13400c0408441a111203004540903451001481c10385880c0c0c3e0b40d6041d6503154850307081a4a80300d00348800000c0004070001da00004100c1413034180c505454081c4030b100c040d500450040200d2041c46002c0c80e0075480000d4150030b1000300c9075041c1d00034042d40c000300015282944090418240500d85030040e00300601010b00a40101c04180c0d811f4202040f40c500001d005000901c075 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 486568291 1250 486567041 486567061
    0x190306091112070201181101020c010503090c09060a2c06191707230109090c09050d020301180308040c350c0604080106090608030408071a0f0304110405 67
    0x2114107020789030010070520b5400b0024018460f0002114400000c0302d500050100c82c00312031444041e6212002e240da1403140b5a810041e400030424280380c080d003107041411754903550f58400f0f110280318226910004500c3d403074402e00340000b000d05412030b4014101c2d507c041c42203040491010020144002c0000b10313a070520b0b4000c0340b440004100c070300d4642c03840e00301c1c00301054203c4101d0360b0031802210300000d54003140400381c0400602405000e40146503400024003c11040e42c4183c2100307060180617803145401292803404c460003900d0030112a5864030000380103002e08102110f82524141d030000602d5400449076110710f00c06e00b0f1600c20142c58900d02c1d40001d0580c000404130139070800320680200c02050b07603100c0300311310703102203038007011100c0002040382d0003a802403071142c1e541c1c0703070100001c0d09a030003000010110440610702d050301b0208021303102d2885001d180018904030f07034800a0100c0c48412281100911a85a0348904061821400c44504405210310450903c0c0125920b0300e4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 486569541 1250 486568291 486568301
    0x20a0203160e010f030f0b0a1103010f060f0806090c090a0b0a030b2407021c0c0605090a050a0503151e0403021b0105030f0609060406080f0106030b0c1309020d1119030609 75
    0x38210f102c400a1006c03071343d100345401500502c40c0c1281794a074000480c071041004046c60180480110140e400d40c00c0910040c02401d040041c10104001402400780613100c0703841140d00844a030103407035030b00e014080c08240001c2d0a607100c10b07602007000079091900e035415403110b64030300c001b21660042c134040002c1c1008010004040d200d02142c0070001c50f8010b01d0075001d940c5003803031480c4000390504219200c030862080e943e070042c0e000c5040040c0304039092401c11541c1c400303000c040346c12500d50360400f004a991412007500710401502094003007424081e400316001d0846115000c0c06541d49030501e0025200d150384007202280001d01c2100780b40c650f01900580344100c00c1c65610f011300e50b4402c020070000c00405014113801503034652002c1000f840521044c5070405030750f030010845515515064100e031800510b051070f8010300740840d2003a01d0101c034489088408856001d61074040c1c43c0c0c000320041c0b15011941a4280002030075a01000400e90391842d9802e403600c08011a594400d080c60640c0c1c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 486570791 1250 486569541 486569543
    0x5070302011b2d05061f0b0f0d02030421050a140313030315050319020f04051603050a060b16060b0f030a02090a0f0203040c0f06020a0804050d03020a0203160e010f03 73
    0x41d0000480451191890038501000c00110b600f0303980ca100f568803502d082420a6070b122440520601d005202d0408201860300180200307040b0b80c2c901001994441c029002e1541d0401c00795800001040a01421a494010310541d10808c80c441030a0050040c20f6a404407c0900205e80d140b9403415004042c103050fa44241c0318001d01080c441d0390340d40c0031801080600303103182c1480c8a128000c03a19071400c0248807403c210301401003501841074010480b02030486c03d02a4070032400d100030401340b504002c10003118120780b42000301e4951240c4108201602458120042d03061000c2800c440809941181342d500d140940000c001e000280c0c8144251030303607203198080d01030b400a40910b0041c00c0603840a0f41c440c5182600040301007e42e499101a644140d0301a2250b40c05c1401c1484800340240340c3c8002450107000608e100c40319035603000300da4010b40c0f181ca48104146522001070600a0111900150b40102502c01c00303884c08036045040c0c6031034056076442c418210004030708060802d0301ea20580b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 486572041 1250 486570791 486570803
    0x1d0706180f03020f030f03160620091903061a10030b0a260a0f0b01060203120c07050a153c0b0105040812090f01081009020d020f030405070302011b 65
    0xa90840e002c0c801041000540d1315014441e012140f07808002c2803010301082020020250842c0800d0b0030510155100102c0341180303070072541c8002c0055001003048032032a840a03a05040088076131003c50720b076880e0a600203000d490421a0110740c0318420382d5070030340c0442d00703c40146105480381c4045049540086c0425040304081000303001a000e070704403142100300155001c400c58111049914100240c005c0d08662003140301000004205051310304901411f114401507050003940020b551101d00060a06405084005400001e1140034480004444d801510740d0b203901c0d074000c0302c0300002d00000b41c80c5210600c0701910703000300005c000011480305902d1141c58000300b4038004000700401007240d030780741800310801c0002001c1e1014889056900a0160142d8030340e5400c4c1c0c1403045030320301d0904160400001d101000b804581c0e459a0100390f48000710010384540589011000a21800b0700c0c00c040324401000300420041d00046240c2030764401e0380c0700c000b01d20b00b841c5140d00300e4079040001090 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 486573291 1250 486572041 486572069
    0xa08060402010c03141308150f1303050a09031b170304061403071106090a0506220f03050904060308030a0b03060402030d110c040c0e010315080a0204020d1d070618 72
    0xb04c2e04c41c200e0101030042c4540703420315200410f0101822403a0f5a844461540c001207860700c1e00030340c911170b0f0950106030030f14211403518180d181e1350442ca0b05d8510081c284440800d00c810404d200303c410402865100c2ca9902481303e02202220007911a445807284403a6000d0000c50000404000d4800310b64494072030b1108030017001c2040005400061084e42000008bd40d0310040074010401140101c5030f01e4083d081403500742c2029410490014000840000b0b401402c4240880030101903c456030011107a404248891400316400c0c4a00f90003140c0c840d0404d00c022050200580c02035000d501c0f500020401110107100303040d100d580031100a035041e004410a2240c20b13000749034801264001d20260f40c0b0f10141e51300003500701c845100c00100042c2d80e0900c29007403943c1602c21029a49194245440c4052618000d241d540d0b29254000740a140c000c41c3c2d1011000c504d800c030854409144c00007102203000c0030a101c2d0340d03040e28802c83e00043c00700c8e5902000c0407222041041668141b501c6190 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 486574541 1250 486573291 486573293
    0x11b09140303090306270d0903060924021201050a0f050d150f0c030b090108101e0606020d1805060702010309210806101412072703020a08060402010c 66
    0x3444151401006825000030880e142c81035034284003480c441c1c3e001106039280f80242e000300744d28103100c5070309090f510303070141000d03c855941103a034100c01c803030f4000c0010901c42047d1a100c071000040112124103a0400329098140045079000f81909038502046118141e80c1c60040011060b00b9109400e90b0b440220400d0125041c451041e000150140809654042540020300d044074080040e40221503a2801e104240c1645805807500d050742c210790341255541000c2c10140c0342c04006803030710036650740c42d02c1c45800e80030a021102007a2140000801c512595050042e44a6170138a188100003519449564003c0e204540c5810940e00003425032801d0184907401034000703080104d42664807110646003800359105508030040c15005558581520741003510a105c2c1c0d801500a0501c240036545030012001e40114040d2a90032960307042c403500c40c1d110f400085d034244840c1200c8000b070040c80c1c680fa42844000d00050b1044038400c0c0c5081181e9a42c903940151110402e4034005d00282419461030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 486575791 1250 486574541 486574559
    0x1120218040b0118031a07020102070b0a32010f0b04060f0c0c0314070602010e0109020306061e030d09080d0f021902010306050a060809010f02070b04080f04180e011b09 74
    0x48080d0010f050a0650703c0843c0304100e00c20f0300f59401107400243d01808486d591b6000380c00c55030440880d00007541020b0a42c2d80d900c4828a00410940c00d060f6101240c51884642d0105016507c04200c1c0c07000c4a03808510074961384132000d01401005100351000000c1c0000000200c4080b2425560b5170740e10001151000c4494120921301616021002403011001c5112f07109002c661009c5400244882072500b00040d00751020b1440801007030b40740010907805030300c0c080740c2c0d582d03c080119800b0038003800c1c003d0f40300884030005242c1609807060848041c28507422888440681c0d4091007160000026917100b1626401032481506c0141c204166105000c1b0708501c450b0140c901c14100800c03c1e42e15180401c003010b1260b800140041c4040b4180815550284140010800c0b05007040d442c2c404551624162454050001007107804009034401030401284250380140c40341010b0b02d5000b803041e132108400f07404104200d20982d407800c5100707024072005808400c09800e0b0b50325880c480615014080c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 486577041 1250 486575791 486575801
    0xf02030307050d02120123031f0e01020d02030414010b150d05060301091b0911070206040605180a3b06040c0905040f0603031202130e0c0c0d0206060112021804 70
    0xc05883d5001d102c1c455500072035032952400780c00d400c3c8990708044080021417010003502c0345030328020381104104220504803003240310001040c80a000c01e00c60a24001180280701d00350705152524804401e220802ca856050441c4503613851000b4408070389070000300081c0801d00313a060a000b807010048121180d000303412070f6900c520001e000280c0b084135030301d80090707808044090007044492548280725065062148041064548508509050459001c110a1310450240100f030041c00300d2041c40713280b840c5440001081000c0d000481044e0380d85040c0785192450a02d10f5100c03202544440b42003403000c030f030790940b480035040c0b41e540310740b90142440010020585203204000381d01c0004601921580215061000060030000d2080e18506008104100050441402c140104502e80c4000041c016950a48010808044054481c6540810300e8442d41050000c01c2c0503111061102a8020441070700c030368021f80b030b2044e000101c4600801203100d00501324001624034001c410b1141425409 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 486578291 1250 486577041 486577057
    0x3150f011d04020f010216060f0f0504050a060806210c0f010206070c0222090516050a0303050f0307091508041716080c150108010903020d08060f01082d040209070f0203030705 77
    0x10b0f5035520500c0c7c043c600305100f407608400007060700c56001c921040e5000c541c1070340511051500d0787c10a8180f600184d0fa146251180300b041142070f030003080041d0303220300d11400303520007513810f00c0a607002044c482900d038200000001c2c410b000c0105030018650001c540248141580c1c0e5404042624903820495650714a401500c1504c0f20a0340708a44414248581c05071140504010070030858032008800b05620b0640101d401001414410000660000141e9103901d641c440300c40d49a0741e400b0000c80c0c030355005a2140c4282d801f815541c0d0f01058000c003915001724010f59100125110300071180c20f1503c1408010007400112003ca00085030058020340b440d45290340035a011800582c01d41904260281c200c0d0020703942d50818a0205a010050b100711408281000da6a914020300000d41c3d060310b019010341404a01d45c00a208183c0e0020400c0a56040c41c81c0007a00030031280c0454413414040b1812030103001400046214180501e103640c11013816540154515551104102e807030f84c200800c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 486579541 1250 486578291 486578293
    0x12402030c0102130305010c05091008071233050a052404081f0504082205030102031504060f15050a09051c030315050102030307110a0203150f011d04020f0102 70
    0x1070848050280020205034580c0040d1048060031418405c1c2140c8840401d841400020030000c00d042d00e40c000400c4d80703e149802c002e07400d03035200300090f6490445c242801400314604510300c5898400c3c1028407110602c40c0c0300449001d10214001044000c51f4003a00b03500481c05082000710f8600701280720488101404007440c900f140c103083c00c1942d041600034010b0383d0004042080c500c0040d0a58444004903900140090b06203516021103c1c85414641d0141200c0301c00c40c0070303100e4080412200205005402190749290048500d1200380803107070450310842c01e1000010f9002c4540d050142030701c000c60100e0140950000302510a0303402050318400380420010b000440343d5590380d1480e41c1140c402c2d0000040daa00f803400404448c841d000d203100d00e582c0e0304010300403a41d00000381d80d405059805c10b10380f100c000c50301091401494040095140c8142101c42408014001c8940d0041140d05040c0c02240d0322204100305c242d000904c0702e0304050758040007402520381060081181c600c180 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 486580791 1250 486579541 486579547
    0x5041505040f0c120b010c06050601020307050a03030c0e0f0303030c03061206010e04060c170606030601030f05100503070b0717031815060901140306130602090627040501240203 78
    0x40071a0640b0700d80780ca22a22190b8614100312407603000303c4120040f00b41c445040280140290029005405201001d081199102e0000704143d008000f2aa20705e038228085445961a038540100a4220304402e0400510310a50403a1181001c1100f00401c0314000c0c0694111307902c640c443c2d549904000c02c1d0560000d030805841041400c140310a501030040b400001c1700f58545800c0c00300540d1000203c81c410013003001c43c8003004400120555802180865405949403a1040102c000d0704c1c2c10b060b50301500346044184902c1d2207450001504582c0d00350256002e2075651082101c0324043c0350009007461100b02040800d089440b8015079000d584869907412261000c107016181c01c920b20390500c10036100c901402910b2501035002d50051108080180b03000382224040390f20b0704406000050041038000d003039001c015240c0c0641c1c8100d103002d015241c41e40c030054004400e200300400d01400041c10307031107901c0883c105402014182c6805012000b043c0101080001034030001200d040c0845c0018 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 486582041 1250 486580791 486580799
    0xf0c090a200a02150105150304020d0311070f0e010e07020709020a02070f060512090c0d0f020310112101050d080a030b0a140301050108030301150f0207050a0608010e06030f07050415 80
    0x744041c11184109a0042c402d007598014551100b0713038180c00562040440285000b40300d4210301c01c8a0740f040c1c2c1a10510312456031840c0a450300003401c0300c99061802101c0000c190000b03030388440c50071960100703007c03070459a80340388a075401c040c15178070b600050700081001c1c80420f28613002030105c46050b00c1102c1a0660314440090b0855650f0042d0000660000340405102808442140c00c2000c01001d0301030742c06640f0001e40c2c0c032643d880c00180000341e036000003401d5540a2100c28492480c440c400d1100120302c03140740d030040d40321104902801e0002460761070b10206084189045ea2406044d094a140064451400c03982064000e0070805880c0c109100072900e60410040c0248007c4400648440011041501307646058210141350341c000c0c80100a8001e4210460405680900b8990301074900c0300c41c202e0410130f03150012174000c03080e0724000440d6036000380d04a04031548031403c0c0c0d483e03855601c20075440d045500a03040c03107a8052242031110b86000e6010f0014509450700c0048101c4d50707 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 486583291 1250 486582041 486582101
    0x603010303110f0f06010614040e010602060414010c020607080613140118091104090203030403051f0b0d03022e1e0507020703080d0209061611030f0c090a 68
    0x100360801c40005034210340c4004150801c01a0121800c3c0940250000b540001c60041d81d40c001441030400304011a11039a190010840840700030386110080440c096071144e80c081d644a1045d02c080354406031262070002503c0c810320804042e810142c1c064400d88d112101f081361280750142005a1107a1403100c0da0820380c0c120f00c07489400d040485084000da600d410107076007840c050542c4848159040a2607800001c03005040c2e400c0750380d8111000100102c1c5800800e1443c019500002c09622820320001d64510b00c503103c600390014561000d00003204030b0000d01c4070904001030001d0159100340e11b0075401980d58540744031400c107404804a003007500034003c10305880041074103800001448841d946e14092074002c2c0b0b40e2240c542e0008042a6145640301c0d0381600c18030a4003014281d003c1460340d881d0741c03000f04031030b045400b81011400c144158248100010503018041e8440c5c454511690100b050100d091140410010b00314100d030740d500790f4003c0240c02442d100d00c00306299a8641281110 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 486584541 1250 486583291 486583297
    0x807230d030606111b190e07080123010e010806131406181902160b07050d0c110a02090a0b06191202250c09050c0d06090e072306 57
    0x15541c1c0400d90b10b107415030107001c4802000c00010681c002c2414441450645060720f508444144c907294803105120307092100b1411113401c04545c03540c4910030f20240a0f03015803154107858145c4148031002031030040c0004e101e00c0c2d6803000d60102e404a144050258021490340d94094006044032080d0040388685c2c608481e0301c00d215105c619640400d0000905111000070ba40d03909403403000c44d0500b82441c001c601e50442c003000300382d66900007485501030301e07003500200b000c543c2c090088915810240c0d4040c09903041200c0700c0007140d103800c035240f030000d09c1000000c80c0d0b01c894802600d10201a034090000391900108040c0c022502c40200203103544a6500a1940703820f02040483c40d040074041c01040130114160034448980140701404250483e40390032003a0340381c0e01d03140300180c030ba00b0315000000c4100752780728070b6100349040100804494500c00130500d0301103e840400c0840c0e00c03200030400700c41c409642c405143e80b00040a12034030340040418000c00684c247c0408282c02144000380d1294 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 486585791 1250 486584541 486584563
    0x50711060c1b07210507081b040e060c04060507020607080d02030702070f03050d1d0a0b04090b0913140a06090303090b1303140d060b13030201020613080723 69
    0x26000034a904902c0d000004048610034a40c050081c2c185041c0004007400224142d0a40d000d0800660354104801003040000a2001000743c51640c0e90800003003000b000c0407607d40d8003441c108140729070000004034030148241c40a504150509003000b004941130b03004030710200e0300a0700400c03190f4041488400a41102c8903100000b613900d1904180c004d041100c0341c1c2c06503203030340010042440002d41c08144822102013a103468025801a103092022511480d0f400c0c0b40c11800000002c04c102458900a00560360040028001000034405000c0c0160b02101c015050a0b5414140c10014031301c01d102410b0800340b00222009241551201001c17541885402c8011076518111030003000711070311041d580705804c00f008046601039902c0180100114100c402c1881c0400180c3c43d0108500754030170f2000e000841d00b11500c841d06900d000c0c003660400c0c00241e015104400c00a0408088020b220746c4c03040e400403056050500c59610027040c10000c84000300751030385070208900c182c40c04020040c100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 486587041 1250 486585791 486585811
    0x6140c2a06030405010504061103040305040504050403030b0433050a09111e0d0b060408190318031a010503070501120b0105040e0c070c0e06010914240a020d0201021c05071106 77
    0x50030305103800c0c0300300c4144051400910749d0070300400010035041019101181c0d002d13036000c502e6a40364903049005085105046910a10f04000f518448540070940c50032402ca00158041000111039000855840d9115143d4050f08030502030004006a030040c0c01d80300745940d401c03820304c0000c10580c10103200051b24991031010218280d0b0307075a800ca00440004850507204a80341c079040240b12903c6000400495800400450032503040512400c41c103988801c03c14120744006459182c241c9906818a54040d200583d03003001003154640030800c14100c0f00f0503125100b0001d5265544000350880f45207482c1800303c1400000348500b11007041d02e00c00e141010195581d0a8645420f4451440700c0d0080441c0007074010820030545d82004114080d583ea9104020346969000c0c0003850892102555020b411007180080e100c04400c680a0090340500c1d40940b095001100c4e0700700e00b00d0113032a039808081da40004502400c03480b241c1c00700f5000b124610b0010030901042c81c41030300d800c00a580030011 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 486588291 1250 486587041 486587051
    0xf1c0219080a0c050a14010c020a150e0108160c140316080903010c0c080f0d0609020c010501050a060c200102160303080603100902130c020f01090c06140c2a0603040501 74
    0x1004940d414210103010100d54282d209810259002541b100110405042c00602d01403641950765800800000340080d40c0844038560030000300074941c0f484080c44e18046030a542c04280000e000340310209145603e03a440d020403000c5c5403680d082c0498406201d6095000400407120b0701045607048804503805031054030b90751104030081c542102d000d2495901005100e0683c44001180d04007165003903c402040390f0f8603104000807103c0141495800700340360b04d100080c442494141904001c0c1298012074481812980c2c421085c0c1e00ca0454801c003e0504000c0011900c24004440620600c0300041c81140c3c40310b010542e1000c4001c0c000d40043e004a8101400c011551038100903d01c400742c034000081c08044980d90100308401a20b2490780f10064450070000001c80c4200100028450060000d100c4070006007000340e1802ca03540151170008644500040750030015000b141c55110100c4010320024260b11102c000c6803030115540c41158120305525882542d844000d180118011000010 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 486589541 1250 486588291 486588293
    0x1e0803010515130b2125080705190c0b0403020601030506090f07030b131a01030512090105090f0303090402070309090c090501140a0c06140f060f1c0219080a 69
    0x42480c4507000d18503507080200640e4074600c200743c0d81842100c2030741c40c0840c0c1710603010030b80c1c14244000b50041601902c0d030a007007095001121110480c0060003c2d064000600001c00442d1910012101c0e20003143e001c008200c107800c03003170111300742c00c0c16945450300000c4540d507110000380380c05032010b800581c080d40050013071003010f1007601e82050560700100510700c420050303180c5950a03440050000407201e0700060500c4d90221001841b81e41c4117480384480340c1082e21032001c0180038041076030103104200a030100031641d0b070100d810b101c005031625801c000c215070030850f9041003112850b07054042880703649125103460004e409414401c0d120118198107240d00002142d941c51f0f800313001c1002c1d0744000c10032a601b1907140d080224040788819551b22000704107449003140740f60014420303460300034543c822502c500b1955010345600c001d11201600c5003410030106841c070707420701a800500113102c000c2c1681700c646045101880505031070f1030380c1e030103007074800e070042850740443c055400004040d4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 486590791 1250 486589541 486589549
    0x403020609010507110c09181c0e010201060e010e1015051e03011d070309051c1b1709030a02090a090b0a05090303061005190203040603060b07020303161e08030105 72
    0x40d801199480e11340340802d285c00e51036607203042d0400c0b894001c0c25032401141c4800e8018175600012031804040741c100925094034110000d00d12105030001842c10b55000328a9031040c00340400300c91888004070296402e140a00c24148030250502c07404103164100003074a00c0841261900340d03941a00c81640f2380c40c0b00500d5851107000161090b9a42d0400c00060140000e550945070000d4000007248600e5943d4441c154000d003451a405030071481010006410000c040d4402d2207803c07226561144480e0b40b0040d43e070301c0d4a0f000000202001d00d03d10400318010860005401e41d250000c0403101140c480707402048480b54251284007005885040c0c81040c0138000c44c150350410703103039501000740b4640b00c19216143c0c040030303056621601c0c00e1000104034a00c0782c0103442c03000024001c3c1e80c0e810405041d000e59039078028854900802e04043c40020103e80c0300c1c007507808090f001307000703949400c004c0c6508580405030030780103c503070301c4c0015610740000540d00300c5100c01512594003295694140b000704 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 486592041 1250 486590791 486590801
    0xa020c160302130203060a03080c0607030b0d0314030c0904060e15011d0108060d06050a14010f030507031704121202060a0603050d11120d02030a0605060f0a1407020405040302060901 80
    0x480225500d5600800c0140c0700d403180d001c0d040d01030080050b02c130740792840029020865640040d1200d000480c0c5460343c0200840c0b1140604100e40b41040300420300001c1c00303042d8107c0580074000c078400d17034542910482400019680121201d800912301000080001c081325411340080703400310108001c0060036a451100003854003400d0a0440c884502e01143c440703011014080c0034108504040460110340340d40707180708400b56010704140074602d0829102c000511601c01d80d0109054880d0000580c03c0004a1100070340b60840090000780341103844d0340c01341e0204038854203000030f01080001031a40205a40740e60079031241060b40e54a4820600003494100003400c0243c0a920300001000014000605540700061500f0a525801c03855500e071820803c28030481640d400700041c42d14180e00701980151300c601500d8400704001900d94040c801c0502402107a00c860210030419160701074010140b030046881800c6009280ca42c031640814161407090301c00700d025034170403070901424401c00e020b9 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 486593291 1250 486592041 486592063
    0xa05070c0621090602071203090b0106091505221707060305061305060f130c02150f060d060f0f0903110607021b040204050405010b0705160f060e0d02090a020c 70
    0x11804040d0401c4040c0c102c8201c0342420702c420b550710400308003040000d406882c2c03015040141700b8056288410003401404000d2801c60b004583e480000c5a4a40a02010001d50b01e5409200b0703516185070b10161400c1c0d01409c0d000c407a42c009248104c1c803080b07079901810040c00000d21807080e84186160600c0c90035807103030004030031f040c2081d007001074546641c40049062280c0c408041001d0b1140004070310001208100d80e0340120314007040c004141029040720350103d480d542122140c00007800a560780a2040d15003110200d00c01001c40d401d45404c8290340700c01c5004075400984403540d541048111202a10038126203a200c1c0d00040c00d03d030300714000d504802d07020b601034403840c80c14880082d100d50520280d01c8880968000002068583c3da056030090840600704000e10758489614803814c0d003015204a07024451071000c007400030641843e05c4c046844251000381c58a0070880141d6445000c9411550001e1fa2180d54030b001d0390314207400f103001c3c0e14003140c01030360b5040c0040b20070b00340140341036 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 486594541 1250 486593291 486593297
    0x70b0c07020102030a050304020402271806062b1b120212011a040503100b030111070302061317030f0403030e0a03050706180507030b06100c02130e0c03030a05070c06 73
    0x20440c40541d801100301c60300d11101c0e10f812a642e0b522480041d000740144420300400104030311030915210310421240321000030403070300150b203280a06140ea0841e1400c40303c0c05d42242c400d0249202841103070030310350b0302c100d9049034588411010758070000c103e0700740c00d160440100903007100d945a190002d80c0c1c020784036245e8005514240c00407500c044100c90611034024100100400018101510810344001d0000107080d204100e1060306004050007012035400d01c00d5180c030207924800baa264085401c1d079036146d00509040e5948041c5140080c411b09401c0e21004070a000035a00c0d0a4400c004501c41c80c031f010b0035624281000d04000b001c441c0034680c0c000065000c6014280400d07000070a4584042c1e01032000300d6a220000e03e12076144030310800042041c420400c01008004880314028841e200650f05140c501f105040e040350501c4640320003a40001000281c03081d0107070690844000c0113600c000720340c0c40c52081c6010900d10b6011344078200002c2d4000c90350f00c0801c182011180004c2800c1c1c5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 486595791 1250 486594541 486594547
    0x50a0605041214010b0613090609091a06130c030c11031c0b0d050d0c0317010509010b09040615020328080601180e010303090e0a1109121908070b0c 65
    0x70607a0b24015081c2031001e490007840150700c8800300000d41103008119005040291a070001081030394540019000384d011190034000d001c502203040d0301c41c0318002d40c0c0240c0d003140c80000005103218210340141029400c0341141201680702d03d0a03001d0a49864140c1d54002814009408000c2c0700341140068036565420820411310348021805e000442507000001c0001c1411134800060794000d0700d42c40040c46805920002c144254020344d82c521458002d031a90f003844070f8120718004c1090b409000e00b540c0101e08000500c00300d07200710041c10a40c200540009912501c41d2851820300d8455124400140e0001801e000170300d00a242004004840d0026041c0580c00c01c030000d018580d000301850304015841c01d1074000361940302403040080094a44d04020755031a030034000c00b0025940101e50762000e1342c00114005007203c1c890711a0100480382c0c1503080024041c00c0120341d0003070020354170441c40750041c510513225028034141c00b110b200d10303d0240e84007a81e14202030311010013444a03180c0c40f414 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 486597041 1250 486595791 486595799
    0x5180f060d052e0f0e16030317061c060509011103040f12090911181206010e060d14010b01031d0a0308040c0e1504180c03020402090a08030a050301050a060504 70
    0x3844007801c4115601840940316010319200c2c00301c2d0038001d44142c582001301e005010700f2642e12056400c410b00c1e0698041ea03000000c04101d40f0311920009002a95070190701c41254405200c1d1508400300402801c1c4807210b09030103001c070484031601681c8503a40d40342805200342c800d01c60b8920010125450034150302d02511940100000c200e0302500c0c032000031100c1c202c07d81c4030301212006000e0b4501c3c1005100441640c1c1c0031243c00101e82c0e114404108800c0421500d4800644c14001703800c64020f00ea0780c1e09101200714070540103891300f40c0206441d8640800941c088202c85009020080009150640440010701340c80040030219400d401082003079940100100700c5c485180d40609200b29151214589203041e1905540074040c000c00d00c0b030a000003240f07100ea5001001c90212400c0c0008020604819040b4183c51401090405190070400050038a90003803c64490010300031140c5035680d03030000d41180c0c41781ca1801c00188000005102900d04211003d005d0007641c80d00720b040c41e0030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 486598291 1250 486597041 486597043
    0xd0615030b0f04061802070501020702181009140a09050c120102090420070321091227050d1b0e010f0e0f07030f0b1f1704020102030702130605180f060d05 68
    0x48a8442c2a05071b03000601c810134403a00b50110303a0a2a4040e01b0f85110390003006087c5100d4100341c80700c1c00c500403844c0c00042e4000ea60f0107140d0300b01025850808040c0c5500c03081c000200017617441280c0030300035402c2405090343e800c1c0c4c0340c1d01c5040c0c3d0340c0300142e52951349030708000c02c54140580c02c01440404414003101195244140d80c20b441c2e050030850105605a5a015400c2c2880c031441c0d10301a0501d51280e04101245110031a94102e5840344400e8000b080c6400f401d50326200c3d12106644d01c5190100035a00d000b45008407118001d41d0401c5d94112482c1c00bc50300c1c102103800040f00c50640b40e0041080985506041c0000c10082040031824100744d21000400b42c0082c2603001016101c81c0c42c2c5042e03044580c42260f90b668000c058500306040d00c01c1d21801000c0c2c1d90442c40208910040305013800031030b91740091085605034055480d2910f9982000003100300442e03101000c65131803c021580761140200c4414055490300c0c43d11040c13901c0f0f244980b12080c006c00c0c241c014050f0300b6650001480c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 486599541 1250 486598291 486598319
    0x10f0b040b060c12130504050a061403060906130812010902030402130c09061d030708011d0111030c2802071a07030c02041802040908030708010f08060c0d0615030b0f0406 75
    0x102600c4d415a11145070260201a040580010303034000e1400041c0143c0c000c40c0d0380b007882242d00d000207203030301c2161100815894040c1203030f641249401c480c00203066940079030700c080440b40c821042c01d41000100002e03000252000d03017001d140981d000050000303524080c0c1240b070460b10f44041c10b0003144a07110740200311500a128410038041003a2a8441007003440c46034040c401d001600325404969500c0d061030180c082141d009402c82603400b036100c210081130082a200a039036550261550721980202c9000340c2c000e290120000e031120054484150711003640c3c00d07064149074010010346003018901c414180802024503d899010010040000d41040315501c1c41501201c001400700c42149a461219809006c029030040c603050000e0f04100d100f002460040e00b5035650300405a0700c031000d6200c10f050310301803140b19500c4040025400c81240c001005924150f01c00442c00d9a5100d4001510700d01410921000c01d0702c8034a900d00c14240003542c0c8031031100c100d41c11307c4030038035040c960742943d1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 486600791 1250 486599541 486599563
    0x10b09090a02040915140d0b04020d030302040e090607030510120201030e0c130501080706140d020a140c2401180b0307121401060b090a15090503010f0b040b060c 71
    0x110082000440400442c0e042d90014510203506001d803501c44007040d00e4800d220301a18400607041030502d94030f81040104a15001d46c03058075003901d51100c0d002c2204800000324120109a020007011444124104556004240500c0140000c3c1001000502130705c1008200720f5450049080412119a00d1200111066020b08002801d5043c14005c40d0406461400303071608101c4401030600510600e5008038103c3d0111829510120703211842210710445000d04e007034603240300f80f012080000144e801084540b6072800c0801150708d80300400011074002a040640076040035201000c2c0940c06104900d680300311001060696040c203442c0c031080c40b44030072413030401580c0d1441c80380d19840800280c000707803c00001c0b0300000717203492038005918880c20401249070b500707145000031300718180029145150710040c80301d41c035203044c1140c0f900e01041e402811020442c55584c0010251028440c950a0750118a00404c22101000510041d2000060103074001e11080040c0da0761305001042940001c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 486602041 1250 486600791 486600799
    0x60c0c0b2505161b0609150f080903070c0603021c05010305190302010213080706090b1608091807020c0a080c09150118080a06140906070f1b0b100e010b09 68
    0x10b2105810090745039040310358000c0c0759255690318544c0c03c0b84c03585054030494003182d581ea40001e4039625400b2170441403c107107602040f045202c0004040c090412035612000c2c842c03c0320f0400703c0c03540741c44a9206160b400400440c0d03001444044c09504592f04411403443e07440180304951465072134a64644c2082d100341c02d52074400d1138403c109031007074040b03e0554441c0256611407503101e9200c0e41c3c494060740305074401f00d82418400141e154050b0181c419030340120040c04144ea01c0394441d200c1c1c2d0750005040e140d01160345006800082017010f50a401404543d00420b035050804007485002101e41e044a0000c0e402048440700075580d4042083d401004a002100e0380e81e40707400140e4a2554455000c40c90b0040e1a2010506200000c0c0d403071580ba0003400107000185c451441c210b01d60f1b07410780e003021032504910b001401c0d80e070140101e0b800340040d82c0343c01071040040e011540120055408103c440580320018000c02c41c0201c041c1c00b006c1c2c0091761007082c080d4500b2f81a20500e00c2003103612402 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 486603291 1250 486602041 486602047
    0x1030080a090305120a030e1b0d0629040c020c0f101403010611061b070605070203040911040503070503011104090506010c020a03240c0c0303090609060c0c0b2505 71
    0x2030a8850380c0d4001c0110f034410200c544080030f9402c2c4101a401400b0034000180c035000d9120a40d1000213030032850403000d030410807040304c00b080c280429803580000603501a52a103100c3d625604400701400b42e84204500d290080d881c0c407c4c00c10060b105458214000c540c00b002e040e055654500022141384041125140343c2c01081c008181c0340d000c0800744174850700c20b01000005900d6089400219100e0130207060751003d0b550404011620700c0150440740c3c00311020f0202070b00054507903115a400481e940116420240c0c3d4a2144054a0104a840000800114007027100e424200050005071004900a014443c24030019049a0290388242c50b101c035242c030080b400d0703039000744011600d054007d4110914603880341400415003011386056124204000205400d200351489500392420440d84e6094484420341c41c114054501360320281c40311560380d0b5020300040c01500c90b6003491101074075940c002c4075550402000c5200300801200c101104d01502c040800c001000f16000350340c290403c1fa031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 486604541 1250 486603291 486603307
    0x100e0406110712020c09040f0605040501140a020a09050f0609060a140d091a010501091401020f1506090109020f030c0307120f15050a081002030c12103008 68
    0x182000540400c041e000014642080c0604540c250440790050307001c60325418403010074000d0116080310017038a60300c2a00d0007600007440e01e0b088140c00030b0181c8004030700403140602558841206541407410346030300181c8294100d8000101100500c2c0444611200040d00c1020a446214080d0020f10038a0002105d4074018082c545080741400f0724203019407207104802c07661000700344141058900180540c1a50384400c0001d1030b42c1d058a6041e940d8402c618a00381410105280c1d04a4041c1940201e850146000d101048480c20103c070440d0098054100807092144465042e04480d41450041104140d100481c0d002c07280c10406004586589503030790102140d11144003c48041442c4c10111031421611054200740b030701858401d070481c64603940b4020013161951034856000240c2101d00005000e0f01e00f940074540c40720304121040d291050000e030740300001c01c045400031248050340b05c06004141c1c40c0d00d44410300390100c41001c001c005070302008000310325041500810320200010031038 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 486605791 1250 486604541 486604553
    0x201140711030d020a081014030a1b0b030f010f17280219050306070f0c021009030213020a030f0903020c091b07050c0f0306012706030c0611010b01030203100e04 71
    0x25403c0c42c80390034115115803681720010301144058940b40444040b82501051280c96401c5421841c42c00400500c1803039110fa940f00340c004401032a01c0704c561103581000408601c680021403080790403404000c541d41c144110508101010b0b00858031711382401060890300c0b240010010340c6030100c0007200e000010f00e40303d40070684070300050080d0400c0c03103804000c05d880c61282e0b41405980b4101c0c19240780d035a0b503c4007203500070202615103001070b800d4000380c009810315800108501090b03162110020741c4079000304819500e03480042d09a01d500040850506a05110b50307600c0c05100c0800344000452524000d40e03600381300800912586003c008100018200010f84029981001d0080c2d00c1e024a410110340343c0100011087c011144007020741002e2a000c210641a0764180c42040d400d03030820014050003844d02c801140101d030ba107110110110b010702d8420f900402c00c075a20b820807650300d52441802e40d00014400c40c1850300600c10300c4240c00394036080344103a030340040c1103800300d031f4a40c1021 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 486607041 1250 486605791 486605797
    0x30708270105040308180a1e060302031e06040e0607080702010614010f11011509060302030118050d120e060a09030e03011b120605060403110a12030f05071a0903040501030c020114071103 82
    0x403d80c002200070000481030314951680c8031341c91580d4025146a40e89e144140c06034481120b010440d42c03640031908407041c0d410b201040e00040c0150001400404c01d2041c03c0c0303403402c15a0068003180b1900e0400038056030900a850141c034070740000c81440e00105002800012026114006102560b0340c4a2a25035095020801d5511480c282e900300d00c0e5a0f0080d0001810f46010a0380a07508042403841500240c110441e040e0b0751020061980d046102c504036040350b000c0003502c01482c0c55180120b1905410030441d400b40d0004000014003c480c1e16018103071940b03142689000764181101c48400c14030322001e002c4207003000d0903c1c8283c01c80014915008040903008075030311403c0460040240803138168a124021004d032010101d898803207035212030301740c405880100050350751007010710f090b0b2046001e05141d5120701040c00b0050f89442c0d0304038070745408445010b840d82c404203040040d90b030705010741c0a10680900003040007811000341c010f2010301c000c004a0a000420070140580c40d410000c0f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 486608291 1250 486607041 486607087
    0x20a080919030b070f08090c120a1b060306090e0618070308031611070b0906090607051c02010f0b030c0f06120a02040906090209030627030708270105040308 69
    0x907244400e8403850080c0e50f140e0151030794400101900020040b00c0d00400345140a2000c690060030361064040401c90080c1008640e41003d015012008000030603024840050300921215541d1082c10520300500b1628294050709146040081000710741501048254110420400001030003030890b0209107010142d0340003d0044a00004001410060074480b11550106a072168501e2148070071143c0d5880fa140116100114100a250003914003400204401040504a90f042108540300c2c1400c3c081015580b1840c21505214801001da0a128151518060400030405000d800c000f082ea51079480d10b0b00b901510320100e40440d1a660355054a40003001c0d242000014540b428071103011f03402c58407339182c0381410720b8801300d0511940d0083d9901e2880140003800d00381c0d2400c800c203041d00200d01d1101543c4c5400800340711038580a0008180c01402007040d5541c60f001c444209000300c41130130f174001411410040803c226a440f074100c4044075044a945034407224081001d410a154640c8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 486609541 1250 486608291 486608329
    0x1b16080c0f0708010506010e130203060d0210050702130e0307080306060d0501080f0f010614090402011103040f0e06060307171905010608010509101401050a020f060c0309160501020a0809 82
    0x240380c0700c50341000541481035a01e42c00080c81540c8a50300150b9820300341d840c2c0c1c00d40c000c0c60068588840303001580510340c04030300208030b90151f654a401040810428000c80070004200040e000250b0900d43c10100c141c1582c03580070011150302d0241c941d124002c0c1c0500410400c8000003080f0342d50b544070309540007420210803c01c12540d40c0c82c0110f54a109141145055010f2102c40d00c0703440d4018400c18040f240c41810080000400700200004800c00034000c03810310007231a8211402c844100003910241803011000e0b10118100100d500380c80320024a018469142041080360040c3d1044401c120005034003407105042e00c8420700d1941040110340c2c8800c2c290f141000024005502050603412140700741c4500308a0340354610542d0600001d1b0080300c80d050811025100294411b07030051042c81c542d403054602100c00d03880d1050400c9025503120071003c5001c410b01090075030034498103100d034000712031600000c1d16040010f512040540c10240101c0c001161041094903084c0d40e401e01c03c0140c2d2 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 486610791 1250 486609541 486609553
    0xf0f06090902100e01080f06190f050a091509020702060408010516110a031d061b160b130902090402070803070c15090309030f05010b12151b16080c 65
    0x2000340402800015400e0303204550341458440c1850244540000c451010381d1402100d5843e02040b51802c1805800c01d41c100c4898500300940c98401105a03000c0c01c40c200d5105c0800e440e05041060009a9400c0180c800d444e207c00c00610701d04000b0080201c801508000d83c07107188500000e041405aa40402495424101000b869203031166103c1d000c1d120b40c0e11099112a5206004c583c3e841c02d64400030007141c0d41046840c50800d80411000050700010489460300e0001507481140800c4840760700126401904607901242e5104000405071440d82c200300d0034000300754140d5401101601c50941a10707070001d402400b0380c5480d0111404160410003907a92401c2c80c00d00100380100142c4213986c800240b00701020060f100f03010340e0b01b243c3c0d00b560300d050990741551030b000301002c00d4800032107166681e0003c9000e15120803542d00c600392811406813081c1084911940503248000f131010200c0d0000070300d1125140351840030b50384031325032200c08003009581310301d4408014401d1f80c005920703512401c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 486612041 1250 486610791 486610799
    0x60c1101111b090a0902031b1507050c1212030c1305040c020c040506030d0c03080c0c070b03012c04030513050402031017010203060603060d03031806060914040c090f0f06 75
    0x1480b040001c1032030545401c2c0c0e9643d10403490500311603a0510003981030300003212108008100281c00b80d4404002441807100141c3c40c00340000075030180300700b1103160300b0003407048010380382c410b40d01807110342608041c094944002c90003a0907803100a06175007800c100842c80e0b090320007001d04607402138040a0700c10004141d551070060359825030455030611590030440003483d1410041031004488450340c0340c2440260465406613031081c0b004008141501e0140551405050100000c0c002014100c42042e9603504003003000e9041e19200001c1c0318407041d4000c12141480c07441100e00d50042c0c240c50455105d4018404000c155001640000e40c03080c0040140440707681d480c94040202d803040500305003c41e040850713850903400201d40d2a40d01507400c1c400507a0909140c411803d00511034640040c19020104d000003040c1c0d60b000082d1041c9039901c0d801d10650700188a02180c401d1968284a86460503540e040070030b0710340b805803401890320307009607184015880c1c0142c0d8800d60b204609205903511 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 486613291 1250 486612041 486612073
    0x711030705011a101106070309030e0d0b090d030608070501052a0610050a03051b0607060204032009040506011701021e1909030309120206070f052104060c110111 71
    0x2102c0b0b0b0840c80350044002c2403030f02a01617000c0d01c1503c3c000d01c024000540c0c0c0c50805400600d0b41c103809509000908080403400c2e0354503d41c10007121700c6098000c85504100282c00e2500411082403002d15180503414010b80000250749800c40d442441c020780c1e10040440d0031981c251681d00174000c004070103220410351500100310300c4e1149802d220640d0015035a01d0420030441c3d000d100c0a8481d4004100c1c041401c8204000380254203030240a0910706540e0707640d51700c1240c1c460307801551040c2e401c02c1e901e004205516405240b100c404c4400801d0f07410152102610782d2010f105281c8044401d40401d540480c0179015224505641c0b18241d45009030003429050940c003014165000e441d884c0401401903014415410a99401d503840d0402c0e1424903030401c0400740c0035401a6805a0140100000203041200c00d00301148a0b401400c8a55000f0b90100c80161f103c0d00240c02c104402d1105010142e8006000000660004201000840a140140c8100f0a50600740d42617004944440340c944103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 486614541 1250 486613291 486613331
    0x40c12050a051b040f0905060402040f150806040c1704050c0a030c17061b070507090c1106060102030a2c03030f030f071d06070501111803060603060f071103070501 72
    0xc0700d08a60308110f11051910b915032146005252051000800512803510b0315840030b0380c4510050401454a500c0306134800202c1c1c10707580a081c2c203400d91300d8400c408641c031514540d0090380641c0c0c04d003d246510320000e4415010800d40a070880710410014062110804c800007080e035000c0c000e01c0719035480e4107006003842d0003070250f03030601d50ba6a00820a61000000c9032841f800f89900350301c00180658000440350fa2140d4410740d40c922800310042200c0c04c89100303000640c0241d4440c6481324800b5859941411801010b060643d08140068000d80e80c00810304000c0380020040850480103030030b918004007081020702a014400030420091014400c8015802001c07500d003000c5560313803941d03c211065601d500520481d01001208041141020303c040c18807a484cc2c40045480f014030078511141c1d402c140f621110298100801e00080e080501c0b03002d822280c158090000c0346002c500007120004060310040030007030b591959100f501414410f541b80f9950000091214a0784082c141010032 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 486615791 1250 486614541 486614551
    0x7030f0c110f0604050601030f0f230d020105060f040f09050d0507140a031209080903010905160b070206161406040804030b072c0a0815040302060106080f06040c12050a05 75
    0x7200e000c1000607800d070700064151113194007000030540c07070f800c0d41d0310544600c40a00045410150012040c000124100c00e503c0101900442c2200c0110244d90528a400385e1088080c003507900d4942400340c6a2138443d0b80c2d01c89080151800f04034500d10300c3e02200202103940c00a0090300942162024681d4800000e001c0e4a0040c80b003c03072400f8000c03103155184c0c044c0030740040c0841c82c1140e4203040710465070000381016025000007410704e46060007282c00d44058020403a8180c1000d007a4000c10390003000c1000c058034000c107071541442c08035808160b4920038803030030003600c00000c405003080020801e840b95103c044102a54154101490070406580050104858100304500014600c0b48200b4418882080f40d9617140e544402c0d41c0c0e2082b003039003170103220300360010002c60000c140007004000a000c2e503240c807403119295141508000703041c9101a003000302041910801d020368100c003c0041030300004200c4d00010780010700041138a0a03c0d5a074101c41d451400d210070000d005003c0d13400709100b1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 486617041 1250 486615791 486615793
    0x60d1505060102120c15010b12060d060b040c080604050702010213090b060c070320090906040605040524271b1314040302070905060109060c021302070c0f0b0f04050907030f0c11 78
    0x10323625140720304028003402d21061910b102d42c1000950914040c402003ca450003808005803400d00e04001c80e041e40c00f83c14980c004034201d1010700070035084c60311400303a0144186c030086040600b1481303024a00b400c1d510a042c0d103070f40c807080c130250b080c0d40d41790894114000344011075041781d41d81d26007a40c440807104050040d011025000703128504010b83c103544900484000b8050682c1c881d694480140760241c0706403260300c111080071514101025114803926034100c12100e851902c0c121080000e519104005081142c1070300c0040c001b80c002418041d40c03181c1c0f0428060804803440800c200f003441000c2c0d81a22800c18413900141c00000708824040d501981c01d54024540fa220054180c0d58261000b074005100c04c2010400144610045504144014030200c03403046054038a00c2070760040b00098455213a40361041012014030b150140003030088a2809003400c0c2c9001100045d8000c3d4171030329001d0000c0200103100c3e1403003030b4000014001419030030801c0d480c04c4000246200e5000181d4040c0b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 486618291 1250 486617041 486617083
    0x10033b061614030402010909051008010e0a050705040b0904080c01020d02070f030e040b2b08030a0b240304120216090203091005090d03090302030f1908060d1505060102120c 76
    0x41902c00d502101d00c80e68042c0c643d03007542442c0c100444010103000341821841010b803036011580100a000300c400100ca5480148095030060810f01d0410909030300891003245040355080e0a80c0320119042d41c4241c2000303007282c0741d2034070707242c0c1901911a10031503074245d51001440c0d000b0460b0f000050754100f40280e45101c226513a110520040310207040d1403035840b100030380c0304201480118000200000c0440890000d108031669510210b82041c0d03401440103849162120460606400302050543c200c0c51a1503404000120a038080c031015101074800341d6035440c0181010300801c072151164064190103100c19664150000094006841c9180b02c1d000e00035803220840700900a0a01940c0030b4009010003600d00c1c80160024020008214198001070200780390a440301c0018003000c00c1d01d81550882c044a08a00500c41d14004007040e1007101448840404940034842010082d00c0501000915072582c0005070b180c00ba000108443d0400000b48004440f1004640341305030040f401c0407410 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 486619541 1250 486618291 486618317
    0x2030714061017100c030b091009050f0f1f0b0a03050f13020105090f0f09090307062d150b18040608011e0903030f0e03030610033b0616 60
    0x1c84072003682c40701940d54803805010180030040d074406817280e030142c20009040c5241c03802064100c04111590702840004000c2040900d03424000c0c0e990000842d070342d20400785440f00007040d4024024000c1c5ca01c0c0200d21100c1184800801103480250a950f100c1540f070340c2000300e0040150070300301d034540c1405a400c004200080840d1044d0355140e03034161642c50402d0021018480c17512404848168002110110000aa110700b03500ca400794100401542c0d50300c2660410200342c0f440c04095500400c030007124101908500000c2610f403892841010581112001d603054a03103280790020059181e0006240f44040400c0465160025003540c1c140030307440d0340c3c5c0403c44c200c560003029002e80c1485442199181c03907240e80b0501080d4030a06000547c8945103d40170125451500030204d154000000d21069140c070b07180d258141c002c03a24040c0580a683ca008405100e0b000c0016100d610b00c41d9100e061282c80d4070805110500440103e80711450400714010342d40d2031007000c2c5004103e1000d5052 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 486620791 1250 486619541 486619559
    0x70f050106060905010c150f06030c080c0303070206040b031302120f0c0307080601030b101e051918020d09081201210308060603090a0c03030518240a020307140610 72
    0x203804ca036016190070741c08a1198507043c16045086a85011487d070f64440c4200d03a00f0340e0f00c02c4101660285d02402011800c001400e0310b0500401c0d400b9219510070701c81c00300181e0b92041164240d030b805c82280764484c0c80700c1d40e05003041412004001d501216110460700b0200d00011040a118645030458458a01e120141600d61285020b158147d401580060000c614100041900101440c1c500103070241d44211040300c03881071400c080107040101c0c0c4100803e01d4624500c80c1446074030041549000e1400010f0794484d20306080a0440d190041006e030a4048143d1001c0744640e04100c516a5920160000382d907911003d0251071b0603491243d8240350304c1007100d10f841881540c90340311648603854407003c001c0e403a00024040c09240c0b0030b40001038002461681c01b040118401d44480e61240d150f010001c04c44030190035018058215400d031401c54032038919429459000755140a41c1d1410141390032411803098a1001d404040d03052440d030a90385d800903042c0e10420521100c0c82c540b03134a0304001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 486622041 1250 486620791 486620807
    0x240b0301080c19270e0313030b09010b0d1223041214030d0e060c12040803150306090a02031c02420105040e060c12100b070f05010606 59
    0x503000703980110302400803418a2445004022440a00f80d009955035078a2241c2c10104607928040d0300446503002c00400000d4001e002c1345170b15000c044c609280d61991b424080b2003591101800e203014100c0030416a00d400c1d030051415520203001c201c00040a42458680c3c4007030940028001000380740c0c03402d507200f5400d48201070707868071640d03662500d45003846144030100704c0c64003a40c3c1e1640b001c0b491014804c0800c01003c444000d00c0700441d44007051040c081c1004001412105c0c19401040f4100389030aa244050303070700c594854107494a135150301101490049450716915014800d240074000c40200c0002c40004540c4210704903600f940c1d00b001080d44c101880d004400241e8000c1c0c00520113901000c40d02c5e603011140c1c440f0419518512421046e01200e8070f05a0609a110b41c40148414180750242e01310443c0380000811f01420300140d01005031041944401c2240c02039004250400359a43c0d01400406c1480d480070707250b049034148070710100003402c1e08455946c6880c0300019120702511017 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 486623291 1250 486622041 486622049
    0x90f090b010f0e1302011e030e0106050a081e01020910050309010501090b060a0503070309060501090b190608160306030609150b0d030806060c010f141f0509040809060d240b0301 78
    0x5001c3c59181d0310848024400d26800481c1480250b204598600001e001d110b1a03102c4155008581680c0e689802801c4604035040320b401046800c00601c80240f00240a030320082050f092402c628105805c02802030003464142984403103014441014107901030082c500400b40c0100803c1280d0b070301c1003044111040509940d40080f420303c8240071541c041c801450b8040d02c58180400d0b1602141d0384d041c1118401d8000104803507440d680030651b401c0c882c810003941c02460b54003407203207402d0007405014603074024001c0c50300625001031010858440d0300b0080003107078800b1040c800d0400510b400d81040d14a5505081120b142150400d030b1841e120a4070b400c10f50701519002c83c5501c881c2c0500045030300c910320a0201d50b407109010090074031944294000c003440c0340c1070f0301c00ca41070a00143e000c04035074541d000220000c9003802c0c08143d03240421560015844900a5a10045c0d43e011450b140a0941c00782015413412194442d491520701f03c400242040680c94403142d5201c0d442785042e80000c4c01 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 486624541 1250 486623291 486623309
    0x61e0a05160e011812120816121e061d040506060f12061614130521100501060305100317071a13031103070c030209060301110a031b030905061906090f090b010f 70
    0xf0b1003410b14044c01c00e8400071140c000c0040fa0041c4045940003c4044030030190002b00e5039071000300400c1040c04000720080303440c016001140e060070b8403076075620b480140480d40700e10b80c0c0f2285986507a40d040c00458950f2080015240303107203400403c903801c40410540080c0841c04c1030707014020f1864050100c80f0a0011203441c2d010840c101403e006e03c000c0030400100921118014600a502003007000c40c0e952802d05801141d2903051010040c141c4001410090819605942c188000b610650801808012142905440d1103035428145940700040511031003441c80d200500902d4a0f10034458160940203448024000b24000c0842c0c0d501d100d450400b9100888a0100303000601d0b0140302c00d03420020080004c143e801c0d44140d40f6030141c1c0050030301c4003c00d0340d491100e80000032170601108100043c1c1410800201c043d00c1c2e1580b0f403072004003a034042e421101c1c0907850410550748400040e181e0080100300300309440e6003010090440036025201981e03403000000d0000018569032007035400d009 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 486625791 1250 486624541 486624571
    0x606070209180309030106030609020a0f0305071203031d0a0c0b0f1804020403021225050607030f12150501080c03071e0203070203061e0a05160e0118121208 69
    0x744800c2805001c00702d0b141c070303a010400480010303a90901401000e14003680e00029522594410008441c1640d803090040480d420030410200d400451080115903825904003071610041c94110020501e05d00101416400700305043c005880018143c00014410091717401d2140d19449002017a0041c40071581c0005400c01c0607600803060240955030000c0c0c042d00250505440b640000d0f4400e141e840c294140364050241300860b03000102e1292400e6051a0b043c2d00c565080c000814194402c450015080c0700c0040326440d03189101c0d08060202081c010b804100d80c00c442000140094428402c481c00a18900041840c21118500700c0340184600c1c0c8403e415030381400400c04c240068408620250701081c0505409a20103104e100e103c2c0301042852600341449180003800c0740300180a88808501d08800c200d2800f48504100c00840c1c240d0400d00456038128004803400a920b00c40004466459900007540e03030059044030b0183d512030700c44001000303800801103036200012120588103020207 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 486627041 1250 486625791 486625801
    0x117092a01024e04062c03030703080c09040906061a0423060705060a052409010b09040b0a0902180d0f06050c120907060e0d170313050d02030a080606070209 69
    0x180c02c8441050343c07040c14000038024551941d002070f8015500120104210364510704039441b21300c03100c0c540b01c00c0030072241c44820500000b013541da028101c5d006050200c882d000c10030300d414000c00e9804816008209200701402840c010001d80310b2489541a0116400c1402c0c1c5c60340e04d0042964207540006041414074417209200007500e40040d042c1a402078001c0044401081003400203511a501217040442c907402c0441201030190411003800b07040c005440105d44d00c41c0e9070b07420103e045442d840a210b44403258800010000c00c44125440ea00c11b9132424002141d0241e0f0b00034000c2282ca81940c08852a00c040c01e001132041d100800800a00e1903a00c2d20f000960340b030340810b80044132802c0041c240340d1200002500780d40203a5812506501c03801040000f1a4814200c000840040c0d650b460100215a24043c09800e4903001039190640400042c11640780e040c1c402c00e500740c003c1700716606000507080181d02c0e070b8018640c400008000b03900040b910704182c0700b02c445050380600103148540e07072 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 486628291 1250 486627041 486627133
    0x50111060604110c0a030c051509031c0b06070f200a06141303110a08030f18030c04290103180303090f020a0609080f06060117092a0102 60
    0x101002c03030100c3c00028060b507001124104650441d141c03098890020a00050624900d054140c1c41c0d040c0791407214100300444850044281ca100c02c1041c04a60100400e0358040b0b0080c24400101d1a00020701040701d10500401c16202c240c0e40d4042d03c02501e1540c16010040e0b0490744891070b480d00802c42d040c00308905886803415404421080c1c80490030018018641646803190340e01c2600c180018640000180c0b8080c0501001440c980c0c0046203070071200001c2d030509006018012400780d004515080054605001d007945488009104200d030b1802c90110030f0840d03901450800141414000005195020f0300c5562080c84026000c0006114160340480180000741c41c1150000910500079006817034419880c809072240380c6911a5050800da0171500c1d00c0c5140740104825840607084c0700d8242d070000202105214104145041d56498810613407801c4002089500401c001112242c60b050180d602000500001d0b400d460071280d11500640c2c1c820001c0410761100300c0040100c07006076003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 486629541 1250 486628291 486628301
    0x50d050c010c061104060e03060f06030d1202120c25050604060b031e01020a030b0102060f132f041107170d0603050307050f0606030601080a0809120a0c060207050111060604 76
    0x11141e03c0110f03c075030700140070361a141c2003035002c0c3c8042020400e800c41c491600340f25032603202c2c941d01e060680381d141c00c41c002940c0c1c1d11480c0c090028003c11000500c08455503404a079000b020506003145c85043c14481e160f12a8071981502444200011040c4c60354101c6851840350650004001e210a03103c4e0b0701d03820010041161081e51510482e029041d43c6d41016402c1798442c200140016183c911311071000d41a01c004500d4036045412003010403c0d841d1110b0421504a02c0140355008180300d00d1404201000020000c0511030100040d2917100c00c0c26074102490a0005030b409100203182140940607601030a58014101030020b1402210300e0740b0000581010361865030082101641e036101c050950340b1445080d54150403a4445940b170300800c100c0203411040039001009950324107800261100e8072000d000b09036610005410038a9910800d00c04800d5050809455595000e46005403401a19202d01e501600480c100042c2c0d542c01284e405003503201030f01c00f40c252070392070300e04202c0248 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 486630791 1250 486629541 486629543
    0x60f0103050c010f170a090b07180f05011d0118080604020123090d1e03030219050a0f0810180e070819150f020f0705190309091a030105150a050d050c010c 68
    0x95803400d1507c00710300607200c25400707102c00f80c513a01c8011b008030b0620540c0e04d645400080701c0303025812081045076841859501032001c107040c210340c46030040f40100c402000ca451045802c0e1181000410100c1c0d01040c2140120f200362242281004046200260602c0c0c1e407030794002c1d050303090150041c07904150030060301c5070344251a01c9010110303a07600d14103150700c01d007405e5000940c0411079000c2d401d42000c84051a404070b05009007029030550700103000c2e40302c40044c003041081c1e02001c508214112000c000140032004046e07030328804610325181c01841c2095407104188540907000070f1b50750021651051000d103004c071407103207010f0310784401c0046d40e641000180d0082d038a10301042465135a00c041c0403ca1103c0c8a03465850400f410f0541c03030190900200d03002540c400d12131000007a04840031908803040a0300210b44a1102425100303017045074840f880c0c055080c00c003040600200f02c0821441200116150a2116122424400d040790300240041170390788059245d40540d070040380200411 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 486632041 1250 486630791 486630811
    0x80618010e1c0f02151003020109140d020d06230405150907050d150204060e030d05040e16050c06191826160305070308010e19020c0c03060f0103050c010f17 69
    0x17454161207a94140700d001c03120400c200ba4440c80910840da80007001e07c0050032880b0181d00c00300f10800010b000240c142c0c10092250044900400410099411210b11020402c1002400b803111880300103e429048404403000e000d40c00480400d00807420341c647c0142c0426008182c0c860800050207425017010000f07803a9201c0900d0700340000040381c0001c10144c0650307542d404544400b001458035058101e99040148241807100b071104c0301c8550318899018804c0c04d05404805004142a902485a210381070b4007409081c1c100140c00c0d00300300d405100c51525010401100c1140d440c42d5204400c5000000c0510300d40d030100d040381c3e40f103148107140d0300d422501c0e01c60700d010301c00f00210200f41002e4004401080c400b02d0603c081c5500112424010720f03036490303080e066280c06c0d400101d0150f045401c100809a000c5a138001c1c42000300101322030080c1c080e00300d5440d418010030314210746c0c509102c06c46a0b48202006a611940310700d0704040b03400170301c1e190043d91403c250401072101d60000c20017419 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 486633291 1250 486632041 486632053
    0x705040c0909060b090a0e09060a090602072f041418010b090f0f070c080d32010305061e1302010e09040308240a0501050f04080618010e1c0f02 63
    0x2910b07115124030002001d034000402e580b11010404e022040049510610500c01c03801c0c00c00c00240c0d400f18540da4000110b290006604640d0304c0c0010081c000c0000c040d00d644028000e2a0000c480700800998800100c41100480581d5a04200980d41c28644552842c004203000ca801850b0343ea6070818040140700010074dd0f40c40610120b203828004540d4070041905101c2400f0840c00e2240c820b9401c04403a207800c0482180039240e007081849285d540880d00f07a07030340421612440c09a250661000c0450403500c1000c00100446c60303620b08280019510360080c04041590300708820441c100c0f040c1080b210350555961191010001180c0076400d0341031100111112010381c0e111b5a83c2c078412886601c5d201c8081c10700905100c002112282c0c1c2c030001d8003410b45105019039441c174000e8100e600900c1c05d1a9070b00d00621403404d850159503c54000c51040000b4008001c401800704402040b0105c0200140d1540d0100142d903007c0e11200e100d9020105424a42d901340300e4200040c00c1349050044842c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 486634541 1250 486633291 486633299
    0xf09060c0109050303160906051b0106090c020a03020f0a02150a051e0a080601020a02131a0a14100306030c0302090403020a050703060b120312070804170c01020a0305010e090705040c09 81
    0x10a40e040c1c202e04641c2c0e9000007040000070200700300700440e040744510348100315a00b041c0d03000e46903205203070030345600d03135003110100b0490a0250821000303403024500c18003203940c3c6c901001e03590707401603001200940030700303444c651003844002401c021080d001403500c41460011640324046030b00c007600c0c44080080800c8203803100e05031b01c150b84a101c25145080e5560303110036080200703541806421941150007003004400940e441e000c04081100c900c5000081c01c11a1542d03014030400f1650741d0540092045000144100d090803500681c400c00340c501144528020b00300320100c2d42140001002c0c540c00040038405800c1c4550160f0b8864480d004a0b81c2d079032056180e961801c5402e80c000c551144d100c0701090441e0401800e5070640d51207520040d414440004014000a00014100d000300010000000d00340041c0700e1550861b400c05c0c2040361303034a000c0024142d010790700078190200800e0510f4000148a906402014880c1d620200a00262400c102c108805071000460070400c108613020046 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 486635791 1250 486634541 486634543
    0x230307110304091104030b0c030f04060c090f0906090513032a060f1a030c0109090504020a1701050a051e190f1d1005041a0403050436020f0f09060c 65
    0x130a00080400d560310b40d480d40c80c1454507108000e05d00c0c0c2040f2814024065524a100100d0b9001580128041640d00940c5000c40d149015603000c514101090030000403900200d9205409607000208184580c5e41c995000c02c0c0c03e04000540103001440ca8061080701c1c5818001804c0000352040c0c0340e441c61105900c6a5099940780400000003079a100885010311222100c50219601c1c20340190645810711400648154a68800c004001e5241d000140c03c5655507000e0344050075103c404455020074035580d1500030001200d450009500d040045440e6030140c094000c01401c4001018a250781c0340200036000f00c84a4141b80026902d400b0408503100c510f0161444007071415000388001d4000104403480d000303240e0070f4134001a00c2e0900b4803000c109400f041402819420030440e8550700ca91a04940d80e105e2039010a05640d1907030b4401c2c07130302c91b01e403080b540c41c41442688520b000402100315904030300c03803203d0046c1c003070400b0046d200a400550020b000800c030020611420440300b1482a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 486637041 1250 486635791 486635801
    0x5031b0c030a030509010c09030b0402040207060507090312081603150302041803020610050303090d080c0102130303080609091b04110a030501170303010b0a0804050c150a23030711030409 82
    0x1184040c1c0010501542c82070303040c0300300c82e40041c041d002400004031006000d444070046001c0600914940d40008080d520b85404951070705a00000c02c01c01071403c0b81004080000f41e0004031400c107503510081200612500301140140b9840020921076404040241c0060004041d01114048201000009a07445124004208100e000e411810000314900241000347c0185454254891640305000d0b5413000011f4940090342562000420051400c1c81c901c103005680f15540f842d0f000040d080203143c90b004e4008226840b94844c14004d455000400000481c00c5a203504198044581e444c101030080b6500140c0140281000940d40c02c0307007121501070f40c0500014800320351210010030495400108580e07030210120003550555041101c1111540709074481503007003110070808134092010500000707440000040c0b11071904040366200b41c01036000281d2000210f82850090044001c00581011a100d480c0e0382c80c51555a13807072070541d800400541c0c0150148024030012034120314900c41c4c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 486638291 1250 486637041 486637057
    0x406090f1410020f090d02010c1506030b06060306030a110f120d09120b011a251104060f0b03040303021e0712051204060b03010209040c080a0e01050106020d05031b 72
    0x15821060351441c0c000e2801d01450706880030b03148104900e40c41d280f042d00541e00545000c43c1c001d4060b04840c00100e4616003201c0024011094101c0808110b41c40707644484102c1e48542d940c2e07c02e0307650740d100708281da020480341d86806070460207056001030805640070b592440000c1018210522460202d81d000c0a4248883d5091740316140307424000d5089888840100603201c1c4400d11880d4940d2881c20031001842a4070088500c6e11b102b0582c8602c900565040320840c81100c02800c07010070484440d001110005d07921483d041980c3c0c4100d003841c3c011901a00e06081c40100c00c0c514180500d0059070000703009a04141d0700703100707036084a142050509050302d0542011501c038242418071058400c02c0b01da50070140007080119000145a200c0001d61040d086140002c05100c50b50109003e0710031614104d034090324188298112503041000c01d4010002c0802c200580500448038070308941c028001d180241e40500c042c001c40510440040d42c3c0700180710f50080030b0210401d50100d06400c0403003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 486639541 1250 486638291 486638303
    0x60c0207080a15060f08070e06030c04020706020712050c0a0b13120903150507082a2d0f07020603100509010b07050615010906050702010203130b0301050a15080c030406090f 76
    0x20318400b0241e844c06040080d00d980081600d15a14101d06c10755141c2440c80345030003160003200010301d1070350103000021034020064002e555440492802c04020342c0244030071161030b09580043c0e0011481001900c5101040703200800d0000202e403149030142c90f00038004501c9000182840340025031000d540400404c143d199401c200e81140f408105414004c41d03180300c05807601c400c101420354842c10044e0000180b29034601311400341c88404c5654030440400e07200d1036000207040481e540320304c48400c07908401203a540454000c49808120503108004078242d0240040c84010094030303252001751307040203400c0701444500ba651400b0a10410342644951160780000c2020401d010703052041550103048069035002a0701c0900c000f030b0480b012801078804200c0041190021079000300101c3d280c040c141602180c8665855542c100154400d0003994024806900001110540060003064524146e1135028242e44c0c2d4046400d02c40d0402071080d00d140d40c40314140d00121b01941b03010000280114 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 486640791 1250 486639541 486639563
    0x9141b0d090c03051c050901050909060d0b070e0f0114041401050c0f06011703070330061743030b1504060f0e04021203040e0c0c07050a050d060c0207080a 68
    0x1300505c021202c440040750900c84104800a5030f0781e807120480b06110800c4821303280c0741c2c5540000c0b0f111408240401407210b10000e06000e003003a00100c031503c1d035000860307601042d92450001180e03944d140304c0e40341c4260f5009010602517a00440384c540c01800c810b24219040818640000c0d103030441c0c42041000d42d4100000521202c0c81114040a103420181d00035450141d15550050540c503880c80c208205c101e1110a400c0307001c42c5071040844100e4003c106020468442c5001600d52003004c460302d8481c841c4100b902c6e942c00700411300c3c1d0980070503a040070151013401c51082082a820000011100850490110008491010307d41c003591510151800009051042c8004c589403600808030090840e901000b001d040c803141254400d50540d004400050b030210014a503000d82c0d00103105031001e00b01001007806a1001510141100300c00301c07802540e035007003031042d02c160301e00078280c02c8007008680001084040c1c00c00c001044a0784100c170035140c2c0d985106803c1010318002122111114 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 486642041 1250 486640791 486640813
    0xa0b1e07030903020123090405040203011107050c0909010c050d0b0d060c030b0909060c04032a030812070e0d02100c0b010f030203070515121f0f09141b0d090c0305 72
    0xb11240e00c1c0a20765814404100c401b040b07015a0090040140c00c6210f82c0d142c80018045440a422a070381c01c070140e02c20382e038483c4030900d02151641d9038100396034001e41e0440c001485000f0305018400c00341e2010348503d4900341c0c0c0311103000054440710380460303045a00c00f80722100269003440b40304c007043d9141d070700010b0031103110082165084000d000c4282c00c0d0302010600007040c0240049404680d440100001c200c100740078440103d0404440c0050700818081c2d0000c20320040c00c00500c0e51046040c80d00c50360707682e84041a80c0180300380c05565042812208454010f0400b5024240f280b1030030305220344403800541d61020611804d0300420041400a5400c1045080412060014100c00c5076950742e010103a1408030894000c050540c0c4440e8207a40201e80301e4001210289416251400c0f00d02e1101d8581d20700b01008441803054810381807510b080700340c2066642003158020100c1d03111402c1c1080e01800301d894140c2007001c400d024540e44d001010300003040c51800764025842200507001450031 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 486643291 1250 486642041 486642047
    0x60906110705090a0c1103030c040303021203010e010312020114090f0c03031e030c0f03090604030906020d0f03020f0d02070f020405072a11040c08060f010504050a0b1e070309030201 80
    0x108412800055120500501840d070700c40f40d43c0303a0b2140c0103110010702092010340031942469a00402c0000d800000248a0b410442c0e02c018025030f40242c007100c4030100c0b220a03104051000b4440c1c1e8117581e80f441c00500c0040c10703a002a42c18001d040c80003184154101d031000d604190240c0b58040240c0c4035285c2520070b402c0034808030385d41c20021000340d400c15407449490701c07030319003002c100c5141c054000001805011920302501e18840b00d1108940c2c132460120070055443d641960140c001c942c51500000303800e032002542c0d602c0380c40c0d2555894040088058207901a41028682c821458001d100d5078503503000d94406081c1081c0500f00c0010403c1003401880704507000600300c0070800c250861030354400940c030644001c039090700c8440c0e030851808900305074a5403071030000620350060400d01500010b030350004190b0f0007124101c0c2c00c0c0c140d40382400019100342c0f08500c0788030342060078207008104200340c000c003410107a552101440c6000e80c00752001803803944502401c802003103d1407014820746d41c0c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 486644541 1250 486643291 486643307
    0xd081603020f03010b0c07030803040b0f0c04031101110c0d05100c02010509071509090f0b0a2916080f04030c0509070e0402070203010f11041403011401230a060906 72
    0x80941800c510b0728401a600050301d1205020700c82503000001252014160100b14080055421000540c0c603828580780060801609840c000c3c500380000c400b0840da13800c0b0350219800c495002510650b40c8940c0e00054446140d00b00200100d802940416502a1100100d50003010302c10009445aa40126080e204440d03851141c801103a24140806c50701d0000003402a041d190840103150f884260307040201c4001e00030703030480d041640c1800b801110a0200c7d8208426811084410b2059142c44518042c0141068007a8481450980400300324080a11008100d000040000121010159203d400c016403051040c1c1c0708030100000c0030000d00101c802c0002c0035010440e000c00c001d0900c0c9000609804409000c2485140c0c005400c50455409600170207045100b0140ae22261907030001682c1c07150041d200301d08100c00120759030b801030701e0f041c4030303140d1142040e148680281e400c1158220003006c44030b000c0c0b1035038690014240940d50310381000c3c400504c210f40d6014102c904103040204051 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 486645791 1250 486644541 486644581
    0xb0402031503160305150901020d0f0207060e0c0a0611031608070b18070e090f0714011106010e0a112205010e0d030f1220130f0305030702040506120d08 67
    0x103e1035440c1440091804222040d400094082d0040b45450b661a1140203104403240340518a140079486400203100c1d4025102c0a40284001c02c011054071303412645580546110951141e06c010307050240b280504001c1c54195071200071a4180b20008a8507480000800d00a440114011960030100700600c6205540b001c1078006210301d2044041001d65034290380d02450314180400d1001440d10700c001c004a080e00c54202d011103d06554407043c52602c010f600d220316000440c40d0380c0100c103107500010030904907060050000c0c1c5581c3d9091880b0010452401c094980300301c104000301c620f08440300140c6103caa05440b41c01030524000026146c4560300c420035010700403514400c0c01180d0440304c082038072145801d0900e2844017101c1a4002400ca1441d00400f00360002461400c41d0351800103001c5d0041c0c00f2880c0c041240c5c55400142c55040c21b032100030072540c0100000300060516400058202402410982111402540c200e042403410340d800f49c00204144208201d15034248a42c034401 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 486647041 1250 486645791 486645823
    0x612060f280f022a030414060d150e090c091605070807080c0d11030909040201030b0d05010f050105150f0f07020a14030706030506060d09050a02090f0f090102210402040b0402031503 80
    0x513940509010b1313143e002c1c510807030406822403580c5000303d13181d40d8103c500e50361078920108840d0111903460540c0441c00d01030715a610049600194165100140e0412503410003440796070b5a40d40c802c50907a14992040040c8100315062050400042c00703640601100d51150a901d42c89400c0e4081d507618160041c0402c10410600c52000c400341c02c004411140040019981500595030714001a805000e0050819421110445210091000c103500c10034000d0003908090000d80d9a41c1c08003c401104988500c4a401003004007400c0c040c7c1143c010038210034150050740c02c20b20540c00207440f8400b11340c8201c02e11a40c45800b01040d1406000301c401800c4c031414104101c0c100305000c1495030089207a440801680c8001d19024814100f1480c030507070fa03000300a9229885c206484400d900d1342616404c0180004d940800d50002040c000c1d1b03920846c3c0c4207400c0d8080351a07d1480c0e000c0c00740141007a81c00a0f0386500e5031102e80c45034001103224412804038041200101000c6c50b180c0703003505007081c3d54 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 486648291 1250 486647041 486647107
    0x2061609120201050c0106030b090a020301060f060f050307090b0304030e040c0306030b1602010e031605070b0c030706051f0305030a090b041a0a17010e0612060f280f02 74
    0x79040114007000d941980a2034021380303c51640044130300500c026040541080b070904200820000d0024880034018400e500a100c40340c0d42d1443e030315665802c0e00500340400d508075028500c261140f0055980720782e40303251942c1c2c030170303a00e440708620355109035000d07800661007242d900328604141c0151140c070117552a040001a02d50303142d000060030b014229081505a421400300040d1003500310f11010714003d0305a0350380c0e4402d00104e40c0e031029140011685070003148000502d98000c41d041da801c666134a4051860311900e83c0d18580101401000a0202071640c001820100c25170036100010b18480d80c0150b54503120500c01422a008551104510354800c00c000e1001d185080c10750b07030550810300c14181e250b8000040070f894078065906034800d001c4108000059a41c8038007041070040c01d040c0c4403202ea024050843c261266400c0301c94038a6481a140803c0001140c6041d0aa82500880e00780b040404c10180c1c5205482601c400d0000c169000302e503540c408880e80003482d2800e90082c1c0c078150 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 486649541 1250 486648291 486648299
    0x112050f0f090d140a02010e0624010206040f0f210305040303320a0207020607060603210c0b06030c040f0204090f061203120204050a080109120e0d0212160602061609 73
    0x700c0c0300000c4d41c070103086200108040701d1060003508034626404460b03055520b6490100c2c110701c1c40006151824840c0100750003010015400400d109004039007000140b442c0103900c1d01c4942c0b283d44502401c540d80d070100700100203d00408070000c076a03280a0756011aa03800d003820010140c603403600c0c0301162920704c494041010701000c48000f080443d503c042a0140d03440000f40c00082c0180c100c00780d00a18006848003c001003030780444217991040100300c248010480310001011000300549001c03038044088030001c244501042e56000c50700408441d4503e4410001c0b4040d03c0009994400c80c80e0041b4050005484500401451504a031820019646001390b041c0c0d400300060009401d2105400802510883c81c1e0119409000081e02000c4142d542c0d04c03006000f000122070588004a0018490010768407513002c0d02c0072a88014549180380855400300070308000b145140c2ca10520500e84208103485a071050800202199000f401040c5402a42801d0041000710340504200494200340 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 486650791 1250 486649541 486649547
    0x513080c0d020904140f0706080109110702040f060314161d220204090807150b09061c0b04030201061703040617061801140a0b1204020108060112050f0f090d 69
    0x10309981e01100c41c2c5109131104d06040b1201c08a12a002c04940203000d400d642448002861000301c03041580c8034441680d03186184400c03900803480c40040b04038200046070161909401c44281204140000945547e81e40e58488000310010845402d641041c504020080710304600e00e401819240045251802d030481c80b41d40c5520000d002e4404040741c0310340500c02000c21482d0010381c0354050020002d100050802000d150040b800881c1c0001a013990000700c4403030b0740908182c1e0400038004170388580b11001040100900b1820071420700208240c0304001c540b1b520485401a4003e40000909500f401c0b20982034442c804401c1c041984100410000035a000f680c00500f120956600c43e101c0d200e9600058110084500c622404c00e41400041020070038550b400c080c1250483d0422080713513407200b50751914020a0707101c9001c100702c580003601650090214030380c80841494070030b164007071129840040750004d48691242031001030401a00816000e0040d410000c1d800003054000d84c000402 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 486652041 1250 486650791 486650809
    0x60501090506032a071a01170c130f05010e0901061703030112080408010f0b090106020c011706180106030b01020606010305010806270708030315040e1e0312070513080c 74
    0x201d0500c0318240918845090804c4c0d0302802042c1801c441566105541070510036a0342c9074800d02200c106140002070362007054405c13001140003e1014045030f030040760820940c098442d184040c1240c40700c0400e130481107103124843c060040c8603101012410305248e0075007100c2d84c0303402542200340c42c0d40c202c1008000000a80e41140c2010303102c841030b00c48074680084203004e42c1d444407125600340050700c0c00c204516013160440410543c2c03001c0a9030790f00c20040382c1c1d40034030302452400710720302d40b804000ea44100054075a0100c0b018156940d18110790024980c5004260300400000b540d6006980a56a05224064015200b4a07090100b03504104545880303070000381500401c0814a4001d10406c40c01003030684841c18503900755400300b40c4d100000f80e1264012038074a80d40c014481d00c0d49445180070300c1070070720741c400c40c40040214580c5138120300101c1c401201311545a01c002e21905503508a9088224410710440e9187d0741c072071003140000d274803402c11500f003c1248c2e044980e102c0c0141e2152840 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 486653291 1250 486652041 486652051
    0x5010f18021336350c0c0a0e0a06120b0105060703030b1e030c030307080406180503160501120c0806060708090405070801030b151c081201030605090106050109050603 73
    0x354030a10200310a644000d10a4044036050300030110022a034510741c41d04143d9004030403ea4058582c169000c059150710f00c015035084140c60700003520f6441ca2406003a0a0044034111100c4460340800541c00c03e010307911003100345000800f000860100c90059500901d600340e096441700840b5641d00110380014026240251000304000c001c0c58480c1d080700e0f0007028042e00811000398826440159034101a0005010703106e07200380e0b0f680d00e060000848500c2a00801c107282032070704103201110040e0001c42507541441e9440c0000c6125a0103001c07010349481c03042c00090707034a4a840005030601c4100040741000d03074a4104003124458001e00c002d075109130100c643e11b644824a260500751400b0b41c030925a0058a003104100c070300d40c3c00c030b41d482c0e060760b00409010700c0680c1c454025024041c150f14010360002c00c102030690b600d0741da0f00c1c4003140c028443d074055401d1041600b8503c003050760076802500c5941d01c45051004901e400e114030400340c003007881d00005035030a10003c5211f03448040c107 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 486654541 1250 486653291 486653329
    0x30901050f090415060f050f12132109080c011e05120108010204320f150a03241412030f040b0909070e0102100906150305010f1802 58
    0x40c030710421a800d80200d50301250014402c01210420240c2c54083d131125001d140302048134200064032950060b81602d007000c1c03600c04007500d00842285480d806580c0582888070b5440c900f084a00015502c07041c00000c001011030701c0d03203130a6583d00c0050580c3c01c590b01020040d002450451800d0f46c3c07201105813101e602841c50000400c1e2910121503a11551006024948007000045014001034008008560080307104203804041080742202c5001600084c101207591040e9083c0c0c0c03030a003d01c02c01c3e840e15001300f25111020581d031503203145030f002d8070003e0002940d4130800c003644000e410b0341034510049100740d00c0255040c11014054011705207070040c400d0709003145407400040100200c0d0040f00310007031804e407126900c400c1031131075401154040d03116000380d0300064001c91042040e040302a005900429441481d440c10800400054205540550700d5044000000d1418041d0000440c0305400004006005078500400c031041c0d003004e4888115440c004e0800340c2d0b0b5501c20b480200d801c0382 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 486655791 1250 486654541 486654547
    0x3030503040308062b15020c07030b220308100f06140d0612150f051e150a1d1e01151209140d020607050d0f150308071505070203090105 60
    0x300000f0003403031040c0c01c00e0b65a4000800c03491050050f40b071804400d01c0c41452500e5204186c205140264010502404100d500c2024104040b8408089054005201b05003c2c458040403030b1034440c06550750340c800d0b80422540801d1000302941c02015a00030403a4803000312040c1c0c1080c4005240038201c03500060b00c60030200311014091b440e98403100041454000488103580301e4500084581c6444c3c0103441e0683c078008a402c00e81c50540545441042d5840d00440e86000fa1801b2046016001d055215022001d051141190f00c03000c40240c00fa05210014002030382d80803922000c0b40d00020840384082184000c0c4400d05c80d9889890b60550302a1b1104602000c20392804403010700414030f001c0142c1d404c0507030000501c40841e00e8a000e0080110a44100b002c80110990340c1c1d400565082e40000e5040044102d615210350010101c25000314001c10079542c41c10204820041c103400607034a172900054800e00700429a00746042d40c820074603050100c3d2815082c043e4481c0964089641401000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 486657041 1250 486655791 486655801
    0x2031b03040b07050705030715050324130209040e07150509180703091a040321090f06140906043f0f020106300f0212150c0403030503040308 62
    0x34401e81d00a4050340000c551150030074100b4980c0c4410a00c1254040d01544801040c10121010050720380078698441c1880c503150010080c145083c1c0740f0190344844007960081c4c44580d10060328101030350b060350001d600c481210040002301c034216080d4a41d903902100d000c010b10070131840c000d010400c42d0300b0b100303850740189800b003800f107181d40040d0410800e600e0100144a45c055020050003401080701c41100f0742200c0c25010751803c142c0b0050046a01c0d503d0030b0201030039802c01a01d41c50f50b030440119401c1d88540d9400000582c42d08100c60702d03074440c1c034218200704035107501541c41718100005140d2802d20741c0303540e404007860b05001c1c450340c0c3d0b060704401c2403d0440f4a10400b02c002d1004141d4030718030990401010002c0d01201e00b8015400c1110005e9010a2103007051300c1d08158028010910485050728000c420000400f126803101b140da61401507503460254004546181c4043c181c1000307941402d00401800500c0c40c0581d0200b80014404650f201c020b590b400780d85818101860340b41c03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 486658291 1250 486657041 486657043
    0x18020a1106070f090501050f2a072303010603080708072d030909050601020705040e0a1a1006020111030f040303090503190201050a200a0c021306030b0f060102031b 72
    0x814855000c0c621900003800b49856008a18075400c00403692040c04072526030004480c507105076007400c230b820b41041c0b090349044017114041079a203503001c4030100072803200d42c0d40c040d003403040d02e0b40007950380d058030890440e0803035405941c050001021002001003c2c110b41c0c0346003503401000030181081d1008030705c0b441000502c80070410604241c1070044aa15a104081540740301044c07800c80c0020140e16000610b201d26000d011300800050f0007601c0c2d598200000e010040818000f514194400c0500c41800300d031a809a151603000100f03000d10245c640103450004018041d4008021689000d80900307249050b00e0580341c00c05201200340145403544c1c1003ca0280441c039102030001e00002490f001142c54241101d0600342c501e400a0046d560391004810072140310b544c1a891140034800020051806240103180ea049103092007074080b0b40a0f000b048100340c8014000c08640d6642505200740840032049070380c4031000c4840300c4074628180c00002d45a0180d12000541c0d0241d0600709198400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 486659541 1250 486658291 486658307
    0x11e05031005150306010e010b130e101a070b0f0c12090d0e0d0b070f09080f0c041b090306020912010515090705040815070309061404110a18020a 64
    0x200040894212804001d80400144030503110004007030070f1201000d0301c900f00070800c0c40c101c401c0001000741583c40e02000046c07662000c030600304109070703505012903019894402c541c0281110040e01d05540d050015840b880b80628400c4444080141701c04d100042044042c29071110807900c405415460711100b40d003003030050010307107640c01d100c82c010013944090011360550b00308519612400804652403c1c00a06140810041c02c1143c81310009046a800340aa107240c5010b2450140da042d5070b250807070790401420a0320301c10640c000752840d80d21454103024480c10000d42d0354a02640450741d540241c6020000d02c4000d103503540201e03c001d8690b13103441d0301044640392000207100620b0070442090800303d102d11600c0c0304a00100108070001e100d44140c0e41602c2e0b035a8020540e004800b2155808008014020010162618040300000d806400f4084281441d1800807045003031a1901091102d01c5800150082c004503008100e13075403455081000422245c00c1c0143d8800c80d41070200d54841d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 486660791 1250 486659541 486659549
    0x3090d150e011401050613090e1c021f140402040b01090f060c1209030510090606170102070c06021606051e03090d020c06190318063b06011e 62
    0x520380081d455008106401c220724214510900480300da80764030820806000344d030310b402000c2440764014071401c40075900200d2140726880460352910300003c00b01c00030000d0350b81544c0058002c036101400c401114001d013480c10401200034440d402c3c4840da4149079047c0140b01038800d64132400040ca05134052900000039204030040080b610751aa100905051007040b8202d0755000c0050a0792480e41c4913040b100144c0364804060000880b081c400b0101410841030140c0e41e141c0e443c1d40010381c200b0a0315280091440c40d40001da03c03280641440c0301c60902e03941c8080207540081481540720b50340e48a580f0b00340e8a250a040e49c40d82d80845041e008601c01d000850341d00344000090040c24080002c002ea40041c141d8210350782410040c007485118095440b041108549070150800014044c1e00418294002540380c44e01c0c098403502c441c010750302e0140040196000c642a09601d048002d000a4003111920b00d40c0b010300402d810015540315014480c01c540c1804c50800502050310ba204904010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 486662041 1250 486660791 486660833
    0x130609020406020f07090b0906090c040b0d1e06050916110d021e010b091b070213020a0f0509030303070f140a02033402040b0f04050906010501090e0903090d 69
    0x241d440350390281d03131124004100a803a2041c8000059001514020001a21000382c207404003502c0d40f0043c80840b0348090044142440c06000214402903150081c05414940d44000715103005c00d242d0000c644142620f11f03610041c01c103e0240003e8589100264006022400741d01a605e0251b0701110400f8015018203044c6c021808001c5160f41c0c00241c00511200e030302c8400d0340203807960160600f210989440c058000640e480000c08106405a04014041310740e1800c51800e01941d00013400c44426521071500319a010403005415a44008000490405810817914056003400001d82e40c0c08010111010050184050f05000f1720466652100c070034441d2805859030907525000e510f0f0f8100084403584140c0e9003141a0007514111145006214003d801451264452302032202801d0344868080c0c00007010442c007000b039103851041a02c40d600610240c90954140400184002030700e03031192031003202c0399040c01000c01300841141c0341a201214400b10449152400300c0c4080c440b2010b0303d80c2c03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 486663291 1250 486662041 486662047
    0x3050d270b1006020a060c050c010c171003030203030612010b09070305070807050702060a0806280302120a031209031422050103271e03050c060702031813060902 71
    0x400c055141020094812a030004007a40d45044111106055100c2c801c01a80302d5201c0f02c000c0b42c401e0f400300d40c1d268800d14000c2d103000c0c103041a0500755900c242c941c4000810400c0c1d0040501446003545070800300c80341c442c1c9600c6181d502c00945d43d00010b04054440c40c0d0300700c800403a02400b50710500d103408000c0e00c80b40c42403600440c090024141242c80d01c1c00302e480340e0f0020341803910500803203e016500a1409040c11003480b130840701850300400b00303138002d0b50103520803081c1d480c0800c0c1c41a81c00f1800c0440000142507106101c0c1200d6040300c0c43c0120f5000741e24220011341c00c134041b90452a00c01100080b00c446034242152001805042e507541640002241c7c440004041e5940882d2200001806d01040c0d80760b00440840302039100c2805001c2d80c281000307580d1811149050342e01030044404d101c5035a5020401c028500300707080b045012440000387c82241701014054980c0c8150607001550070301240503488040220300402c0c0c41e2007403510030b074040d100480715400b085c043d04000c81c086403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 486664541 1250 486663291 486663341
    0x114011d180403020c0103060f03061a0306090a110603060d08030c071e052b0f0306031a0103030207090204140105030c0d06060f11070305070902031b0c0c0f041803050d 74
    0x601c41041d40e043c2e00500402c803000c1000e500a0081504440c00c0207a80303d1403c0c43d64940740018034040d86240207501007c80300042a540410080e801515004080c00e0708841600d0a40c0140740369111181c0192010302c1000003540e117000600382060380064903a69240c3d241e620309403441c4038002c0020a003420640c4807170700c4c80350640146004241320b0012103c0701c0d100700070840c11140d03046403540001002c5001181c0c01610032503540780c4010306801e0110b10141c4940d10258103c001394201c0340400000b800400038580d0411400c030050140c900110724140c10140c04078041202c2e8441ca0341403100c0080840d40700100308086441581c0d00304010064107132910700007891408074003007100000700c084030240d02100020603c28101c070703400720040003002c1c5004010301c069000100802183c1406501c604e1711458507200030b0582140b424060442030001c0b004024400d91030368885400346241010302d0115140c90740d0384400240c0c150900c0d40d100c050803e188000341004a56011444c0d00c501070a403 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 486665791 1250 486664541 486664579
    0x140a09020c10091518050a031b020307080a060b0915042c0a15020c1504080906040608100909030509040b15070c140108090601030f02010203040b1b0d0203030114011d 73
    0xc41d045004080030302417008017030b08100c2513280503c40942907804c00113003080043d004040f9094245120040c50141810741d400190030100315074085003194000d40c15410030440203100702c2c140b10908407034440140c10702008080843c0c917406100c1d0f000301d60740d40351242701818207034200d80c2e00081500a070a400071100300322502c3e203640040441c2d0030b40d103a0035144e22440090090780d0700c55204800034104a041c89101414107200030b04113070307a410000c01081781d1548513040100090601c5441d881400e00341036031101410401c03540005c6e2564541407503100001c1e84881214038503441210042807240c0c0c43c0000400f61000c980380401c10810020ba030208200d0b014110000b00e40c04404031a504009000040d00e000d070081b03a620803d90490001800040d001e0003e103181240188100d9040c41d84070240c6580c607a00100001000705d41c03464880154003001c1004c207a00c048540301842c1103514110348120b00000d10f88070b075418006007a0300d40021102c501c10014501da001030a200c56504e11507665 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 486667041 1250 486665791 486665813
    0x4050c040908120108011e0f2c1207080403080a090f0f1a040b030403120b0d0605060907020d02030306100c1e0227060d03020c0a1e140a09020c1009 65
    0x20956244909000140b81c6006104540041051f4600007130608405030184000b081c0340720169028942e02c842c5401501a000c00354501202002c0c41c40028a004890309407038580c0c1c5e82800c01c0c2c041c404028020018110340e094800703c0f0360050740c01e074032070780d4420003030300d03192002d0f084003503003461101d00000d407040e003c0e81c0c01e400c4601c40300c10102d0940031112800c419108030701828a1101040010600181c440e1103802c04100c00c0240014401c031607040000d481d055804d10a4401980b100c051107410700e00301040c0798100120340014003094441c00c401031340700d010061041d481120305810712441d0340c0c0141100341d880b41e4081d80345a035009003042a080b842040500036409016001d510006201001c0f00040f00451480440200c5564001c200700c00e0460700c5d4002c6046020f01042c40f02c883c1c4411030100007409070b1040442215015030b001810050060340241045040ca9000c00c540740c40340c800d5030040c1c400010001d681ca55a030241d99181540484510380300030326101523035080c46844210 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 486668291 1250 486667041 486667057
    0x901021f021306020c031e07030b04110a140d14070e0a14390c030c0a0b060402280c051e070e010302030c010e040e010c0314090a150504050c040908 65
    0x500600c9540320f0604aa8813032003d5030480d01030740700700c0d8007070601e400403d0b0300c0c8400419542100d01041c1c50350b0306d07603d0f00003007514201d9000580c03403102001132820314000000f5203103880f0600c8041c0d5442000401d032112501025204258000c2c200c8484130301444041d0150200020101e22418503000c01d400070200d5172080b001c0034078850013290040ca0015450301074a0100c55040000084c4007200d0381c0880001594141a40d00c10448031440c400b0510140c0302d101b403024044c12201c8a03504002e1690b090060603903216910401240c250880356118405400f00d2400c40c080054400000c155110482300d040075240e482008442103007080c0b00003c0c16910001030313040c0c8007001e954111300d60380c241d02808000c0d07042e00a95291841544103a01d80440d00ea001080456a4008490913a084036200760403800060b4461a00449001303c40301e101d900902800c0040c81001c055450319010f00000ca40c3c4115042d85801c003050601c07004004d8242c400b100144100803400c000e19180c0d8480e400004 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 486669541 1250 486668291 486668317
    0xf0904060b030705190203130603140f01051c170313030e0103091709041407030207060b0607030203031906080607200105091b06040b210a021e0901021f02 68
    0x60100701d46480d80700307680c01865582c442e94180351103034140d2200e012484428038118401402201807050702c40451030700501c0c85413000205134070070700e12441d0100c400401480403405000010000b64480000782d4942e00e100c4107020310032141918003441160304908003000502d0002c01031000c8080d40d41c11248026219448035100c3d140004010741c1603845540d40500700500c1813918031560b50b8003600800e8041c10040000450040c0251448042d403401c0c8c407030741c0c0040c2d4041941c100700a0b8a104038201910100c1d1100c0c02c010199400a643e1b1100410302c190380c580311005540c1d10312642d004200070749008825242540b0301020010100e0601080b0340070098a1040030301c1840c5c0046c400c2c40d014080000141808400d5410607400c00245c04400310303000001000009146d90302140600030040664000342c185003c603440362000c01401600c00e90b401d501c104001511030395074805003a40c0540d05003160f9140ca500d01c005078100f1801e5043c00c41040d280040340e0f0301c188c03019401081c003441504 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 486670791 1250 486669541 486669551
    0x115140102060f090c0d020607060c35010306090c1d040b130c0501141309090203010e1207060f090209090f0f120706271a01050108070509040b01140f0904 68
    0x3200d88040c0c6030261213851a5800070b03c9407070618281450401602030002c0c01440c41c12085582e840200d0b00c49058034000030741c0e0301800d40c00f1803208511121290000040d98030842600d9071607072003500010b01c8000c0c08550b50b01041030401840d413032250002c041d00110b040104011203069081024111001c80300340c400040020409130382c8038880300500d600001e500117064200401035402e0800e900c252400d85a080c840030095160709048000074002d068008280c00c0004e10505081d50100e0890000320b42001150309a180c0806040d1046140c1007500816026264402e130300061084400c00b941080d0601b04100d035803500082c1c1c10001c0013907103003100c2d90b180c601c4520340d4640000d4440082007031810030a04020400316048104040380c101002500e204012560240300290702d40115400c0000d035045148a2402482250040000713081c444294682042c00603c41d200300d1032a54400c03996480208156446035a80100c020006090141d1b00c080007a1100e0b044d41207400503a00c220301301 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 486672041 1250 486670791 486670801
    0x10b150702102d02010b03011805071a0a080402040204171f05190203040c08010603030f120516030207060e100f050c0c03070803040f02030a0606082b05090102011514010206 76
    0xc0c440021101c0780e052491807400f48070085211030b112105481004541d00c0c1c00204245950a200c2c400c50341e2441c0e510541c0814140c504141007414980c8918841c03e1010b44040c1150071840458415401074500300100d036640c0e1002900a005981041000c4251020054003000b40010f61a0b54100080000c1107030105010070340090340c0c2d044811064611070b1250703804141d0016006560010720412040d0640d9850300102d03800c44a19078070990000c3c9020600144c01500a0203220902c440c3c48014041440c0c0521a181c1524004500004050b03001550006200c45075000401c8208010151650030440d000400d009c0d1044c8404241071924103400308d101d000d28101182c0542210b10003550801040343c85400d2903400007007007603904065807040840140e6090080003034a920900000840c503080c828164600134481c01c010068038802c0d94071f00140c0000326480e0004048074a41699520f0403107004074054910410122a0300c0c0d9607504c00b00703103c03200c0c00100c2510304e404e0303089400940d15 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 486673291 1250 486672041 486672047
    0x180b0913060302061e0d1401030b0a0605030d050702060d05070e03070815040b06030709090b041e17031e0a0e300f0705060907080c030f031902010b15070210 69
    0x220b00c0001d610800401500b2200a0340280f0304940140014155040103180001c21043e60f5136100455040d00b0090010b0040201c01480e803a08014034000800400d42000c01003951815070100d07000502502040c0c4808650f220740071500000001c05050200381070800380039281400c00f591261190045440106e103c42c400216081d16032042c24030809903072a5500c41380c8501c840038001c0c50700340c05944004105101c4500039004054414041c0c40c0e60743c13506040c403c0380c0014042011074441241071000001c035554501416003a80e140c20b03d5a81c9481d0580701078410b214103e070300c01c800c0540d2020469000484c1d80680d21000440c0191100c0c50880400c120728103115002c00040e0303400b07207826544040c9241000c0e0412031018806245003240a48840d85000011a0000f40d6036200b843d0500c0702d91020b120b40d1403145015801000c0481c20750901903102d000e0481c8045c15601d203661800909031003500925202440a02005410140251925001d80c8a000142d006100202c000044188 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 486674541 1250 486673291 486673301
    0x30302060a020f0910050903032d1206040507021006120521030705071104141b0f07110a050d0c06020105160e0111010b040203010f0e0a09020102060412180b0913 71
    0x9060910130300c1c280207041000340e00c140800700b8004006041c0201d4080e038508000034058800e540100000c0204219040301010f00d15144c2e414420505002440340030303014252043c1c04c10011103001c1080c1d076418000700d00c0c0080e503184107112a41820340004458008a55600071070b80030781c0035610015030074a6481500c0300c031070090600380c500420024420502c0394025203215841240341c01c0d4002107410000d4142c2d04142c8a0050780c0020704144041444410340042e010401d84030102d00703000516003a842d80c2e015501d405410707801e24441c400b280341e030b0f00b0142c8005000020b105112248a0b801c2900b04400d15004800140d8a0310f004120664401405005646203d03a6100d84020301c400044803400703101110610203640300c9003161070940d40c500145020307004925004448520f00b40040341000000f0b0600a5620b25003600030002d030742c2c00304069070300c43e42004250354040100c000403030307080700d4207507045c1541802c5400229a5201e01c4000301000f880407201d00507120b54a000042c1214 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 486675791 1250 486674541 486674557
    0xc0a17160e0607020d1211060f1503210702030f01023010060c03111e010609060308040e10080a0303062c0103171b01060501140309070621020d06030302060a02 70
    0x1945c903070705042c00141254551402034181e40703012030340038a010300c444d0300d00300b0195242100000c40d0302c02c00c055200800d61802d00904100d0080444079000b0320f5800183c90020b1100079030510005035001591020401041c000308040021561440d0184000103d01c0f4070521449211045080c08040115406540e5000d4107068410300002071900070240e80d4060320003002c805005c4610405007a2a406110340c0e6051100d141c450107600010010076030840304d164201c401d84074681002880410411025501540c07001c80c6140c400345c5460040d01056850356104c0c041900c40c4200107420182e00d0740080c2d080b00c0900c40000c40e0a2680c800031000c040c408001c2401000d1200010070100f1168483c1034542c2c034400d10341030b00d0301280c00742803940c580740c1d02c1c0b00000a0707443e16420042940d1068000d0f040c415006c45060450404500564a4204c80e215150404c0110708007030070140141e90700361241c4541d0300305c119503400080300800c015052610081d0301600910b000507050f0303a418003c0741c40c1c00e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 486677041 1250 486675791 486675799
    0xb0d020307230a0e0a1e0503071a0708090f09010909050106060e0303070213180521041d0405100905010f06050609010e191502070f080111030c0a17160e060702 70
    0x209110400c4613000d540034001580522001800180e04038107501e16840c198800e5034203403200e4246002d1509c1d00446074440341d80e0740d41c0526a5407000b0305a5080c4c0380f4084e84040095560000400000c01410708030070050b60001107400005203860045d480f04042d00e218030300a00c24141e4546041c0d421800321b60480f81c16400c03c005040040c0b0b011440305420011040001070500d6050309007209020445504542550281e4001d90400d990740340000a03002c0c007980010300d0241800070703c120030101c0758400342400c1c4640001c10b040101c00c0c07083d10300566284000304a0503081e401c1890203442503403455510145007075800b1070785041c450221440c241068442d541c2c191070810500407030f01850b1011300c1d200000e08402169040200445240704601e036801800341c1800c1441d8580303031702c84942c450702c5640c0c5003c1140d000c08004900381e99112000c4c00724107498255500068801e4203a540d11503042c04106070030001d000540300040c1d210402d25594851400021005104a0703200f412400b80d40 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 486678291 1250 486677041 486677047
    0x16060f05030109050402040e0601150215040c0b0a0e03010203040f030f1d120a050d170108060f04060b22020d0b060c0a081b0f1c08100603150b0d02030723 68
    0x60f099a60700072513002403025000003400025040042d0600800b0b80011035141d1000c0520b00d401541081800e001d509066009442801c1079582d01d88030070308602c40c0414086c5c0c0030640d48400382c020709941c03043c1c0300080c00a640d285803034034201c1100c0e11b80d41e404401050301c9400c1d4030000b900c81d17490224414140c2418061001600b801c00000000d00e031018020741c450030f564600000e40501c080c00300490951180c0c030905080490300130050301c050304407503101c1d03000b030003001030070940d4001064001c0e811410010b100066040030400e085841c1454000c81c410888800c801c148096008010342c41030008104100c1941500304144c91094001c49400d0360703c0101c4c00c2010698140090460120b0a246480c0c5020074a42c4107081011410307100d0516000324013021000a02d01e584c48074886518601500e5038a416183e10030071a03c20b01410b002c05aa078455000e501d0707040400f00000d0a2031952013600d40b6121641da074040d501c2220103c0c001410b014900d07080540c10040212101d00d074501d0b00f82 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 486679541 1250 486678291 486678299
    0x504030c06020d091e0504020417121602040b0411070c060807020102040f1a0417030d060e0402131d011a0f03030909010e0a090f030e18070207031506030b0916060f050301 75
    0xf4000d400708400905c0c914203070001039a0383c5a100400c02031401c1390300d80190740300c40900681071070303c0b00109801c0007104015480010644202c1040110f0741158002103020105012500400c1000f0f9074000f01d10380041d4a17420322440d000d04a04031031441e56000d03203030340d58620100e0903402244101c02c014a10441d00340300d42ca5038080705110400000c0e4103d800d041c1c0e901038070258050780b071280d092181c00018a00d140469103001d035102034214000f080465042c6940890112003407514851000343d82d4240a10f1022448412508004407100080c4541402c2e18040c3c0701d41142041501c5c480d03400034400030a2800c002c400d40d19000e600070107c2c1d10581c40c122654500f00780051004520300c3d9502c02400001e480f0712900c00c40a4069591a240703a042c500c14001c0b9041180000d20031032400f1010000c400e5400201c3c0d005581e8003801944c41c0c00124525140a05142d8000800c2d1064203030820055260000d42e82d5680030344954000f1027290342e0301090361113030140c0782280000360301080148 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 486680791 1250 486679541 486679559
    0x16090912180501080c131d070f140a11060709080f0d08040b07020a170408010c090b0a0c1403070501200406020309120c040f0519270c0e04030504030c06020d09 70
    0x941c400189007040b031500c411700d0019540f9040c2130700109040c590b0a88070342d0b880c00241d007c2c030390310618030f041c03524140714035900c0036241700b440c050060102400010305100c69480b40d1840c1500409860450782e450511b170320081d0100c400782c040e13240c1c507210f0703400b181441510010f1019005455603c1e2128940c40b07a444184844100420b0b0744254442c5050120006102c100c075819200300340800c19484500703084080f403d4822008e040001c10462080a2080e0748041086800001150800c0b5003008000d103480c65059005103580c0c44140004100d0704103128040d0000d4102d4882c0315a032410349080e5003450340c41405240a8200142d0040c8601e02d01d9091100601c4091102c0b402140c19444d001c400090644e14140a45480c903034542003808466001072009140301c00382c5641c14807911580940808074003186540711001821a50344a02c01d025040304101c006c0c4c43c812425201d58501410301400a0b0301510003121941402079001490b10b20100e04e01507090410780e2043c600170b103446004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 486682041 1250 486680791 486680807
    0x10200c130e12030a0501030c0501020a02011709070b031003020a080610061d060d0c080c04080a0b0403051306020105011d060f0f040e0d181a0706090516090912180501 73
    0x1505661003524192600c581032803003d10f101d0001c8603004030351981103280500c10303540079034001c81c15036001859200050303070040007071210401540300c07a00e55070761020112840c0c03048070f03488507800e25000020303c00b000d03150b69565000d4030b000f5540000080c0d500c4140d20b81e00d51040354020181030034140203000340c0d40f184030828903909420404091421500002030600d44c041d41e002d1641664440f40f4844250300003900c41d5102c0069412036083c9841d24441c180c8405803a103004240c80d60304000101018040c4003500c1e00c0710350f414000c3c940a612070b140640204000c0c041d1100c132000c49000c1e1604251030340ca20358480d0501411440a607455034080c409005a800d111a510649503030515880001c2000303696094a011f90b100445081d20101380e900111050700030501c121100c2c410b2603082c0754420200c540156100c40300007442007d81c100103060500d00c1e2908250218600c43c00100d05a19070016480e03039018039212012102c810200b0344900b40b481c407070301079815124002002698011140 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 486683291 1250 486682041 486682061
    0x703031b0206070b0f07110c030709020c030d0606020601090b04050c091017150a08120f070602090315071101050114010c0602070f08030405160506030606070302010b10200c13 77
    0x1000b410b142c003d130354003402c0c40e108803407021030030f45200c0420003800d03440900b1002e0000d03400d010b400582c0c901c80c0400c1d104c1481d0700402c2d041c00c1e0002014101481e0400880710060b903180000c20002d601c03004029210030302807050480c0c0509122a050213071801e4480c1a014000903044c291502003520248003542d01d0581404040c000403403c50151030007074031038540c482c140c0701000c0b680b403c032081c04120401d2403c2c0c00011080d4040340d1140f1914420104031010b4290041075141c031901a40750000281c811001d03610313014081e058200e80b10001c66400305000c0c29071038403020000701e0005803003422190b003441140c407140111035442c2003550150408a103418001c040240c50a0180e490b0350316082001d0f40120b0300014004100020b0007414800403440d040305203e040800c1e443c150008040303020207810184200c074009190b0341014000d6100403450803004e4550218001120400390070390701c01020404245150400781080d10b5800324200c1400c0c407005007004821240b80d00008010174400007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 486684541 1250 486683291 486683299
    0x1501080c090a08010608010f0e0309010e0a030c090609111e0a0309050109080702210a0b19180606060507081806040e19060e010302010503130611071506080703031b02 73
    0xc4140602e44a80301080082c10301ca0f400403c0b01480d14a0041c211400010743c1b105141c900b81160000140c00300490384030100074a464404402500d000a10405540c0e000504040c10410001813903030b029000907080f00c401d060708208001c41c0120742c8566124030140035644006043d46905c6031401d4402508000105280016200303166030345141c00c550b070010742501c0301480030401400318034012070b034000901d40a000500301d941c01d1465150340c81a044000808280000e0000344010104003241e842807100400306000c9441d05c0c0c03860030702c2044007203803d540e1181000300101c0c1c500d00520896010a030320121443c580b0b250003c0d0140150350b0441082c4c2e01c036204000025500c44020111801461003010000d42c03c2c4650348003100311405070b481803200e1480d0400410150780c014013a240d00031000026404900e0305032070b00900508106031b04141e800c5000c20301c17105100303003503c1019a0040008042040e00c1e104e1909942d5a8070f240f0004000581640c4508000703402c02425150040c4050 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 486685791 1250 486684541 486684547
    0x509030d0c0e0f1c0f030201020909071e020318041d06040b011806050f06070201020f070602030a020f0c030d0f02010209100c020405102126040f0e1501080c 69
    0x312000196a0601c00399000504030000d810307000e2800e040364421441c000c1302d03694060840000c078480341500600001c0d1410003845c0781041494000e4044500d41d02009142e107003113280880020b0805950900401442c0c010032600c5a10f86000204640640c0e103441c1103000c3c245001420400500a0580c490701c070040300c1100340d1144c1008200341c500841c42a030010a1642c10311803001c040303d80c0051103903842c2d820050100010b441d04d81010465500030f031100c69a8070150b00040c0e15050410980203080d00c40c241c800035102d533001c0050000d840c615800c1c0c90403844107507040359503003e81840307982d0315402c000100c130740310b034050720701050b42000c1d0340009818020000d0024948140c1a041070000c190071004120441c9454031540344c0c054a6200804800350812085460a4900349004a03007007440c2e460b40703414040c0710180f0251b0302c80d000e2104a40040c0d0b400d01d002c0c4c40d070070600c503480003101e00035001308810401e02c68242c03013803044c042844480b800e080011201d04030080d1212065a10070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 486687041 1250 486685791 486685807
    0x3050919020d060e0309090a02040e060f1f02010e0d020a0203190f051506040608061308090a03050f0d1b05030f0a0306051309030801050d02130506030304150305040b070e0d0303050903 81
    0x303005002401244c50061500c41c002d4100b8440e000e80c008101c1c0314928030400052002c0705155079807070b4002006480f0f04451022400226180440d031a400888215501103040c5800c1e038150400044409004107036503c940314000d06913a40c02448000035070603005020142c0401d0317200d5009001d203d019004070951011551205030409035035000d034503104400b060810045040600400d0014004200107020502d454a041030006514603802070402d1400a9420a640d03a140c110030042d54000081e500c2000e020308140790303103440e0a01d0030800f0619240074032240300140c2d800700e414560441d000d14600302c1844006000c80e8405560740040c0b56035601c001c5080d480b01e01030540007542c40da030001108070040c18023900840050340b00c180b048034486c0c40040140c13186500c0f50921184610085801d4448900207419405103801a842c80701e1410b48000c08554142c21642c080e50080000d4100d48d15a45c10444031106520011600500740b804140c0000c3e00ca82d01066202c41e1880030f80b070400d804 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 486688291 1250 486687041 486687053
    0x2101051914190b06040305210c151815191112090a0b0403080703060b0a020a03030209060708070c030b0a0b011b0f02060406110705091006080a1e0f0c03050919020d 72
    0x115810664840d0b0001c41c0c07141104004003081780230342e03902400180c148a0650201680e801484e134062030f40200c4600070910144211048002c16050981900c1d020503984500e491402411104072800c44c01000900a03442494490340760451550910986007003032880440c0495070025046200b0342c854008050045600681c41714002d520075503030f4620a003420f01d0001c06490b510340291114180c02c0054030002500020f07601d141d01c1e41400c0258907440c0503000242a03004020000d040c1c648009180d030200035610f81d0301c4c03013a648515104442c035240c0e224000211601da018607404181b15280002c0402511400f00600c41d20882050340c10400982c00304040e50400d9021201042001051300e0000d00f0503c41c020181134150f500c3c9025140484803003421080c00c0c0300e4241805024800328107011090380201e4503040c0003145424044649054080c0148a0718040c002c0140c90200c28185852003800342d01e01903035460006041d0203010310040305000c20740c40307812680030741d1311152640040c003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 486689541 1250 486688291 486688297
    0xb070807050705010923060f18030c030a0e1e03060408160c06080a1409061f09090309050a0504051005060c0c0409050102120708040c142101051914190b06 68
    0xb100d9a09078000c8000044014071814600383d000c6c4054200c0c0c810858010342801070158011001c94511400c105c1b480302650451061016a6039140800141c000304250440c00381090300c40b040d13070aa840310342c0204054150580b0841c489030305800000108000c11003403800350102001d0b40a2b00741c3c02003810f5444a50b42d03000d90307200102017900c1c0780c100200410300d441101840610220b003010245031510126032510001400c400815601130f01c0c8103121641c00c410f003006807600074000c11500c0c069082c090066041482514840c00c039040d004912418907018050250140f00e60100a00e414201044559042442c64051500c1101c41510745c640d202d00030403210394012000103030303101c07000c01c003a0a001c20010842c1c414045500244000103c03018106c0003102c8500441a00c101a280b00140c841100c1234000303c643c0080188a001010040d84090301a05900c0101070b450700c0b0001940040c0c814000400d8500c40800d800149941cac00c0c84000200109a400002050202d4400040f19a0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 486690647 1106 486689541 486689543
    0xd0f1802030304031b0e010b031f121211070b071101140a03020307030902121c09050d08070c030c030c030308060d2f040e01020a09120b0708070507050109 68
    0x2d01440b2451000c0d044038450100303156590369440c0c100d40c000341e2b954104201c0c03c243e9024040500e48a090440d0b181d002e000071104185c9c0c550f65030140513040c4a4040c00b00800c00c102101030b043c040c00d00644640350551b6124000f600b0b2940070303280b0200d1243d06114540d000450b1015502041d80c441618901d0b003d03a40e0703500e18004038050601035100039082071403c0c041401c00e9401284000702040b83e042200000400014102c54100c1503120b002c0d0440311004124020800f818001c10010780584442c0c4202c640d40d50720ac1852001725070041d10900c420310024010550f000790400d0f00100100d40068000360303680c88152603d81403071811004054010f00b01102200c03413040b80e0654150041081111032030700d000b1103008c5d5001400c1c1200103000c0c0c24000c2826065100c08000250308075803080c13410f5171000e10039100e00e240a04240148101800440c000840034003528041c0c07 = true := by decide +kernel

theorem cover : BRFrame.Cov 486510791 486690647 := by
  have h0 := BRFrame.cov_init 486510791
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486510791 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 486510791 ≤ n) (h2 : n < 486690647) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
