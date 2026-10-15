-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4573
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:03:21.58689+00:00
-- url     : https://prove2.me/submissions/ab852c3f-14c4-4d50-947c-71c5545459ef

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 822302158 ≤ n < 822482014 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 822303408 1250 822302158 822302179
    0x180b0301021b0105011e0b0a0302070302150f09010c0e1e030309060724060b07020f01030b150a0818070e040309030f0b04060c020f030316050d0204031119080a02 71
    0x15a000e4055808407002040306002070003a40304064040c0400703209407030000400c40c2d00090944040b45d81d06059451454070b052030321440007402c41c0207520000c0243c0031801030501592a0360102c43d01c060003041401101078907403c0007540d49003126031031040382c42880b200840030b40b0152502d03a00f0107011516000340d50101440c42c008a411403050b11901c0b94007601c0003030880108003c1c2c1040380100040c803003034000300c0344100e0300f440c0844102c0d004070300200d28140541c01c014503043d80008907149040c50080ba03500703491004104080600780014920200200e83d905035a61710150b01c2d5440400c4108000c0b0a4141900007500c0c1c001c2c5000320701c5055a4000050141405015944025540080c40c01034414190510040204064404403011802c2c203040d00c940910010320641900c0c071140156145444400040c3e21241480504109010050101510440940c1b02a00046000d02c2e00207070010903003c20003911030304580b0380b20148001f0410900501000040440a003075040c0c5212101 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 822304658 1250 822303408 822303431
    0x1020f0d0801120204090507060f021509030414030c0d0809040c0c0c1203110d260f010918060f020c0705011b032d0c060c0c110d1e03111618 62
    0x5005140706c05059413044183c0016480d511041d20382c5010850740c01e45611074070b405007440500c06c3c1500d50441a5001380300a211201c0100d0851101c55401021560074a1903440490010100d42c0d90681d2614004542c48a00b07040500681c8072680c2e0390b01e8241c0c00b09080d40c4d0b404c030340e001841c00b80000c0000c501110808050251880305017458091f03048070f2840243c4100108103002014400c552600c14502d02d800007848042414020f40240388040d90baa801e02e9021801401c0e08200d60041d16882181c10300800c80364801d50007082d0f1020001359441e0740c541a101d1600c01a584698104052030359207a100885020540c0701583d1f141c6440080347e209800d00d56848050014080c1004071810b00c0d040759103070803800a0411a10803d400c3c841840481d0f0281c4503200f1400f0040c00d02c141380380000400c0d10349802c544000500c102c03000310490203110742455401600b0081100032402a082207040300c0000c000301d98030107614100f4041110700f01401d40d030700c14031504981460345840daa1107050 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 822305908 1250 822304658 822304661
    0x7021f020313030b06011d060a12060506070c210305181f080702060f010b040504090228063009020f0306070e040506040b0901060f090815010501020f0d0801120204 72
    0x800410a801803100b0070f44a00300991100400e46400303000c41e0441c0302d600c07543c0e103400c20245240c4400400c128140b481890050ba06480e00c1c0e040e0b0807145039950408196996001c002c0d080050048190f00c000600b881401c10706040340c0740e0501c5103490f032300a100000a038420120b914210200382500c20510350b110200311100d042d101002c540001c2500c003004242d60141e0518480d400d564200c0c0e180d03895400d501042500d007030196070785018080200f0311103810f19400c08080148040c0040e10b005034401080d90410050101d401d40805000ca001c0040c65840f81540b070b1341c258142a44010324442d205002010250000701001e0240c0b902c2c403081c10740d9210305c401000c26101805030b17002480c222900401004c07003007800c2481145070002240c8203041601c108006120050000e103616400c00005490b090080000c00041041c0c6060100742c801040c0b0084107480c101c200d490075107504000c0060f04100d001d0039541035036441b000a4441d10b81d131003000103045134058100c00c010f072080e0b400847c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 822307158 1250 822305908 822305917
    0x3062909012a3f050c0f030403050109021008060f0d2603060411031026030c030a0f0302030609240607110f0d0309091802191a07021f0203 61
    0x584042c04401902031200035800a0a1416400300c084089071064032048405886505030581142c00714510301e1010f030060b00142202c8040004882621840440c40781c6103501681040303c20ba51542c071440218180020b618001003c0c1d8180901c051800802050904180f24451807090149000b4a0144800f0348140041000340300003075100305d48070a150999903401038584078000ca02c1c01c0468040e402e00c000a03a4003401c044403c6035085440e0100341030000000f5100342e0b6450480c186165a500030400003444280d80440c003031516054140c6000d031500a140ca61802418010420030009603079074690168803400b45a80380c0496562201c50022207064040034030381104c0c00080302000d020320002203030144941100c03030340c0005501205202d1143d81c081001404120108002c1c020b80000390803006c103904d0302c1d105a2104607030907000070ba003684080d42e801404044400042c4025003540b45030b00b489002e41c46a0503e4401d080d40428070f8074000c505241c0c982d40710f9030101c44400c0c0c424412034 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 822308408 1250 822307158 822307217
    0x7030c030e0312060f0418080c011806090c0608130204051906262a060706020409050f0a060b09010e0616080c0d03061203080601110d0306290901 64
    0x201d488900303440c6080503000d02504d44911807407184000d02801c3c0b601d800751100c00300714403007000b9003840340c1d80d1500066001b00c415040300d5503d40da9102240c030540d800c01082c8074001c402c0440e0f40b001e142801c03800c01219400c54010011080c0030800c1104803071414110700c1d9810798002a19988100c0550f91b0490813404100503d4200000054950301c03113003415601802348200b45420306030500446585805041d0b004450701100c031041c00d294048944003451a10010705a645055a580d4400c0102d901c143c10024100b903035041401040954480219480308151004008190804419011601400301c82c6410000b5501100799140c84001c10787e40010320312003c4052034070152030110501c1e082405041d80c14802c145001e100c8520074003e00c000c86d402401c880b850001c0c41d4808031803100c0d0051240d81804a000248a0040030401c0820b4600320b00791760015026082c8210440c100320800401d01900f50981900f600d00398144046a01c01002400c0030140001084245000e207004140762 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 822309658 1250 822308408 822308413
    0x11e1b09030f21090302130c080c0f040317040e16021c0e0409060902012c1203132601020304082d07030807121a04021b0a051606020706050307030c030e 67
    0x200f50302d01c2c0c0111040c0207880c400c4a07204401e030f41e024180001c0701c0d20004940e0004000d40040f48400368600300030441c070380c10fa007080ca10709516515518000601b006403049800c00024003081001440f00030300c0c4d00f20000011401c014468041c0003503951050b503200c5017469880c41070010310140507594428450901500078000d064207801c10038001c03e40c14600340d0100b41c00d91141e80c50f01a90b080c0c03c845110307590100c48020f1741c0d000b05002c282084a881c0c8440d034801008042d407040b4000308460010880c400c858280c0c2c1403000c1c441103a5960b01c56016081e40c1c018400d21000a102c0d009031403040f40800c04403030490580659500b180c03184010442040600064054245640020414031501250311155480c4050002c003404580c0c00c2c140c00000403044401000040c9019002000060600c1400d6100e000c00004440d0900c50340704011951540300510150501c1c029418600050501c0d00103861100d1510101401d14800280300008055651101084040c041c0e4802d40090031100d04 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 822310908 1250 822309658 822309713
    0x160c080901091a0a02010b061c0f06120c081209090a0b011808070e060d03021504020a0b0a020106090b010503100b0a050d1113080d0c0320011e1b09030f 67
    0xd90000f0780d118400388401542000401c2c5902d0400b039040f6418001e0456071590030392991141800180040400040c42c99111600003540d611024813503192540226000131840c0d10b07000c1c5061400c07a51071000e0303009003000d0041400e6560342ca1002984240d50090204d003072408480100c40031a480a44548260180d400c08a04501c002038050151030300400032050315201c01d41045560311107810020300580c4002440d407411410034070070030b80042c40500141156900d8660b00c8600b600241074250040c0e540b00300c2004038080c140602140d01401b801c00c9803440c00d100b4001070210825000f00745041900042c2008590f10840c00c5442c0e400d8441d03000c00a4104880442040c1c0e40300124407201076440c0750010820b90004a12a18100c07180e80781c0f6180032840d940d040d03941c8204083c0d142c91000d0001d0b44144201c40c28041e03c48000804001701010b8180060b00c801120b07512100035450744810450008801d03089a4464142d079000b500c1c1c2c1c111100245844611880360b45031140300d2015400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 822312158 1250 822310908 822310949
    0xe2b020913140313030602090d150b010912050309060307020a0b040c05030609010e190302011107060603200a05061b0708060601140f070206090a091e05160c08090109 73
    0xc0200380c1d4548125102a4200341c0107001550f03d014030410905642a00d000420001c0c2581c0c0c0180000e6102078809052048a07440ba12071812000345860012522400c2d500210b60f800311070040a08007401825900328880c4d00d4807a56401904540c60040310001b012504203802001414a0160310022640303c620709860140320a9886208180c003911071038000ca060150103000d090500031949004005481c09003d44107120710300e104043d0300359540c0e8101d2012030000f10f8000c0109502a0300003013141ca14600d00300000f85176002c001856989020380e1058075603949280d03a41110000c41d41d02c0d454003a00ea84a18400c2000500c010445c03084100c0043c010382c01150952280009883c0e401d170702c06a440c0038101511820100861011003003181100501d0b1032000741148800140151440a44440d4181d04481d04000b00800c020b59124511504007a039000d0f060303020f2401c440c1e031441c0a0807100701a2a821441200500d01c0b103001c00c111595034071a035a0f0000404020f405080c0c03604500 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 822313408 1250 822312158 822312181
    0x1d030d240e0709030b1f0e070e10090b0301080303160f230c0d0e030c03030a1e050c07120c05010e0303030a09080c0709021801080f0711010f020f0a030b010e2b0209 72
    0x750b506030102180c10100150164626030f030b45100307a400d61100c01403060680100420303030a00ad01c2641c1400b55501e00803e0044070840a1740c040c1040303100440c3d4030f040c0a40619040044c030000d02c001c1000c2c0058084001c0c0e03014840b841010040d0414452030458410030a9040c02620764800d218815826a081c019074043c030085107001d0107409a5013502e144c20300345512441012004004100307020441c15900e2000550355072120700d2171038100e00f08401e02503030909108070381e8405184884c81048050501244c20304000c010070007403d00284041030503000c00d807640802080c1460507542c681021061180d941c0442e804c180b6010203840d00962100284802500004000c1c032540904040762117240d4010302c2203500031a14004018542e6980b040d0407204010940c54910848d501c0b41030f50480c43c00240050141ca00742d030040c0c0e039210102034100604840d07054014504200d01d88000c01c500d40c50322540074400d2050301c0040020b51340d03080a079a04101e881c02d0300139003140000c0100420f102c080b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 822314658 1250 822313408 822313441
    0xa080309060a080a18260408070611030c190b0c070b0a050901060b04180f06081e0319081603062607030b130b0c0901050306010c061d030d240e0709030b 67
    0x110454000306ea00401001c8145000e207015034141a0302444090021500581103040c03001d080c07004030781c9060400620541080c18070306100854041c204006004c000317040c010981d201005080c201d06001d11925202d500040150000044554880101e00140d80a4015034042c4c808210861b54444e51804501500485985c102c0c03909858126425010f14040c060041141c814800610641d00c5070041c0b0200e07005165050380441c8402c020b002d14000c3d007050142110011610b40c000b4618041c6c00e0300e40c84080d0040d20608040c90110240010b881001c11018141d0105103a1010800b050758081d00e0b107820b0b904080e110007d40344c00c201d14080b280004550241c400d000c094007644410a0004460203565607003408509d0500c00558654462514100d400d0300904e400708404040203055429000c6c40b90040b0041e4100240030b0750840c2060142c4240196a0f0002034000a20280b000d02ca00c41c180c01481c3e2466140e1011a040b140b01d04d4010000d15002400c11240b81403034480b4500c02c035074 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 822315908 1250 822314658 822314693
    0x9080901030e2409010c110a060203100e010906090509030c0604080a090e150a0605030411040b1c14010c09060504050d032007060306050f0916120e0109020a080309060a080a18 77
    0xd100361b0b5201c4900c40c0c80340c40341040829008150010117980c4001c06908001c2c80001740305426880003d0080110240500030720303601100007001c60804010303c0581d08024030f40081940104040c880e40704000460603401500940b0281e1110785051049a0001d06a8032908090203c2c00a100000c0d4280b2460340c204041110b000410315a03500e4165954082103801811000030b610007c1302da400c2030b40025010350801058111210340c0c2c1c682422060001d404156861100100c840c551f03000c09219025000c1c05506011051503d030400003051031190b4001d03280118113004c070500405005044080040d60010f459800d00303105161400d59a1040b0f114160000f401c1c628006118241001050034903c0c02611a904650742c8047d6902040c508403481010410501a441000c3c00c0c907215640d01e0450103c00801d0b4001180100b01d40500103402403070081d0410401d000c45a980c100c21100503900c80c0c1841a01175484c1c201c840700030001580440940c0841000349402c010301c00711030b50710481 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 822317158 1250 822315908 822315911
    0x31204090b130e031801030f0c030504020112270212120304051c08070c0c0b04120209010504060621090206030a0c030c02070302061c0207020a090606110109080901030e240901 77
    0x145920040040d00c01942c1c120443d03800c1002003d8803e02c07415600c40c0c5406040c14003103841c02030616030b001224000f007400000a56a08207010441da40035140301140d0304420000d0001c1c120420407030034042d01c20708203844824080bd40c1c260031515840c071455040d0b180395094882c4415044000c4580c2d6004a804641c103000f01800c0d01602c4c2001c2c4413503030258400d41c1e07800a15075104041998003907041030003900c50243c034801c001104a1580014000307094983d4140c14022400d205003c13590006800c140d128074200b10051000c591b100201e004900d401507062100302d1400c04800d4014000d84038080d4000d00004200451118244c2025032000990b0390200700c4015056000c07a103440306400000d501407410400b511900400d9031814075614002d8000524018056001504200359548069038442d1170340010854039401290b8101d0084602e0001d0000c5002561140007607c41c000000e4107141d6186003524281e482001581c50745255040c40110440000b0800818003004803108149903 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 822318408 1250 822317158 822317179
    0x180213021614150f0f1602010932011407030b060705010515121c030e030f13050109080a0b0402150d02030a14011203080c03280b040507030605030a03030506031204090b 74
    0x4102201c0704910800b00803030030342e05c5921406221010010f1041c0854215901c40b00c241d008110b0010381c2c00114564a00300d1b804c400c00c190188502a40d00340b0058070b05914250010a0113041c06c41041d038000f0140c580041d00540796000a6418000c082001c2c01a6207488104804d800000c107809140d5041103951102e4203a0128035207540341c01e040e17040c920034001d07c040030000d1402a008411048411700c296410070344282814540c640045d2001600c21020305010032855030003040340b8010700b4156002e070040542039150442010005030000f402840320302c4c80100b40b451100241c0344440e545400035552030914000700400b4121180d10385480c101c188000041400000d58030300d600311380c10740b1450340c50f54516040031480d401c01130030301d51424642c001c0190516203000800280441e40d69002a188580400303010454400030100c0b0b06051030800107005581d400982000303003030360500d000305043c0d43c1c60300800c2c280200403140c0c8031101320101e0081030301a001e405c8914804420b5031045600e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 822319658 1250 822318408 822318421
    0x702010c18120b0402040e120d05010603060b0a050c1504030c02130e190c030b04050d031107031706040603060203010f050f030303151002070503031305030118021302161415 76
    0x40307803010b109030008100c01c1d010803000101542d442950260000b07000180c40d005d4090564103041001c0794442849900080d442e8412040b441142d01425103460304116607420840c0003502d905c207107010801400070100d1510000d000412070202950319049202d51581000e28018050100984080744641185800c0c000d190184d4441c5c0844140524000c1032000043c1111052a441d0390006440f4a4007081740400499140e0070020700662207800282210060311100400b22480c0111050742244200501e902080e40f140300d405882a8426040c0c2458071490005802000d00c0c2d4001442a0300220000030020361243d291021900700b82d80000b90302496008140d12488211042442030f503101d4a400e4030360410801501031004240101c800381c94440001a140d500150174959202910003c14861401c0c01c2c0509105c01c80354101142c9640c0256000038003060283d107841070026400700741030780f144404104a45440f6040214602081d4500c68516141e450083c0d00200174107011f004200c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 822320908 1250 822319658 822319697
    0x30506040f1406060c01020d140f0901060b09280603020d0f060509011208070803040b01050109050102030903060106110a170a0206010e040b160507081602011e02030d020901050f030702010c 83
    0x45165a0b49640710305035582030401805810070b12990440350345c02c0c0007215100c1d503c0d118641401800c1c03400c9981e54540210b660703120401c01442e07015141d040103001c00c44141d00000b528004031003180d0070840280001d8190110480001e10f9040a2031203000004030aa0140d0041201262041c01484981c80412001c01078644a124003070304042c081c001040300342401101075910a20400e1241d1038041540c46900c5190410741c1c00350381034404c202c0100400e60f0461070b0000207040a0025504215603140001c0e12040148a034205105031880020f104102c01d1121200d00c5502000c01829011520521107040d00310004403005845040008142100c803150303818810366100b451045e0740d5840c4454100c603109031403e072405000e401d1041c000000c0407040a40548100d075014007103030a20a0000501e60134084e0001480513051030003a2081036404011101203041c41000582c0e44e008210041f61984101441205050030220501c040c00c0e6040d04a66403641e0b0640e104003100010411060 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 822322158 1250 822320908 822320921
    0x507020309010c060f15030309140f0d0f0215040e09120301030510020708130902030610050c03040e04080403080c0706030e0c09060103050a0905060117060a0902030c06030c19030506040f 82
    0x2400b1511216500f000a00b00d0303005488220f0084001203803030301170811803a421818a41045000c58001c00050100000c888a105511142204c040c1a801a43d070b01145940c4220350001e811020404544015500d405540a521144240c44107684596608408198500940e00c5a40501030248482001d24400080d681600d0f0824043e081d8506030b017144c030000754040d80e005c944005003407108188000d607840500d0020300358000056940e103090400c0261000880d105802445010f00011030350b42d00008c16101590548529a20580c4072400c04031550302075a070008004e0000010005e86402e03021035042e0032600691420300c0184580402151a41240441560000b507000b0000306158030075004140c020801560000340140c0c01d1311076a003020000d8002090f0b030301143e02020010041003245641c446000603040145280590020703495001300000d0300c2c810b130800320201e2a64030b0304604890710740081910011114000c1e039030180140c00229001480b4a1401600d031079103404a00410 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 822323408 1250 822322158 822322177
    0x10060e0606091908030d090b060a0f120305040504110403050f070305030a0318050d090501020c060f0f070201110303070305010f0b030702060a023004140d0c060902010324060305070203 81
    0x60303040407034034018020f2070864464103440c5160203600000704020248002e00c5444120707200480c1e601070a0a01d44500710014145500030910204108001400c800b6864190b80300c85450304481111030030201c9041c0a00e8101c80d50041c41c2c0800081041070030001002124420800e44002802e01c5030f686032548903501c00940f80c1e8104001034500d151003a842542052818180103041340300c40d0b2a200c4c500a0070040c0000809d600900603c025030b0100102803003150121032103031a107a0742104a20b0940142d4414081c42e040115411046a002d1006d0300c0c400130400080320744030f191200c00180600020b200e1030000321010f2a001c00c107a0b500200b100d02c5610150000c201c40d460300a2120002c1d80010074090102400c441084484200003450302c0c504a0040040314641c102070500404100f0031092221041d840300d01204038082d000b10000140c3c81d085200041c401d18140016005080d081c400c000200c0c0b0300b64209240d65001011044c1641c282d507504009540c0c0715203059903244580e0680 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 822324658 1250 822323408 822323419
    0x4030210090c120c08060a0e0c1201241d072705151201290906040b0c1b0907020c0909011b0507351608040810060e06 52
    0x140c12401059420900c86a440750525060305681c1c0c446030906255600e004035199407412908201003201000760f90381001201004001c0d200688014942e100720817501d06000d08000116140c45840a501c113a40c0700d100e1591000000d0b01c0211a507a08e0410f07030142071007085d2008088440309060ba202144a9030b13071a110fa254146951070040c010321040c1d4203242055039016004692501c0d048595841481e116040030346400030901c031030511840503000a4240c181d04100c400784004004041c445d01c0d01c00c0c00f0025542d01601001c1000d521854106609034000042e98401034a0009242100c000c070707289030ac9006025820400041003815180701c00180d10a0f80c0298951504200d001c1d080114800000390103000440100c0082400301d820f000400c9000c40e1140c14000700004c0c518082caa00d6036184d08603074a08254901c4031062500c4040f10000100d40050101c413085011000d240e044040c6a45940c1c0d240b0310a9610940001d814010300d081900c00125030040003800340c080c0900409 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 822325908 1250 822324658 822324673
    0x50403030306091116050c0301020a02070801140402030d11010e0109080408102912070305010c09090606050301060305040f020d050618070503100e03070606060c030f02150a0b0a08060a020301030b010e040302 91
    0x8008444170020b10709072894011841d00600360341d024401090040115000341035854a440842c50031a0700154001c05141003104c00c00005a4021036102c0280700c65081401c0b55481c8002d03814010210246022029840c01c1e50540a000015002d8001ca506480440b516481c600c043d001c26030780000840941ca4042c0b903a684003091103003810fa041c1c180c003d041090080c0907010840e107400c0c840d9006030f0340c0741d5440d55035006580e8043c9100001e480b0202c01486001e1621800400d203110500c614810135035a540414201700390f5a141d80d5041c0d800070400d04e170b014081e092841d110703202903581c0c00c08003070101250b028400010076040101ca00090280c020110748122103c0641074040c0d03101501d020410419002038158418940640754560703d40e6148d64aa140240c80303201c0301c0d000d001c10f41d4498031404c050812040c10050740000c1100e0049144035102010500d00034540c0c00c0743c80d860146c44208030800c0010b50196040740c0c0242c62420040e41c1c0c030010048101015030f00600143c00a00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 822327158 1250 822325908 822325927
    0x7140a080a1a150306040f09120f0813030f0507060f0e0c010f0801030f030e0306040f0b060604210204061a0702030c0105090109030b040503192c0d171303030504030303060911 77
    0x40184d40d1028000e4408100303124011041802c03100140c20407503100740b1004980d0042580160f1101030304156007819042e03070400f80c5441d44503000e0240002e080114a4110490181c4550b0a544010750f02500c24000c0013030b0526544003a004140300c101080c4104a2261202d611803200c02070720181d50b440b030004990035030710b60181c0d10410380c20a409102e641d00400050391410800244502e0081c105503086d0125031400d107050010251410344180780030710061290f00ca01c104c41601d00c4400101e440c900b580316102180140815607c03d0882d40e07064034000320400c1304840103010040c800c409803000140350300c00545482c02065400d500060003843c1c203100003001200000d40240c000c504890410342c202032038514419080840301c0000f00701c00c1e0000e0201481c2500301001210000412400c1c000d050041040b0ba010410060100325000e050015a104904101c503034001641e220340c13012580303030308014000740c2c030500c800c4000a242c500e0005104210303105490a0740041801c2601e00b20440 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 822328408 1250 822327158 822327199
    0x12180905180316110916030509010b0901080f06180c13060e010b2a0303070c0201030605090c090108010e07081504020c012c0106051807140a080a1a 65
    0x385105410520030400c1048a4001c0018141102400303c0e00c200c0e4440300e1400c0c03949400c07210901070048080f4420300c504401d49030b52810f0a00c42c81e1800040540d00c04403114050206c5400440e080440c07035002103415100803481d403c507450310000b1580c46071100c5008a0b2120140e03440030120390001001d0744400d28090904003100790300003070041900c90301d805103c00c48520030790051403c07140c00224050b0107070203070052000c130203098800040340c2075201d0748094991100401200c100310414400c8421680070342e00880160402400100141c0781183c2c075180268030a0300c0440c04110300030000200f4481941d1080d01c40c0b40310f5590160381c2c3e01d0711600580f00080021225500c40e4081c0111007010809100e903a1941452006105000c01c00d04116025400030048003010359044c0302d000c4c0515110740c0821364111051030080b509a65848008a4100c034000e000e1404040000881c17030710140e4004001c50040c0c855005c1000781141a400042c140ea8088032126000b000c81440924401c440303 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 822329658 1250 822328408 822328411
    0x6151509010c03230a0f020a03090302100306080a0c0e09030304050c01350703060f05060306090a0608070b030a0c1b0b091c0203071a0f010b09060d0e0a12180905 71
    0x6400c0040340c81945446000344203001555000400c100415044030307055010050440c1056079002405498500351000ac00c1500c1a0201a0285520106c4026401e10a5000c40b0040c0041407d5410341403003480c140fa0b0025203031241c09013010040b80440c400c0a00402228003903588038000f44640301c881c00055404450f44540701c5100b4014100481e4180408104c81d0002d2030400c00c803400e5031401c401d01808441254000234107006111900b44603a4072000204c0390814400c0f50070340d00c03960742c003e0501d010381030503040503100c3d000311140080c1b40d003040005107000d024980d0060012107403000c0111030f0b24105e00c030300e10340c40342d01e41c82c403100031038a05055248c01002e0b10041d240d03a44000100ca07001c240c4030600490059100080c4101032203040001c40d0300148c26000c0d0343e6844e080c04081800304881c18001c20b160010000344249140d6039200c101d80d401d8118500902442419801040d190030640300d0a84032003c6507641880c02d2441003150308041400e51600c0e03800c01c2d05004111008000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 822330908 1250 822329658 822329663
    0x3110d18060c030e0d03200607020d080402030f1212060f010e0607031e090305060108010b032104090c030605040b030114070e010207050a0906032607030c051e06151509010c 76
    0xc4d6909042d513203440710480411514029120744d10011104404106915181c1c2d501e5403c0740c01080500c44001d03801302d00e0041e40041d41c54010015100c50001908110300c88140d10058490103203aa001c07140303d40060b1000042c402c1c41c00113580e45500030b0141c240042c500260004211140320851441d010014280c01e5020b40ba00d00e00c0c40f40c110003070448140220100602164240004108100c81003009501400341c0f0360003401100e03a403002280c0e130342000340c4441100305400c0344d2a50803c4070f03e50540b00144009070090180c400c605002074001c29441c09640d0140d0309089030708000d800e050240d10141c03140160fa0700035940c0ca00b001108d1020385269901e04601550000082507500d8500480183c850b00d54001501d516520340f451320107100c099890a40c4400b901c02420004001d01a10300e81ca4240c2040fa130340e640249001ca050503a000c404c01c2d0381d44403008010081c0000090640e1041d000d4803071944402080004000030410f014445144d010380070804003040394843d20b000c0d22001d2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 822332158 1250 822330908 822330917
    0x403080304061e05062b080901230403030f0e0121091a0901050609100515040e101802090a171c0305060301050708072c060703110d18060c03 62
    0x10003100c07103c03288401541c4500c105444e94140126880c01003030034222004045a40301c00b01001c00030001c004020080040c0501002103032406099001d0b80c070840221480c0c00054151004005034125150045d0000381c00240c0c0b517010801680e801580755188845050b116542c07131002c040c800c007a200341b0f1070840c0c54050b43c48440c08400101d403400210300a403001c11248421b480d20080b41c2e401c55030010820f03032049108109000100d0704080b40f1a082d41d4007aa90001000c00380d4480105601c1144d125604800c60f640403ca015511006000c040d5161041021f010b0001400c00005030700034071001c5070344074103420f008004083c1c0e0a00302401401d4a032040d200b640c0701070780000020101c10a0340c00c005c20b8840c020014186000e100e4650701c0310141c1405181800c0c40070f80101a41c031a03084640c3c0003107610030506507a02070a002c20710802e00041100b5580d561515008101003a0032928400354403034110f5074805ca0340111065100d9132514041d0401c003520b81030086403400c015602c1074003440b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 822333408 1250 822332158 822332171
    0x1e0914030a030501031a0708070c02030114010b0903061b040b0c3a020d1b05010902120a05060604110f070602071b0312080f01050f270f100b040308030406 68
    0x52400c0c0050120a0120380b0000390310b6146081519404c11072070380c1502a50301d81010445560341001e68150080790a02c0c16607101d01151010078010804100c442803c460f94800025101c69100c00401070070109900351800c0340c440d4044a0440c80f0003a44400941a00380400d110803010301e00508080108401220803174409420403500410640484172890b10b0f646040700c000719100c694100d2242054801006000400305004040841940306190554064001d88041c0039094024591594004104400c9003140100050751001c1d40346040b40c19024100004486207450300c01d00f8a01c0000c00082403500901c400302403480d03481108102e41705682441a00c020484038040102d240121250a0300d6090544c05d016070101e07000d025100c1005200070801601c070905c00c0086046450a0354894040c8000c0400951803000e400003008546070680c1088401c400c1d080c1ca41c900030300e0256910000740e100c046488110204c203000348032000104000400015a0000c01580d1160191100081d003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 822334658 1250 822333408 822333443
    0xf07050f22061e08060105090a0e0715020d110a080a1116050f1c12050d110d0e12031f03020607050115090209031b010201110304031e031e09 62
    0x7880d040200007415541c2d6080c144036090007200d0041d942a2240c0212116a291035007181d0b40b40014010140100060408034170a030f074650704040c04040d40d02e03080d660040e41b80c10b0708010185080b003641c00103104000701ca02d000390150018000440911000d00103002c9c050310b500415a00103005002084032420544540b04014004001c4004d070024040b60390515080401602190700180c072449000c1d14078499140c1070814500d204907981c0092031203040321901d4429120340c0102034610910a0421003601102c5078070707400800700d1a5080c44100540d8507030b00072a90341c9030800317800111070080c2000810745401b075210040d90307da0001e4416034002d45c2c40e40d001c5110798100440450b620380d11680481c7c45e4007125030b40080a0b14184204508111202c40000c3e541d40400b107941040701c0c498894408181d1003900028101002c0c00c007116628101032130006c0403103100184a081005403140c0c040c1d0b04a100b40914000da00710452482a0702d0622810b1500420100074100c82c0725654440c64681e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 822335908 1250 822334658 822334699
    0x50304030c060903021003050705090d050c04020d02190908030f030621031201080f0304030611090d050a060f051005100216180518030301180e150a0e0f07050f 70
    0x504610383d00c40c02c030341d440c5105000c03451300030010388001d00d42013030104100143d00009503603462500303d504d1030a001d030300d040082c204924801415002400014060310142c15500103000c0004040711401d000100f612007100c2511140c0906202600708002018910a02402035608810001c185000404141040101589180090750100e070004145c40900066a280e21303401480104050030343d80c0c41ca45101c40d01c80c400c0b070000802c0d86035a0262081403031106070036200840b00152170900c8440e00c60a10702c0d80e80c043d00b001103c5a0341030547d11988a2118003070680030706425213864240d0340c00c2c5010040d15071280d20040b030852088004000100c20300842420043c0380e041d0802c0fa10711009103580c4261140104003030aa5411040c400120800010480303044031070f600302c0d001c000c20004184030050402d104800038548502010b40c16040000c00440c0d00030204e8407010401414a04911900d8171000761601586404c001e05c02c0000d030074462180c20100c04010f00002200200448566 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 822337158 1250 822335908 822335933
    0x41e05030f030114040c14040605070302010b030f16231516030905010207050105030c0406050c0708071e1215050c1204110a0803040308090402070606080307030c030311160b0405030403 81
    0x1c03440790405101345040d0402d4400c2400300c0c1103500e0000c100660710740758688244034074409d10040010004801c828580300798001c0115020090036510032010000d00c0e41d0742c0b030700710028040789210170240000740d15908000e0b802110b8041100307202d440980380200040381e02d007284203071a2100c1c01c00241e035099036200ca00c81c001c1446900d52a481d1822711000925100f09500460b051140030418442024040000d550803207800786025550790310540e050f1400d04038154400700c540e1090000220f01031030698002450001880b402c0708940790b0700c90071901d4003070070f40340058442100064010207607001504160760100c44102e41610744000d030b42001c0000001280c09807030b444203152030800c09180142c2d082c001401030b4401182000c0c11515000d4191203a980414401c4e507000882c502084940e4000c500148003403003d07292079013101c0c140036010f5140c07101d044000918226420312007445400a0350a42442005d10040128207555001030b0104050700688083c4018440000040c01c80d03001c45 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 822338408 1250 822337158 822337169
    0x1e0a1101021b0c0a0806040b060103060305070305060a0f020301051f03150e160302310509090c0406051c030c0215160b0a020306010e0904060f0e07031406041e05030f0301 75
    0x410200400b185141400c542c101854412001003900b00030714500041e041e40c00941001c0715a00d20349480005070010441580000c10034055010000306210000c101244030313009088061015510403a480400c81c4024041ca90f803116504061000b40311811810f842d0203601e81c01c00140701304c0054040c0302c0ca040541d21007514040c0c54020040328120b1011358120041c103a0034194109921038100108101540c88425201500856a000b000c40d0b881c2c9414003d12001c1c24802250900d07036001ca440c4c0883d280803030300030f50414400040e0350401800b6211a04000301001401500580c0c0803601038950a500780e9000125400c032401040c0180014842c0149003a0035410032602c52070b200c04080b030b00600c601002e42c130500411107940d8100d6060407910001301c0780103040e503035146002d200410104121840740f5141074001c3d80604000550b9001350313409094894041e01d0980751007a5104400c0301c004008003082c0d403140660401850900080910490640e800c3c0900e0941a41e116007099116 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 822339658 1250 822338408 822338437
    0x60a0809013e0a05040515091c06050601020601030309170a0210030e16080307080d090c0e09190c0905270604020a290a0c0b0405030307141e0a110102 66
    0x400a400030250030765a80a203000c02c8682030290a060140917030090788101d5000301c06014400a00a041d80c4c00c40e900368000030b01008c41c3c003841d0069802883c040d43c0302114000c0c5045d003c50380c03035030000600b14100c9915613030701590036003031803040303a84590302d6440e2106512135a0b031802d0040e1b58080c80380102e142240c0e00000c0758806c0c0081e036440c0104006d10403001c03440f0760030140400c0c40048221159981c1180240b5a210903890b2a00c0c014119031314043c1242e00d50b0340002c101a41e800600c980100301c01011a01c2e40f685030102011204400e084c020007024032100c0070050000290480b40c4d21010250041041c0d010b00180308042e0301c04c00f4800f240540003030042100b10f140a600b0721001d403c4028141c2410003441000861031482802980b41d4202c01203581d003c0325101d4499043c503039034040303d29800d07814540b80c27a9035607800c2514084086190500d400040300d80800a503032285001740050107640d00706083d40209540103c5080082080719070705150380070407d0000b05200b1540481 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 822340908 1250 822339658 822339731
    0x2901020a320f060f0f01030c12030c0b0a0b0114160605131211071203020303070804020f130f0b04091e0c0b0a050a02010b030609100e010209031c031a060a080901 71
    0x101922130354801030412015940210050000c82c030701b004800c0a541c03540000c0100c1c0c01441c20242c4000c16805001400019074804100c15a1540d4121480848082e2600020150303508a010502e0042401c0641d5960400050b480410744035007020f500310102805044203e0f560307440350300710002001001004a1050300c1450b1481100300401c0d002401641200c40c1c0c094550394009440b0b02c80a44404100320f00407012500b90346e1901c0e905401650010309904d020340146920001030320b007541c00c030303450680341903102015070820f0300030b940460794044031042c003c400402c3e600d208444112000d80e03204a010002260b010116401030480804580b181d43d16010204802800e5500d1440d80031b000313400180c140160240005225035521031814404a01e821ba104c038242d009008864060f5418401d10910400980d10f020050b01640190342e000d00c0001d000003410b80c15200c0c5040c3c40d6820400410108403a1b500c901c500c650070201840010880e10035001c0340c00071504c4a4010151401c4c0c0154 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 822342158 1250 822340908 822340921
    0x110a020d020d020a02090f1f1401021203040b04080f070b0109092609040e030c0105131502030603060a0b040207020406080c010f030e07090e0f012901020a320f06 71
    0x2c141045103800e840102140015a808203400c00c0d409440c001c501c050040c00301d51010540007100c0d480c032004401080010b641d0348180d100c482c0d0038450003070250080e40b00b100056250f40040f40d118540094402220f622140d885501c00d51005403c2c501c030316400c0c82910300042c03503861078600130402d1000104000c401401d261039000354090007000c034007101c0c0c40520120074412040e142c0c1e90070b04a0b80014003509000c0b01a0541c85101d441010552900c001c008440c007032240c0f40b03045503010700c140364586000351601008030f200c00d54070540d00d46e10210010714101102c1c0c204440724174004d4005410b00031182c0c0418162842a001400d40313400c900340352105564042d5030924816041d1505020000840b0441c0d5103605640c050410015110502c014a4070360400c03907054400041c0c1c0080108a84030700c0f5048200b00380340c2001c0340300e2004105845440d0710010744007040581110320b100a03c0d180d031a00e03820041120000c801c0321080c4c840c510140400c00d220618010581030090006441d002 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 822343408 1250 822342158 822342163
    0xc0601051309020f010f020304050409150b010f0507081308010e2104050a0e0a1b0827032a010e0a0b0a150e09030d0c0c0b01050108060105120604110a020d02 69
    0x20912041c40e89001c801c50056654013001c0041140c007804c001c131400031149022403c51003181c126a4105080c00426400c001c0b440000040f194042035040003140da0100044032260035028100e0006001880110701180000c402482101c1d02d503105086020b946130060350943d025941d0255580d005036100d41110000300300c13001602d5054240301d81c83c0c58100b0b00042d1803139106008907807120f01c3c0000090140700c0c1a030b000041d859030b10700113100d0580303860400400c00d002c1100c01440c940080d5130700300445524405805007000d44080a10f04016014030000602001044170489040d4410301410b4840405c1c840e4840d0a03108401401c4480c0e01390400100b403000150044900350300e04001d40391120300100244090303c03a000490b400644501d44103d10314000c90001d100440c1c03030403c420040303079000f6600361001c41c401c10005402c0eaa1310703001522240c200b1180140810300421020514483c2c0c5c25201e68000c100070000580c1c0c502600b0490242d07007200d014440507a001030f408260a6404 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 822344658 1250 822343408 822343429
    0xc090115121103040b060a150e060f220626070c0606080a0b0f010e010b0a02010902100c02091506040b0f0f040e0103051603050a38070e06030103050712170c060105 72
    0x10394140000c1f0b0729007600030100c0c0c3c034a610072204200d0399440182246d61401e045aa541904401d81070b10303841c0d070f000c0381525599039115600f086403020500003415405a41030341140c440c01d062000d0600118018480f616030028002c0042000c0950070100203250361282e60f014001c103100502407440c25140c85c600b00c3d00c0140100e0305112415004010b4201860310450654181e0760300142c90340440f4000780c0c090480200b00a5100500c040e0f0403c0050303106070b245003003038000c413030855a513241d9260042c04262110300c1150813810400092102428030001030014100581c0410300e04201000c1c0c504407a00b0503041f040c14403501000420038440d041061030145800a601d80203103a10b16a59039a45082e010401803403800000d003040001c0303070004040c0002c0b5a27141300200005900fa0708440107280d003110b4800202e00707a4a0180800e04100068a050b0f03540a4000c2c80c00ba8281403045482540325501115882080046c1c2e00329000c1c00c201820796884648000c1000e9410b000402c04503000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 822345908 1250 822344658 822344671
    0x306040b0907060302120a110d0f0f1d0706110f030c010506040b10050405091009092d080d051b04080a03030615051207260f0106020c090115121103040b 67
    0x6005180d152401200c051f84c01403848280003aa448000340d0f02c8003180602e4403450a11743c609200102c01050360781046110b0700c0760345000c10a107024aa031800850200c02c40158059000410502c1094080d60f07a00419050940c200c90303a041c00c0e14006455540202c030490860394642c001c0c00090b00382400760040708982240d0300b20400d80040703402401c6001c3c5204907446111140049840807a6032110040039008256050000d403c40d070528101c0c0300c60401c00100b940012104a04040e0010700801c181b06500c00c1400c3e00e483c40e1075401c0310140501800340d00003440240d003454450103015000b000240444070180ca4800a0b5040242c00c44083c1d600c54001c031035240300741d1031141d98044110f9800840316980c004058032181c1c0b0031541d40c582501e2810041564440c0e410f821004101c280b4455080c201202000d0381e29640120303164801d554070181c01410038001845008101407007150107500c549050540c802c1c100c54584251542e6170000c0e84541400028001405500301c0086c0c0d1114 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 822347158 1250 822345908 822345911
    0x16091b02150f0a0b06030717010b0a0504060c0507050307061e03050708011511010f06140d17160f14010c14040b161703060a080115060804030e0306040b09070603 71
    0x5044222035440728500502d1050b51080403400210408941d6022000d80c4002400a540383d240151016103042040c140303080c518130742d0700000600ca00008040310003004103a668a81450320301001a980e074008244221114081c2900208094804005100c02003141d5501c4105220f070445a54903400e1820728000d00b018100010000b03c5900b01c801503046a0900190a88183c1a50070485071141003601e810080c1d420180c01d008041c0b869001201543e40f500404804107001a0030040c000c01d018800910304e408101c0d40400d40c040102c0900210418010300050b9030f04150f4800c000604002000c4a92400c10190030f1400071003449451041283d40c10301d040d00c4c2c01c0203100e10b81140210702c41c2502e4405c0026200595030008205006002d81c401480304c0408901044c20401340c10032075481340600d8103a5800510030105004155403c0c0062403050800b80c00d0174002c489100000300142d081c4080c8a039a5582501c040001c944154054460384032030703092482d42281040000c1e4440300406 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 822348408 1250 822347158 822347173
    0x708060a062a3518150d050907060f02032d1b151f090e0c040e071706130b062716050a170703110d0e010c0302072316091b02 55
    0x107a04c1c186440940c0307070072a0070b035601406400c030200c43d611035495224011800d0000f401b00380701c0300007480c00903104c0c552900000d00c0142e09080f80d89000d16a03032610036290711440c07214860769000001c482071188501061400c0030709050a11000841c0b101400c55500805c5503aa40351440800036421072041244003640c2c078075203040305502c5151401400241c60340c1e129088602a07040145507915100a0001d00c9110310130140c454523072881e4803420043c2c0035054071081292402245203031082c030320031644030b03014a206d480d0700940b044024011034101000300260101410b4040c5100601204900f0014161405041d5284102801d64001040c40020700050b260150402e58449000b1400d66481c1250741c0d03141000c41c041c100c990000405044001009911384e0556000070302c11880340300003071200860250b0704034100d02c6140c9000d040d040141d50340004440e03859888020f1001890304807142589490000764014180d40c0c010404103503a0b90740100040c440081b0b000140d141c41c00505500d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 822349658 1250 822348408 822348427
    0x5160315110a0e03030c071205071a030a02070213050a0e07153207050607080601020a020f040b0a030c080307020f040b010504060c05031201030b0708060a062a35 71
    0x540501c40c0c00b0020702481540000941c1c40c2042a5150540c00034200e03004159201c0c01d010405401580c20b8801d0700400d0030114200c000c0d000d40c0300d141d02e4030021040c516030720644030b03c000303401c480d104a07800348041300341ca2510086801981d000e0001da0200140140c070b0800928580070030356001d00100036200c42d55950745508500944014415188002d682001d8030007004114080722042c0c0040500215400b014440d0000e0503e114400c0c41d12281d401e5154000107a03507491000000030740c031282040c682d0020303060a1b00440c19101c0b009c0e02d8050419100d03980c50a90f180203402c001026031021500ca02076261040c44c10410220a071820404060242c000a00f5403283d4040c0c102441000004802000000c208880d000342003100e1500181d41c40349007240207001d040d1603110005107410086501840c1099012085801035190031408881c0e643c050041090b00c0300740071911841361084031000c00c18001100142c1000382d0044084411000e0400c2c805c5070340070841c150309041c1401078000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 822350908 1250 822349658 822349691
    0x13080f0f0a0e01020a022206050a03030c0201020f0c030d0f1704150b0405061503040203190c03020103050106050307021b060423090f01030f020108151f0207060c05060a0b03070305160315 82
    0x44c6080041c0c2d05511420640c4e9800236240d40d903c16508a50b40c80c00000506078482207060001c0e20036400d5800403102e1010981d540c0085070100e60349a080041001c0c4054040d1010640010721424040c02040d11039030341108900c07044038255007401e007034a101032043c0f000344a480c090090840d400c10060070000081907401c0355140030051a8800000418299034081100320a640349002c0383c0c050b9020145454840c2208500c8100d0100382400e0002c100140030340141c2e03110f103000d50700400c2c00040d01c12a41701e15402e2044200d82204081101145141101c0c540310142c580c1c0040380b0140c41000f50a104010300014025a40f41929400500014070043e5040c0038590702464000751544401c5180d84007402d01c004495031100440306002d110311214011503100e0b560940030365480c3d50b500c4a0039614141401c00040c5240c2024000a0126580350312610241c2c8014080307454160b12a925146440410741114540301001001082000384165aa08002003590b030140440c92140a1258 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 822352158 1250 822350908 822350929
    0x260f100501270c050f071a010e22170a0302280c060b03030f07060b03152205100203010303110d090b191710051201021213080f0f0a0e01020a02 63
    0x203600c40d1034500d480714144c40740d8241c40105103100d0700f183d6513075140e1404001c41d1403104503e200030b03021320300002001c0a0704220306128138031408030050040541d4a241011800780d2a003220b07807003d4000b403080d02c804014092300243e46140c400580c0d0b20040492090030039480d603502455081c600c0c010498080d40032901807403842e440b060100b01d488000f000281903004485201803003007408136240052149607001034042241c21b900390f4020301010544442020740840740c07d14162851061413055014800600d01e201d8001d400b542c8550840728000700030b1713034000c1e441036002a8400800c070007003010901c103400c0403022500300002d0240c03910007150700b0b6004043c4c07c0b101c009d0882d55a03500160150f0a124132600c5000740311f03481c5280c040766510482c0043d005072030141c0c61800550500310814400c64008003030b048203010789580c400c034060307800100d91402182d843c0b0090084100c442107910140c00c0800d09001c00c90344030351940c94000c0c074408900d071388281103600110883d00962108403010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 822353408 1250 822352158 822352229
    0x801090b01051021060e070507030f021203060609010905060d14011d070807110d030213060e150901020f0706020d140a08190e2a030d0801260f100501 66
    0x1458000072083c1801485c8550141107a505050100702143c1c0e03200008100e024480e44408042440001040f691003040c0e540c4460f2086040022074058640701010703203251401407412405440e124404103560740c0203075a081400b143c5403a40c4280308181035000d18050183c109040b00100500302400c0c61040c8081d040c541440007038404a1500c0707100d078480c032010503a01011034488001041d4014006d600070900c641c0100300040021a5241c4078009200b08500002d040d8180c6583c10303258841c6681c029000c0d181503205101909940300c43c18000c3d54014105c82d0094124088500d0010344040300442884090340801c00072000c0090300680443d4101c40c4071280c00c5240d9490b03a00074001403038070300e103140c505205081c140c10740701107416001568888186020300c1600384907070034144c0d00c044225003c00030501407001401845a00c0c2c0341101d0702820b0311034071500100003d140303a0a180c180d0240c00420381142498004204c0d80c1c0c06003500501516050440d501c40d205083d0726040701c008640c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 822354658 1250 822353408 822353447
    0x60702030702061b0607090614040303051206010201021e090f090403021504020123091318060504060213090221071b0c0f120318050109031410060801090b010510 71
    0x1105150070f41c0759040b0f0700c4c1d0314402c007115018109480c01810004551084100081014040c1c8601481440c203a03011660b042e1605410003e05090489060307000078004c034110342d0300340309401c43d000e071035072510460001985c003641d950102d140603c1050341603c007030325000350714150512000030740c001904083c800901441e4800e58a840c401221011103a41d445001d034001d8921034803c84100300f0040012540c1160780c01581440000c004090703940c20018980d521aa80441c07001148981d000b081d44a4030811005141c480c1d40c0c11f1104902a4540000c4d02c01075012689004950b100c20300000003141c050543c80b02d510707241c4001000f0300c2503e082c6400d140e80f03411444041001c05050940a801d42c103000c900d905861b000c110411301c40c0e03441c0075000110007500f00901068003651441c03e83d44113a44601c102415900c80c000c1a03640752003110340718454450004a00c2425102d12001361000800201c2d101c0d4407418900e401c2c0c18180c0001d441a403031403295607081d90b0008079181a004540c0031 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 822355908 1250 822354658 822354667
    0x13120305041a07020f0d02070f170d14040f030f1211030a110a0203030c16170c010e1f081503060f01060e0303070c1203032d15050a090603060b010206070203070206 72
    0x205d00b032030103445402a04e480307403107886c036401da80119122081d0303005128404038480e1b54010383c0900d030b42104c048081c0d94000e6032a01c40380302d1181d5101c007010010640101c0c1303403640d14042d24850320b02c594401e60703440000c940c0340c008110001c0350300c0360b517640b05180c0b1041421401d000b560301d074401c1900e14001c1c4a03007a1368000503003809000030481c458009041d43c0c0c4070310403034201584070546411401900c0004030070204200080d40f1202e103600030348400420b00c050315400151421100c1f10529070b4410101d9400b50042c581d05689007604441907070302c804150502201c070340342c0f030030b200402c0502ca5040b072420008055100c80c0c1c610704403203035440e101c10300e1103e18003c0713400c610981c1005043c560324010080380c241c0b09141c03d40c20841c030a0f1740c104100f04107005201e8040300c1301441c1a00400d007a0000c1c10000345c40d900411032503601c280001114a0351203000404140d03c503400780d0b03a81c41e10f4550400620496118a11540c10280050070300d0b4038107000001d4582c810b1010003031041c0001304 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 822357158 1250 822355908 822355921
    0x70c05061812011401150203030f061804050c03070f0b0d02090d0b01030303050402030d0302120f040204021b0c1008090303130f060204090906050a1509050c0c0613120305041a 77
    0x1070441075a07600c058400440c0700c0240850a0181681210f480b0500c60101c00004800c01c402d030300d0400e10b40c100e50281d411a1605900d0708284440900420f80c03007400041e1a500704d0410b42034081c040c5210b440100794a000e42002e050500d0308560000c40d00d407e1000c0c04100502007482100d04440001d100141da88448200203482c501c00c810f409448801ca800000c800c05070136501450280d8000c60489244c02c4410804900364801d480802807c2c86151000ca0740740028000d010750444e10040008d4140500b01031840d0070744094038040140d552091810300d86030300300070624182d991100d01e0410030300d2504000c29552441301404810481d4000c2c0554014025171154032800301c0d600410940d6520b0b074603900c8101030004442d0a480c1c1c145080042214030303030a4030a9014841ea540310345a121807070301e8403c0000707200c001c03c030694540003007111080b06070081c00514411008403610030400300345401e1611201c2960030313011061500d81020311001c60f10281d8071020f0041c4d04e0302914403039580c90 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 822358408 1250 822357158 822357187
    0xb0a1a2d060c03073903060f0e0d030b0f030102040312050c0c03011803320a12050708180601060e06090103020904060905090c0103020f03070318050d05040317070c0506 74
    0x45086407507901010505900300a2030100d000102d40c60305110044d1401501e00b0702e01e49400300780c1d90040c0030b03901817000c00c00103407180c01121101842c0c00c0300103002200209001e040010300e080c42400680d5441c3c18140c0e41c0391504802600b07601c01d8000f14105421503070785a1590008028190900c003021400c038600d040108407007403080d40301600a004c1110400d540c2c1c1c1107440119411000b192000050701d140c050b00d204034401c0294100000c0040c1441090541d0a50340310a42c0c48041101d0b4200c855034907200d07402003c2c020b010b41d42e1842040d00c1c18103620541c1824442c074907a0b260304603000410003941d01c031060383d00742d0710f041b180565103250000040e4000d11481d4030b41070b00103043c41800a185041580540d1150304404159031441e0341c030f400111304034401c055510040c55000d00200d8240c9200703074480764000480381d0044800d4101c90300c85515019007000307003000099002505204001368585078441e40900c18404900300754180d540d0b0080c00d661401f0f11400349501040700c0c000d03840384 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 822359658 1250 822358408 822358417
    0x1a060d09020d0f030513050103021e1e0315030606030f150c0d050f01051002070e150307030506010806040507051002030307120f020c03070c05030610030f020406030b0a1a2d06 77
    0x603041d68030f004a40c0c078010340340360010340583e4041d50f02c040000403103502900844d1001d0032050101c40b07143c802c4151a542507044002070240b440a0103071042c16100c04640114016001c0f02c48846441304030f50105442d090000308824080e40003a903160070041070005049000c7c46040c40d9100d20b6654191880b01103002e03905640c4d02e0582060b060180d000d0480141905a03102550035900380c5460a2050307980b01d440d4450340e984c40c0c031100b00064060000c81840303121464010241c0b00d0341c5030303139490350340c0b4114081e0040e01464010209000401004018040c01080241d944140070040400302030f403030740002003040007031140b0450380700b0500c0e04a501c4141c5002e100c500440d2036201d01c0c2c109590303d030007800e0200c41c0044940300c0410303546000169075200d250b05614030b00f10b039400e5503503084010000c0c1ca8100e030000d44880011000030300403c2c0c074901ca12060100050081040e0440010b25681e19413010700590b4092a24820101004c0748901002c2490381810391040140b40030502a01c01c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 822360908 1250 822359658 822359663
    0x80f070516030b15010807051209010204050d0309140a0b09122b081506190201020702030a20010807080a0c021f060614190c03120509030a02011a060d09020d 69
    0x251071501104201d02070700c103140501c80c14003420070036140c00c0f0b00550b004c03d01036805102250042c0a04c0e0079114600d40801e9000c940c5400150a01ea41c8501191600c2469102200400c0d00c0080911224035040700005000c54104d8295038103d1814550703440707d101310391060303000d0f184032050015403550030480031030804818006171440ca0041c0110140841d00280c100c0002149840480d00c58080c0e221802d09004006107107602e4511001243e41c54510302c1c0c0c2c2181c1c01d554017070201c0d401580d03080c00b000080f82d016004c442c1380c0e5091481501d08010440a0803414400b43c0010b00c030340191301405c0503920400da1000003481c1800c01506910300103d034003030003000c04020100e243c2d50101e150454800c40340c2d140c40c1c054000c048100510b10384e000d640c90700c41c2d19403a18010041c3c01407007080c1c000c16503406403c08490219007804880103a4004884460b00c81d480010070f658907550912500c400b880844010b60f803541c014000082052244074400219907886544040075581c800980020255 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 822362158 1250 822360908 822360943
    0x6120714060711032e06081c17070801031e0f060b06070f141c020c240d0e060106020a0f02100e03060709090614100311090303070b09010b010309080f0705 68
    0x1440b04445c032246120403001c038090042164240d25400c41500840f41501c01040140c10300c00c0c0b012000c0f60320301c10440070001c10441e241040101000e042d014103401941150717906005036040d810204200802d048040b0109201404800040340c0760240c6080c20503444200071030003034014030003ea154092844c1c060f0440180c003915a040184000980c071400b9291420303036803e902c1c2c00c2c0c3c40400c898004049035000d40c0004080c4a814070307040c04000d000310aa04240001c020340114000241d4101c16820002c9669500b8400f20780740041040130b006142c0e520061203400d80c0c2e691a00144402d4110003030041941c4444100264056940c00c10240c3e00030702122040e1402410081c0503c5180c4030340c2e40c0440c548500440c180c0c40300d90401034240030191852641d886800401c0b0001c0c0212154080c1222044c4410090758cd800e000610300e450041222151500303001c00d0440c2125600340d05103040c14588001d030400990800140c031920700710a514551500c1030707800c00d1405d002e1950550b01381072 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 822363408 1250 822362158 822362173
    0xc010f0905041a0a05040629070c03150f0606020d120902030d080a05240f0a0302060f0703090905100b0703230d0c081504181205030612071406071103 66
    0x441082080e0b00f402c034110b03400d80c2d10b15a502d0030301013141c0e9280112052281c0541000c4c04031074042800220102c01e1130b00451078410320752204d841c0d081c515007007150201d10717800b0022400000d60042407810303c0c04143c01c10a0f50710303143c001707541d070b050038200380c404d00c400e000800c0221011980300008040d000b805690300c100048038010401d0208131015001c0b1486c0c00d020681c1c860700101c03203c584014405401e6103280003141040307480c803220313009154041140071010006845040260800c80c0c81e4060031070302c1b06810b14000d401900550031060300300b480e1004000da00d00701d440407002100c1d11045020b603100801d040032507940d0303c00c0c003580340350180014180907568a20f0000300f00b030182c2c54508000d142211041210362070f000380c881c2c00481809042d21106858140e0002842a4030b0300b11003142e241b01c683d126001110300c50b400b44045040401040050b08258180c3d0000450000c0903042e0641000944410104101b201d17034050640071a18800b00030f1250850700c16014010129140f5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 822364658 1250 822363408 822363431
    0x312030501031a240d020a0801020a020c04050c0433050d0f090f1401020412140f0f061f080f0a05011503050c060c12070302150c0403050c010f090504 66
    0x18000c288411550070218000d10101c2e0094400c00b2070041100c1d12141d02040005485200d0240f0500384856010301050111030050791a001004003e02c220381c00581c40d0902c41001904198055500d20f00490426081001880c003032000c030303010f0b00d40002c007564a0b81c2c00c050102c404400c052120405003090b901207000001c0e00103001e041c003102c00c05820b0210b40109075a65003070b100d80e048000e00c6d110300c400841c40007030103084d14415400502c400050401e50782d41c813510094040c0c0c150a881081c000d03c00d40c00c1c0018280407080c411400f0000904940e4800000140d40b1b06000b06004555a41e2040441903640c003151018000c2842004403064055801d9446488040e150780450b200c2d07282640c0520201c1ca1004103108983e000000b4040c4606110207020741c2d42c0c064680b41c1054065144620282c030148009401054081e03402425110f8500e500c3c080342400c058040c64000905200400c0000d40000c0c194400c4036003843c0c14008055144020b0303440c202d594110035071040c14486c8150a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 822365908 1250 822364658 822364661
    0x30b09030c150a060f080604141f0906110405030307060b011808060709060212040303080c0708042702070f11030f030301080c0102060606040f060c030e0d080a030b040b0901050d0606031203 83
    0x1a104040c0100072007950ba105005c9260307031612800d04507070000800900070420060a4041c00c2040106a990000030304404094104810805c1c801d080d96441c0c00806001048c4584912101b0380c0c20558079060410b000a540d90042e0140148210749400b20b40c0c01036441100c2d12459940d211b1881d44401707882e1092135450b2101101d0300000a89140c4c40014001e200240d036458034904a218546480d0858808843c40326000b441160b000c80c040000314001404240240001c0160841612850002d030100d00c1a80c0741440307c0320f21260060000101199580006080640c0d2000c081a8142070b5040804d0800780026025441404080000645081c005c00d01104030f0800342d0075217070303150758885c10450180510b00500400b03e85d14601840b190380140000f10b01540a4101402e50b620b03403100180c28414040c0c02240c1c008008a200c45a07550140200103c05e10304a4050041032610707004a10741810501c5031170310411a03000c190052000c140d2144001d16000807803031840c1c01c8150740280 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 822367158 1250 822365908 822365911
    0xb16020a06120c0903080412050c060708070c1d01050f040e0d0201020d0e1c112506120218040506040905063111060733060b090307030b09030c15 64
    0x10030941040d2009840d01c0c130401d04902a43e0340021b00b0340c1420b05040450b40041e403503800441d160b200d600b494001d540e4854000e000280e108000003030360341c141d5280981d40d11103d41d1200c0c02000c3d00c001302c0b003c0f0f14900900715054070006e4503040c5011266000040c06092543ca0072400340c080d046e0706a000d0380c1d040d00100071074415a002400781360076a0340342541d2000761783d01200c0c42c0050340d100d0b068624840e21120803440d034242d04a071a00c00080003090042c000700080701e0740000c0a024204019608030202ca101000904001c504100880020300701204103500000c1c071684e964000607075256039507070014811076001001c940c0d8074548048102460010940da580c842060382600e180f590360a210400f010943c404017400d9034204100502455400052048450010421480c040c030019401d05403002c000112103803403074204400d4060210f81564000e91940003040004842030b40380020744c0011a0360201790752046a4401c02800d04501880c9250455400780041d4148d440766000c1c1102d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 822368408 1250 822367158 822367187
    0x60b0d1103010e070b1b0c1f08010e070c062708091206060307030b06130e010f0509010e030a0e18070207060210050730020a02071409100b16020a06 65
    0x1c00c01801d50803c1e00c1d68640a510985401c03000401440c200407100c83e42c2040c01d000d4210446c0d4500a00340009008401c60f02031400c45041c5080500414947c4a04008c0c01461044003c004904000d00010408800d020300504400e032035a104410504020b1414003040003040c80007070104440307180071200c030313030000107658403c5040e00b2000070302c0000458182d003d044010000c0c601c0500c1d5a68170510254001c00d80c9901540351421603044059030b0240c1340c442c5821a00000d01c406017100e0300340c2252406032145c0c0044e890302d1129408507a0000841d91110124100740491050712000519845041c444600480c401c1d0420b1000140d00006c0e903a003966090340a075071013800010028422500208c60b0b0000040f03220450b80708084000c90717480143e038020815601c4458030003c262059900020049005901c2a801040b11041c4518400d4041d02c080344c15048030700300900d009000b07080e2402812702c100e0001070035208a044200b084a1007550192044143c03599500700a01480d8400342034 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 822369658 1250 822368408 822368411
    0x17070c260c0603060a180209040906060503060f090727060b0a080106050c030318160e010f1d16020709090f0606120f12050c0105040b0105010f081302010309060b0d110301 75
    0x80c0700745261401c241d03480707240041c00303400e4041d150942e0f10301d000303d0500f5001e00e8640c1c01c000401e06900c560040c0c08000307000d00804a082468002031614003480101024101d854031400d0203142d2001146d030344100c40006001e142960110009000004401602200c15601c0c0c0100014070342c41241c090f0a6020143e11485034aa0b0713901c400782e5403803040400038521900100000b071042d02070482c1300310b00d015a2a0803a501d204c0800820341d4a40c15580040c00b10580f2880100642124a240d9401401080440c0503900c020101e12040c02c40b80500b40145003c031040501032524400c04c643c4c2c00405180f2414080d80c00c103410038a0b404080c22406076146400c1c03800210380300000025040160ba07101c001402030011544448290080780912030040050403c41010409000d01540d4062401044c205c3d50b254074120000d005490501092014020420200304000e01481a594510740d02820003040300304291400c44014007004803a56404820840c034203040c4012044c0c20800030505030300 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 822370908 1250 822369658 822369673
    0x6011803050a052806020a0e091005130b010806240318060604060602060f0403120212090c042c100e03090a0509012711120708011217070c26 62
    0xc0302600f1820030540040d084d44d2140da4000043c03807a0f80213208480042c9051b08c3c041c120640010302c103d5050356000558200400c0a2106103010a04080b11801500c000c0000c3d80c00080007904100008040900c280c036030107c2e13800b2548503040d00d4402003d9122185a4034644064407d6145602c103584039201d01c600030001d8800d05043c800c90044c0da0303090b002403406946a40c2c0f15500a42e00420880070004480e00c0e161034114140040c1ca82c0c0f0100351602c0c20280f0705070b110340d49480d0710b02a0321449241080c030b140c0e128a541801d4050b00221481c0c5103507000318480c0006240191100704484428034042901d1340c840c0010004d040002c4085035040e4070247e86004010b851542801184800034918000070030012100003d0416412010070108600c038210100203c2a00820400810408890b040017000d0b03601003049809008911450f070140c41194035050440b9100030404403150400081010500948600140080044000c80d103182032422400581100500b103810005105454 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 822372158 1250 822370908 822370933
    0x5041e05090601030b1e0c03090f03040603020d290108040807020303130302030c0307081905070e0c0301051503070504060c0f020405040c050a0f2d0b0307030617010e0a02060306011803050a05 84
    0x1c55050003140701b070300e01408548495281c292158005883c19006206603580b0101c004018005440201003d4400580710f13000c003000b810948400110300341c0301d402102003190a40340d0f030241c40da070451820300c0c1543c0a5034030f038035251116110301d0300080d40c1840041260303d0750301d0030150744070103881c420f5050382e0a582001043c0b41d5200001d00a03c41207400080751046008601440803c0241c000c80803510130950300c640c0d200700b0030010380d55042c0302d560000042c80142001d10610021583d070390302051031807401040040190049000d0341d0100985000707881c041c052801180034906800030001c000a040c203250500c141c003800d22031140184450400050b2001c070051120088074a046034103244c03d1803140034040c118542d010103041c0f80116450224920600001441c800d40e00e680b0000bd2084c00c0941c18500e0522100c00c5501ca603040080d40d02401c540480c820308030b981d065810544941b69000140c1d402000e280c855281a23002d4007001050110018491244a005905a0309451001c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 822373408 1250 822372158 822372181
    0x402040e0109020d020f010c021207061e020601150504181e091703060406080f0109060609061503110405180f0112050a031119080703020601051905041e05090601030b 73
    0x2c0c02d0195100c1d0f140032400c00542020b0b00034000750f0f6014984070103035080e9540040c1410503094200445a030001d0424082960021214407807200c40091105510b079035501d0003036842005020b030200b10202c00d108608580e0007401030f0307800707000035401c2d40807084200f0009100600c9103c250001c01c910411010300c6000b405c2c0700e00d03240d0700d0300b01c0c100e10b207820510203074010303140d0010f02540e820a81c1c0f4400010108001e110707007007010402c02e0020038202d410741070050a403200c60b0003601580d460943c04104100c22b00c1d01c0e0003242001418045003641840781e03004281d0240d0703805241c100e4000d44010000c1030240c480e6511170440c0c0c070b65910b07851b40c80b4a9840b03002e00e0361a03c003c0042e40300140c1c04000c01e006102c02a09101a0780440c0e2808041c11181001420b40030004c58085801041038400c01d501030101ca4050b02d001c1d1522825a8000d41d854500550280b140e0350240e0354440c1c490380c001b0a4640300001c80c0201c00d40501807400c05003402c5907901400d20095801d0500c40005c6a203481c45c4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 822374658 1250 822373408 822373421
    0x6020615042c0a060509060f0a0203010f090506122d0705090408030a063b0601120b12030a080415020903030a2007030c09060b030603030a030c12050a050402040e01 72
    0x40101c6842c000303180c0424001c0d0820201d20302c41691285200040c00105a400707014400c0f15644081c1c104ca05103903035449003060025003884050f034018070040c012401040e4000c1c08840d9000c00c041100c3d21204041550000d031144000564003c48040d51100650041c00082d6520b000340740d0700e040c00d122810316840788900c0c040d5690000307140d40802c000c40c8591016640103042c90340005078596440c40c01e00c40e14140301000a000c9807503a00c1c02100d0340013208003003411641d18182d158892034880d00082c811002c1c003685495255a0302150415502c414400c00400c0b5007880c2100d54803822800d000c0d002000450b230440d806231280c074031010042601e0090300c022150250083d8102403900c04142d81c00080e580c080e06080800ba0343c8104103e004210141c0150b00a0b09000503090074014443c0c213685c02ea8015040b2440204140a410389000040b10315619440c54001402490f4040444990810b0741c804698103017002d0a000060005501945c00f43d4400c0700d08000350300300107000034240d444 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 822375908 1250 822374658 822374681
    0xd0e030d091208031905160305060108040b07140d020301170705030a0c0b030606070f03080f060301090c050618101d04050c07110a051908010b0307050a1703070c0602061504 76
    0x20302c04000540158003440e0007800c0b03000441100036122184204841c001c1700c044080b0f1902e82170200920390980f2410741c10000c00c0c83c00945038681a100e0703110310203018101e541004840c44140e144221208243d40d000700c0c00d5802503540b56540c2121358040120200d4691250064102c006910701d07000500781d10705613010a20807481c0c2e18088150146410042017503401c0700040180d03400207122141c050151034400d40302c0c5403190400c4024603040c140f00514040c0203a01d0409003d000c9850007011000310303401121201d45d00c40c01120041c1c1c0d2800c0c110246a0070200c2403440790b80542d0008414070f500261020440042c0403008100000d0302c40a488104800900700210f074040350b100451922800005080d1105855503440450b01010303580c0796070b0001d05c0c10360710103220f818000e000e4920180f00440c000c0146a0034400002d4100130a489081c0891088107545101c100c418819903104a411900080b00655070f220082c1d240c9078103c900c0313190002c21301142c00c12890300788125880a01e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 822377158 1250 822375908 822375929
    0xc0a0e041502030a0f090f1b0602030f090f030708150705130603090606050310020c070909050316060b03070902041707060f030e03070b280b010203070b07110d0e030d09 74
    0x7041c001000000e40c0060541540e1035111400d103040c08081d0300a568060b84130b640c080500d0300031401c01c680b0b42940000600c0c5000c60641c0c0c104041e035400400d64008410003003c540e40c4400050004601c1c101c0c0005168142c022000d00142c0000e011800511410003a14420040e5803035880441c0d0758443c895480c440c01c520765500344500d610a41c0b10ba4800f40c89810001501925100024039040c414180f140300c16400185030072624001340490001001a080240500092903544a48038020001640c982c0301c0c1d031640c440c00340001500030b01070310500030b4190b507002034680d400705001e035006000e811362600040311070200b4140005040030454074540d641185401c85201c0480141140010f440c078988010b22101e000308540c800890b001c3e0291944880f6400b54201c00c0b46d62143d40800c2810405203042c2d40840c01d640c002c0101c42140e0360014003802195507210054030703070340c90207070b510341d154411468040344058000b888110101e030218100c420784150203d0445080b180ca0007a0070b200c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 822378408 1250 822377158 822377183
    0xc0919030b1518010f08150c070825030323100501030510090f0c09081203010b1e0d0515151c1803021b1f120209120c0a0e04 55
    0x38550108545202d000007031001c50304060060b50358014110a1700102c01c50074103500301b04103021040110200b10342d00d255444855240100094442d4001c1c070b40d01400ca81800568840395030308040ca049420b00d54180e881c42c01401c5c42c01c004006205036001c035000d00c58107141200b07512000f100c0341d510070042110015403081c1403000441c003819014001d001c41e11030108000c41d004005000b2440d000104440000d82105d0741200105001181d40c48803145030025044030040788030ba04100c906481c114048543e60f0704803c407014210f070300254001c2044075030108200e1943c00f0584c112034007482c01c0045d2154a10421420041081c0d00c100380344160307010030488420000e03050001c20320b40c41c0a0800026241c4642d29020700130040c440000c60041e000060380b00c030202100210281c00c4a0241d446011f41c0c0a6403040b20341e44802c2800138814020400c000701000c03406501110281c110140c4818501e4000c1010103a503070001c150100d100e00350314000407c00450581c0500d1056401443d101d252 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 822379658 1250 822378408 822378421
    0x6030b040b13150f1701052505070c0504061403010c0807020c0f030a0c12061103040f0308060a0b0f180612040f030c050a11130b010210180b0c0919030b 67
    0x1841401e0f0614003918405000080b0407243d00d1002000785580107100c07030701007040030350282140c0004000c02c02401ca1041c034040482841d600c00318400c0c041d814020755544e12401c0041c0009500e1340308580c882c0c2401030204080c4003a01ca500403680094009102060030003c040d0380c0070341e04584060069000500720104c030710300112201d44007200941a0307803c0c1d0704161654058240d044c1c11008000c10194554000c10200380305070803107809989205400e50401ea50303983d40315040803002604000304580807491680d04c01085400a0290000d900e954400c20400040305810007116503001c54846448851281808012180500301c00300d50500c40380d6580d07481c000002e03030a0070709404101c480b241a100080b0200b00810845009070b4159804046440030051070341180d1006083c40703400c0c102c025603d0703600044c40b4141c03a00c20442c00300f2110304801d2103440007403040402600e8000020f051101900000e0300401c0e000105541c0542842c0c0d249080c18110119403000411000601000584 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 822380908 1250 822379658 822379661
    0x12020a08030c0f0705010c0c0b0106032a0509040501080715031503020d170d06151b121110050105090f160c1a04110306010f08070b031305030a030606030b040b13 71
    0x1901c543c2c51205606150103a00c402c0e08407004070001d0341c085901d07118100240204400c03040e00501031031400b800305614105031140005251302d85c00a140b003902c0c07824100d56004a003603c10782140640f041003e584c1d22105143d95031414802ea4502030200841444002e2103401030440c1840da0312100540d03145517a0900400d28000441139503942c00300140e0b40c889505030303401895400f24210740400c0d4141042107911b214a640c2c80e05505225070140c41d003504240d0300001c0008907400c061341004005200c103040c0d54409030a0341c01d04140c010a10360744502c6046a02c218141c64055031051040d0340c13021815410f02e4401e41e8941c420282c400141445940f040c0518001c40d442964815040704e507900e041c1241d024180d501300d60803c03442161603a20304040003814010080d005401c8642031078005141c1c4c072400d441c05014058200040003c492003080500740d0345c00c5900c1000c41b40d0740c03444c0d64001401001c00740100d0380000d0502500240c2441c060040f402c000c40c0040405044501349200d280 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 822382158 1250 822380908 822380917
    0xd0509120a02061206030c010c110906010311040b0315190b0a0509060715050a05070f03150b04062c18041b080a03030e012307090902030a0912020a08030c 68
    0x1040d40c803070300165000680b01d040c0a041da0b4808501e11280c0ca0a2150805040c03c0001111504004000c02120045403420500408200c6c040e500c010071615114012000b91412581e0316100020000300020b2005400b002988601c1c4410704486030f009155040115904880710070701e042c040c031550f0a0000d140650f00519040404c2c0c1441464200100c0200c0c410740c105050545240d4003d2401e4641e18890313019190740004108010011880e0120001e007449100d0f000020425a03501c0d40b90103000707000303c0100e0140289490560300d0750703030304c00c80244090422040e480f600344500e4186c6a9a000782402d116009100078131a0b00c11200d0181c8000b902c110043c000d51b5080d280220000030307000040199070152035000c0152035010464140070342070364484200c65101d40c0c07506035040501c41001c4602c040021400502d802c1a0322513410840d069030044d001161054400005d009070321125a0001500600c00e011568041d0a03031030b03059845141c000b001030400c080c10000a10044140300091 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 822383408 1250 822382158 822382189
    0x10230a05250e0a060c02130b012a0609060c110304030206120603160e09011103150f130c081519260a08120f070c020904140d09090e0d0509 61
    0xb0810105000000d96500b0720750b01140205407a00480002d5003041ca03c203140d1409580d00c103118074083c40c00000c21040d07200c00302c06181030098001c2d800c0012403400404406800040c00d1045401f681000e90041c0480c460b00c0703000c94100001500009004010b403021a07400420503800c105c20312140c4000d50600034400c55150041141e103071101a0385814200c098400d11400020601e00044820300f15002030200700307840d480030320800c001000c0c038005142044105441030103042d10b160740400d0544034000d00e0780000030b00b0800c0c26011540d0103d0f4682c8202c80760708040c071040000da028442905103003008016007030a6104144012840e0705203034001c9000b807054040300d11002d15012800c002c108801285e80d000c002504802c1c1c0412145500d800c40c81500c0d40103041d0822843c040e18107047c00c40000d000e421200c00041c01c2c482003403002c103031f00c440c03c80543d0810f00f0f10300e800400440050150756400c83c03800c116424020000185041d035242243c4034146092000300c10000c0c2d0344000d0005 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 822384658 1250 822383408 822383417
    0x6050a0b030f0f1213050d08040302120a1514040b0402030f01061806060f020303070c0303060302150c0d0305060f0d050f030a0525020d020105030910230a0525 70
    0x103804258408010900442ca0000050301520034120460390819415414004032040c041c0706030303004407140d403400404484088440007a40905481c058035240140e600195000c8500340b0100c403400c401207011007045105407400281c1018031000041150b05200c3c100c100500c002d0006400244508240e54125000a0407295140c20b4183c040e030039103030140c00c400303001c1d50350500b00842906180240e04c050f010b182040074030b81c540918020b44c0e034000107002d0002c2103040710742c10b4107050083d030044000e542c0203042c0f15070003000128a03510341d60042804540b244039001c40103043d00d100780f04490003190028072145d106011002004040c3c0d14064064800b0b000705211841c2d0700e54200020052030107103072034031500e50441c0d0700c854480700052020140541d0646541c0070059a400603004421582401e04035140d4803404a1180703080c1c1c0b0004040c011629212030040d11440400740d100348003500d61000485503680c1010b0718145d41096a807120ba80800c0920001d4140710300140d50544051480d2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 822385908 1250 822384658 822384671
    0xe0d030905130606170705030705130f030b0916030506060f01020111070308012d06050a051b03031b0f0f09130603260a021e0106030606090e060105031906050a 70
    0x54001e001ca8030071035404503590741080210713681100d070511154108000c0c0c070305589407402d000b6000b440010201c0e000c0040024058501140090410028188081d0007800030703030300d03031510054a82007595101098481c81c1c0d03100c850802002c4142e4181ca41c488062300c140d8071000107020702c45081c1d42c01c090655403142020a100301c1100042d0030100e01903a242c18607545801c09a4900c040940e4a0000d800145003101c0b0709425089800d60443e501c0789403940e035640c1452421190707805609482502c41a89100c00189240000051805080900203560740c4158404e583c0c200b81c401c4805c1e402441000340f10203200c0c590304201814440f00003038400048030240040d104203c0b980c0390411200c1c4c05180d50440d28103907180b0014482508902d41d414175003c0040341c042d554115980110b152110540f513284a0201c013904090020341d80100300b070281c152100c040901800042a8804840c8510000011b4a180003c1c89001d0480f0381c178100340034040305880302005020005c0404840ba526000c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 822387158 1250 822385908 822385919
    0xf0a20030c0d1503020405061005070b0606190207090e03090f040504060b06030c21061c05120c01020903010c0c0c03030503040821070305010e0114131d0f0607020307030e0d0309 78
    0x180280c01e80314604044005003944100021907c018000328020315400321a094040d0700501240e07002c2e5000103585401da5246000a1050300c03c0911081a040100c61800d14030713600016080706a50014030140900018150140d40e03070301481401d280d01410f028030403a06818036600058002e4003c40700400d5049620020503d80d5006440040c0c1c10317000042d80c12115107600340400e0780300042c8140129107041450010380400c040c01c0714802845204005c10b0b040041c00c0101090003087c0c002072a44a44044031405e0007500420561070081d400c1c111510010f92050701c0e0000010380c007694480c01ea41c02d40d10112140d40004004903002c0ca020444a1011000707a0500920b10340c0702c151203c52071070426801010b071103060340b01844c181542801400950310a245500380c414041d102c54005001440c0e03200080c1c1424280c2d00e40c110754885400202d1503000c0341440600020000304c40190b16148000ca81d0391003044800b82c006442010403402c1d91514001784503400d030103890008500c5032540d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 822388408 1250 822387158 822387161
    0x2070e0c07141207080c010b041107060b0f04062903010b1905090a1215050405030922060e010e0106020f0604110d020a0e0a0f09050307140a05060705030f0a20030c0d 73
    0x1500b080e0b841071000714440c0f035505024020340110742307002e84040c41015400700d62060381c0c2c011401c0050590b503c0d45802952600d4014428103c101c0c010801d0000d00d5a81060200800c0300c20302e11060400c179081c00b5007083e05120120381c102c440801c0010300c2c11340010784246051500d01208810001c040000803130642d1000e4018002c1d0145041c0500c40c000c0c01e2502c03090501485400480a0341040304100100301d01000b40e92034042d09a84103240d05017043c40c40700089100b240e5a810b0a441c221012681c2c8101021482c183c8424a05080780c6036240d200903a624084400420340d15408040014002018182d181d400885c0142000d84100b90703035030000d441c50f141d940006800056800c00c01c020440720703004d41103032200200e604000d0303141103460300e54603407040081c09001c0f085007102d0340000c00c10401c44054040d0708901a00c607541007940c0014615482540e408142c42c4a80c40801c01c4084d4501c100403120a15108900c201741500e098516150002424034929810a2106511502d0103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 822389658 1250 822388408 822388417
    0x1e020a030b09090f07060f1205090102030604050708090604030e040f020d0b010210060815060307030b010b030402091608060d080c1b0414060a030b100312050a02070e0c071412 77
    0x4540300803034001003580500c10455401484001c00b03500ca59001104003002003905000c1e41c005183c40300061251000561303404606101f041e01c0700349007000b042503101d4113501441c01070b02c0450b010b004640700c540003250340300c8050b5070440e0981c0205010900081c0620003010303200102520204141c1d4094034000226002543c03010f80f801c0e01e800b9516000d6a060000c8440780c00454400c000090030201402d58030020302c41f104c80d00750f8403031011400984d405c0250400542e4003011100c0782c4d60711060001030a400645049001e10100c0700407e0415250850a02e15403104da0348845040c0e440004005c04030f0341d900420b4500c02010054070b10300b6401404801101900325100040c15044035046c082118101a281c41a0808600600215075a00b00c42c40f0201d0342c04c00b40740c040d40e40b16004820701c004141d600003000c0201c0c1c2c0070a140b07015013140c064035a550442d025510f4403a0344150100b0842d004035080d90b0b10300400c000d00000500210030504d2000780003802c0b1111204000705c40380080c0d02 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 822390908 1250 822389658 822389677
    0xb0a0e1504290c0a0e040e0109050706230f03100302120c0102100c091e21060e01050106020c0d0309051003060e070e0a03200d120207080c090a1e02 65
    0x46103200088020b1003820308601c0041001d052048034601091550140c1c09030003130403010010321442d50405640e5a0700019003a6056400820540f402882d199603101c61078894000402c400c00c1954003020941004a4031003007440001a10b000200110010694801405846104160080400035880e402c010124401c9081e00030080c1c0030f9114006460b000161808040300340c1883d5130000752642c85501d0500321203a10108140c85007215403041000760243c0c000c0918580e041d58075003005203144104007240c600407681000f80c2190081514282c42090141a0169000111668180c20700140c0503444c1406442e210001a466000068804e9070007400240060f031194401e001d00c8002c400d00d603401c4030b518240491000c41c041c020803000c55152002810b14050160301d14040e4022859030100d40100500d6071190b1040c0e0710302031140346041c03a101030040c45020004900c680300000d039504505070040503c03485030740d1420400c000d05015405122421070750801c40e00843c0036400540345000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 822392158 1250 822390908 822390923
    0x207092f030106030e06060f100908032a06040215130503100902030c094f0c060c030e09070201060b030a06330e0a050a060809010b0109030b0a0e1504 66
    0x514050f40142912403242d88900181c2103401403001540c3c41c0c080396220f0b140103454920011a86200a5800c0d0119901080941c000041c490b001745441c0079840c034000c2c051109040949600908859903114110f90003500301c03c6000036035410214070009401d03d007004c50101c1201c02d86401c0030034148607503010004010b5440303000c2e080851500b4032816241748800e590380400752a00c82029401e03c028020080d543e501840880d00240c2090080d8481e04101084058002d2017035142c80c0045d0f00e5551070541d00d660006502042c841d124180d68040700350181c0d0788548100d03031070b400c000342020050b2207401903659881c0700040e010344490180d171149944002c000f5000c0e00c2e00984090000e218080311243c00000952103e0458588070b0110a482c801d140003140040740304040380d901c12260700540d80c0000702c0320b000141c003913000c614075200c0c101d80c030000d11203901d1210055503401d0007400000c2c03400c2200800501100101c3d070100c00010b040200700c0710030032428110401141c0094a003170700c691 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 822393408 1250 822392158 822392161
    0x32f0d0207090f140103030302031510180f14190f0f080d03020a171f0b0a0e03030403120f020a06020301090b010816081317030915160207092f03 64
    0x2142600c0381c1c043c520b056034003e00000401c0c42041c0601141400010285a40400483c180c1071185d20f02503844c00d005444940c10411900020b0110b008103480000c0d1400003500208002c1310961444088440010036181c16031071001c10003123100e0003031154040d607014007000010140050240c0f4401080c3d4001d10200031410070504a052000b4404400d00b0300d401003201031221544001d0080c01040d01d81c0810109840d52124080a800114802126503d1800002c5600220340f0000e00102d0b009440340c8400584000a241c0c41e80a00d110181410301002000d00255000f0800c2e030081030764900c10744011158683d180800c176042a0058144565105154007440d6040b00040b500600c0c1e0400398541400e6490008001d000c00501c0d040501d0241c0304120100040c1c10004612501110103180c1c4905e0244140d83d540c4008007190301056401002041c0e116580c1c2c1c14060381940d80340d010b00b00e0b160500320920094400003001c086800782105010501c1c0e0400c9007264051103494100b1581da = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 822394658 1250 822393408 822393419
    0x8220b10150e090109050612060403020d02070f0f0504111204110405010503060f0c0c01181110051c020f0c010f09020406050a052d0603011719032f0d0207 68
    0x5400070801d0344814081c141002400341e42d80e0880c490b045a00307028020032240d40320408980c5820300d54071403080f5032040400348001c160b00403a00107504070320703036084a4000d0390341d1003175176040b250f54403504035540c0714081d007440306083c00d400c404c0074079100f0340b011480c0600103802c0004038a01100e043d214039203100344035500c0d45018000c160041601f2001401507041078641002c8512001d4001000d0200005410701544400c0d00030500d100342544400c01b0a40042c10101c104010303522985104001140e001080c0c1c1d0b008809a6100f440c408030500891803580c20011300035840001003000002d0f043c010021501c0090148998103200c8840115429050384144015034540d034000d90301c034090708030051115031100700120034154414400003c222010344400b084020048001c0d03604050004004103165000b54a100c80c0b10700c899080380d400b02e00e0b1911002c4064001031000300040d100514022141400710300d1005450030814868918545900e02c441c60409400708502c05600107078410000c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 822395908 1250 822394658 822394679
    0x30f05070b1207031d0d03020c062a03040f140f010501090204060507080d110c07030c05010804020f0108070e041506110307080a0c06110706020301031103070608220b10 74
    0x700320380c0103000e00b0400351202a1811400c0200002e080641c1c542030403c580400090104580518006071000d070203100c0401000395200c1d1459000510841000c0741102150134690954801d110100c21076248140b1404c0700680c4c0050010340341c0d00d800041050204c2d03000c100107245c0c031003140c004014410f4400b8030142900d030142d1240160750308c180700811111b41c0000840b05455400f00d51035507a00382d48000940141004600413220702c5000c01c401c510321000042050a0303d0140042a0340940c0e100c0045407210001c880082d0000c11014030b0082d603500518a0760b810050b40d0900c04648643d080100782141c484004114a090304240208030150700415000e01101d002000b440c42c140c0700340c40714041849010b54150400650883e00014420a41c3c84018603a41d14030740d40d80c0d1041c0c1c07401d00c40302940003070000f0743e0540c1c4204904075041c6000561074003240c0c80f90702d40b0b4000759170b0f40c4141c02000e1988441c040f00d0045a441d02c80015a4000300c8610400042000c0140603052441c90f02 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 822397158 1250 822395908 822395923
    0x10e130f14180601080c0402210901140a0c170403020a02030a1214120408030606071403040302090c0309100e0132070c150c05071e02010e0a050a0506070302011401030f05 75
    0xc201c1d411040040c001c01701c0c0031425010500c0180c50150ba560031242d6890b800300d03900e2098a800312040c0082c800210b0064000e0290745541001c04100740d160480040100c1c3c82900544000c00c007081483e0703400c0580398014951041c000d0058828846207600860305009201030201c0c1c41a1460b0300061500e908040460848840412001e08000304015220342c00302d40500090b040c40008000030391559a440e003103510440c1d000c00707012a4450101300307151f6240c0140c002203108134484000500c6101c540c0080e2032181c0900c8000341098598040e902e0001d1004407000ca500395250317100703107a03102c1150300c81544402509020000340050543d03c0100c000d40580007c0400000b9081400030886104510049001c0e0100019800780403050607942841010401000c003460b0f0500400526002c401220881c3c1c000c0c0c0ba4000321014440400180c1a81400b4096100c416040284203c2c2010303030242101d64424000010b00d001c0200305030200d55000d80c8121b41050300060000c003040310510046 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 822398408 1250 822397158 822397201
    0x14150a0609031e02030a1b0e0612190303290907020c0a091505090106050a0807020304050d0323120a11070c0b1c02040b2106010e130f14 60
    0x41d0446045903207042000c4690049031540d0001d403c1c418080d950301340008842c655103c80b041c0c1956a041c1c5900460700781901c10070a10350031600000307485060000040d000358541c04040d1030350f609030218004010320300c51015010543d55442410150f0303070400000c20f80c0c440310003224450030322220401165a1004000030215082880c101e000303512042c2c030b0ba01c2510700c000000f02c0d1008108400328103c0c0d00513030143d0b6020100c9000095030980040042032900c04541e51000141d841290581e620311440c42141d40000000d100381c2c0c0805e204915900e504440822001010b95080500c000a07420444030709084680460500611582c0e81c03040d02070340380d9030000b13003800d100c0389e40c881e002c02c417a003480f540004110010750b540b03070251480d20f20b0b43c62984085086440c0c035118420803117980c00c8080385070148400d01c680801c2d60a95000518410341050b034400115059110901094245c1c0c2c05a02d4825902d40c0740b40b410b221014080c403010b2042c0010304041624141d6190409141c40c2c0010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 822399658 1250 822398408 822398417
    0x15021506030d05030402090a0906020706061e06090b0f0c0a14190f080a031b020c120f070510090f090c031410090c0c02040513050d14180414150a06 65
    0x440040e6080030590342c5c09a0101c0e0400d4135659010810b5000d4190f0700c00080810703100052210400c64694045410344610340010281c1c1d0358440d00d06103e8036044e018030000316460071401c000a485400c02040300e46101c41c80c05084c034040702e019038942100703042c1c00c41e400d2401ba442603a40c0e40c802c001070600c420300080703421910700f01d94482c80c109500901e40074090810006800080b14007030f41141d000c03030f50b05000b00003a0b1032500710025142c4000c03890581c840e5040d42c0305a210360340000f462880c4412081c0250201616100402400141c103280d042c1c148008107030001b419543e44c0a50000822403400049001316902500508031a40c590265400120642c02d100c5a0103210020070f080d5407585c40002503029105d44162000d40e42c51000a40c0a4101030411a0701000e500c0020002442142117480c0031042d1241950861541c00311040d40720b00c00e011203429000564802e0200d84c50240001500505041b8204091f0034201d90800d881d40001e10145800c0c20071607940c0004006904c0c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 822400908 1250 822399658 822399673
    0xe060324040317180d02030711090601021e01060f1208120402040e03041d0c04080a0f030513060f0f05031003080d270501051308030103060e071502150603 68
    0x40003003040915240150500c0c4000000030304041c0150707401c0d05081140f0201e00b032185040116001c0d441c0d0002e44000701400b03410581036400f0700000980d0340e120760048210007060080d50510100c1400181000e04621074800d00800030500d01a4001c0c60079516070011070300358205002010144915441111201413404000020880c0305066440c542c074040000703405038680d400054003504c0c40322503140c0075001c00140001c02e9441111004032000e1141d640380038540d04d860a401443c0500d1160583c07681080e500500002c1000001110030b40c0f09003019801d00300d5460340f0700504640c5070800000b0682c1c010b2981e080541042010101544515080e803030352400c50b0700c4030004412807000504451002c07940031851441a0040b21160184500e02c2c40f400801104480302c1141d02c800a071069481c00c03020480081e0901001d0840c541c1007248203155902c3d603600d88004040c0d6003881080d90080c5540411a4030f42104902000c81c61607000b08541c0b030422611810380c55001c3c0c80144203a01111 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 822402158 1250 822400908 822400933
    0x50607030503190b0a0801150b03131e051014060904080d1d0114071202090306040312020c06190c03142706040b010e150d1506030c0f0e0603 62
    0x1120390080081e0001e80c03d1001103d0250083c0c88084501c0d948040070b1840400d15031015070080c02d04002055041c6081070391000303402d006200c01d0ba0b480c0220007180f024400843c80104070006101c00c40142c5402b07016007a1101c900302800c1150701a01e15851303104e9a81190355100d40c058010702c00301c4516040d428280c0d02d80105100c1c28442c6803215417900002415805c4041050303072801440c000078002004400030b04e20030030070100c800e5004200c03080c0340c5e000c0c01d20083c401d0f203040000c05401030000b5110f40d1000d854800440c50603d141c903400300140784d0305601c00d000803030252200100e80e01c0010540740d401e06c1600d00c5000340c0c8040500e800140b0465500300c80c041c42e0400b00481c002c490b055040b45000c0c88000700e10110070101d1045205000420044d158118100c2e40111814115501e51040210b00303251841341c0d650b841481001d586000c0b807040d80504004450040c80041c89507a250b40d2107404031516444a6031b00c84501c1c60400450f1300d0001001e07484172088014114011001 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 822403408 1250 822402158 822402167
    0x50703060b0a0905210106030c2912150d030c021302090a030f02030a0c1502120702100e04180803040c17030d090303060b03040602090112061a1e120a050105060703 72
    0x504c00c4038071a41c502103032054264000e100d40c0718131800c2c20009200c0603407207041c1001859818400c0e81c00900104140c2140b00a1624900d00d004050724900381c13070300e965542c28500b08100900000b8007864144090b46160b5945500401074500c640c88401c0303581c0c0d540c010800a40090442c882145004104030100c65580310903201c1035030341c011403841a446407030020030b1030001421001044103ca0303240c0812504146901100d656016034204c501d4941041e882402c54080c4e4a002504520304d0181647c48034045e19071440400c0c0013404c002950000703604502d40c01840320030182c801c3d1400109000c20300c0502403400b4007171b1409000028107203903d80640f5a903803040008000446940e00102c108161103a00210018074a00641d142c490030a400d00030001c0d4041e0824602148645030302844404160143d001111049103d80a480c941070300042040c2c2c1c41140e8520b0303800e036824500d58402e5807038030103441a0108500301c000c081c60055115402c40781c040e0800b0f442075006104400003c0d522 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 822404658 1250 822403408 822403427
    0x30c1205060d061d0d200d050d1a0319030801080a0b160c0209101d0f010b07030507080a030e07170a030c050a2f0405011815031401050703060b0a 64
    0x11200c00510b501340c094111000c070700c240030031606502810843c4040d4692160121303c12103104c0001c6852a80030412496a5110100381c0c000400c8041c0412640025142d02c180c550042c000440084048600b0020741009090441000d8a1108013508818035074080d8072540945403400c000d0049c1107441d1980303911000c0007080996401255003440c0480e80c030a1004850b4154094800e403000d0602d00651003000205009460300b4582103449858030b4101002c0041c0280c0410707a141d1090f900740014201c0c1640f20302c40580902074100318071070010f82070100070808140c0c10342d0f000403603002c0582c01608101d66944a02e119000c030544584c1c03a108041070035141c013a4103042500c3c80b0001440e000d0700700458018054800c0b91505047e822405440b22501800483c1c052210551844031003000110303130082c06100d8004151150a59048481c1d90000764030200103450000b44907680d40e43c0780900040d0b081c0c0200307181d446000f8082500e40501500b4042e00c8110003e0b030070012002c00041140c0306 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 822405908 1250 822404658 822404663
    0x5030a0e03010209180408070b04030c02010e0d031706010c0b010b1b0304060e0d0212010219121a090414060405010e10050c070b0712020708040e060f03030418021306030c1205060d 79
    0x5281d0215040003406000c4808c0c03140d22034407034103882c509418007504400484000b80d000c5641910301041c685440010191003960503140c840c0c1ca61108400c0011068004108506020160440380040b4241a420324000c0a0030b10350b1030341d605040004a8031080c28000148426801803006001c40358000901c4a22218255a058140945400004c00c51300015103d1006940300046d4010720321151981b03890400340680b41da0460203100341318402102c1d80020031007604407007280e01d5003040c40d01c2c5001c1504280980480c0c05001500c1039080d06100080ea01203500c7d82d9101010b981e444400c0c4100b0940c80603c2e201002180381040d0084243e11400301c2c000c01640711900020b10721405408030030200005044115200c2000b451705201580c050302aa811526800002461500d48241c50b801007000181c003a40c14a858904000069003103402418205902070100d040900e40c1e0003014001490140e4010a0084140d60050301c6405155001039401e0b0400003009065124051074100459 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 822407158 1250 822405908 822405949
    0x6081002092d010311040503070905090307060c0503071106060a05040f111c06051203070b25120c080106140c0a060204031110020a020f0405040f050a05030a0e03010209 74
    0x6600100090680c00c10001c0d00210710500031800d0041281d06020b4031410b1801e803410410085640000c0c00d0600940c03080f0b6031f1540c06540300b03201c0078803580c0009401c100590300f181d013000d80320707030710b01c400d40c0d6200320030030300140c1c01000f08240e00c0d6001d0055407180c59040e0141c4440d00b040c50119410303411074041c180c0a541c0341c48071156045040d600482121650103201500c0c1c5994020101c40da0080e03078002d441c0c4509040020810345031217540802c100d0701c078200941ca00012940d0304803103420000c0c41c4800c24804403a40c0c40000c1020100c1e200310740c4041e52950a07514070708045404581080039214204898100180801c94100e58003a490801108546e9108e8501e40540b902c0c012071102d0081c14940080350020030000b2003041810117400032501c0700500759814104a0341c8412046001c2c3d802100300c0c0c18056941000d9110f550010301640c8240c4001d82c0d2515601d02d04051001c04a41c142e1001503688440c2d0307030045010071035100840096281030070780c01c002404442cad0350700240c8011 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 822408408 1250 822407158 822407167
    0x90a0b03040f0c23040509060609090a08070b27070303231b01050105031513060209030d0804030e030a1a07270e070311070b06030f16140406081002 65
    0x10403080d0382200340d1640110f10f80400d5455a0150402039100d8203d030740e0304640010110800d14250140c0b502c00c2d50341000078001642c4102c00c212100501900400e4203000710340519010500d690001c0c600d2502800e8800340506014002d507401c0070340509000404d910144181d0140740c0d000c50401e0407250545031201181900031130120052244400380f81c3d1010b800500802d5060350511407004c008c6a00c1c000300520317a6158103041d02c484424200f002c0311040200040c07040741e1410519100d031030184c5001401d016060000c44c1c40c2c8081c03036a240380400c8407030007000b00305a80166a1281004250003402c03110b10325646192040004034440b01c0078011030800224114803c00c208000d2001c40800c12890000c1e006d00036400743c80f86d00400880310ba00d4400a003549019002701201ea04c9440c00080c9403100b10f4648800440780a001c0c80d505000340000071010b03035000c128801c1503441c0c04221070025460b002c0c4140b5101400910303280a00d0400508100d64080810f0781c1c02c003808042d0016940c7c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 822409658 1250 822408408 822408413
    0x4090503070b1f081b13090c0f0e0c04170106090203011707090b010e0d140a0b180a030903060f0b060c0f0c0415061b05060f06101814010519020a0215090a0b0304 71
    0x1030190308503040e1b00d0140313000f8001061004030421034084401c0c9094107011a611504400c90b00b0600704c1b5945028101000208101c0d10744c814285040380c94800006103940e1181c000c8001d90b4401c1c0c0c811340410081000007440e54109005030001001c141c0e204100c14000440040c01e02d54920f246144a141c0c42c03844503062203410718000c030840c40304409a82c02601c0314507212080b4981500c2041480c401c0041c000c110190006039031110941507220f11603d540742d0350f1180f0141c00040308501406032108a4842651202c101070603040024202030184064100d00702072a01480c003e60318421820043d00302075907443c955010b8241c8040385020144201c0d000d00614041001006c01000781c81030408015101c1c0051200e140200d804842501c00b204690f54201c0b1040d500c0c40c007100801c801d45004100070003202000c1c202542d81170500038100610141e001882d41d80f80c0b0141c1001d80c004210034011481c0039001190b446000048640c00c08648102180c0d0b48001402940d62440000000c0f409 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 822410908 1250 822409658 822409669
    0x418120e0a030606061e091a0c0c0a0306061811070206091f020703121110050a0f020f180d3203071202060a0c170604090503070b1f081b 60
    0x955040f000c14820181d660400421a8450b0030210181c17031039401e4900503491044818104480c0408541c1c154a560310308401e070705a000c0c0b11049d050f0b03c0746121440290310f918050701f000318043c902c00648507140109803a4126180180101c02c00c4c60240c1d81b070f2400816034240c810703690f010348180780c4400b8031030003154500c2c0c85840f2180c0c144500e0028400c07a242c0c0000c186068a102c2c03040c0408400c04d06100f61001c14612803807012a41003160b00e10507111065005c07682c0b0600701c8401007030240b0034a060104907403000314666036604001442910144000800c10310703a840984030060b10044031f840300c000c980c0141c8551f01d44980340c03d02a990010a6200a6051100c014282c4e5a280c0c0035141050322001115120f4000d4060100050101c20081c401c0244101d20717902c13003074402c0302010703109a4201c800030095a44656260081000305008001501d82c45200d01781c0113039281081032a001440b42c258210380c601d81140b5109015010010500404443c44110360400c40880c03e00000d1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 822412158 1250 822410908 822410929
    0x510050732073e010503070f1812110105130b0d020d02030a090311060c2b021207090b040317030a0e0d0203040314070620030408011a0418120e 63
    0x3040c540e40d0010b81c0407500d1038078203030108044090b4010144486011030f41c2501031290395140d8003140040c0001000f070340c02112503240100312441c14078441d80000c82e504d982001141c015204010b2144424020090600301c01e800d8450b090820074207110501d00b150701d8410343c034051450aa0404a001c00507099903805482070102c40007000d54072413620b904039100405d81c50034150300003171024006940c90720004c54000c2c0125089411030b403400c405194640d201540c210b003003021b120540303400050ba03104c0c14400b03070410350114035140c610707420302007c0103200c40460382080040c413804000800006c0c0d402189005501405071200e0f884c0c0e5240101a8010301e00c8074140f841c680603d004461040d9030120050080d684110600041d200f084004a43c4e01c140901521003c501401c00c442d00581c81008240740b00d12180003181e24141e1201519400e403640b4110034000c2c03500207010400940783c00d026002000212103207050080c0c203a525030f5000700100700c1c0140140488145502c01c0350300d4120200 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 822413408 1250 822412158 822412163
    0xf021306050301180201030f09020619141305030f0c030d0f2c01030c03020906090103020c1e1f02120117030c0118030e0303043f051005073207 63
    0xb00008001c13025160345030681d14000700c0c00039140060a40120040340301c0d440311140c01070465401d144044441503110001c5480110a000c80014503c000d286d550300140b0480081902c494000c628203070501d4174084a08a0407611a0000e403c483e0080e100080c10b02c0c4420001d1400101c8000340810a403010380071a003280043c0c07558084089800c0c2500406d480140c202a81c04104035061408206c040b4000c10b46d07903640c020300820481026600c030b038002d23007100d0414500352010300c8504aa5035100f64441000403429030072001e14200c203246040c911400600700dc820640ca0225102d150200c18101400703440d184104510268201410400564240f070020200805c2203026941c3e4142030510320740009c5000800f03030a03940c103584c20044182c6040b5800406903c4c129902241c02280195500c00c1003d507034426451001c0d0680000f00390801d0442c0200048c1009003800002a001c5c1c60b4002c0084090100c3c02c0b0f0704001051504015041c0c10f03096100211100b00d03400f204802a105c4c08001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 822414658 1250 822413408 822413411
    0xe070b030c0720030d08040c0915031220070905070c02030d03091e050f01050702070f15030f11090f040507090e060402070503041e050108060a210510020903070806040f021306050301 80
    0x1035004a0300640180e018034000c00c01720001d19689c40000007078942000c5a01c8114131108030400000c2c02c40c080170001985141042d8180081c05040b00812040c2d80c6001002588a054100325000940c0716180d0802214a82002c0c42c1d24550082035540640c1c10445080540e112000340c14403214031407661500700d00700d0f0105443c980c40e09240d950382c403180e041d1051359483d10022840f000c2c00002d0850481d202c03c50a40381c81c83c50701d1503036110480c44885582c1455282c100310800c1c0c6003e4425104500140007146445a0903101809541c0d9050044140141d240005001c1c0c856005034440044410303018240c0d080d6030350034010901078014402d00420920003c03c010500d52f0030400038001401c0186024800183e848004580c06041980c1c19a0001c03d18070b0140880321101074100203500b008982c1c0d1900c400c0075551145016140207651318055400705a0321700390b2a00340314007001440071200802c081d08150b03d030880d54000d002c400a10030100380000030614002d0b4ec01c09401410010300 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 822415908 1250 822414658 822414673
    0x90839012a03060323010501051903080c0a081b06070e37170f01020703050f090d0f030827031803070f06021e030313080f070807060e070b030c072003 66
    0x20355822003041e12620100c9501f81b50020916003003260b401036000305c1000703076107010503c0d544961149911400c0c2d9200c49000e17445602003c00d4245c0000d200a50030711a49500802c40c840c0c10509058014000001308501d21700c80003140e955968100407100b01000c40003110b82c40c45220024101c0703007503040c2c0314640b00f043e80014034100245030b044107138002501501c20b1261a403072141c0c00c034400c1e1100180425014003010b041450703001c000c2c02c1c1600780581f80201c03189a41e121854030410100b0100c1c00a0080f40400101260140903411950b081303884015071b07540b20000454403800b4003e400800241005800c680c1c40d41e0410000c80203064040c00a1082c80e1103450003900c807412100000b900c59841d00211555142c00411a486104a161100000d10141d500d81800e0760041140089900c3c09215040c04500050000d09010b1700c1f07103c1c0010301c610000612030501015620003c5181418402c0000f0540711000329080c155021640d0240c20b000c60032000c4003000300c0300d02c1c0d541512500341c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 822417158 1250 822415908 822415943
    0x308030106030e190f150914010b01090e190603020924101709030d020c0304050a050a0503060a020706090b01032003010b13090839012a030603 63
    0x10056041e203000742d030207114450352000c1d030540d5441c0c40400350340406208880040495030300e440700540b2501c0740c0004290030282c04160002d440154000340e0750b04035200d00d8a6407802092040084440c0e013820320034100c510380340042d550010000d21525000b25038a00421810005070f20500146a0040c103622b02801c1400c5403042000c2c0641205120300c5510144200b503182480158031120b100c0d03a500c0016460303d884518884201601171025803006004011041d01d40c4e00181119441000003551960301d00801c01100d58800d901c2240917600c100030074460f0703490108000d41e0004207205c02503070350b0525251020043c560b401000e011700070b1400010080200c0a01840341c01402081e620030003040203020142250f0107460800d500600d14004c0583d404100c3c2c2081d0081405121224241103610340c80702d03a48400030385c6e51003a0040046099000c214008809042c48110f040200000c05800880c21130307030b0001c00f104000d040f51142420900038803a40001010315484818240244440d1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 822418408 1250 822417158 822417173
    0x705060403030b0d02060406050d0e0102160308060603040515191b08150102060612071a070203070603021303060e3c1207260c03121501020d05090a0e0103 68
    0x40e50210000303814254030003190310b003803e044400d181e001401c0a02d031525000f010b8856a200507640e0500d584c881c041207254070380c203101503c1c4540c40d51300c004525800c0e5103802400b942d0010812481041c0a10901010400c005018101512403004a800e00e44498009803001680d05103403466050424540c1d02c03500c00310600c10034000c0c4198941081545a40d07003042120316000a2850040c0e0020000910a10b00343c080e6080420811041c0c403401c07070325103000402c440319040490f50450700018a070700031130804001110062070b1074a02142440304c5610300701c113040d18604c4080c010700d403940041032301040203011204a045810852350010500001280c80d48842424040e02206660740a1045540302051420880c030710f400d01c0501d8241030342d49540752005405401c000f200c0c0c40304030000039170900c0d000421998444000840c0c540030f081000380c0f0510390003040c8421003060f60300e10b0700450f60005411441c4162074180f17a40c860403c48089a80b200043e0b0003d10844081e000002c01d00c40342 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 822419658 1250 822418408 822418411
    0x60c060106030c111b0112061e030b0903040305330718050301020c03072603191a0306131103030d09050c0306040c14131d0705191811070506 62
    0x22501c40790f0840860300a07003074440c4100d84080c0e00c40c4e500007050340ca2a40c49001c01287d2500c5070400028807546403040b000755050b400b07400042c003d00201d410310600620408403a8851845c00046250508650b10580c64490b010100c49944807000280f20058206003003584001e254001d508080d0310304807100a00f140062601451010354a45c4041124141030003169801d0b44000021032625119030341720706502d11038100075036400002415514841c0210b134002c50140151030b40e0228900c02145208007200c0c0d00c81c036040840301e41010480e00350385011070b180398000800214480b4400040c1801c40045884120540e0315000001c0d100d00800c00c160f0200f2030181c00f42c0308450511703121609042c0e80342e0060ba07018140b03034500e603002c00c202c0452500d096580c41016000d0740d0007514250340042a41c8121074004944220a82c488045030402c001c000005c05040343e04d03007400b102c3c8a4035100c0e0003400d80281440c03020b541c4210038403081740d40c02c1031034a440c244c03822550b680d040e070510540740c200 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 822420908 1250 822419658 822419681
    0x60a0e04170c4b1534110703020a14030a0606060c0b0c090a0323010501090f0b18160e09010803040e0106020105190c030b1201061a0f18060c06010603 66
    0x704508883c01c0f02408a040358180c0950001883ea0444ca00041032018000920b0800500b80b10482d40e8200c58003a051011345601e00c02502034104c0c512240a00074061031041600568080b007810009691103050303040032184a046003205801c1c2800c0860300b0080c8000020308810304140d0700083c2d880d40102c054400b18000c511420f555107550454400c5842900001540706802840503c0482c03e440a6000d00e40b091201d005080e210b0b07044020b0960390240d00801003566281800380c0c5446050140303a181c09402c45002c2d40f801c6140603041c00f0048060324400e1912103036100880301d14002c02d100c80c1c890000404e480740540c1d580e41840d65940c418091019a0042c080001808a0050081c1400366840348a08800741810b082180c00801c0c200b05403408041c0c9814404034141c4583d1444401c6210042c000318042d8145540d640f08041d480c108800861001c10200006800d4030003a40d5560786030420a246c5441600d0002c0d0041c003030180491100d0003500d0000905640507400040f5100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 822422158 1250 822420908 822421003
    0x515010212120f191104090b0603100e09010b0409060509070e07020307030f120e100509031c09052a0f010509032508070608060a0e04170c 61
    0x41e291814404540a20b8954490205840011500e050f03c19141994001108014000080c078111072500944407840050103005100040c2030154034028000c0b100e4800c81515000d26505100c800e600d41565a4451302040c0d81e50040403403481502900700d00d0780118010001e1000541740d05249008200541e080300d01481031103800110711000d10105881003089802440c00d00006031420385085c274007486454100b00713071007029944d11541441108181c601500042095200e00400101242c4c00a400041140c0c0700b4031038001c19040103e1503040c000846003020840c0e0031549005071401d1041c0d5454075500c0307402000c902648a02201400d00060111410208090b2800c01524544510015160542c102e102100e50396040c5503064541d10201070102015617903a0040641000040e403c91000503158030300381f1145140c0b440513480946203260170100c10b07044c1680c4100b11100002e0207c004850081181c9601510a005000c01c90b440e16410905001000202040c0840c2405409250342c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 822423408 1250 822422158 822422173
    0x30d180503191e17092419060f12021306062606031015030807030c06050609010b1801021609061e06051605070518071e051b0c0301110c2b030b040e0105150102 70
    0x403810740101421126904140c09e205802c0041504005400b281d00782e8202542c1c04002030f4503502481400c0c01004141d0702c0004510599120740345d064020750305410480040001c0c4107595501050702101c2494540300020b13010340035100c0483c000c6050f80050b0030720401040c03050900d030f00144083c403140e1142904020700c0c1e0f00c0000300a04140c0a00a20203203410510a001d207048034284034010000e814012514481140000780e808420070b80c02c005645512082c0c1080109a0b50400b45034460340120b286001600b00300f0300814500860100b02e00e40c2807510404020f0001c18001000505400f0b0400c100c0200e46034862400318000395890000a42c07202c028041d40e0010008105007a01a80e5a4518188110903220302d0b07145103210808040c01000c031a4030669801348200c4410350550b050041d00d0f8100080454105005103240f034481201103045045a0310030040b400f00d08003010b080014912084401103002085000a841015864107081c02055401c40b025000000400d034200e0f03401 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 822424658 1250 822423408 822423451
    0x90d0201050f01060c0f0c2d05090a1d010903030b01110102030f190f020c011406010207030312020f0403021c05011d030d180503191e170924 62
    0x700c50084424a6080340c4820050001c1e0748941e00342a00c031800703550050b010300807585a0102050450303000940104001d4a031000e2810002c50320810020b032000340b03403d0a80360030003052640c5002071402d80d01e1952040c050548001081c00d00180e0100320008124800c500c1c540500180700600d0b80501099480a241c40c050340c050084034880d606007c0401510b0300ca1401000d01101244001c10f2200d8403000c075494141035a101400582c0e01030030011034050480040c44103c02e1019100c5411074210050070b0003c00d0b0081945c0c041c130451000300507a103487c8101c0f1000c9901403504020340c0030b01c491112241c80041880c80c4140c003030143c0004c000c403000740d415241020408100e008075030307001070040c0a510902680028842e2044044801800401d50748860941d40a100d0354945030303080c026041d00745c0350f0001c00980c0e1984c01030071450b0320310346804c00a084100714100150030304980d9000203505070801d1010001c0c0c80e80d90f682c0c180c181d41801964440d0894101c0700a00081d00c1e0950400c0b0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 822425908 1250 822424658 822424661
    0x4090c08070b03010806180d0c0510020a09050f010503070c032703080304030810050d110604050a18050105040522030c0215120c0406080c130b030a0207021003090b06060a02160608090d0201 83
    0x2501f54480000348200441098140c03018500050b040d141800ba114a003031340081c0f5400103140090030780d543c803500b281c00e102c200000c042003240d12504001c801d01c10031690035044090020042e415043c0380c01244054007054603141c2942210111045541800004101a042c088c50041e482521941d080d0340d212090341c11940e045100f0640d2003000070040b40c000c07070026403481c0d8448202800e10361400c0c1c0c4a60100322819015400a201c0d030921714040198034903180b042ea405440104c40600c06424030145540322005150444168048880c10840802d4082c50185011a6021302110401c001148031040c80703401c401400100303070343ea500014030001801d0007110165002900d030320b80307592540c8044406941110840e0380380caa0307000401203034984d82e80003e5813240c007144101696410540c030500c0680d00f440c0d86010207240c14422694001114880020352003801aa01c5689132005260100e10f00365412403000000159680089162507011321000e10480240341160b9607032546070f504a0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 822427158 1250 822425908 822425941
    0xc050c01020105250207050607051507050304030905040209061209030c070608240102100e3f0a020c06070c03030906080c03190207121205011a04030204090c08070b03010806 76
    0xb0002d0f00d240c4d00003007159074051403803000d455142c41150388440e1180302003451035211960030307540307540041240c4110a0a0751042540030f4a03078582181181850754014110040b207000c0e45110390b801142c0344043d501d40100743e854106100000c1200341c00c02d031a003c0d850741e000c06c0c0750100500404101151860044503d5801980e03031240000f100b188000300c0c0d01d41c18028101860460103100d800b501074001c00e02540329031b244082c010309002e03500f82c88510510640041605d04082e00001d401d0410020f000e0f00001852401c001c0e10703034401000c82c0c1242010340c020340c2940d20640c0441d030b4006002c25410488140c9220b9101e0b141081c2e1141e81c282e400c00021180c0f601508000c00008022495462a540c100e0031840d001604003607480c2d88110b85500d020340100000b445201424002c8100b501400b80180704181d00307201628000c0e00c1000c2c040c0b085010207030146844094030f401b000516030034940203210000a03100340603100c90307200403164820b10030303401c0030303c52040400d507140384401048 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 822428408 1250 822427158 822427171
    0x5150a0623130f1e050d030c02240711040506040513031b02090103081903110406081302060408030c010507080f0f0a0f0507030905070801050f06010804080702030a030c050c01020105 80
    0x20328407000c4020520601da00098100c00c003803160902c002001e40c0542a60350140800003103103103000300b62600342d801d603610980c0114840c0c0c40341c101c1c480200b90000c00101e031035501500d0030091034007030701820f04a090000100c0c24141400140c2d500070300116184212001c00d00325400c0c00103880d03482c01c0000369841600c400440000707845030311001900881c980c1d914101c55001b0b40008007075035000104646000d80c010354003510001906060300e400c4180400484841703003401c1007940f006803180007042c00303240600c20174000c02d4004580c0d01d803841008810041d0b030051013036554903110040d00391660040801144130390708090104036043e008061540c0306502040350000c0303c3c0e5650340f0104550102405041a203075465441d0b441c900380601a00c0d20541da151000304170044503103029441c15509500c855406e03458071086c007a00440d410341c1a0b412903400d18000c20316032902e040c580769502c18030000940c180b007020101e8003010b42000e0b555144a00407010b071200c09450134016400d031002158035 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 822429658 1250 822428408 822428447
    0x5060304021f0219060c021608030415032a0206180a030e01120e010c02240604090320071814062119021f140702040f05150a06 56
    0x10450080070b81d0801860500303140b0440f0f0001d07004140d10020300354540c030706880c000d854a4000c0c20302c0342c040010148460240c1c0c00306405078901441c40b80c0300c0c0180d000e24142c129105160384002031003900a8040e40f424090240350700c2c030030a510459140ea000c1c1480380540120b40025a080c3c0049501c86121300340030000c5c2080e010181e0b011102c00c00c4001c2914188200200c54400084040c4290a48042031100026424110341c0e8082d10707050b09415010480d5262400044803900440002e54000c202510007180f090703982e00e0107503a00511750a82c80c00500251051100b202c9001454801304c0c1c428a4802180c0042841500192106001039258460240002c2a0710342040d010045424503c035001a4880c4490701e8954104100d03207a442001c0384061180206502d00f0a14000a05801202c0000441d100c0480501408400e82c4180e01036400461020250f41f115017100c8141c4094040420440c40c25010009584200104c5030340506140240414443e00564024000c0c1958105 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 822430908 1250 822429658 822429679
    0xb040501050d141003060b030309011d01020a0b0a0219031a0d03120f050417040e010e04020109030803071805030c0a0905090304030203010606050d0506010806090f07090513060f0506030402 83
    0x55a00b640800c0880b510943da500c800091103085034403e0340550303d10307098803c00600c0d42c1045029103480700640d62081c0c200f009050456030300b10442180b448482e001011480c88000010303030405801500284c07220f10810200401845594001c020080c0101544800e84003444803c40c02c41e561703441b007040501401e00701100245490303007c0c9500c60b4449d2410b4420514803401e44000c0d100c10300840800c42c0d07100d805100800c840003050030100e4a9240000303040c10f180140e107092440d41807045050480b2024045000e41e44101e05401c043c40d0010715103952400d0506008007041000e005014204200c200045140c2c41d0204d000325010100134140000b030360130008490000d200c06400a401da11007000000b006840a002c2d56000b40f1481e1141521b0300c44a0b100c01c0c054600c0101041d0410042000300041541c80c800c0d401d400620514103680c0c84c0da607800781a100f58500e9005280d00640c3c0c04400c3e4044103043c0c01040c25200440800c17110143d581061202c0f03401309480013503008880c1103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 822432158 1250 822430908 822430919
    0x8061006050a0833010e0402090906010503070302071b0e0a0e120d060305010c0203091c03020303070e01030207060e03040f090e0d0c030903080301030318050603090a110f06030f0a14010b04 83
    0x1d180d034001242e004802640700ca081007001113041440c035407a006000780c002d441a07543c0c21503601e110741e440070388066142440540018080c002c1c020841414840040045031031076204ea03040d682c11a030700024520600f043e850b5410501111403190903110061200010810b10302c034090b106010526500400034140001190041500f24004d00d0650b59512040000840c50034021606914880d03000f03140d031460b02800f0302015540045028002d50f41c200c0c00600001c3d80001101d1303010005181c844030031080c180040313010344525040907081d40d01b401c0c21185550b0740800104103d95000071100c54066032034986100752001d841c41560782e9086040b6201c030071070003201c0c4039040912a150a41c242901c0b80d0303a0a1058100ba0025400240c070a21461000b50707802102c1d030702500045801500710300d807801e5095552480302000801c0070102060403421510750300c40030300206800900d45c5403a80b6050044505410085803210243d030306021031549002e2070940b603031741a82c840104030b9192030f0518 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 822433408 1250 822432158 822432167
    0x1107060207110a0b0a1e1b0b01080c1c03030b010c02060319180c050603062101050604060506091e04020c0f0c041410060f020709020a0c03111f0b120d02030408061006050a 75
    0x141b0610074041e000000744d500c040d56480480301c7c0e62107822141d0b91941843e0445251802e410030490003400480c00c4030000030100760b4102141680340c5800308000e542480120340802103a24003d42044e000f000703005000d00d840303001c020310b000c128604008100440d8500ca41d001034101c4084c080ca801d0140501007403c00b07100956116001400f0800b03a4550350181c41c0030840b104840907450b943d00d5052110a1802d8001c69005040444e915400c1840800004a10152004540850110121841020f925241c042c2c0704186e1402095a4007420500300c01a1119454090103226515020704000c00302c0c1919151401080820789061809040290980340c10411208034800e51140d510002085481c90005040325101079541d8055120586005030480342280701c0c9181c5170300310040e22082d402020480300c040120301e00c1d0101d92a01e1220216082d03102d02c1401d517520b80036420281c0d0481d81c0000083c000c40b9002c8040380c1007956000e180400303044407030240d0000242e0400a18103000d103e07 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 822434658 1250 822433408 822433457
    0x6090a1404271401022b06030602160204060b12180f07031109070e091501032309060709060e13230709050102010e101107060207110a0b0a 61
    0x1500000303a4424038600032030302510002c0742040d90780e0300c01e840c0410824a9049550b05072071901c02503081c164009403401045c0d52606070f00b2104410191451043d00040d0021402182c20407403c6580361032024001c1c0c0460403a19060780180c0c01d0040000380b100b03014040700c0c450010710b27000b004180c6a490041e00b41d44207032622140c19100340b4502c40164001030000300c00451240e07545100b000514001d000d04203000a03c450144240c2c00c4c5c00c0304194a03100003a0368008180c0c40c074510741142c01c200580c003c0803900c3d8803141c61a0070016849050a424002c02d00422a0000f00c40203035413800c0c4125903c940600802002854589240034142400c1c9903000c141c0d20803c10100c1c19885d411400f000e0740800858910800c40c0c0700d42448142a00041401c016050a00c020b00c9510110300082d50b50385803000c000c6404036521802032050041031010360b00703400d40c031400075941d03640517042260b1603620940da02881445040d034006014200601114142a0b00e0784500c0801b00e0030250003140f1690 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 822435908 1250 822434658 822434699
    0x1703040b04030611071208010608060301092a0e090102032502030a0302030613050a1b0c03020307081e0a0c020901050d02011715100228081c0b120105070e06090a 71
    0x1820301c02007001500d002e006d140469001c0c0e840702e10b250303d0800b00804c0340a0107030115000c0c3e45014031b850041409200d03a0944000181c00b210301000d0b15040450801a556000d100b500c0042410700c00d003807e06400a5016005c1103084501a4595203c1c2c0f5050b64006411207015030703c200460061035010b5005140c2c89540103080215004400343d082d0155034003200c088102603601c000418804c18010b0000c0140140342c41c0011441c2190754020391341c0d2150050160800340d000c80c003a030801a10145101060710a030302400c0d201c48000a002d0540049890103d05c104062030000c00e16050182140310540e40595451050394201129046c15440251101045101d0030444d036049403941c0c000702c2c400d801e1990080218169200b5600c81030201c3e96001320030359034050340c5000810700d26002e07109101d00b4a1000d440c01d80010001100070316182c0f00c400e4100c10f804296658290040d0b00c8217200d07501944a01c0700d035400003020404284205000254010b00103a0700740000c0404404411804a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 822437158 1250 822435908 822435941
    0x41404090206031f090606050409050a0e0717011b0f2118151a060a020f2a010e011d0d02040204090c09120b150310090506011703040b040306 62
    0x10000d070081003042c0d10441d00b20403950100001e00c5200940148088010009102d0030001541090002800d42c4903501c207028455460b4004a6208402684031202d2400e4010845910340e640d420030310140341d407a001c1c98080f075203003030003141d0b41307080406801050510550310301001c00550001990070340d25106683d20700c0340500c0800f13018140d40748642c14605502d00032800b4950307a9031600510134507080300c002d2600703800c2c00690010681c0080820a020380300b101d14644034629402e00b280380c5958070340802018400c1001c459103400c01860458000018100c10031510300c8c98800648203088a2030710703240010312650310360081e90003103001307940c503d9401008003600400a400103800e80c1c1054001d403128a40e54480b082429030007100d618010420003000e40354000b85070b01d81103c02c04004142c401c2c001c881041c10720f2142d605102c0d02c6c0070750442c404100440803980c1015680c0c2d8000f402500780c03800f04180030042c044400000d0b60100c400c000b024030715060541d52401c01814404050800c0b05 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 822438408 1250 822437158 822437171
    0x807050a0506090609010605121002031308030f061011060c1e04030c06020606180a051e0a0903030b2d060405130e011103010302060318030c150105090106080c041404 73
    0x141003441034500841c43d0fa00107242e5803d1000c0160b0854680764421071003140212604040103c0104800107141e00c250720050b182e07a03802d584007404120804000300000d20000400144952031501540991005d0702d13500a00e010f41c44050ba038100c801e050004480e40804001400f070358a01000300f0032a44075130503081c2c04031003071803040005800a82048414001c0000306108595040005641c071a00850308590410750048209001c00000b4080c0c40a07207445000182d40502ca0010131703019250050000a40c51400c80507c030000d00a1510840c00642020740200d0140760003a90794454007400d40801c0440c000903a05035100f0b400340c848003074100e003040c4400916695100714004a0b21040f0301d02242c00842e4680c041e0840d0038010160080000900050015840b504c0960344c0c0400180307402e44400c541e0301c4c0b10501d5405028051980c900c9040d4440904080c4bc0000c2d9040b036105840c060401c1c0d80301c0c4400d40d80b182d0101c1315100941c9040c0020041c621000b0085510010f02410001d00d8 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 822439658 1250 822438408 822438413
    0x10317040b030f0c04050a0b0405090a0c0c122604110405010b0f070f080714010e07060c0209060310060f0e0f070c02010807090306020a050408060709050102100c030608010603061d0f0a0807050a 85
    0x111f240075400869010340c0401d04100d44d04200c075015501c0315010b4005c1101d030605080c090646001d2240240c40908006580914140280d00b101c10340c41000341c0c1003885502c10200000d045030304640896202d42040d031800410b0a1900901e030588080150340703070a00924504040040c1c01041c000d03903020a88105200119074041c2c010580c0c5800752115000c1c40c1203408840d400e480e041c1c0c540b81c0303142d440751b03d08201c2558403c4032450840d5046403a48002d480301c20009150142a403000d002aa24000300002c401204a0540003194441000f425040d03540c0b0101c814810422600740c008590000e06080041d8800d110240d4408864107003140200d807a03445103012a0804007048010400004061160b107030204071460740080103240500841c2d05210000f92108100584000056201c3c0300d2016558020740108001d800400001c10880399607042440c080c0900000c08030700005450320602e0301000100343c0700c86a541200c0104280800c0c1d5072035400d81c9d406070300103075858000c01010100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 822440908 1250 822439658 822439669
    0x601050a05010c0c05060c0a20090c07060b041a0f0319060c09080a0507050a1202010c1e020613050a120f021e030307230d0207051302070206070803010317040b030f0c0405 75
    0x3560b40b0101c00408020b88503140030303074405440309401da50109c4050b01c0704d1582d5440f600203e60259120461948500c0b2516040c00a0104400010740c41400c201ea001c030141c0c0da40b0080c01c0107810495660781d050041d081850780b54821810710714140d000002c03841000c00c100e86c000100a00075481d00308185580d03400010f0074001c052500700c4664020301d030204054500220b00380081d1000f40d01e15410400303140d002034010342c40540010030284140341000c3c20035400b030040f84074250300640040d82d50340bc498506098080f0340e0044a1080f0306042001c160a601160a280590352004000b4000700d10b036001c000106e604151010300c0150400c04484050714180068006640f04800e401d103442c40c204204060041070b6a01203243d0340c00707820300c9040554006005001c030380c02070b81d84030035520405800001074418603001940024000540604202a0070000c5049a000e0000c0c0800203144640c000c445100d9803080d011851400d2022030240708a0781d01d03140e04202044c400b035180130b0380c4001150 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 822442158 1250 822440908 822440917
    0x160507080a09051509010503060904051c08091006060912020607060f050a0b040b0102030409091403030108061503030a0c1506080111090f042706060b040f090c020601050a05010c0c0506 81
    0x4000b41000c08204540e04003e0310030446400d000420b14100700c03507400002e0180c0030081000e07220342c01020110b030500c8803c1c8040350003505200b000203482c035003400000d000c15905444001051250304c1049a40000c07a110354401e17961541d5840408614011400542101060f41643d10006c00c020a5000611510543e5848400e4040c049064904985018111f550340c2d44803900031400c2c120f00d4551a0303404003c82d01510440032001452004508000360141d00080e2000750500c00040041070742d010009006d84035110704900710310201d072a081856120f004c0c0e17404450100d1441324601c40003c141c0e00da00540310313851b142c0000b01c440e542c0c980d8509581c1c2c3d1f0459181c1e05000001e001c401410500c41500340140c0548003840f241c10100003e42d80e40d5166101903080d0340483c060503080001c250003490041015241c0c080d140e41c2c0705d040c10304026040b0b00c01c0302555442d20b100140c60341e0010441c1c0d41202c85c010107002145140c0703001524001112081181e4410078100d01003510b03900c0d0000361 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 822443408 1250 822442158 822442177
    0x80d020d0614010806030105041e050102070210030504140718180f11040b0f0f060702061b0d1b120f0908031207111504030509040609140415020a0816050708 69
    0x1041c0048480c0024013124009000c840c044e905140801002c02c030200303e030101103c0c01e0b40d86000c100c0018109640203004140000354800d59201841030200e0707068021501480c00b5108130050100200110799944240c3e104000c4001d04210089071441115405040d030740314550300d40715a03404195911221030325042400c5441c55a5040303844128100f81c8164106d0200035500003d210402074006409540e04000251280340700040d003a01315120740055541e01c07801c000e40c4560005201240903198556078007241c0009000107201000c880a16014068a45d00071131081000b0350032800840e0112840b00141090207640400040d0001c01000140341c1410321041c50b010358240850002c14000340242140d985034081d105485508132048010b903040342d80f41c10290f40d1049407101250207031400b6401208202d00d0010084c6c14a1800c40d0740d50300c00e03403080c400d41d049951000c031031104038004e1489880000e09264005113040f803003031842c1002860705080080c2042110394070240c40f82d0210b0100c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 822444658 1250 822443408 822443429
    0x151b021305071818050601020a08030c0418090831060908010605030705061815071a0609091203130506010f03050c01080408120a06090f020c0c09010e04080d020d06 72
    0xc000c100c6078010300c0c980e118468084408143c501c2c080c85000005806143d4100ba15521400f00d500c2c0c0e030003040b107983c803c0e610891840e12441c0840d02c41207541c01621980d140540070070214401c011b024450260714036403007050b090401c55100c60b2403d20b0120b941107001c00410842d01101d24100d00c0407190000c00c010f0b07803920720780713420701181500f598515481103019070700144090119949000545800700d07038203145460103901e44400107601e078a28000740d01382c003000018400188452003242c01215084904c03103c070030381c0720a010f20017200342c11220700d400c58100e5503040d00e4200000c0001c540208800e0010781c100e582588030242003000c00e030b22070036a14026403401c1042000501c0804510072090078015014030703142d00c50300c4417403090400d1001000d0711780e00091400201c66100401603e12580100301c1c03402c03c200304000a503c0400c5102280c03242003582c8860346441c0301a91305a600b103219041543d1256541d4010503000000b81140702c9400740518002441c440c0f1501e401805654103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 822445908 1250 822444658 822444661
    0x720060c10060e07020d0810120c0501080f061e0121050711011103062106010b09120a11010f170903040608160e060c071a07060c0207151b021305 64
    0x301e24080b109154010304603088008104600b164000c80d9501909581c2c1c100001c89a0321107003071100d11116a040b508054422a00100c288490740e031010003a16000e0302d80c42d50716101c03003407900a40d003411103420344c0c8840007003c4c2d102c05010560100d81803500605113003822000040341c0c000c480d00c9551100003c80e907210200041d1a0b4807255a001e0300344140001c0080400c4c5640d964400d01c4003c02d0640540000701050761480e500300a02552215408140c5aa658580400148550101e1030145c810406095404031454000c10b8044c195940854940d9010328410015691040380c0e80c7c0020512403800e00070209190f9001540d44036403048000745075914104280900b00c074001400d40844401005101100c03160410440c0240d0581150705070340b940c01890215152501c1e80e0403544182201c1a1218211032200c0090b007400b5100320014800c0749015407040307940384101d01c50150390030490818140f440e400740318038030a03040d0b1360083e52214403016004181c5501010100c039030034a60383c0c070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 822447158 1250 822445908 822445933
    0x3050303100e040c1a0c0102030403080f061009090f02040305031605060c0307020a110a0f0803030118020c0a03030f11070b15101709010617030406091401050720060c 73
    0x1101003000d4055a41240940c3c00c1c0350301da88110181d9800b80c002c0b9000d07849000240e210020341960b18140c80d00009540e6032410340340040030100c040e0b44444048424030081070403441c0107040c0900c6002950f66400a2503d01048140500401d0f407502418550811000c404030300140700405940705050b1080000c01901d10b4001c0c540700000303010541403401402480030403a80803880788107060300508035040c007000000c005081d005031035201ca203503240b20729400148a000800518102c81c0c003c24560324009210041c0000e910451904000c13a4010506440006e402540400e03105034035024005108401084903000b04d9000b0241034131405448030411055403980580c00c3c88010064480048154100318042c002a50201c040740070703885018006041030300c0940c0904000c4c40d1800d910005c1c0407400c41d0301520382d40103011b0b10b00058242403005c644602d030303c02540e80115040c1d40305072403c041d036101d1141400c6034070030003140f0002401c00d002059032014003034040a102d4001915040110a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 822448408 1250 822447158 822447181
    0x1503120306181009023105090c07050c060c0f160f050d0302030d050c2508030105040f140103081e0f03070c0203010b090109050610110a060e0a0b101523090303040f03050303 76
    0x1459150419030200600c4a603d034229000d411010703d0582d2a150591070bd099800c1c0740c080c203111034215134081070f054407413180020050042da0584050302e44142c1524130291001c1090700a0001c00c80d8000c03403c0145003411b02c2c039140241d020340306507420410408840003c4d0b650a4414800142c1e0114100e0f0742c02100c0c00c0507400706840c0a029900da0b514030341d19003c41e40014807646115035a18540e80002b0700140c1c021904e0300d60401500701e0039686034070301080d0b81c5d08110307020b8000d448607000c0c003540442d80c0c130100e40c1c40010b82c145080c1190b86418003258100f0b040c0c88200c0e015505c48908800075200e0b041503a020b08420200401c4518213981888020001c1494550400c0148260500c08820200302c8401350340e0002c0380072580504642c0c0381841c021200100070442c95640c2d0400c8510070702c05844800740c5450500000414896480440300c1174410098180b001495400c4950f40305e14040040110800180070341e401d00d1703a0303003032800a00c84056000303489a800c00820000081d080 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 822449658 1250 822448408 822448477
    0x1201150e0109090b04030315030605040605010905130c0b0918071e030903050304020618030319090603050f060d150906090c050312041503090b150312030618100902 72
    0xc0b020801424403940c5816110306006003010b024144d440441e240c1002c8060005ca015603000981407115041c03600d002e00092000f440782d10f20b55880d09000c1169030b422901c034190350b5908070741d08040fa68140300900e027041e480041c940740e201d0044140d2990450449100341e205643c161100d10324291294080000c40c0a00403080e801c0500d070040100010b504030703084d00e410680669406032650300c96025822040000d00702d16a0510010403088c080900841c0316032041d80e01e40c0c2d1608905540e0b010103609a540039200110646060800100281000c01804e07902d180100341d03c60038210347d014008200c07868000d0a0f103003252036108030014400500382e0100181801c0e03004146001141e14035004038061801822010903420250351450751003070700074881440c0c000441b0015800c0100031340303014801e01400e85001c0d0003044480c400590155094078801e80010b0700003d03402c50300f0454503002050041480c01d11054004020400c1262440500f10300c000c01c0310220000c8605400030b1144029 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 822450908 1250 822449658 822449669
    0x9090506070f0516020f0316030c050d11120c1009090e060c070f150c0c05010b01030501140609010c0b0112030212090f09040807060e01020405040606030b0a060e1201150e01 76
    0x1040c2d001d02c5107040e071001c2103400043c0049050f4218000342c3c800074905001c4101c3c100d90510480d02c5480311203a05002c50001c5a200301e14040c9829510f8043c0319440c8509540646020b8041040605c0e07400c0c207450764a21030541d00d054070b620b40e01400000e560030500860843c0014028076040c00303084075500c1080070000d9200004c00103071500d1080c1c032800740b08104000740390215001c401e40400c0b09100c60082c806017411803d00000480107001440b5400052080d2115800d102c4040c0003075010307201d900c2c10317a00c0b46042c0040820414050005680c44030180a0402c40030b00800d001084607809100d0281080030020803000c01d007818001d10b00721030a005601c00706020040354030207985100700d0804440040e0f68a4074203680c1c070301b005c407018024041d01506560a10329180700b40c00d01036005100750b0b80c04980400c0304a8981800700e0488000015447c0c100407890400d00c1854055800c455460350010485603da10780007140e1400d5500396003e080f110094000c00b444110060b1781c01602520 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 822452158 1250 822450908 822450917
    0x92232061e0303210402040c030219031d060a050a0606020712030c15051e071b060b150c030702010f0f020a110406080d020606040c050903030d050603010906060909050607 75
    0x200326000071079101c034561280201c501e40c0412080282c4062090324201c3d02100403043c400d0080004495040100720740c200e10a902d8180480c282d14041d109032001c020604c0c01400e01c062100c081a401480000c882c10024420410f842402c00005c00c90703140700701c200d03003004101400d00e100c903041030710a10380101040d90850b200902040030625041020a5010320345081c0d808800d0800342c000361014110141494201410008200e0750032400c5c004e403030700c0b5210340181617a03440c0c4d0881d07000100024142746807403602400300114a03160032000250500503c0282054860314480520781e0001010101d6904041030007030666803c90740c0958810310a091807940c003402100c0c02901e070558510000c1c0821904800c00c1150303103079684007202401c42841140e08400581c070000e965017800322019031040782400819030319030f482007061702c081203070140c015070030300c00c0d45410900a4400244100d80540d0384000180c04910303e8041c1c1001003084040000d03659041c0e04095050210040c004414807 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 822453408 1250 822452158 822452161
    0x30109030c0602090118081f0c020307200301050106081905160302070302011508030c0708010c1e0e0a090b010210090b0a09020f1806010f090506092232 67
    0x3034015054a0714240e01030340c0143d95410305401603424010344a420035049040001c04602c0c040c000481010140411030455110075009010030284d480c49211500103070800c0c0035400000b00c1d20b0494044e00c590030703400b401c141000100404d0031100c003680007000040b108400e101200ca0189003440b1501c2070500140224a4280c82d4140c0e8011250030000070150700103400c0d02490301c02e5104591440517800d0015440da40c0b000320b5540c83e0080a8501c0e050f014071880040c40d00c80510802d8810b288030344450501e003803201c280d84541d07032101c440603082c0161790000d202e003550ba1801c564090a0740410014040010000081c0303841100ea56130410310b07182c4404800401c140042090340f090540101141c43c03207061010903c0750301c85001040e0442d0510341422020a010f650f054401c8001381c0c2c1720000c50508180c12144200540300351078020744100646020350030310b00e1441d0358000700000195400c80014442d1411942d0200c1c001c94040d001d00354102401000d01314410130400c461050300c015 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 822454658 1250 822453408 822453413
    0xc05030406050708310801060f03080309070b0a02030a091d0f0613050f06040e030f0d020d09050d0f020706030e0613210305012610050603030d1514030109 68
    0x200e00c9107000381d00078444082921010845130400300c0d0004141c151090000540010303111850188a00b0050034100c954003001c21130220511804045a01044090b1005461a103641c80f02c1da2002d0498070941c050210301240c03000d0b11800403e070000c4207500556580c00c0ea024002c0c00701c080343d00850070300c2500348503110100e45100b1295400c01000b0400c000c0d5611780c0000a80c0100e01000d10800c51402c18082015100d41c0c0d51400340300d40401e0300d05100d18070061640c00d071680b20f0b02c40300c950080c0307050160299000980d8040e0596090540340090300c01005d4540c2c1c1e2170010a98501000500c41f4166507000da581400008000e0106050510040314401009900c4840040881c170f0245a4004010144080d0ba96092000d90f20b0505100074150b5643c0018082c00090280c0110300d541e841c0410060030030521a1182201d486000c1c21004000b0085c260207040041c000650500c4244050b801c04601c5114143c0042030b41e00600c5004c0349441c1c4c0e001c246820103c9807910991408884101 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 822455908 1250 822454658 822454663
    0x4031209151404051905040e07050603070e03010b090901051e06010e1509061201080c060a0507020d05120a030614040603020a0e07120204060e03010b120d1412250c05 73
    0x50180d18240b0321031800710041c0c01c00e000c0c00ba03a44130550000d800000c000224042e0b90104d07065460654003845081c10158205a032a5068450503410081c10000140e103a0700c114101c00c00000001c00101d260090000020b0100000b039071513100b10f03559142400308101d030320003c041000160000c01c0f4170601d486000039191107040901d8600074140c01800e1000010020100c0c0d01c5200e0041521340c0710244503040c15002482401450130b030b031003040001109441e0440076600c0100e4607546d03091402d15940d080c00011001301e00216076920440101e030303404803817441c050180541145c0d400110185010801a800b4020f40500c2d4000d51038094107101603280c0e40f0b441420f440c03005164003000d45648a085803e40c2030a6034003115a803012901040b40c681c45031070406c5510007200240b2903400d00c1001c121030031081140c540b40c07643c0003c0034589014000d14110101d8890b0032a594103104045a603500024412103408600c207032212614584071428051211098900303180c00410b0380315550383d140e03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 822457158 1250 822455908 822455939
    0x20606030a110d06020d060b0406110a080906160b0f09190c0605030601050c01060303020604060c180302010f050f03010f0e1305070608180307050d0e040207020112092604031209 78
    0x40c001c1c101d5582c43e00c180300c0c45030102e5041802c452003c002c0342e5920a40e550f1590098010070002624580824150a0300007461440c035035000100c0c149050159000c20055030b0080f0f06000560004509032004101d82c0300714688030b1031726034000ca6102d01c2e200b41c11a08120b0061011011190b0700d600c0c0c44003280e00d03080650296030751030810980c0c94480d58010384143c0100c3d402c46e04c0c1507080240200401d0b901107503080c09a44035450900800300c0c200420389a03c1058083c802e61844610005c00141d88034840c010030a1700c0c1070911616015004200d087c596200740c0240381c50040b8140100701590603034010980c02030210344d2003192012140d851644038030303080c41000200400361010031002c54822140300414119030301220382ea60403518015417510203072044180410740d42d0000c003079281452300844440903416903500340104c00034030066008150b038002c15101d060320050710588042585405000005000d140b0707a072034510394030300f000e0458411030b480710030401c500303008101c3c151907640d020 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 822458408 1250 822457158 822457193
    0x1b0c06090302010905060405010c14090f01081902040f0f0b0c03120403140408210c0c1309020301050106050418020405010804030804050f10020405010909090b01061d090412020606030a 81
    0xc1034184581c202280074082884000c1d0890040e80d00f40820070505502a800b06481a101d11400611031440c2203451302030543c01030b8000860204e03d105941c8039142c580d9002500080448101960f42040c1d000ca810642120a041220080a11140c0310b00707240c0d0002010091081441d200f41a90069100c4c05100381451014280340041000c00d805080340c02080078081c000c16890b00d035241d01c080c0e5035422141144000ba000107071200700c1d000d601c1d001c840b2020342c032030300508a6448110034030191112000001c00340d02c1d920150403005aa003801018005d15031a80c2e16600d803030402191000348010b120025030651b01c100003c02c80c503604880d03400c0d401505424454440e84c0d840c10041d0030709002c01d812074170b00e0142c1544806216000d9001c0c00c141c5100380d8a064085840304a440d048031150744014100b20405001042680d12801110b00712400c0300102c2c1e01a50041000305103541c2003590100e40103001b0404440646034108074a035400402100144000082903c99426a40010800 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 822459658 1250 822458408 822458411
    0x150b0d050a061d04060b030105130201031404081b0102160c05130501030f1e05010e210418110c01050a0903030f0c08040201030e0703050a0516080303090c04020d0f021c1b0c06 77
    0x102400a180d00806d000714010303000b4849481c02c0404107500c5184100e0482c0828174045902480c2901c1c060000d2041e03a01464a500d4000030340021100f102c441103c0090541d0201715440042d100c007050409284e10a480e21080b05050104000e260043c1c10440310046182200400100b2986180070803c5a003203d03100e41c0b00942d4104640c2d0142c4007181c041c240f03600300301e507003001ea0f4030016204440d4451085032008039580c0110b030048501c11481241e0b00c0b101c0d41400700b00c0035640c0b0341c00100b6260010b42600c1c038182044c510503003540c00c115045070790380c0c3d0ba40700e07503009058040c09040c0584202403805c000300072a00304082c1060f000584080d0405aa80c4082462181c0411240c0c02542d0809e0441e00b00564914003540d4030f10111800826004d000c1078001020f81c00001541c2c000e4a0400c0034005c541d03d00c1c030522000f0b412210030f0b29945501c8041042000d60640f000b055901100c00302c18004200fa80d0048060301d8607280d90302d9403002c5800004106545c080715103100194485030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 822460908 1250 822459658 822459661
    0x5010302070f1b0302010201050a020f03013501020a030609090807030806120304090905100504051203060307270c050906040302040e030c120d050f060a0e0703150b0d050a061d 77
    0xb40200b8403500200001d080000011419807a142c0f6582c1c600203da200f41c0c001e1205da40d459661030183d01905003102d0b54004140300601428624151f281c031440405a51494070800001210141466507044560f241e54009400100d10350b0502918020f03000142c414841c08030981d032003841d50710451001500b00074450000c20300980d1000c50601300359094600720b179111034840c800c80000302081d0204581d603203d0004074031642c25060003064402c640001c00740200c91110b000c04040c80d44000d00440e80f50140903c01304010101c500750850007000c24090815000303560940c0d0084580c542007440600c2020321100d413013030340d5400c105c4081d6a8140e902003064062100240d02c3c0d80034820039907496001d0f1400000908010b5006004c040031101014009a184c0c44101242e1441c1a1200da4220303101000500042145aa16942040d554540010040c1e000300d1030034440381c00f907000161a00d1001806800f2401c9074010035420600011b001c00516103002c4881000e0510001c040b034040e00c0c00300 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 822462158 1250 822460908 822460913
    0xc090b0307080601091703090306060418120e031b011719020c0304030b01031118041505060f090c090102160f14030f0102130e13030f050d1503050303010e01120c0501030207 76
    0x1205c02407015801c52022071038124070654aa07044200028003a109800c0040d8186c074090154818910135650700107850580c903111328401c0585078100006010781441c11301410340302000402400c1820f02d4094240a09402c0018901a5403e10328005210850180490710000c002c0d4458004e1b4400e50050baa079100310b0200303046000d964000707070050148000000c01e1080140a1030100c82c401c4a003c075506040702c0003006200000d58000c1c0c5000c000f11050070700b44034580d010740d4200d10b000700042030394030305000012805c1d0300c11a019a05071401107000a42940c04005005600c03141c441600354090812240408013550340c45000d0204240344501040303624240148a108080f080081d0f41d80d01851481e80d842116503c03600006007102c0d000148040408a15111400d6250351441001d228a800481e00c83d044810302c0b0451680d504a1400d100400804041c001c501c80c2014541300d43c54000f80014441059202d0035555040300762040c002a604000d4074203076902400c0068a410250 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 822463408 1250 822462158 822462167
    0x7080f06030c0f0a0f1e05010c0c03150b042c030403030e061e0301080c1005070803040f020604090f0f0506100503040602071704060c0c05010201061805090c0306040c03060c090b0307080601 83
    0x5512080821000000110342d080e41005450003480c0c141b050311001030f565400445001d0b804600c0a011541006030520000d804c140c4003032010b4080755404203800154100090886004003800514106214041e0501d94180281c404d41c0070b181801540c00c1034a5510054912420b0545140c416400020300c12100f01e440c001700a4160b0304c2680454a81da1a01d1181342d541d10300d200d425100b14000405810180d105d181140e041c19400070880e41035448a0b40e03034144881c40d840080b41d003c00248000709034a030306072003201080184030310049545041240346a04951000e00602e01a880170200c9070301c4c181e00481180c4d040340c0e000350016a604410b0801c0c10044000340c0403016244c00020300020004d602994a2020502404075440015640c0d0010b9080356014403a600003c01a4941981d21800030750050794040d18220a03904846900400642420070881d422206c0b44082c1c0414401d006080c0324488a4021034146401074a0410301000b1450000a00e11000c21106600040180c1d00c40c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 822464658 1250 822463408 822463429
    0x10c05030d2d0c09051e090705040e0a05090a03050f2a010c0207141c1209150c1e06090b09010219080415020a0c0c0e07080f06030c0f 59
    0x18603208110100300c404110041c01001d00249030500460245031544080d640300c0c3d8003161000b500c881611070316100601628a140b00401c2c580090401c803030303034000d4850a04503842110741e60744482d03850b805d001d00c81d0311100d406032425080c58540820802288070005254400c00d4260900310f8031303451203481c1c00c41c65110310f0007007611100604100d18131b000d410000c10202000c0c103030003c0c8105080814201d80c0c42c10240300d8034000f080078038043c5243d403d0000c220b00d10004050000041071a46440304c07529041036560080002c3c2502204225000c3c0e2691a000e520364240362601d0750800399107031400c1701d02103c5194000c040b02d10080c0e02c10044907070b01071060158001c210202c0303464a050140e00070f4200d420050076401c540c0500d0440b103481a0755440c462a4025220002000d051203d40d00079042100c45000340000940300a000c00c8807612094000c0c4201842c44082d841d00050013403004401070400000148500b062003500d84d80400c03001c900c0301d010345003003440032000f00010718507804 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 822465908 1250 822464658 822464677
    0x409140a05010c0e0306090706050306041103010b04030201180803042102030d0309020103202a06011502010b0402030601050d050408041508160519110a02040e060f011e05010c0503 79
    0x2440c0c194030400c50306400c0b160b0029429290000070648520130b0503100d0074122240441d41c2c10003101404120300032000b80d034100e00c02501c0050b8112a04040d20715951080e0800706411f00701050030000c40d03a000c0504449440c08911030142c0d5450000394581c0e0b8001c901502e105010040c1d484070b8010141d00c245485c0b61340013800c07a0010148200098014a0450010383c0000c0c1800b44520a40e13004541820281000416040c54501c0201c801036042d500700c1c40d44052400d0601e00e48925445c1003184034044c0c40d02940406183c0a80031000e4211162000b0050146005004105403070b078211050301c80020b10000c0c0812941d64614040016100da904140162822045a0350400e42d00245652146c0b4000030300d0040c4444500c010782d824090540b454602c000c015507801d5880c0c0c807600840c0d42d100a10310444030300c005580d002905550005154845d254009410030014801c0c800c0004c2c01024060046c41c8042040c0740109280c4056000313031410700500c2c000790300c10408204101c41200c40b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 822467158 1250 822465908 822465913
    0x60906051e0708030618010510110a0f120f0305060a12020420070c080a0b0c1308060c0d1508120702180c070209010e0709030204090f06110a020d1d040914 68
    0x464504030f1515081501c03c2c03805803d40b0450202d590541031170050681d100208150200740340e00204403420752105400000b41e0244001c0340e0005080f20f83e01c40c144512038107000b0710030752003403034001c0c5206600d0340b40c10101400d00062000c0c27915004070020545003600b226000c0c41602d400418081c0064000d6541c00101d104c924500c0c04100c6405405500d1051080300ca045545a82055030780007e18800b4010310040c0c00460140c0b041c4000501d03a1455603114130714900e645030011800c0420071110f40d42000e0300003412400c02100c1740701d03c140c0e8551600c9000304050400b00e10301c0c0e954040d910700d260480800503816041d5640d0741c40c801042091315810307607164503240e10986055004424101e021305d90000020441c0c44a01981d940720707103425564245964995004c201c0a440303101c40665030000c0100100740403503030300d01804ca040d2403900a1659a040300e80070003882d0503031245c00981001b10025050303403d0004485001000c0e0412280828060030504040040400140039110f407803 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 822468408 1250 822467158 822467167
    0x5090f0915010f030b2815081f090c0f08010b0f01110627010509010605040b150d1109060c01060602120f0304080901021e0d02150103050d1d120a020f010504060906051e 74
    0x250301c1d940000410500c80908022456500c1c231100e665420701c541600821210081032180c00425948008484c03801240b0f5668619540c10700b05c80c4420322604100c1d80741c7d4443d054040607040910980403107642c00c0c6880c04085008041c425200e05000e401801011300e500c0100d8901103500300c030304002d030b24400000c00c180e08051030090700800d5070344a441d024078205094005149070000c0c0086522015100c241e280c1711110003410018441c80e0107068420a041c00f49404135200c0030003034070512504800025005d41041c05c0689801c090865180744081c0820074a405492440190f0fa081640280b0150b210742100006038100100d00051281740c0404130300c2e48589510019010000001c00d4003942c0301d6900f10307110754034280402d000140c05a0301c10944140340901c2814a180d0865007580306041100b01d050000e040304291202000365a40040c43e00300561805501c151848042400c08529143c80d0500182030a03031988620414040013048001c031140450103062000d9100b5403100303594 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 822469658 1250 822468408 822468481
    0x6091c03030b0a1d09010209060307030e120a0305060a080c031027050703031e0518010c0c140103050f04020a0e0c09211009080904090c05090f0915010f030b 69
    0x580b101d1038146500404c14804a4400c0c40103100321046481c0260009280d5076801c10180c01410960740300c07100901c9019503090700c028001002d0b0020128a40c1c0104d050b0400104120030329905030081c0c5204c1d000b5481d00e0056660008054400500c8060040340c0c203c80b4450300c4e01d404041c5803d00d0b20404480c5220401c0000204510040c0c0e4031940326106c0304405460304940c0001d4017018280410002c1242c2c0141c0c0c040702007589010001454050307001840d540d03500d00540080da00616030b000400340580915038041c081d00ba4000c40c40c41d030b2580b49290640015081a10a201d211759524014002c1011409880101d928184026080c907000f907a05203140014020032812111050007a80740b2181450703210700618845d04d800402c0c02c3c4c20071900500300b0000f00340c11142103d0b401001c2c140005d07203880700d03da89403081a5021444007c3c0c54030700342c1d1a003822025500200c01c13a140c10014080440c5001c0c00e00c054a40060f0042c03096500d0f03000e00c3d210500d15211003c071a8000e4111075030b0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 822470908 1250 822469658 822469679
    0x302100e21070e0903090a1502012009190305030703050d14060a150e12030301090b0901081009030c08030f04030e27040206130306050f010506091c03030b0a 69
    0x8103510030303980c5000c0d00e44030525401154491007510302003030b0419070040211001406a09410224a034141d0340760030361010000315035298a5010642e40680c80c00e82c0c0c0c107071315020f00c1008041111460080c92902076014604183c2c851178204520131a6244020b410b501070000c41c44000c4c2d54001c007220340d038800905014000d03420116020a400c2d00b800310301e00b40fa00d886513159000e06409024141140e040194007090785c00c00241c81010070030506034001e150358400220038445800300000c0c640e0f0b035040007220b1080c1c91010b03407100e002c0c0c03000c540100030b00000060b00f001c0000b44a0800503440d801032a0481c0c2d20800e1000c0500560408000c0c480140c10418801e4056031107501e031001021400400d2141001b0500c81100044400200380c85180107407101e02070303129100070011031034601c0c0c0c2d1400305c5030484640c105a88541d0350311b0405c814001c4402010703000d400d00321441030411040340c0c0010038850241c25144907004148841404040c000c1e04070000c4803200404540040762100c11506 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 822472158 1250 822470908 822470927
    0x1206330306060605091c021216031707020112200c010507030f0e0307060b032103010e0a0908220b04230d050601150c081206031506010f18030210 64
    0x1101580381c964001052800303182102c02609020304000b00c6c43e258070b881102e0320210003105907008184120b080300042802e000c0c80315640b000d104244011303030035400c5c02c1000c0c2407071014407400c1708810070848005d80e80103202d4450013491b511010400c244110b9084891900d14402c00c40842030105000c4001003040d00014816030990340c0030000303128016089416518103050300c200c00d070420460100802d100c1d422640c04150098204c2300d0710b080d0010740012248509034064612180440140118500b04251581203081003006104000d29900c450500c0c0c810b1455039582a80b2080110f6042d5a0324510b000c000c011420060342c4481da50107141883c0c16038071b03161488070103040c8141d5001d0f00e040c040110b0400c0e000801411940c4c201040701226035072450154041c401400c5050001514610007003500501401818200d03003002c0e803d051070050752100366080b01c10410104031389030740d000f2095121a042d07031914051440300d814150361540700d1030700081c0d048400c42903110740c665009800712 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 822473408 1250 822472158 822472163
    0xe1203071215050f091014040204050910030b0112080301150309060e06010812031302090c070605150a05061207080a090203071d090a030c0830010609060912063303 72
    0x1100389013255040026a0204803404030702c03100c0d9880300740308100c22480001600340016000600d00381e01e8100207091204200d030071003043d410070310007401045a00200c0b00d005110700c0e444900080d155079030390082400305002c4ca540d4200c21031042c2012501c25001154881d800840400074003088400d03075610369209010f410000e00c501c04141c05c007150001d0490384a00545240000348114660170442c03602e002400b4030510b00750601500e8081902403107000e00801038200800d04001084003440800d6196074022441118140002820040031501150b400f48240c80e0403200b5995992202000b4000c10300040c1d01441110b001007004000c100301c0d080d100104043c000300990310541d43c0c640e01c400180000340043c02c0300e02c03440001440c280107040b0605031046042c03c00007880c41c012403010f03140c01c00ca0200300601070040106503004101c0340050540f6141c180700b058101a500c2250090740e41c0010729041e661003484d5071001b0410b00581440b01e03054054008240d182001440c030390001e010a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 822474658 1250 822473408 822473419
    0x100b0d080d0c081308040306050402031e010b240d090312110408071224060b070b04030e030d090e0a020c07060f0210090b06060304060905010c11100e120307121505 72
    0x10420b2140a42a000e0361307513074848610b91505086907100006172901400413a050b07c0f078049030f00e040e04004140c00d080c881480c3e00004240c80032500300404140365080c000950100021000d00c032501b6501254a034094511012422141f07604e000c0f6116424846021603031850092500108118600104116a151340c1200d48141d2621402144081c03203460050406600da5040340c2c417203501e1480c481d02220380d8100090210742d181c481001c258016041200c9802405003008100741d00b01c2800e10440300158000c100b1000204400b40c02d007a42070241c03030202c08200300005c115500310780481d2441d110795826644691f980700000f50207604091440000b5028500000309a0310080c440c46031481e03041180c501e420344906092019030f90025005807000707516480c9550101e2824080d95843c1c02ca50b90321519904c00c90007000c0d08040030032900c03c4445040500380b2881400000c0c6000c4a00d4408034038075aaa141c0001c02d64002d25550808408503042105086820b00f150030110111402680d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 822475908 1250 822474658 822474661
    0x32a0a0806072003040b0f09040c08040b24060a02010510090504080a050c01091403090f04290a080615120c030d050f040308120414030a02100b0d080d0c08 68
    0x1000c03501c460341103500e0340005110007209103070000010b00e8111552442e2098034036240d200e113002c6c001c5500c030081c245084140018001c080307082c580319039060082c02d490241032600b010362b51100e164101038a149408a510740768040550546031000c800c00000600b120340d00c1c00402c2d03000c0c1c041c0408072102c1c1d241c1c04a4550025491002d07019591041d41d20525007880e1008018040c0c0301c5410880c0100004c0d0343e15044032000403074211000e00d816400400464460f16030208009410036042030a13130181c0c0c00e021104210080c0800c40120000e0b6542945101300e06045c04104140300c281d020358494850b00b4284100c0e407076520340c5540e003140145c41800081012090303d41d504c0403d4020325400d40d0000f200d01c2c03409072144000d000a02c04c4819098501a604d4580200c0354001d00d40c440c11080717150301031008001016a010945004600180d41802d040322406500c40340007500d0340c442203032210b01c49a21952000004030a01c2c1e4070811035074036454210061801400c0c3c00d600034011890620 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 822477158 1250 822475908 822475919
    0x190903120e151501031808071e060e01050a11180d060e03190e0a1d0603010f11030a140103120e03070306050106020114100b0d090809031e0c01031811032a0a 69
    0x40c3d60040047e006882940b80802c0c0e40d9546912004a90031140b04c0d4094540704d000143c0c00340110b040e0a011240003146a040c10b40200048401c02c0480c001d80d10f80403c0032070301c10951240e010310a02c00845040d860341c061828003c01800e07682040c410280400540b038690b0f00150145402600c2241c2c2e00d880311f0005110502249020303138003400e08400b00d0352865881800700c4154581e80170300040c00220b02040240c60000c156403200b50a0240c100000c01001034002a9105135404070342c000488142e1545180c41d41c00402c40c0301d40c0c4170401c108100d0f04024040c2c900b0841ea0b00110741c0310360108019a90b44400030b009040b960b042d61401c0141401240c84024510801410f883d90041240d14004000c04000b00401034410b00322803060081c0240b8109650500507070990407200e54910412580054140d400c1909121101d41458074002401c85100e103440308041c00301e6030014a04075003140c00d100091800625405c02000580c80100c090084a2446400c000303801d0181d4900940c1c548a0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 822478408 1250 822477158 822477191
    0x18020f04051309060e07031a010b03010b0c0f12090415080c0f040f0c020c0118060912033e0606150304020d0b01030308190903120e15150103 62
    0x14009040444000e010501140c50542840003219190040001e40c1490340e40d6001c09950b0003007009501900200d50070000d101001034503580403040c221746c00003e9030618a810030540018003d400010340c0108208181003020030400d11118003079000c0f01c5031024000100050356020400700742c062401c1482c20440f041c03132424070000341c0750b03044040d000302160340082c00a04003502006951054481d64041300103103141c85120503d0f582d5074054281d01b060300c0005058166215111a80c01030305070340c1000200c1e0f00c01d455000303031001c81c1101c0e1613481440c1800c07144c0540c0640e2103200350a81c03c40c603c3c004c80084d07006440900f580710300d4100301e08c203a84c074154079074508451954001c440040110018219240190b034480c0c4010140100c400c1c482d19141c0134440c00f42c0003280459005014403141c0e8142c40c0c0c00000b0444240d0080c401580b060f90028040d4040b42101181300303458a400b805030200c00d10541e1b8040c00000059503e0303142034520054482d41d4215030b04d000c00d103001249101500f10 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 822479658 1250 822478408 822478417
    0xb010203091003050a06031a0103050606030f0d210203090d030b0d0f02120a1205070b1005013207150c091a1309050f1f05011d131103011802 62
    0x50810502d038111103000d074041d003c02082240d2859031224044002220030a1004003501400d448988960462a00a2820710050b29541c07003540072214400554000241c40300c480b030441e00d03005100058124044429070200900c500ba95800481000f8801c0000501c01030107000664051007040f0301c42c0188500f4441006002d02820f0405100102505040a4040c00710ba0882c04603421651183c44211040446d9a80c2000042002130f0000c207014142c000c00d508100103c4135181024139007400a85002003075480500804800385943c8120221151510054021082404e40e600c4680c500300320740c40c0300c050984008078506001d00102c18892207048081c3c9400c5060008400444008801c494100300d81c44030491594070781c04203c00300103012707682c06801c40241c2c49082c1c0c1080301ca0040d1501c07441d203104071190307071a8108100680e40000003000328884000148014031418004c00c05d00c8000f0b84645600d2800c00980000b40f14031040154103c0e440d06000718100384141e20440144d215 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 822480908 1250 822479658 822479677
    0x2030108010506130c0509190b0c1011041d0603011409030d0f0606200f07090501082407180302030607050c06090703050a030807031d0705040e0105090721080706050a0b010203 77
    0xb4141f1002c60141420314075034482911548180d5900d03a983c05c07000b0031a600540c070b00d0490f6004403861441c84a203902a06901542550589003818113056180303052400020111011440340000b19407151400e40c48002d219400188a602d42d2030140711041c0d80f42d20460181400602d09a0400309010079807041000ba00c00c0d0f640d4001800c081c00507100002d00340712611607039600895054040d041b40030000e520003041c0f4250041920762403d8082410240d800d1118091084c03900401000b846c2000000c80c1e11031201e0422036807003c0c000441e0071714108a500000d40521400c8d09220740a900b010142c0b500c2401c410442d54996510410652a4030552000804550100d5040c1300024001e18015074011420b25000410750f8a18420344074100200c00020a2900846402d0100341011701a06016901c0b800080c440703410005d1008c1e41d030780c25a00c40c0880f0b80004030861441e03116051000e0b610181c00900040d2103546604160000b040f05542000d2068a01400e01c42c20754008800e1707840a14 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 822482014 1106 822480908 822480917
    0x130c020703140c010e090c0c01060b19020f0a0b04031403100f0b04051e0d050a05061e010e160e060a080f01050105070507091e02030108010506130c 65
    0x502d54032900d8001444012a0f039070000e00100103148140c81021041d0f540071001c0f88039006000189030a9400c0210000c0c960907608040c10900345804802c0124008240040c1d03640c416900e072038070b116000940c1e5030001c10501031042da0300c1802400c1c1280c1030a91a240c8220329481121700241c4035100c00c005021a206004010001c0c20001006615090030180002c0044070480744210b40c01c1c00e50420002c6540310b45204040403540300d01164120a000d182c0f140d21200c0440d5444405849640910171400100c14603074103c9030b00c2c1050f01c801d6121403142492503000c0c44503c00030300520314983e40442c0c4035200204415001d035074030140b046c1024040c103070a10f40180e0107241006000d0041130081074012803100304a5400400004180b00404800d8002415840b82c610440e0b101100005003c0c00642040e84244011600c81e03c0c0c82d000b080c4010300b01c07401c1c01246130004 = true := by decide +kernel

theorem cover : BRFrame.Cov 822302158 822482014 := by
  have h0 := BRFrame.cov_init 822302158
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 822302158 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 822302158 ≤ n) (h2 : n < 822482014) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
