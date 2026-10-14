-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1657
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:05:12.86019+00:00
-- url     : https://prove2.me/submissions/82c2e41e-8a97-48e5-a96b-fe129e1d353f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 297841726 ≤ n < 298021582 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 297842976 1250 297841726 297841759
    0x20103060509013b010303021c0207050a0308071406070e0306010e010302220603081201030b0601091a0f1201030b060108070503101403100903030e0c1e010f170106030902 75
    0xa401c00d01c1482d10840404c452071107003810307903100d22140c0501442d07a0b2107800d61075040031007100c800740c00840160303010303034000c1000444030010035419088a100400c9220304020100342d0210b040e00c00202a0302000c143c240030400c40c586288a281005000c0b02d14500c3c0c040c0009001c00c080201d040e009014130000450b03095101440b090680b900034240f24a10380e6801c1207181c500c100c400001451690361000440001c00c50742c000d107060560118107160550450614086000c40a004103040c46150b980400c40045c610b8084a120f4100c82c40403501c465400d4041e4445214039554080441c00500c00401000b1044510318000c64081c1d076140031039030b50413505844070704c41640e04a054180143c4204008030380d81c0c20703010036114090305481205075040c1d03c81d0300b80d886125040303000c02e84503e94080310501c01c001c540e46020301251903907861040f1010300c00c503850440030b040e41000783c100e007a0710000c1c0c003035075001103819018030b062401581d4502005004192296040b44221109075094869 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 297844226 1250 297842976 297842989
    0x106030e12030c09130515010e030c0f150c0106080a05010621110109030515090f0c130b010201090510020901020c0108061f020c28090905030d02090612130201030605 73
    0x104250301c5107589140c80303085180303000350821040107034014050780da6140111014000d0078016a01d038110308201544800014040e83d05c00c0c1ca03000d0107544103d20418240c0e540c0c54054080c45000d50300c1b031115840c40249280b0038450600000941e600b41200040c10f14000507140428901400007044020307192170020341c40003900d020700d031040d40c1064000d0020035640002880601c030141000c41c0130603034903500d0034108088a25096191191341c0100070107840244000000d500010b00034100c4803120070001403d0004048901c2d403061365031421601282d00075402449469004803c0b503058200310110140070b903000400e00760060103241e242c0c405a5004000d214000c480040c0700021701040040c1c0c8401040340325283c101148540003080c0c4803a01e8104081c46c0103c03143c907090180d86144e805035101000154045c528145c034090003540452004400c2d01c504400300e0070096551034440d80015130a001d0341d01040300c00b00012040c40083c90348100c00c01103003403003a2800d02603103076204200140c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 297845476 1250 297844226 297844243
    0xc0812030103060e1006240806180a140f01080d050915130317090301060e0f011e1503020307030b0d05070b07170d02210403020715051209060106030e 66
    0x21104024001400020283d0f005400001c0200781202c003c80c0d840c459440560750350f81e1000032050b080032409408110107500388004004141031141d982d050010205850031102103401d44118407010109031505501d030011500c0c4814000d240039582441025010f00e86030a11540c20a8403a4810001140c2d02aa090350340040008003030355034010040c0541031107a40701d0b00302c2941c6440c0c15180440040c6103184081c142021030f8207825121642e240505084503c00d030480d001d40741d81803041041e02245643c2c0181940d1680800d1010030800889a08003217007660488a0860720b6003850709901c0d47d15034041c605c41c081a980c2030168160b503101f400929024418094599000301c2d5051000d0f221100090070f07518820348016100d140c040301d555655070014000c59500030340001c0c000b065003903105051000c0080603400b10030305003080d540203565030b13503144250030031400140003401d9400e0003001500c00004400580c81294039041e100e071500c422090241c0808a272400b5a0403096110000d103508 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 297846726 1250 297845476 297845503
    0x705160203010b30010b2d130b01030e03040b09150d0c0305042001020a0305220b130b03162001020a080405062a03090307120914040c020d03050c250c08 67
    0x2aa1f202e0850350b03c10020310900130071065000551810318640761001d031300c2e0b24116441c100103a0300401d080018159004000c042c015580144820b00022200900b00c0340410f004403050000a46043c000f062240500b912442203c2c0c43c129186010035010742119201d5480b610111840205030507442c030220780a650340e14016031281440d9030009000f0001030014541d80d8a540303c14070710301080c0d04010b0841da004504280808510355040c2c4492401c00f1014186045d03400b415450100e0201401d207523080385210030400c480d072001c0400000032498500c8451400001d5655070900f40c806020300600b030f54100c80c0c0e0b01c221030025035900142d03c50682c40c0080390030700c1c1c031380d01200d912149116000a4812100350008000e09400150f02012100c5001c20302d07110307240e0451804400343c180501030303540e07940a1030600c054181420750102e142900c40a80713040c0020389481d20500300010b4000e90302028a840708040240e42c1841c903640038420041c1c0301e20b13004c2013140d44402d16540c61310301c0b45c030000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 297847976 1250 297846726 297846739
    0x60b040504150c031d030403050f030304150207020a090513030e010f09050d05150f07020d050a120c090503010216050f01060510051606111803060705160203010b30010b 74
    0x5060b819154118090f500007a1402084922801c050a0b94040b00703444031070314a03400000c0420401c1070501a003a6034889070805107045203441c2d11452031028a0380d10004516500045034000c42d99000303060350280c40441410400c91410340d462104000180c00103a0219040804401c0c1940c41070410203d041d04a0340c845050629002c10300c00040540c0d00c04450301c0c02801c0701103a400c016400081c0c07050031080104490350605100c0a41040b0800380140300300241004024013507a00510920b2103039446000000d400c050650044a60b80d0058005035815400020281c2d8203103280700c810603046015009490350700c0403802c41d15080310351522800d90030407502c22008550600500c041c001071050200140c071038690582e1180115000b41d825050310b00e00110b980171090544001d0714890242c25401003219040528014080f401080d0b44e288400460707019840440d20f0030f4201d440c6140c4050282c1c0716186820240c06040c840b1581c454204204c0340c4030440516405000703110b103505001c0c240 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 297849226 1250 297847976 297848003
    0x31b050d02070501060b0708040302013f0e011d0d080103020f061c150f060c050c09061206010306020d1401030309060503060f031b01180501020c062209020403060b040504 75
    0x94040d402ca0b82007a5065540c600d40042d0798119840200002c44c403440c2d6050341d40307056200141c800e400d91580c9880c8000705070005000b030380f418103c00380303245180002e04099a5640400034007400e12041c4000c403075400c000c000f14507000c161070011400186542580c0e148842000c0440c0c1c040002d1002170761240e0b4100f02c0c004142070100052038803030103081182d00c8011500c08860251107500c8079482014160a400304650200080c02c170000e003c491800b00f000340300c02d48a0130754889004007045d125860010104000c0d5503a01035640308010390005980c025039690904034003d40008415049941c140036282d82000c00303028010b4180e941c16203070909002c0c142201264107070801040345402801c2da10201c030090341d0400c045081404c6110501e86061141e1000600e2490143c07100400001c558030140600d03a0085801c40e80f01c3c00c1954196207174500c03120500c02c291629035043d240800f5203035010910080c10380080c0f00303030b034040c00303050100300c144000344021210101c0b07003d449003070fa4148 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 297850476 1250 297849226 297849247
    0x110102030f04030b150619030f05270c1003021b070b0f030a1d03032509181413140309090c030901060b04060c030305011e0509040c0f03080901031b05 66
    0x61303a400c1400c041d90055000303404401b0a0280c0e01ca0940c4190200e041440d00c544a035040c001d40b0b032a0702d41c80205100b1400e0421030301102400e06250742c02d491201c1110040c003410300300443c0b000c111004110215041030344e02c001d0020343c000116424402d081402c6c040c1003c3c00051610100e403000c0d00d58901d0402001002031094101038a1707492825110700340340c1442c9224906810049040c1d07400f940d540e04001c03e4403141c12400769004454100001f0400300540d0300410b003002101e240446d9034080d0b83d003000304040100100000440c400501c03a0038000418000c11075900f01a100b00500c00300311039a107007800d81e00c0c040c031504198000c80e150001000740d1403e0b006035400c0030404d400231400c1c42d01d4041a88864011307411a0002911140600c0d040c9585402074038010060b905c0320b01c41549440100307180000450294601a403c11804141044103800c000c0004000c01d44a80b08001c1d1249001c0c21594850442d0b14006420903c6030060510548400014245140c8400c2e140400044 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 297851726 1250 297850476 297850493
    0x3030903120a060b1c150e06130b030a11010215040b07120902040603051b09090d1407120504170f0a110607051209040e03071e0c0b070c03110102030f0403 68
    0x1401c401d106078480900250310b411341310140183e80c60392208000d0300d45540e600c10f01100c200c0246401030110f007890400c0301047c804040c42d0010002d0324040a09a4298280c01c09003421208054040c864013013464140300c420b4030395074890502682900c100f411040343e2404190004c0e10082d042050b60720115140c54000c014000008651410100c4c052043d9000a0101c520550060b205a0004180c00441c03001e06041c581081c2c000318ac03180c0c25401d10030000c80ea6a244503002d4018010080d081c0315460902506440c0e40325031100d520400c0d9a101d100080c4150010712a1820548030448a00c0c0105004034004404441560042010312000d4450f4924545144019500540e00300700000204109100c1c81d008054844501566544010b051100300c91344803c15200340e82040c000c0e800065203500c22010610000c1000207003820150401605807103180c0d03c0034504c00000140101000850081641164012a500084210fa1400590300c80c8101c6501100143d01003106000181c0c444 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 297852976 1250 297851726 297851731
    0x90513031d12060906010e10030803040f080f0f09090a0e15101d0610170c070510291903020607150204030507210206040308160b0a090506090303090312 67
    0x1080b24086a070407842107410708200b90383c44030403a04004014080c66249100480d0040f1101302001d85091440c0c580b10075900000d0001007110940000e40024801aa41035403255824150342e65a075006680300d184090f480600c010303000e00301d01800102c100035544900c5c00d214101c880606602e402d40c140c1d4140801c3c0041002d2030380c5e060510040360340404200f8590503410004405071070341c14100104036031032803444081d5080240714038203601d0903060506040e4100004100c001c0d12460300d441d00da41841611489081c1e40c0e441c0a01d1041e00d071946c078114000b20140e2803030805d00300c020070051020803445600c0e450580d64201400300f0040c100302c07005242041c01002400701c0d84600e100d14a09076171256100fa42c1c603600c032010520600c0720f8490406600c10402600005104096020450901651002901c01880800c0d40c50b52107800c40030310310986a02c090074914030b1600c0c0c840e81004040e0760100382c48602c1148002a164900002128000d061900c010b608001e003020300006d000100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 297854226 1250 297852976 297852979
    0x23060a020a0602040602010911030f0d0f020106050d030806040e0105090c060c160303110d09050f01050912010c0809070e060d0b06030a080c0102030103152901091d01090513031d 78
    0x310344807800070030082d20150001e00f849a001040d408941e040c451f5014040c0202d0600c0394022495a03d1141c0d0001801c40f815191030a1181d40c0780d14000050340107008a80c4100c3e04048103d1110b001c16900602c00361107088111801c101802c1c01711040d0303003284c0c0112040119580401400001480c251001e07020071000c0104903802000710240c95842c6050079401180420701140c0200b02c0b18105102d0700741c1c200f0b0b040c64000039140c5002c002681c10624491a14107002d000101c010342500c03010b00c0f4084441c5000002d0003400403d00000f044400d0403a0072508900a851011640e0002c040c0c246009130001407081c4c0908070f00d91a0714500c2c3c3c1000d030000f585842452481f40000700c5c0000a85141d904a000050b100c2d0f1450401045075005200d51002e1341c0c0c0303049102003d20340544000e804510b604020b40c20340504000040c1c03660304003600500d081c0007134072091186850404000c6410303550711920a01098440340405820b161028800a012600068071681e20001c4140c880001c0c510 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 297855476 1250 297854226 297854233
    0x80102071a13020a0b030429060603060d06020a09030215090120031201060e031606050703032007081b12030a09031412040309050111070306050c07081204060623060a02 74
    0x1426400a81300030201c0e402404c80f084040100710900c81d802c0002840c007210f1100c000c003950a0f0400240005031b004103210310644021010030929160000d480c840f490340310340119039920001002a2056805100c02c9214000100c1c00c0074041c0b004005480c40d044040c3c40340e216135003456a400c044140481101805440b0500000b44003c42419080c0d0092050303031980414481001c0605080c6111020481490401d0f004100030550744030003141c1360355801d031070300241c030345410f20b0741e00b40d0403c070340c08050300306440420410140100716009090030030b0302c5007102440c144444d04250b120200ca122180040b0b40c00e0002031240c40340360b00500782080c82450011a1448240080c1a1a412001c181004025840204810145c01c8007a0344090082424001c400403102d08a50b9690002404014111a02c400125101400303000980b00c00c140c1c4600d41079140c0c18401101d20b200c4038125019104142810340000c1c1c2c07120748442c0100300c1c1d02a80711000808403103000344400c540c41112024214031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 297856726 1250 297855476 297855511
    0xd0912060b0d0b071403040b01170a0209011401030e01050702061f090f0614030f030912070e04050604030914030709180b09010e1b030c01030e250f080102071a 70
    0x151100440b40440348515001401800c00d0440104015003030b55080300c010104009000100b00444c0b8441d045a000d031180300d10346183d100341981480c0c541768000350400250800032031080009040e003824000281d030700b0862101080e01d580d0983d407050b41c01901503006140803604642213403c3d40c00a1981c88040c02c2c130a9030f40c0c2e031002c604442c0c0428450f01900d98400003409014250013100014a100720020600d80d404070101a89078410340c115584104941d0594030840c0a05000000050440040144851405041442d01c541c030440e4128005684008041280b1818207034000c0c40c00d5000d001400341606000d070800003840c0e150000c80300350000031000c42c00900c465a00c64440d505c04000400e40c102c40203003403031a01c940320122411002c4800e50f5000c09490010384040b051601746000304007652070600c064100841940d00307048074100b0740c448a200813840c10f4540112440e074007540468a65500500e402c0f030040083c020032804030700040c0d05c8894980c0c8090380d040800303c000d51556a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 297857976 1250 297856726 297856729
    0x10c0311030c16060c1a0a060506030a0f0c0f0f031a0904060c030c0203070f020f120615030d05040b180a05060a120506060903192306060f030d0912060b 67
    0x160003801070200d050307100000900c0804480d01d500f0000301038904000000d5034050b540c04440000810b0100d140c404514009180c8400d150480b00050a01400b195600e0601d54801c40c050103070800507107205400c002d503019809200c3d04103410200403568500e404e615802008a000d48940283c190f1402c00106c01214640e58000708240030714807603800000c4e008000c020243c141c0b10f02240c102d0547d003042c0800400700d0004103440244984c1140d00100d81070210001440002000c82c158600b80300e4030041000044c0b1040031100700003000c4084852286440d0002c590b40c0c0300b50300450183c0d0500340100040c00312003c810b03800c4000014012840b0544a10100702d45401c43d101040010b00c5a42103081101c44e280b1446801c1002960514a40801c82c8013081c3e0780c2c0d0b0456000410125844150320503c110b4030000c00364101c0030041601414103820406075146404ea0310790788030307019451401e80c036440c00090000821505407500ca00c0380781390165400ca076451a020603140c0c0354440032007c078503 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 297859226 1250 297857976 297857983
    0x80403050409050c090108010b0316180801020a0c17091f11060907170703020a0512010605061b010b0108091b13020f120108070509041226090d050711010c0311 70
    0x18041900c030305511742c40c00c140010082c080686c0a180c1c0c62508200b80180d9140128442031a2042d03070801e4481c1c102c400d0000ca140302440c0c4c0c0911a10f52010410030100d503444000c80100d40e004202c0a6542c4014201d130351038030b00c22420b00c2ca03400718a07240041c510502013200025100001c1c1414809131805903213170390405c00c04a5036034500e508000300c1070040c0f09031031074900c2d000000c20005020300da00315030104840030020b0040c01d100e219440340384041910250401405008050030a9841d41480e014402414201c00400306280d400c081000c040383d44aa18001e11562800d002000101c1c1081880e224421500b0440340d08200d0315001c103071000043d030000341031601540141035a00c01031000e490414090680000c0515049010b040005a40f03010307d00340c0141d041640889105010034050300c0c140d02d8a07030840b800220740e00e904d191082d030810759140710f03108100a4601b044070310300044405205281c40100300d41800f4107480e40c65440380300113021041c807900341440195100e54600b0f19 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 297860476 1250 297859226 297859231
    0xc09010509090c152203170f04080a050c04060510080406020c101e0b060703080a0203062d091f140d050604060c09050a0b03160e040e0c04060506040e0708040305040905 74
    0x4402c03030002590002034511030038505c01d5041019522440f14199070701c000c000328658059a0241d03901144030f01d1140c04550841723000f054440e08480d58001a454440d8843c00c501032018843c0d1301d400e4002685080a14003d40d203000c1d6503650302407a564556680d8001d4008200c060610320580480400020991040882c0149009514420354001d503521340c0c142e03081c280036240141c8052000d2400240c01602e9140c004030007910150f100d0b5161008a00c28000a20842c01c4140d016030fa403141c03498041582030b01c0d0141c2a603c150050307a5901141c401e940d00c4c51042904510960000c105100780042d0008201c6001003d0021400f910386070756203800c1e415207040d9806c03950f030680c800c0f00a8102001e80c00070074040d00d02103955450226901900e00004000c0c21800c406100d01c2c0032818401c0300031040c10032004008016103014460150380d035451580045000d10715009000ca45850a8401c0e58111501c031409003500c2c0d91051012225101c0140c802c409001d014080130588128a01901e1b1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 297861726 1250 297860476 297860509
    0x910050c03210903040e040605060d0b0408030403020601050105031315110c030c0d0e06120615130602010f02130308070f050604030c030315060e0d020123040609080c09010509090c 79
    0x80307503001c0c10385541c0b00c0c0d4030015225203100d80c010041006a5006d100055030702070340003d80007a040d5141c001291801c84006402086440301c582000304220100010314003c900039030032a095aa200c0006603203900c8180d4000aa000300300580c0000130f0f409109a04000d00e00c0038020079040c039404035051341900a100511a81e40003c1540070200070700f04000400e0010034607001c03805201030720200721544500603101070411009400654140c41e00748002004085090400b03a84050f20024030501d00d105000d454019400c201000421580e01c0c026074034080c10710400380f01943e1459441206541c001082200c200c2d00f0020b400b40815402d12000c1e201354040e4491500c051400c0c60000d00300d414108060702c0302c8460312401d108544e800640d6110b640c1041d50104841c01043c0016500180d1150280f072440010031040d0a590f12a14090002c444103074642c100000d89550b105d6448594001741c40381c02c14041001080071789000007405402ca001d810a440440030710728080b55a0081040400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 297862976 1250 297861726 297861757
    0xb031b090a1103010e041a090d0f0503010515030928060b0d0b22061a190305101808120103140102070503030606090f0d0510050106090503030910050c03 67
    0x4489a0405050156002506940c200311080d01801003040500040c02940c100466070b030001401c0001d0070458245445000302807082e03e03d40003420300d95440d60010501c002540c00d09090781d0080c018400e590603584010203181901c8890114900207030001080c0100700d21038090340142c426450302c46040e01e14101c2c1c60b101740501c0242421019266070040c03241c001c500307040ba8000400c1c1200035081d080030784070555050002e1502d02c1c18405a0b00c510000c1d00151070400806000100c2c0303207401c1220031003514984200345160f17100d40f094410501c40a0000e4120103503031120025207070300c414030000881e007104c10001ca181c1c4500d2015001043d06d00744050350080184240001c1c50550750006264200035031821041e955000d84134000030740707070702d0160b800824602c15561758502c0740240000302410048000c1d83d9801c1c0b0750b50b540c280c0c071605a400c2d807802c0d00200300c25108100318400c7c0c95003c1d0065147c420b440c001d1100818200b0243c0c01041014062602501d10a2004008805030014803 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 297864226 1250 297862976 297863023
    0xa020a030207140d030e0103111201050f031515060d02040801020306010809031602060304020f0429040b09010e060a2d05030102070308040b1306090b07110601050a0b07060b03 77
    0xe440e000d1190030441603504003000f403a00c02c0d5507042e1243d4081e41d1518180c0c035425034900040e03002d0030354149500818031001c200c24a101148021050407200101c4480c220145074006050322640c0784050700b6036680080c0000344800e900e0121a1210040282049103401403070403410f0101d030480d4100c089165000000c1c840c0a41c0e01015054200c3e008402852a081404041c6401820341c0080240900d0010000806640d01c60048900102c4050001d00c00c0c0903c00482c174918040c00c08049528100c000103004644c00c080c40340c0c199030200544950400d90a1051524031244000c0c074095000754008000300b02c400c84086091b0081c61400c0c01c0c841444043d00c6032a00c004800e42215010340c1c8180940408079510540031500141c02a200103403e03215012142c4000d04549409003456017060306e603208104a0940b4580700b0000c1d80e981c1880354210320402034030f698080c4141c6a005040160a000d54030008005000d81e038400d0300002103100c1003030b0100741018401040e90540e0703044082d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 297865476 1250 297864226 297864233
    0xc12040209130203121914031b0c030a03050714031303030b1f09050114190f0203070c080c04050a0e1c030e0a1112030a08150d020402070f0203161d0702070b0a020a 72
    0x114100d100702d42c00c010307c8500ca010035204d04c1d404000c1000c4040800111078210741000d4000f1500c4003001c41007981d6440452550141c040c18003600c4120028819201c0388250360f06138420380b40038000c1001d000122107540c2d00c04901074241075174511303031040768070280c001c0900d6145258075109401d5101e805503245401c4c000341170b420b01d2030980c1040c014100710300d464a5200d00008404100203041c404401800305508900d035014072480204004070740c1401007804440001d224000b500112421311040e5910b0107090103035441080d89030b085034401410108044615545580d905e80c0310314002842d4601e0300c00d1076103440c0010f0415148440046460a000d0402008580d04900802e0045141c0741d02c01c0c81c0202019001401c0d1100007a0910a142841e910900c0d240074040c2c000b030003076484040c5400c1459006000240491285c0b054002401071883d0314100f401c101e403502040b1090803000130002c1005c0c8030009280700704500440d01c02290100300c10000c0d00c0b4200843d070007410b01009a19 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 297866726 1250 297865476 297865507
    0x32c070312170a110408030a02061f0b0a080406020d06090e06090606090c16060f1d0d0905060706090618050c01030b0f13110417060c1204020913020312 67
    0x501d520100241540d9100140924140e00340c0c0290940700d00054141150b11584568012504420b4290200040001c440c5a0016038240079040524901ca00c070a10340b103004203814114420b401140405104c0200307130a001d003031030581c010301808015103031a035100c804000b2a200c64000707000c0603941d01c0d0a1010b20404112a55203c3c01fa00000c0a00d030030035800062072400d0003408201c1e41080014105011504001d0901c04280d0060090044140b4008890b02605101a078111800000b03890803881403030000354000344058907100c20810341c0c00d18080c030038030780c0c003100c1c0a58009403540311050000b1460f01c02c0c2701d51040da0318440002c0c000b0b1813406500345464441c5d4141090704003900c01c000780c3d80e0070110400007501241c803000120580c000d402c1c05409841d041480403040800c00042e40c148000c03645941071100e4080d94004c0d82d035000042c92038043c82c4100a441703000800000c0050401d2403140f50041c980348071409540c0728660000385010152500ea000e00b1401044070301c0c1941004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 297867976 1250 297866726 297866753
    0xd06150302250203030418022712070e010627090203010f0803070b011401020a0609080d0c021c0c05100f2a14030a060b03010312110d050a032c0703 65
    0x6010502c0b80444039000255240120f000d0a01f0002c5411514800f152555040f510406803c880e640b8000041007180040b6803030644070103000e11819401100315250110b01072054039006807841a0300d03401c0c900c0c01c0720a410a0425240720909004d04c0c0c03a0700501400d96600248003115016a8941c1040c03d6440c41a82c40d512400060b4414441c3e14000b48508000f14156040c80494025007800e980040f0324140d11894050009480c0000310001d000e1001c0090514851a050902c003030400c0d07490484e910000c240802da0542011600300c40ba141c4500c0b503851319240950111130149980001d50021034081c2401409296a00c0c480681d6031000c0803491040d16900211080301030034020301c09070080c0f5142945c034005400000006000d801c0075030190015000c10101503460750785070300e0552968012004000080340c3d8404540d802c000b00000c449900502c030380d0303c03070303040260b040340c01d402600d00c405002220700098660f6407100354440d42c2d440d907420000401465881d1943c240410003002c1c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 297869226 1250 297867976 297868027
    0x70e1b040807090b031c030902010e090901050a15030f0f0303060e0711190b270114100503010603121103041a1209010b0d17041203120605030303040b0106050d06150302 74
    0x800d020306e414246211446403040e06d4140400c5003105480101c0d03049000c164903d0b0300500308800d1100c01d1a0540c481445403070440c508001d040d03c0a8601001d813040c03403000624040054083c9800541000c0b003143c45188a41030220712580c17904541d29161078210346660010300d0030507000070310500400032138074a02c058280b0140540102c1c0c44201d0006402011219840001e0890f40b030701401560784034806220810080101e91441c000940c6201c20950300142e501c4925080410f851030103110b08c0c011254016004110b0004103401920200401c1c07e018095020902c000500044640e8052074090b04441940d41e0700d060440c007245c42c900000d080d10f50584c0c54141e143c04030b0303216201d803010015002049500c803c90000d0061449110b1a040844000700748d50a4104050300f002000d0110b0600d00400d20005031100b0074550742c0d004c100c0e400b621590600d401004154002d40040803020710145000c200e2a8480644421108042c010030b0700190f0300085804016001407400340305250f0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 297870476 1250 297869226 297869233
    0x611160b010b180103020c0a080301080106050a08070b071202010204050d0f2108011206060504020a09051008070c02010813020d1410200313060525050c070e1b040807090b03 76
    0x20703c0c0d20b8980c071030503142e15414164001180e000200040018080c80342d8400c072000e43d2503031101e102c28003a012034801c0d076015101d0880042411440455501c0136296802c0e002410101c2903110003a0305001d181410b002d5560801020400e52240603032000395901a11401c90680758515000c3c240c040000c40c1001000d008034044170700107070f011040a044849001c3d012007100041e0502d07034010b02d0503602140e0701134800207840c14100c5c0c105403220308030754007110130780c03910512800240d61604040300d080e0002100065280015030042060b160450030000b0035003206100da0b4003041c1d0388500503900b80c410310a40b900408039000c00b00300d0500d0418000300d0030f00440c0340ca8509400c0070402c0121210070041d003c00040c080c1020b010314585440e4014205011500306444440792410301c0c800060714201085002c2000750780181c0031030711140b01c1d02c001402044d10303003800001d01ca040900201310a00300c03120600e07510460f800203070028105c004081c00400d403404120104031403c00c600c0600982 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 297871726 1250 297870476 297870487
    0x504030e0609030102040906120c08032b02040510030b0906030c010e040c0201021905040e060d02090a09060e0307141507050d050601021c080601080a0209030d0c0611160b010b 77
    0x90348268006100d4200780c039815100c0d550000040e001e80a00c3d0800ba8645151803070003e040440d0601106c1003074080c41149c042d26840d03070481d68891080d08000e913803030301e20784401c1e0324040f03120101213240031048400103003000e80761b07c0055000150b00c41703008002030302c0d01c3d0f07501d41500d806601584c108504a004090078a002070010380080c0c0528840391055aa030f003441e0510600170f404542c0c14400c1c2130100e042189a41ca0b01400c250414000c1000c1000b5080000e802d606108000c017100b1600140b00c003a1f0340d5a40c410610140250b54401c60f80280c0300d0780500441c1c80100050f22402d03100301ca030300c2551030000b10040d00c6d04002e1820005181c030014180143d150300003040300c105074180d01c000b240030389e00c020040c1c1c40c1c4625460840c17800c0c049001441c0c8019800501503004200076618824aa00e401c414031040e40108070392a5855089110001c4810b4043c1c0e01403155184940d4001c2403070002c0e6425400242c1014032042c001000c921a55010441e20410484c05000d0200300242002d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 297872976 1250 297871726 297871733
    0xc1c090306020c030a031b2102120903040303120506060708090f030714041a09130303090210030609140402060a0e030705091003030210021206044b02190807090e01080601180504 78
    0x342306c982d0900010078042d112a076025804543e105041542c601c505820900c044568940c040d1100b9400103c05c4000007614011038044e032400341c3c000501007800c010f140d84612045900100103250300a01107422024a0b0310306001e5080202040300001e80045605d00c10301003a2051006214580c4228403008100784d650b0001c40c41d040000c5980741c011301a00d0346003e130014888890701a5015030380380344600005038150024400c5d16154481406041c5d000b150010701e5180c03c1e24000e41c0401e043c000d0a281034400c0f0740c10350aa60005086400301a59000030482c180402d403007400340c8820030b00050040c55010000e1410b005c503242c2c021843c00e607001c1d1a040500f60b01902d100c0c41f4a49442c00400341100da01100d6091884058a0482c240c3c1001000d413480e1800c803418994803180014003500d408058420b0310170f1004100010100c444881d07508541c0c08100400e00014096500c1c1c01094481003112094080d0001c0c0000b13100760f5041c0842041c0041d0003269400d82c840c100410071001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 297874226 1250 297872976 297872987
    0x1c0e032203051908130909030e190b0a020322080f06011d1003021009030203010507090e0a020a0306080a0b0108070f080c011d030d0201200c1c090306020c030a031b 72
    0x303c586010201040d004180f61001580c0300e04085200ca03042003034000304143d4180da0081c8240c82c0711351070b406405003a01040c00689050084036000051030003008105600140c00102200c010f1403050702d10f010340c400d05d00309840d42c50285e00c003041d0320103a4090000d10410020600d20b0f0b81a000200325562400800c00020301125803409030000c0c80c0c2001c1243c42d4401b0603a4000b840e03009183c209501c1c5458801040c084451100b644651309000105100c03a000b0300c261816101e1515400001d96541c8403088003940c8903480c814105941c0d010005108401440b80e040c5482c41001c01308c049516011703c1c940707070101c02d810840001d40c903150200310161002a2040100c01d003803c209111407009449611aa104d8501c411b81500400c10345010540d410740c40500c62005800008201400030400d02d47e49004888003081281e0011520f0119008290b00390000103065107001e001c0d80e601e9a070740300140e8018034112203687e0700108205444607010b000b079040704c0e52511a004084140d90354010300 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 297875476 1250 297874226 297874243
    0xf180e1c1202130e0a0f0b1c0f38150405061513030507080c1c080c010f060905060f1c08070c060507140f0a03051c0e03220305 56
    0x2801080301042400407001c0c2c050f00d0404004116460b00c140d5a01d0f400d00340349104a0748513100da450100034843d03403400c0b44140c1c4181d05010305000d006906994513a0504541d02a0554503414501800c50001c5c403d01c50401c1903060203010300c9105005082c3c000030301d180141c2102e00040b00d0100300030004450743c100c484c640608807004285501d0300000f08841010320707003541c0b005020005080000c4481c1c14800011207110717104913540603550b030514640311300244800d00c1c0d11402003810902031500f40c2514805d014020000c3c030346082c140074002d608442121407005035540e128002045018918883c056200a041e04c1c03400c60348e00c0c5000000e420881c440010380320b094070840c1f01e00a00051100b41c902060b4014080d00c010b03600c8000251581c5c0045400b15510300801100c031380d9031880800d248802d10301c1c2c031000300850b41d01581c040d1100d4128078407a8500c40401900c0fa00c80c541580201a50205880041d40c0d031020a20040e91880c1044800d04400d0490b20301d00b00005000040c00b0320 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 297876726 1250 297875476 297875533
    0x60c02060702060f09030a060222030b010e1b03100501080606120711070b04090506150c060103020f010e090f15040905060f0a11190813050a03180f180e 67
    0x150350744210401c4c0c201c240115843c264061044d0350800041160030f90080c1241459203046580140a07040000d01142aa00004100c00c640d140104185e4074a018415040801c03885804900d101300c00d0045d1642d00308550780c580d4015288010030041d45c004054980103c0195405880c01045204507030f1180c202a10317150412086021041d0941000e0091101903c051402c1c555255582c000410203032500b500c16a200c0c044500026610481080403140403c034101d028090981c6941c007000001d221081d08141803101b003120303241c2c09a8407041e0244c415000c50314541050308200b856107402d540c3e07101489002c0c9141030440c0011400c00102c843d0300c01c0c209a41c120070781d69440b900c0000b0f001094080d44900c80003081b40070324940d0940c2e5031803507102d0340d5483c0c10310755031082e400c006820384120014020350004202600030030b1003080d042d81d20742d0003407013210029940d1350052510030350702c0c0c0d0203180000c03016034540b003280949014500d10181e400005107003520448132103001c0310030700f2030410 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 297877976 1250 297876726 297876739
    0x70204060e0f06190510030504061a0d06020f040b030a0f0e240c040e0705030f060d1101030c1e0e1503060a05060a111e010c03060e0c1b0706020a020a060c02060702 72
    0x13051551032043d0301c0024140c064100b205000c10340c0303805400f03804199021110203040c40c00344880084055490703c3d511000401d01c084000d02c0e9190710000350300000c9074003020380c01044003140f0304681c100110f00410301c2d00c000040c511710602e2102c0c11144003000240558200081c02800d0540c0761140c1da11018482c038000e0400d40303659a140302a8821903018074100c650302010084404c1c0c002d0041c44c480c0c1954016900c042d52101c040111106100400414407200c103010302049500c03030f03402640a00c0b0603060840c141070b840c3e10310f8114100e0001400000442028032000c450424185181c02800c0a062490940c10240000b658958682c021540a002f0210b4858902c0780700f140c400411403c0041660ba000c0d6108002c91080c01e101130300b242c4030b03600704000207070420720900c54502228140021008603440c0e8042944056014050010024203104403090070344405204010042250350002c10340142c291040c80400da00b0755000205000c0804030450260b00c803903040b00c0c2d0407036044540 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 297879226 1250 297877976 297877999
    0x703050615090a0e0c0405100e0303070303020d0207051020070812042405100602060411130e0312042d02010e131506020105010f05010c060c050f0a05070204060e0f06 73
    0xc64507007100f0344c3c09100c45a0810040c0007a15070000000c00643d5403d480e9060342e84214034055426051240541d0f42540c0104031120102c1d20070381c0680071000c01030ba00940b5010b850703102c0918055040d44082481c3c0d80d5800407250001070080e0340307581e41055150700c80c02c0c4100c0b0b440395203003400780440e960603405000c00020304000840e401302c0e88080c0018004444042e924100100400b42141c3c00d038004100d840340454403900002c0ca00344200e601c0346045088158035414007854a0000d1200c5607015102c42c02144140b0060024000405054041a14a16084c1404c48000d018588450720104107021251405100d142d03c03801040d0b020708000a81041a0340420b044500c0d80362428100d0b45030021000c00b8500041404084600c00e8ac028051039884868a01c0c3c1e00059120703050218501030000d40008050360815031001c2c40c10704050781030030809501c075841d0341d02290f60368000030b4001610400310b140610604c4d014203080d0000806034900560a84003004001d04502c2c42072000048 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 297880476 1250 297879226 297879229
    0x20a1203090b03040602091302070822080d08090106050a0602031917040b090d030e0a020d0f062f090607020402090a030c08010f05010812160501020412080c06070305061509 76
    0x1c52030040501daa02030341d076460076081c102d0094004104092044803151804801580342e402a5060303642c11a140e989441d440414200700800308000c00704080d00c00103000a040030041c482c000010328140c80e5828a850540c4040342100c034a600040d00c50310790f015043c0070075a4001305a0751009030007000303080c0201c4143c2e006c0e2074104270b10080c2c61844080034100410440ae000c0054000c08001c0e04a9800304280c0c1d174142c064038510301c1c116401d980440075000c003511309200b510b10054050f0115031080f907066119030090320284812500300303c03044d0b9154102e103071411a158090600c4010300c64102920078001504611800b031020b8403403600440d210100c0c1d61112851750046510a0034184034550714120340f17004c0c00c2c0c0c4d448031001d0945000e00000c4c01400100301d003810074030001c840914112084131202041d08110f1170949207503509010200d440351200c1011382c0b010303005503200d985400301c4140031071400b00c0c020115000c1505000c1804541d407600112043d03000400005161240a90360 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 297881726 1250 297880476 297880487
    0x40321020c0d060605040c0908061506090901060c1b0e01060305090102090a230307120821070207260c100c0f11040605010503041109060103060b0a0207090c0903020a1203 75
    0x1e508a074808841c680a03010410030364401d0084441c01c2c3c40c207110300c17040ca52041c0d44e44290b0380f041402e540c211500245000b00000f115540280b00201070606204c03c0c000401c3d01d41000340c014030082011103070801d050254000202c6408001003a2811242c3d0800301c0c4400114018410318040c55100c0c40456650102034040d03c81110001d8a0012030954540c203640c00c55030403410300c000d01c4150007403010075030401241d0441594141e6490100f03100d02983e404181c0da0005021040c49100400c43c10102c0601001070f60088071194010020a03040030521a40c80081419003420690304942c24a03641002007a01d092041d404c590001d8144a28a0291142c030201c1e6401010748101c129114100311a003241c1c2c8407480b500740e8040010a865100540c0c00d071000b5500a40910380c0310000e5900d5140000040394400010714006c03a9155983c40380803400e0708111461000b5820543c028032000c041c0d44500381c110102480c18590440c0396070082041e14589000700c2c9000b0340354070490b40900d030140 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 297882976 1250 297881726 297881743
    0x180f030412231e010207080712030207020a0f0515030106020a0f05120a030501150804080d02070503040302150702040c080c12040611040f090b0303040e190e010e010902031204032102 80
    0x32602022581c1d00040759224055031420014809004541e0f242d1a001482544d090503489100249803949039140e01c5100303105c0700d0045007010380801490005840d0490341c00c00030100411b01c085800e040000704002d01c0028211000e080c1c00a00c010003c10798005804022070350000d1108840180c2070070403a041501081380d42800b03900c0040c48040165160f80000d0480e4042e4001903802c40040100319203151003038401030300968007840b510320f007101c040c1e008220b040d01c00c1e001c4034501580c0c3ea010540780403a402981d6043e500100340360702582014060015003024a207401842c80c64214054040c0740150301c41124a4a60440040c0800415a01c608031030340d0640101c40d155a596223011618103103a0250180131414101c00348078504002007540c0c2a02c40b21006a01907540b100c50400b00c0100c041307a000d88540d1958100d161184c403c3c42825902c0d020240081881c0000b8010304d450304031030401c64499248100000c1000c21007250390f100050f8414009204803001c01d000491810030382 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 297884226 1250 297882976 297883013
    0x100608070c050d02150f0103030906120f050c1809071d0a03051b01110609032b0504080316020703080901030e0f06010905040c0e04021302160b010905180f030412 71
    0x202e0f443d0040160b0001280801c4492452204100303030b40b04c40309481804800c2c4002008150440002c0c01514022015040d500c0040080085c0d5040352a4100d0b00385c6200344d6110740c00c01800030f208400ca55a0b060480d13032002c010742d16002c0b01c7c146548024070702007100814800c2e07448203c05100141c0c7c0ca000d00b010003180c100f03044030800c0060100c2010040d15140405002c5148581041601180440c200c0c0c411130740c81e40514148010141660110901c1001180b68400411422820810b0610450b4000d80c003d07042c440c0c884c900341c8041d0b820640006150410f5501045040002812110445a143c142840e000c610020307001d08291415107110607029690203030900200308000d1603400701c0c4c890ba00800180c1e4856a858620000c04642550040e4220503202507410164031241c0040c190000b4140b07141900300c900d52522840305000f030700b00d0350100d6110402e20120384c8600000003030840070000544071034070540300155628071a52151020240d10504040309101c48291300503860702c070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 297885476 1250 297884226 297884233
    0x7030206090f04050c041d040f0201080406021b060103020f0102072d0305060f06040f050601020604020111160b070b09011104091116060209010f021606030e0109060603080408060f100608070c05 85
    0x18050101716081c0c0050054a89105100c10200124a25114002e0042e03070005661100200035400450352040b00070002e41d90141c00b0400c0101d80000100b60450441480003e401c981d4150f204100409118422039411980030103418815130114424614201c0f6100610030040c001f040292484070289a0019195000d103000f00000c01408190b40da1041c00122420000880c40d005110b0032901309a50301030069005200080042d4003540000b031407000400100c4a408005c2141565601c007180c2101c24106404283e0301c0c01c12060003a0a031304000e00000a01080d5207080201c0b160f40030b05c3c0f00b0400c1305602c4240d54010901401e0468844008866064a025513941403083c081e501c0403002e503000420407001d101c0c05c80e01c082040060034501c44100798206107054812409091020212011135680d0151351000811500c100b200451198501940b158940703a0001e05007100101031046204100c0c0802c079000b251940705105941d19824040c403e034031482e00480b00e000c50750100820a12 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 297886726 1250 297885476 297885481
    0x2030f18030a020a06081819120306080f0d03060e0f071404030606090e0f0c010503070c0204240e010e0907051e09010b0310050102011a090717010e0105010e01020d0207030206090f0405 81
    0x2940018854400c00241640c4d040c00c04203110030b19900c5280c5015141c070180c03229014800030300c0584c03940501203827520b070101c0d000752940b6800742801000300d00d02031150700804070041610b42600800c0014601449406014548104407604540000b0850340410030407100d10205102007006440145030045c40c10012a034071825041c000b0180d00302002d4682c41001041882c00400049103170003080306a49080c1140c640080684082071000d000304e0303000f41c4075021032017a0000b203001138080049108209210303c0c50800c541c0070400b0103030802c40200080900b0848002c038009101012100700fa0b526810411410b880040c0440319100540d030f01240c44000000c0e02c641b1540550700070803080140c601415a80c02c0164220340c0d4101804003603d040001121141c50000c0c20f465214816043c121030000d04819015900c0000342c000a1140980d840180000d50307018030000b100341401c0c0002d00c0c498810f0040a555a890b52100034440c440014a9003020b0300c2c1c180e12160354941c054410b000c03d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 297887976 1250 297886726 297886739
    0xf010c0513090218060d0f050c0310080d0e10030612050d080a020703090902070606030506090102030a060e07200309060f030103110d0b040b040203011512030f02030f18030a020a 78
    0x40e03018040d41c814a420040c404501041140b0840b1410b120079541c0010310b00c8000140001034009161002116503242d050281400042c001c551061042c00346a0707070350749444150482004a0307900700901076401215001c8035160000c103400d1038008200e40c105c0c981e240400b4218040d000e250001c2101a80c400038003810060005481402d11080d62526140c0c1d0f40c0300032178482280240840940020f042c10010042c84c2090b500a2055038000c0c04d020510039226260303203150440590301801e4903940001005941880e5119981c00b600d03a030142048a8180f2003001001a00381d024002580c1c042031504c046031001c00c0003210380d4107801601482d160701c0c020000e02ca194100340300594402d81507007200c41e018508208410b11113680451410307400e0f2101d82b2610b0740e05200500c12a00341d07585c0c2c0d00418003060410052030040c44001c104100028640c60014081e00400c80400155030003400b910a0450407202a100e20129180459500c5044400044c0c80d1100310300000c4c0d008052040c2c04241c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 297889226 1250 297887976 297887987
    0x109031502090a15030c1b030c110301050c130b04030308061c0507080d020606030d27120c05010215161805040614030609030a0f081e0a020a121506110f010c 69
    0x70030107845c10000342e81407110031346820395602e41d16070070b143d50225070800007401a055117080500980750024004003410109003115070a42d004a20060040b440a2601c45007114a0001d08000403540d4101895030fa0040c0000300c000c5e081c02c0c1f040d1a40198915910011901d02d0780c1d040e0000304a40c1420340d2a4801c2d510b862080c07100c0d0f001130068000150440c02c00142c05e0100d00e800d95102c08116500d40c000300c203c2c0400a6010112030b0000000080310880804420481c1d80901181c0c0512841c100003e86071501c000c9841c14044281c01c00c1090403080c26030301040000603402c0030107041e0112001d0481d14001b9800003035106140604c0411000b00c00c07140101042015000c9445d50303116101c60f15502e005650a2100168010180360442445044010b400202c1d41d41e00722841e00d030919200c502d040044481d49001580807408800a80c1c0c004081500c42020b50410442851180c21020768991640682d509018a650485111031001c000c42e0882c90b034440000c104107150000000d14 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 297890476 1250 297889226 297889259
    0x30a0803150f03100c050409150e010e04110f031504060212060105040308040b0a090b07051617100506190305010506010f031e050406020903010606090e0c0304020109031502090a 78
    0x1254440701c41000c19609040c20040200980100240501401e108a400103001c0174000d51003001000d00002421001d03500620b1043e501e200d21301040c440c28860f40c2641440164030803010b04004405000c0402c000c0c10010400318000d0380c4614031410700c0f0000c83c0c5080104005400c00c40841d101300800e00996602402141c844143c1c4444252030320b400441d054091404003401c0403200b081b040003a030301444000c00d40c46002d800d01a5100340d8541e00c1503403a400180c070a903410f801c0518071b058149441c07503200004e00008103900c0807800c000d004c029a5080354400344030100c2d5541001c1081c559071022210030802200d04490b00d95030301c920b00b030b9020b8401510040e0104160309003240c1050b00900451000000618a1900226030b404030103025100c01361081d40c49681c00c10200c22203803000e000781e8001d040c0a484001480b441c0101061100c1801041400c4041c802d0084c0300041c2e03401034840044031b41101c040441001250040700003885001401c5900081415002403464940302c0000d0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 297891726 1250 297890476 297890491
    0x40f0509010801111204110d08071203060b09010e1903051501080d080f1806010b120a090503031315020a0c030215060306180a060c0c020a0605180409060b030a0803 72
    0x250990b61000064241c400e24524a070660205100c0580e525071070007400c0d60300c40e021b042030036001c00304180810915070106e02c060301d60840000e000300034011440d0201e0002280c91404020030723031410340a50301501400307201e1410086840040b0f90303680c0d5105825041d540e9210b070b0180d180d580d20b03d80380c0d40e541e8041034000d031059030440000460036004071b0445684c0c941074032940350350303505c0c1d04158840520051680003c445032a14001914cd02084214040c09841d00410f6a544503051568445e81d40142441a400d08112000c400190040280d0350882291541e00388558243c0c5030124040503e0f00c200700c400c0c0d00c0401c1c94059a940541d10101380c900980a0710032000c00c1c4203405c12041e030100d801030303050380c03111010034039044000c2c010402003041d0005540703080300d0503030382d1303805981c000341c000c00c00101c43c43e40c40c809601d40104251700070400d45c18600e01e007180b03419403649102d4560f40020322a65807081c5040600441f034000d1a5a00c1000302543c061040a1030005c00503001510b040d03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 297892976 1250 297891726 297891739
    0x7110d0206153d02100902060f030910050f18070f030803071b112704080a1404090c0207050a0602072c0a09110a03020303040b070203031e070203011a01080a0c14040f05 74
    0x480401562080a06d00e40d0044c104074900098665880c4951740082c1004480784176072080a20121445c1c412940030361b0184002031440d04002c0103503054290381c040102c0050308880410410800c14150350f030100d941c051402d075125903079280305030b44a100481d02c0b0914600a080201e040001c1900540c1c0c1a90003240c030039420410814401c0150102e44503000411008200450302042c452800b078000c880c100d15007a00380b401201100a1180c0240d84070501a64403441012800b580600000c8003601c42134402d10f441b2442d0080c020340d100150710481303004d110f48140ba02c428520200020340b03070610100f4600000e05101013860000d101c0e8040540c1c1c403600f004411015850700301905001c80e50010000e60034a42415225a800e5102100480e070501c401c105405002d220880c0e4200c20380c1350340f1003041d109c0110780145403e581850341500c52011001e18561642d03a040a841340d00605410400030f0b205080c0700082d6400e40200390382001c0c1d0781c030116000070584408180703001980c00c10b6610 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 297894226 1250 297892976 297892993
    0x3030216050102030901031a0a030c140301110406180f08151b0909060a15020703110603040f0b04050a0602270a06050717070b07110d0206153d02 64
    0x1030015000d90341c000c1030700580040000e0851503120350008403002450034182801c0c00113a80010302c00e04001c0d4070494041500020800c60101c681400c00c820314002c1d0001d111880d10f00501c00801e00c100c0c002ca0080c44982202e400100d4400c10050000d0212009071404264840400715070710000480c548000c0c005080002c0c5024405810f03043c1109040e00d0b4180c2023544000070040e58120041c403140c0c00131401c100020346844052043c9180e1b0a864000d0700c243c40c214184800c80141580c0d401d40501e804000f4480081c0e0403e8501605681041d0402d040da00e45140007401c041c0d08c050090304050003c600c482c9400310420485820071041d0441103400e04d04a0140300070b0844501c203072001700d2801d0002d8000320302c41c2e41c000f00c2c000c03c2031b0110501c1d111144d95400c141c680705942d80c10001c4c040505a04442e00200140c201202140c0018000341c80d00701c2c42c40c2840340c0700398032030740c0101d180d032031501c0000812100c100c40c056800d02d4004000441401c3d20410446810590001440388600 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 297895476 1250 297894226 297894253
    0x140c1b0c151209071503020f070507030803040c060e0a03080c0114040309080c012a020604080a0c0e0a021813090209092103090c150403051905070b0408060a050901090c060801030302 80
    0x1105004ca4040005904d45c1864015080e0020f401122103c1c1c4584000c214000004009200e85005140b04445041c1c44c0e04060910100916107038010f801442a0700038078072410390300e80217071000f1a1b500c80c20345659010055200303400340044481094944011105100070142c000e0078100075150304504032107080301c0d100e0044900003298071040510100e611503281d4445641010030040500250155252aa8a007138a6103010780701e1005a1b09004154014001c501c0c407910031070b030131192140d415400c203074854010601c03031031a001d41148a03503451a00f52005071482d800190800c3c0d001440d03d0954030b0900c2d00f154030f6044441d0b45102120368000c5401c0402130341c0301980e00400141d0300504040c205403040c49000c2e610b0300d001141c17002c4188000400210208a400804016000303440c0d40300003d490718501e0704c01e1075080030345070703100070320041c0414500043d4075680010041400300305500ca40700420f00502d040d000291076410592004649503403c0188281202e2007582207844030350700d040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 297896726 1250 297895476 297895483
    0x6080604020f041419090203060907050a1d0f0a030b0a110301210512040603150b0301120204110405030703050a150504030f0302031005031e01140c1b0c151209 70
    0x80300048410010300c014130010354240c8a80700803400c00b034084030343e030a849001c0d51120316a0341d1124002d907400100708045428032216640c0c01c40d42504140b1b0a1981c9442c0140c400740801042d00200104106415282c2e0780b000f030100c114940181400c000c45440c2e0509003c040310442e00c5444903428160918041d4890800701c0c1c0c100c0704c0300180c00d030751023880442913031504140d220207990511481c403460001142c581c00410041000381c50000301c00c0f90402c0034450020095100301c84d40d40b420300c010469021803003005075a903a0704075400a0001900041641c40c0c0c062a0480383d050321843c2c0000c004c1000c001080004c4900581865080320f030300f66080b01c00d5920490307000740052a04090360107018003a80107541c02c4042d0000c5004d045858801203494402c0341c007104984600e541d00c1e542d02c002c4080c03240da200300000200d9890545070215002c480f501c00d42d103074418480510070450890703540c18400300c4801080107160101c450b0300040b10040c1a007103c41e00408140c40b1034046580940c001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 297897976 1250 297896726 297896737
    0xc0903051e0c10050c0613050609062a04080109050106061e0504030213090615090c080c090f120312310825120206072c041805070608060402 62
    0x248020095186588240158001110010b43c18850103114501e4002001d001e211b2142d945480312100d030041c00d0030020b281c10300c0604078030b100e5080030f81031052960382c12103100c80810b00e0341c010050940f2070003403880c00ea128550041c0e05651a0000b9a01001819004001260750aa540200c20030300300340010700204040c81581e000c20700400c020001420041200c0003210145040040c950860303031a600c05a030320701030030b42c0708003032111409010840e10340c81070800d0a041480c00c4003c529060098005921030a094281f050410710740203d941c3d50b9405100d0307940c16004094a8030342c141420140f4815400f51000504000b170703e0104512100d00c80b1142c440d840c40e0080c00c40c5040006d407a60714003940800303001182031610b588400c9201c801d01075654009813181c5a0042e103003004040007400c041016000e581003025100c10031f20145e1855000c8443c0e901c0c9030306104108110707100054018060748030304070b000d02c00c2900c880d001d0090114100e001c032150f41d12074030401c2d0b03a0102000201d1145 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 297899226 1250 297897976 297898033
    0x924011b0209041a07030b01140c070b131716170606090a0f021204150b0307030303020a0306051f12060515070212031c0c0813110d060c090305 63
    0x3060151405440d06501003074105000c0d45503403036000310502d074003410410102c41c103201103a1200c2c0b8840780c550340520110030404041000a0605021106854440340c6920079540e080c0c0c004076600280401038103160004000300e0000100400c040461203403900c0110f64001d980e401c8000c3c0c001a100110f2644062050105010300119500c55003000b403141d070301a107509015a43c41014032a00b42c41440204280714807401c0448291510749400d1048641e2501c0340e1000a09100d0150341c0381d180092140192541824056221900544100c0c01060340da4003c603840910f86414240004046500321043c21080c1d641c1c814029800b0390540a803400c1c0d1081a40207400006d00c605914414070140803154802841200301e644070711541851500241d890815800c680d00b801c03265070602c0d01c03a0422540c01824805000c2c41c24a004131186540c2081c060031001d003011401d021980c5941480d0f5541d03030320600400030319601400052040080b40030880d442d1090810303580e40c000300c0640b2070400071407 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 297900476 1250 297899226 297899267
    0xf060305190c110303070c0c080102070314221710060609090b01020f07090209030609060601080a02071109010f08010e0c061603020a0c09051504020a0e10020705092401 74
    0x4010040c84001c0000c94020b0081000a031480c494607242032000318007402d003617610441490b02504060381504820384c051025a0700c10001e20000a40249980000c03c070450314840c0c880384501d42c0030400000f041810301c0d00f03081e101008141d959603581c0303999a00008000b207a05402502c2d0207601220124010f10b801301d48048800c01118800c0d4120492280043c811344002e800306000007071401d003040d08041c0d582c40d00400c41c51402d040800c50300358010100d100610faa42400c400107401a40b015003000141d03900000c203482880000050520300d083c000e0903c040940c2d4510287c0d0b01030089000d000119401c02e075104003100e0001548a903044070003400b0501c1c09928080c241c02c2410580012015802040c2e07062020401d11045a001000304040102c0c851a141c03070203100b06843e010710746203c3c40c070601005114961055510b11702e41e80c20754000040c525490f005925021159200c070f58080401020000c08ac941450504c1400d07040242515211081400541c0d41540f0b0340764050242c0d1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 297901726 1250 297900476 297900511
    0x1020703110d05070807150203070309050105070602090d0b040c0f03021c050c0325050405010e150a090c0908070b0f07030e131805060708010803070b15030d090f060305 74
    0x581031600c5600420380201010411001070b62041d0801c101e51707000c03543c00e8028003401c0010058140901c3c0020300300e0b00c060752505809650280c4005540c0c05402c0c1048000b00700c1a0410105604485d0a0b910092450103100310300e1400800d15182110115420090750100107000c3c070204440805990780202809503400300c0110110f070180d64240240c40500c00d0a42400312510140701d9100396034444100c44104c120343c0c0503c400b41c01d00135480107001c2d929140040000c03a00c42e070743e0745070862010303100500c400c841c400000d406422260060f0b411646041a402d45041e042000340d41212040707016505251350311601500240240218404401002c0140c007000074403c03016507860860042111501c0c1483d818458111351004400c29944c150800164090180030000203903c40c0d04c52401c00815810620116164007411600511840010000c141c141070801a80440b440000d001ca0f8441201040e00401c900b10078864026080c5007481d001c1003a620a0040030f00c205048131006a110 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 297902976 1250 297901726 297901733
    0x30301060e0103180b010b040e0f10140316230a05030d050a020106030c030308070e0a0302060a0e0d02040f02030420030604030e030a0212030415020312040201200f15090c01020703 79
    0x3002080007601139404082c0c1d0144c00100a0000240600040700e589038030f85051211100f950800509095024003400c000c220048080c0794118041d20320f03100307002d01e800c80c400000c02e00c0e00d585501c012140294100000c1082000c0040b0868842c1c01070b0003d021324a207260520802d130450340500da4040d002091840b02c00382c05034004044004a5200005d880c56a81e00c0f504448030840d00100c1c0040e4820050000d4550300511044140201711030301e40c812031441d030005102e4494549030f40c05000480d2541901c44d038592100740859600175109110600700171004c000254400ca504546842c03a105078020500f0a01d924041c6500001d80144003c0d11951029699030400d822080e07454403d816103c00161907a60010740e841c00200d000f9070722203080c41c400c06403038164a4110382c1103600c140b020701c6407400c407054520b800c9502802c0064410140300c038500c20041a4480707410712486880d81d000c06001000900100c050202a0711400544804580d1502c5881003150380d070044e0300085003880030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 297904226 1250 297902976 297902981
    0x303070b070f0314011206110412121709060a0c020f0303041b06020d05040e0a020c0a060506090903070302100203100b0c0d02010507301503050c1807050a08040501020904020d091103030301060e0103 87
    0xc1d1100a4907a800c140e038401c03400400c02b82c800002c50720411017101401f40c20741c0000c040c4070107940f0000208440d1801804199a8000040805428544503100c440300e1328028800c500a203800c050599030360b4502070901440d814625115610180d014401c0090b180e0301c045010707074041e070f41540c0301c41c80d285c9030120701c074001d44010302101a060350801c605846184100041d070441072151070041034501c0c1c1003003005030041c0c2c01803418280b42c00420030b0000299002c5092a05100218030060322516402c191012000b90350b0050140035000145440b2003500c006540d140100c843d5000f8401940c0c0c14400f112600d5043d0750034002c8003000e05081029004500c4c0b100280581054006001c400e20020900069825072094034a41c1100c04403010742e003000741010030b010b107501d04406054206810014018070a100070207040081706008035080003021f40466141c0c24000b00255152100c10780c0810040059110484040094000064231070a0100540341224200c3c0c0768800c003003003685c005401 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 297905476 1250 297904226 297904241
    0x30e160e18330708100608190f0b031f0e0c0109050607050a170903121801141e04150906020c0f0d06060605030714090a03030e0303070b070f0314011206 67
    0x81030100b1107103018000040c4400e651040d04166911001030400200c0c0c0e13800c0815680014081003c000c041000040b50281e2141c0d001e06081c1c0001540101d0403280d070001c09091110f145c0c1401241c0b8240c040c10210a480c4214030080c00d4100f045014141c441503075080b0840841e4046003412a04002a241410160081a0045081c0e030200c071210341d210f03072500d2400c440d0303032400c0040450b003c6c1587c2800c000d20000000c6000d040392401d4215240380f00c264444000c1c05040080d5102100c402c01081c0e000d6624282c1020401c0007001c400c600b0340d100907007050107444040325451844400407842100c04d40216200f940261100c06031100c02d000c07111540342c806a401050640740d40000402c00d204100052859648840e10390415410051001001410640f21010705106030340301c81e541c44880c50100e0741c0c1030404000c12031540c40803d041d03008641000d082c901101b8104407480d83c10015000c98151503580400c1104030007103100c00655802e01814490003403039140c240010310113a11111 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 297906726 1250 297905476 297905533
    0x103120309061b0504090b03150c0a200705090c0909070302030621010f0c140307080a1d060105010f020703051209010302040e0a09060516020a03030b01030e160e18 72
    0xc806403e801007200d018109a40b8000003040080d00308040c0c40e00744200042d6680c102c000c1d1420f001503148001e503d1001501c90a602540007446804449c01402c0481c1c5502c1203420610040d0f4600c1d56040d1034945510a10b4000c0050500045580d5100d008507020b0710002458010652104a4110000c0d00010011034100c000140703040400d41c08003e07002a039200150010502c054031902c040b0680d040c00303a01805125205008000541420043d41d50180040c6440183d9588812010028048282e9840060f0003825080a059500424154140c407402e88400a018a0203d0100e80e1200280b002818680200c4c95544015904c400106050141451701500f065110303c0c003540c030644142c0c0c4029000d540e403480320042142c5400b560b81d0090200c6200b10f14044003410180d00c400e030b4440000d04050381d078500d00700544e010340e00007030a20b5206401c4030460203a038100d040400085002e0040d6901d44a000140f0306038508111501c5401d40c000640a4030764000c00c2d5012a03440c1d0303060340 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 297907976 1250 297906726 297906731
    0xa0609030c0b04270b0d0b16020a051005070509060c0102090a0e070906180302030f0d120902090604050a060e0703200405010903030807030e010c080411010c030e0f1903080c070806010312030906 85
    0x51700945e84007042d5040080c020305844915040240c051b01d5070f07052543c00d2005540041d035800012a6011414000c484200310380800c46907602c001c1281c00b4480d03c2400c2d540050007280081c00003205501034810003005540100041303482e202c4000c00c4800480d9134800144002030306014462060018806080e144010850b070795860358002420b09000700040156076005c1844801001e40c81130780550740c0900003208000e481030580206002800041045010380d4444d004141481042d620810040c480303158895043d04203a5001009094111080680c541c4044001e10a05031030008480803a54144c5030310756858034641d0305445880005008805140c1da5501c02105000203001c2e050725181d044e62400780b1480e19240550a01090354117950410a0811500c00000d402000001881004903000f4001c03103420350020b05142c002003000107080c0c1600364008200803803540500610079042c07065690b103c0d1540042c1e544c40d40c00348000b4001a01c1000000100d81c000c0d4083d012080c01504003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 297909226 1250 297907976 297907991
    0x3070204050c03160503011d06030f1e010b010516060c050f070b1801151a0403060905030306010801050904030c150207050a0f0b0106030b010206150307050a0609030c0b0427 76
    0x30200c40040b00d111031515800001c0029151507101103001d0251641131044c25941401c840c0844980d00c01f032200c0030f82c6154400700d000c6540c10414201303600c44500441d41070409103441041c8000c50f0a6600e82c2c41d6082100300c000f01d6000d007050790010010510280820300454a882d0050b05030020540e0610404020381002c00c0c015100904249011700c85036034003810000c1400c501d03500000c1e61004140d2509400800b818180e0048100700e442103144424821160040000c02d0311880d0300061045107080c0c0c0b50820050080b025600c1200242c840c44600da90325418801c07a8241141c00a000815403e2034100042506a18221000f1000001410300819603107184c0351101c41c00c000d80d090840b941c0d9010801010f10004c42c0540304a1034144120242d100020b581c6080c06850078100752410f0840c448a074608000306001420001c0c08050784640d62003003e01142801d0000742c40004440c02c000c10844a250f040f501200d510032a401614581800e0505040400c1400006043d0b02e4101 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 297910476 1250 297909226 297909229
    0xc0311030f01030302070509060906041515030e010c03090807080703050d140612070609050d020315070c05010b0307030809010e120303160206061008042d060629030a0e030702 77
    0x255114000c1c4901d140c59039415424081c1c50060b140e031006100c1e480400c00c00c00e031511a0380b100c81c1c0064042e0b8020031000c610024403601b156040d003015010120740c0050149580c0d141c2c01c16940c440700c6900811110541130000c0701900c010380005843c0c071034104111030005910900034601c60740a454518201002031008070213603007441623002840300030300b030600c1a00c3c50080d0480310308a401c0c8004103004c80c0b0b8400040e0003044588106803150003448160300c15900e050151100324118503c292046251103074001c1c01c40401c9410550b050f61070090f841489060004812040ea900f0118850801008000441e89001204211500f0100c503117090042c0090070000356004070002c0d004440d05071400c2c003000b8a81440200359611803d2155070740403090350000b1200b41c0080d04802c10801100c107501c4414034000010a0003241b04111201d0754041c01035943c03016055805046841d010700d0302c0701088421442c1803046000c100340080011030086805039101750780d80101c4d481640c0c140f01f02e640 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 297911726 1250 297910476 297910511
    0x7300f0311041508070e0f10020a0f0b011701020f0904021b0a150e010212180313030c030308070e0901180608010203010b0409050c03090c0d02011407030201140106020f0a02040c03 79
    0x703000c04910540500768200796134000a01e90b5101d8070310b03c2e003d031080e0415000a4400076000007814001c1550145c00007541d0700c00d2040104040c0c00c40c540000355100c034a090180c1e078009110f8185010460720041d0344020060086400859018010030304095480c0e04101c001d521018040345001e54021244009400620104142d94083c0202405030491211a007051704c1c0100ca8802c07550744100b2a80e1b032811050300c2c0454003c0c0c03103802402020700600828614521a04c10030142c1c50700c0100002040003c08600310041d030703100b035139664103d8a0b20300082d81c40d40e0b550034101c4e900c0700b0b004006105200c0360315018060519403520100d46284d030790410908a070b000780c010780c0a641c800202440603140900401e0741000041c81c00f04d1440c0f0b004400390340c541c144003401900c55000c512444040d60310500039a80c1103080e44044507a40c000500d40640208080f40750400000d42003400084d036540041840440c0380703400405050116950f500300001491101c101c107003450360355900c0c5492a000c10 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 297912976 1250 297911726 297911729
    0x302090406052a0d09081324090e1306060b0c01051510020a0605041505070c0210090810050405100e0a03080105040203190b01030605040f0207300f031104 68
    0x1c00c40014541000900b4444081d2659044120641c036001a007001591200445018410303d40300010b80303000514181c0a14030581d0b44803c5414000343c03010076103c07110900c8000341c00e82803891701002c1c0011402568030042e544030354541d0340010000261054080d08083d0106440307450000f86260b10b4800d00a031b640c1048103280b0319a0b6454041110040040030140b9640404584a007521901c0381d074025070380c4010f41c8004003000d45810104080250507041c034040070101031030038000c51400703a00040038003d512809900c0b494110000d40c0c2e00d14041c1c1003400c10385030318501a249071280e42100034098100035004a42c507205005026156101606c907501e400701c3e42501034001241903060051807464180c200390302c103a204109110744409000080031240a0000010a0402d800001a0014010755000c95009420704001c90713180ca10f1a8014000396102e425100e9019040e030441006d0a1010314400c3c0b055035a40c0d24003580075004034a00345030030b5040e1034081680d140c917095007241500203 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 297914226 1250 297912976 297912983
    0x601030e0106090b0102070806280f050a023006010f09050307120b0106021b0f18040605061302070b0628290c120f0f16050c01081905060a03020904 65
    0x255600d0810f00c5d039040c0f00c100000c122210007045c040c10511440610a0b03028070500b018603403150340c1c401d1040c0940d08038524107001d0050420030b030314004a0080c0030398000c1c00d00d5031041a40d400f500300900134054107807101142c0498035030b0542c1e50300c00040d1403c0c050f4a01403818080d401c00005103e41d020071150014209402c40c051000d1a98038000c056207006812101c2503400c122207101000140d18200c00c4009401c440c8182001c000d400844c4081c86050051800592004100411300881d0b80000f400340c41c00382c46800c6004d0380c130413a80b01240502c0a00900a0017813030f001c11994a000500e55840c1e40441c0302c6004401411110440c82006075409090540045000c03100340101150700c401d080140c1c8500549014940d4090342e840d0b0b80492030000398000080b4000d003001e18198292420b8801b42d89001d583e038100d9542c1a07540710381c001d000f1a050702c60701d41042030a52042560a006d000c0c070074a6032503914165020000a0700740200b880e0740040000e6400400346e075076110541e000740d01 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 297915476 1250 297914226 297914231
    0xa02070203160905070507030f140409141f0501090e090f03180307140303070311030f07050f060c090a030f020d0803040b0411060c0a060e0309060403140610050d020402030601030e010609 82
    0x2034212000f090301c000510794002e12401348003003000300e60030226000401c04145402044c146500c44642107501440e00f05940d02468100c44049041e602000e03180901861034512001e11200808a00500810b020312800a400d2000c200130100d01c2c650180c0e00088a00241d03194041c2d0710048514580000318800326544200c00060601c1c1002d01214000e0030f0003c030811210541d040101340c1e42e00c00d00303000508020341c1c440c01c109070a9007071040c1e07000801c02c03100d1796550301c0940c1030240ea119444140e41c2e0701c0b401908003062240d131041d0119200c001300130304240d86c40b900d540c0390b090140c81400303000c4c1e8020114854810010303215200441c8607a100b0b600e1094141854200302190b2006401d14a0141c00100031002c41c4e240d00049183c80c0c280c3c860340100d15180aa40c051707041d4085c000035281c10150202c0c001c810030158409403412144202c0031647c5540e02e0b6458952078482c00d104040d04404550142e10160078141c000703641c00345c41810041100c3c010405031600b15556035010480d85607 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 297916726 1250 297915476 297915479
    0x3120203071127040606030501151e121403040b03010e01080d0905031e0a05030f030910061211010e1203030105120a08160f050706050a030f1808030a0207020316 71
    0x5002c03001400718501640c041c0039034041e4075540400c0440c40285502c9030441a00000d00300012034100c0005564040000d2040d0340c540c0c150721010015078051551510446c2603002a00040f07400c08004585003010160b002103138546400704003101e0340c1990007030760000704001704844010100450080ca60350801217010761404908038203107118040c1300010003002680030401070391f00154510303110220101b0100c179a82d1544d403170307403030100000c030020a2404082030754083c04803401e0107140b055241506454003d200040300c0c00c11101c050080a01c00c2c90040114000b0070000c94180303400c8141070400b00b282d0b07040d0500042c80c0000c0c42021001a43c0000014000c50400e085084d400c03d844000400201c64070b90344c1d40380d00d030092040740c1000d02c809503080c4082c0203c2510710f0032404c3c1c1090a85071800d0700c59100601e65880002c900700440c0c1030001c0e0404d075401911424111150502c0900344070011607843d1525980050286540150240320f2040943d5040c8841007107969154403640085 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 297917976 1250 297916726 297916733
    0x906060a2705010314100308030a0f0f020d060e041a0a0b120d030f1107080a0521010305060c030f04030806030c0a06020705031b030a062018150c03090103050606040312020307 77
    0x180c4400042d02c1e1700c6500340041c006100f05840e01c86091707aa220002030707220f0392900110380c024004104a140050f04160b03da48100c40c07550b004040142d8200c1050102540341c0d2441c084109098500405905c44c840360151580c84406015401043c480e0f4003003402519130000600452641c01a4220340d0010070741003071072a405200d544000710104e40b05004c40040090142000e00a042c000b4000c040300082d90020a4070800840300d0340018a680f4484186001078800c900f00b000b4001280c0600c11400820080035841040c1e9110303002001109869a9843d42e007184c40780005000141c01d80309841c2e02c44025500c0b15030303610103090700343d0081a4545c0350004040c80c06020b4101e41011594805103040d4a440108003203a4090300140c2c04200c0750500307620317400290a01c0301600e44c0e0250100d80c0000e102d00745101422043c1040324400e000849802c5801480c1c81000b051140c40e500c10050110307194000d4001e01da21010041c1030720704007030f070720b8440d00748070328042d00701c1d04c01a0000034569040 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 297919226 1250 297917976 297917981
    0x90a060e1002010612140a02040203040f0c0e060d020f0a0b030109020c060c03270a08030a0b0111011109010c0519110306070918180507090e0f010504020906060a27050103 75
    0x1c021035100903c601441c142e15040a94407600015055072500015065611360821144800981c0640115503d1402e41884450060703400d200311203403048030b070000551400800c0d00c94010700d401040c0c404038124079400c11654820303641c261600300616510001d91503060340c020f540241450740015940301c0f03c90500f94180f420040c2260000c0c24148140700c2e10072003064a0700743d040d100d0a5140d482d00d90240e0680d00c1d03c0e10700040108000800400c003c600b82c0140c02a6800b407000b0388070030750401d206000359801e0300d290318902c0026100c2404014040d602c28200c00028500a40035104840d58a035030803101701090035402e560800c04000e8441d21418100010381e4400010310700380e948603040c0b40202441900d0b030030300c2d100c8540c2c030b40d406429004402c281076018954890200d548840d0364112a4028102c40341d01c41c0201e00481d01000420310301802202c7c03055500800c040010358030401000800d4003d500700c01c0400174210080001541c20351242034010315184010101185441c000406 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 297920476 1250 297919226 297919249
    0x50610060c050a02010f1103030109090b070804030804060c051e03060319050304090f0b0301020d05070906180e150603090f074410050103020f030109120c0503090a060e 74
    0x10481c20081d0740020481c00700b80e142c41c00f075092030000d01080c0410000c54001c20201d20a036860300002000150150041d4401c02641d40b2a6400540654400005031054402114050042350900000070001071656001c405080d52a00b002c5040c183c03007500d58040d004600300801c6074850b0000c14450306240800011480c80540c0c124401d00000c4d0b903444039264011b42c4204e140c0c60780c641644075171042d600d0700280d0040c0800390003152540c9500d01001c02401d4103843c403d01090b98003001007446446015203440d80c3c5030811f43e4404240c41e01c42c588241000c018001d44200254000701d401603601d1f400154080d43c0000001c003802d40c5030402c07460400b207c540c030074180c0a000214401c41c0c5c4180030410a2038000350740c0100101441d040c00c450b0f0310352440000000d039000d542c194040c0c0403001ea0001d4180c900a0b42d80141c403a0060003030500b2640440d038054001140c009000141c544074108041740c0758401c2d1f00362400c003050303900402d0111074540c0000020540c4e036803900b000b504040d00c8415 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 297921726 1250 297920476 297920489
    0x302120a08070303180b04120f02060106020c090a0b0a170606030d0801060c02210d09090213030210090915081006030308070e01110d02030307020d0804150207110d050610 75
    0xc880305281e071071a03014400d0350001000c0c15140c5070b112120035802c0b03005810545d0868a80364092403c0e1814103030794000c400400c004207020300d0a50400610000340c03141070300c9164004041c400c014604100e08038034010440810543c49a41085460302c40d0b00408000741983705d40c44400c82013040070301d030500400a20302ca000380d1000c002400c0d22680300103000e04603003450030510241c040034004100440c0c1048454180c8a041c15240c4e0004200003840c2c00c04a03102da40c2e441070342920341341030b002a4843c9100358445907680301014400b61800c8a20742010546a040011610707544101a42c10f580000e500e5410494042e14100444281840426405034070b80504215240c1580c0d070142040c2030180006040129880641030300d170740500c0c280e8034034103440c104640340d44503d88002503030b903401240c8100050040702c01d0301701481d000b4180c41c3c0c01154030007149043d101d060300b40382000350010001514207a0300e01500201302c0e201d403170100c0042d6000300301030000740c6018002140010310950285 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 297922976 1250 297921726 297921733
    0xd06030302030c0d020c0a0e0a090210050c0705010e0303071e0611030604050109140a180218090f0304140d020a090e1005090c09060405070c0b01060c031e0f0c0206040f03030306030212 81
    0x51039548040018094400c02542d10201e6110740c0203c032700404007090003e40010746400740c00d00e02a0000041d0013000184001c1304c84172500c07030f00115400e0b098521120b0f0580d0040c415800010481040541400501072100c605103510751075880a90340d540c1005c04286400005018035410680a00d501510507004140b00d40b942c4d00c00c0e200000ca02c020400d28107650f40f41300a450b0854010035034140c844d0024111001403290f1140020161020f84000c2e42a201e0604e4003600300d0004001d940403281719403c54052214030009001036400300542c12680621001c03400306002c403c500c900c820081d0090300400c2204421410f06046034000740c6108070507400707401d08043c60380d100011107238081c0302614007141c05d40380c0c408150307260781c1d2844000b00658108400441c46950143e00e03034610074020b54402c4d0b803e1058800014000034941c0500000441c90207010180c5ca0203280300321080c03440a4034141c50595a0014454280a5900114000380d12104204258a00310042d0b070141c040b604c014 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 297924226 1250 297922976 297922993
    0xa060303020d08100504060e06041b02032b0504050c101803081605030304081c050609070503040212101e020901200a060507080405010f060b0418020d06030302030c0d02 74
    0x650b07180018100ca800708083c0302e001500c507000c0c11004000614000d00b0601803641c030f0301d2404032100011544103000c0e525000d81800180e941d50724100031100507401943c0352815030a160f511000c4400740c000301441c00080014600511807081602c507e0244000d000741c588800700300100e4aa242102c0400c02003540d00c0c580201c0c031056084070440b54048003895403071407445400f560146600c4c5029107540000b104000a00c01c0c2c50000b891400c00f100004400e0400585255080f2002500c00765044407845000818050099000310707000350004003d039051201d91900980f810b40c1445402c4001520362001c0d85031051881600c2000310312180041d400d080411000820800d016103041a0130b1081c0c46480c0105a000e1204004d4507811403c18440c5107003c07030000d000f482d41550202d41941c82c050900e02c191200348511000c0ea241101003a29007843c0c45030b00084000c441c42c000003807690800200b01042c04a00c10b200045200380c01441d1684204c400b09410449500f95490942d0058404c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 297925476 1250 297924226 297924233
    0xe06060603160207151e0512071d040903091403071409061503042d0b0402040c1206140114040b0306041d010c0e0f01020d080a0b0102150118050a0603 66
    0x3500da02082124402002030030300c000880c91304146602107039016503101c007009022607001c4e40c010300c5980f0380c5520082508502c041100c06200b075050070110602d000303010a00b000e10480e0001c91441114020440407449440028111425400101d000c2421104100300e000c03103400500045072011000742858929045580440c41220080148558500c038000380896588030030300d0020f0030f4409000e03a00c81c03600d4a0440b203c80e0580c0110701014603e21030107011035124500402e54240e000c000202262034550070b00c005441c43d0038020050041a0b40c42944903c242d1103680001c0201300c40f0301c2551607003072002521610720501e001c201c2003020401440b40340d10075021030ba00f000f000c0c0c170300040d0600401070780c05601000c04000c03115075090114450207a6803001c22a00880011103540640498000069030f494040c442c4000215002400184041030705034480304030010180161040001004008a002d08090b0848104072003841503840030040700d803195660082005108009460460300c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 297926726 1250 297925476 297925489
    0x1804060611030d110c1501140a060e101e05030402040f0b03060708040501060b0d050709090b01020d11010b061210120c030f03140c0102090306150a031209080316060e0606 75
    0x340700443d841c0d100e041c0315075680000802c640c11100240c050718402d0b42e401034454204902845595910505813102e20503900e0102e4120041b10082d03110810840420024005045808404041803003558181c0030003240c0705000c40d04448865a035016600d117082c0c8104011505079041030090a4903120010142b42c400141c00d0b908966903050550096560b0703e4010701500395600a070290303400110303401d140940c0b01c0d0802409031100c0d489492089440308481c40444001d007505a00583c0000c0300c0702c81c01c600a61410084111761030002c6031901001010a00d29417000418000d05040502081000520490308030b01504140040c401c200c02d07581c40b907440312074080c00060b046050705400741040502407002440c00d140720111041d19a4002410a4003c1d040200414002d01030640091102c58004d510304400c458000c1840171035038115150314905000f500c100900b805441080402c05000400260001c1d4102100c4400080a0392600c002070310209111843d040e030100090140135038414 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 297927976 1250 297926726 297926737
    0x602150c131a130e010314010c0206130804120f0311011802151b251a09060c10020d0b0d021005090d080705070806070903050c010e0a0902180406061103 67
    0x250709800b1000c0d4041112100751203852443e04031210001c800051140050a1a0303048a02904001c04045c400c0b8000030b0030780e0280220040141c01c00c600180c0d1414180042100d041e0150f001c01d410a0384a015115501c1c0506400b0350b01029505600702c100759104143c1b4032f0010001c00284002c81515800010100b11490021310400310840c0b0107050000ca07400380c03191101000c4054040d6003072070b030441d41c45a01d650164080300640345c10301003401010750200030494187c05100c0d0707000a07111414101582100001c90f83c815010440404204001c01049008a41301a030040e507980016401c40b085404440e102800340701d10754140320243e51102444d560b4012300e400c00c00e555901600002e5008504440d0080103200c021904d6824000c0008160301654824411102607864032882034071140700e10710000f48258021845e4650355481020039010040000d070144015580380d40030075040ea04504813a40c803078041c0c6508820507141c1402520010400c5081081410400000701c5032a480b60 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 297929226 1250 297927976 297927989
    0x1d10060c050a08030a020706020a03060503011b09150306030b091c030b03150604060803070b191e020c1009060f050c090f040e030c0d09060e0609010503010608090c04060602150c13 79
    0x800020141d178150380440c0c5c2044d030320600466a4480305030014004181600401d40690f18206a8203000350030205282503082d071a403120809142340601c004480d00b51030100004040d1941c50010004e00240704107405650807102230032109200c014030015140744010b1500415051114602003600c000c03c100401040c07408507407207076650741d0012602400315035200000b98071001420b0003d0000700c0c42d4040c05902c3c1d548410164911412241e0259403024042446c66030784114404034640c51503000f0040a0701d04019902080130f800080400c44040d440103840c05078a0b01d000900f5044641b00b1a64003641800c0910b00348000b290201724107407003942840703000c4e45d501c012100c502002001554030384075003c4111841a0b0500c0340040562546110b0714010503504015a0302500d050003d403116264185c1d12681560319050088481030310240620310346008407008681e0725151070143c1000f80400d50020440380c0788401d800048404010303c4500b40c1401448006a4000b14417036040440c0c08 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 297930476 1250 297929226 297929243
    0x1030803060d0303061502150604021819050406060e01260a09060902040504080c0609010c05180d0515011a0c0309040b0105040e24010e030a02191d10060c050a 70
    0xb10718042d002030072160840c0749208121900417441c6640010204030310350340451000115280c1d00140800e80c0182c007600314884812007008806400d100c44000074018140354a03600380c1c4c0d030700e001046c200c2e8119003208000a01030750010354103503041801d541010407000d9550302038411007410401d036480040c1c554140345458428882c1800107a410561600e034009004100509203403416840c0b69021012501d0103000380c00004080882c10300c41c2040f4413041d030312081e01d4140301c12040b802d815081850f003030703004c0000600880451410000c1c0302c0000520b800543c20307035040205041c0701009090008589030010001049010004410340d90000e60030b94001c07502102460050391030f80555080303600303420040000c00c40c645c0550b0004400d503c1054070f1001000c00340d80c1c01101d0400c921001c940d010340c458007082006061072582d405220484510808c0c00ca0784600b00d500f01881006244480500b04900784414038003402401c100070f060f41e00382000c0d10080fa40d5516228280c441e4090070340e00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 297931726 1250 297930476 297930499
    0x1211061510030e190204150806010605031314010504050c1e0904051c0c030f140910050408030a050310080a0c180f0c18050402030c070b04020303070b091c03050103080306 75
    0x14080d800081122840c001525802001110410080709013400103a01c9a42009000203201103803030031042c16103058002510301c0703a0805205680e0b0b0307030001d800928902003100341d20f03010620000039001e92140c201c0000c1041d00341800c0013817500002202d9035100d00d01e400c14035075058610180c48007038844180c07039025503a80d42c2c0c20000e0070040c4440c0b12441c00308040c0c0c5ca240c00341354014010003180d4444e4883e01d50184501b402210000212448070300b80c05002c00c01c0c090f4520300728910100c2031700185807492070251a2601c1038110740201244d80d0200ea0048140003c480e8101c10b02005402a0001840c8040035600c42c151413217401e10a0f28540100c055040b516088240c1103520200b00420080c00411604d040c0100fa50440008400b45182d0386503010030146414003c03a4041e0f440304010704e045c41c5c00741d1101a844d00c0b01920880c3d061004100d810001054409118811a80f54000c2c126401c140002c00020385858440f9004141c500001030002402074410b5a41100c81030b076003102c504 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 297932976 1250 297931726 297931759
    0xa150302071523061c0b0a141003031808010c0504030c051203030c0d060f0620060610140d050103060b0307080c060d1e0905010c110714040902011202030412110615 72
    0x442c080c0050f07000c442e0802c5241002d00c506ca44560b40200e600410803c02d44201c10716000c00041c0c203130313100e10610b4000c450400100f03125807149005890404400142542c0d141c41c203030f003111455803c034404681d005c20100700340b014489800004080950301d240d024500c1c1d1004035124800101490308840300401d4010700c8800d55031001000d04222843c8528054841c00041c01105400142040500720585140143c120100d181c078000c80e0003404001d554610b8020913140d0340200d070744462105400b4404070319042400d008940c000e501070500002c149250106050820403a07401415a50f400582e00c40700944640003102c0902c0b01203200042c404540c90090710454205d0700c040404682007404841c140001075000d504001c0140c0c4131485a013000242c0c0c903440f1a01b0740f00310086440380103550b503824201500309070005441407502d40c491183ca0150744c001ca80041c1c40c15242c1100040605621640203481080740024101c01420300b483d111403403201c0c500c0103146442c000e43d804020b12495 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 297934226 1250 297932976 297932989
    0x20103050c0c10020d0c0309020d031d09160e010f0c081b030a030515010c031403090309100c030e010509061819030b040b06100f0e0a15030207152306 66
    0x201c0c01c2d09003030300d4250740c65404510194104402d080011440d150001d41d00d14002e21a03084181d9014104151800843d1002e85100d10606090720340c201c08a080780450303a643c10b036481e101d10740500000c00300c0c41c41300c04010013800741101024144850304c200c0f20703440c5800003040e0215a501581076035035074400d070064560035030108860f15028400070030302c0d03030700a43c05820407407060b40000001d0544641c0100112000d004650014010a03010610100c2e207111820086900110120072280382800450214810f407106140003800501040d2466007016486190300c141b9841c246000c41c2041050000524948110803138215285542210340002d40c440320312140b00e8840785110700440560328200072139114011075044a00b5040540020b00610348605c20084410507a560b600c4400301212040d00e840305020b600e241d0000048800280d10809081c102d210b524160794056150b54152404110924004805c030803414241400007409440580300d2140030512130118101c1d5480d4100403a12 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 297935476 1250 297934226 297934237
    0xc1104020d020706091b180e01060305120711040606140a020c040e151e0711031c060501030e01090809010311211f0311120f070906050406050109080307020103050c 72
    0x4414000b10303c210070b0000c150310000d03426002d0203002d041051502c1400701c40740198019000c02e00b04d60508a841d43d60b4a510043c0300c140c21800000d122a00c0b0f444080c505601c3c010140c1e004100081c0c0b01d002c1202041c0810083c1d00c5c180c03420320000382000c40240c1700c801d0500c8240c03a060f001041201d001482081796040030240a4810090303030320040406c0362901c0c080e41e888103200b001c1e06c0c0403420100a070040018099440304802086494140e07007295030300d80d00328508c0000d20003401308850100031184500075807410107000003a00c0d49844005810340355850380d81016a4507005039040400c0c603203022a02d1124003441d0000701803440f0059010039000e001e61800140c0000e142d54145069003204050203001011844003c1c0019001100740010103400010301c1c401030010000c10a0600e414402200034207902035480c42e862542400f480d00c48143c0c44514240e4076000e0801042c01d080c49010f0151500307281403008a424095403035544d01c5508c00080c1010764400002c0e00001c011403e490 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 297936726 1250 297935476 297935497
    0xc061c050106020d030b01020a0f060b060c010e0607090608060901180618020403260f070f0209090706090b071e030912060203060418020d02010c020105130f0320010c110402 76
    0x109a50712002c00030350314007a08988101091901485107621360000401d624001d91080c00c000030020030350344610203009541c0e202d541000e400d21010700c43c80c60038007038825001c1461004000525010f58010141d00700d81d032241050044000a004207070700d8040d4160306664600904c100040000c2d0b401c82d008015540c0000e001212a406a001c81440c0b90020000c487c0207604592640c0900c907581821004500c0d1050f240141c03c20071140020500300c041e081d880e0254661000c0d201058001c0380703140070120b031510000c0d00614001d0000541220800c005040094091400d02d141540d0b4800700c000c0420340004844160a0003604151283c1c0e526030181800010700d810000c940d140030400303074005460441c03055040246802d100c0301d2060030786451a80003401413030f201034190019594045410010380c1040030402545542090000c40c5030300802d92a54040c031001c1ca10300f0450090040516041029150304180215680e4003840020500350480048075207480b182000900900c50341c1c2c05013 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 297937976 1250 297936726 297936731
    0x604030602070b0703061d060102120301030b061302030907031113090b0a0e03090f060901031b2307050607050d02041a0301032303030c0715180c1202030c061c 70
    0x110802105801401c09180b0071120000c16440700182070342034a00c0d501852440c10114020107c811010440c3c0707607000708041c016200d0740455210500e0a5038400d80081c0d87d51018541440641d003480e2104405e100d03500c3d00c0440c158282480420703140c0e030180c4405425407000450f408915994041d088000c080ca0203410030504480f403030281c060b014100c42e042809450410003694080e0003200311743c04014004d1041c8104a00b1404209094000180003810103035030700440d0b10f420351002464400352042d038841c04124210761895142c014107035816154804000d0255400203240080c900d60081c80c6c609100e40c42c1c0c04424003810003800b85a000705162012002c00046035120035000b14140ca0140600360800808510300354961148442064030507072040000450041500e00502a00c620461070503010031040344420068034120381900b0500c211008405040002d81c40d0244010b02c139070310350154444400d0f0002a01c4290045100c3c1c018000003a018070b160311142d002b41c07c3c6028a0004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 297939226 1250 297937976 297937979
    0x1b08040e07031b022122080601050310060f090209030f0d210c02100c020a020d060507030e12030406050a091a04050d021204090b0301060e1503060f0606030f10050604 73
    0x1800f41c10902840079828108080d03440249102144005014118800d1807014001c210300e099100e5000303c01c00807000003041848000d0644203850300b0020045075008180741d50421003058242880049000700252801400704082151100c00101b11000500016200c6080c88003007402e20030003148008940c000c0c0d1100802840e00001c11301484015682000d5804031203040080494140080000250748880c80f00480b40e07449800c0050301644a00c1540c2802042c2d5000c50030304286a03408481e400d1300c480410000c20350600c52210b400015400800300500e20400380c405621000d40b024150703d1f15500000e0300020306401105807564049034844811808401c4103031481c00c140e80403540c2d8050b00c90000c2c4002c1c400950000d45040c2e1070101c03481c0910b41403229008280315038129806549607840000e0341604802c01600c41c140c141404030030000144105810701380e000307000b40e181c0c1082c0400d0143d6900c17088292940007403035464800310340d240d0303105040054426030b10139507012200060 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 297940476 1250 297939226 297939241
    0xf05071413090c0f080d08011719050f0106060302040e0601260c07080f0c010b2b0212190c150807050d090203100c020105090606060307080a02040909060b100f1b08040e 74
    0x860206c0b0043c80d41d200c1d845c036600c072404c1341c15003000e01d00c104d4150b5004296580240e54080401d80045105100300d40c0d00150410645007035070700c2a0b00c02000b081d0301013400c00080201d490b520354400707424640400d11090320115a0321144106c010100d08a10300c000007000c030000c0804555030300382c00028642d2510f1208a9103411640910032000c190350074158200b00c40d06025000600c86048128000000c0d070381d52450080107004814103903441056000b140d10314a0050181d021120310b05151400c1e8100c140c100030000c0c65040e0302800103800e190103040300c01c030340c4401d10304d802000b41c1c80c05aa603080c0800002e000761134280f8003c1d41c54018940c0700e11022086901800c84a040f0f900203000c1c958030007090980340e5104441e801d030010310030000561003070320030581143d2218060314018209900c899007201181c40c2c004080b01c5d86a910052803040d49451030f0365070717040319540c6440e4560301c2c00100000c000300c1580394288030080180407803000308001c000503900542103004110300b56160103038 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 297941726 1250 297940476 297940483
    0x804030b0105100c021e01020115060206040215040b03060907031508300f071b080303070306091802060a0306080a111804110613030f0f05071413090c0f08 68
    0x10845200d941d40c041002c410071302844182d481690020710740340350b980d2000450070031510044502c50445d5610042048854140c001d244060141c503801080320f40f074a44140400c90044500d684010303007040c4030411040a40d101100d5000c0d00580b121501a1078120055019003074442c1d11a480b012038103004203400000080d80c44240800c50b626071080d641c48030350850784261161102c0c05c82c0c8000c0201030b04500e426030051805500c69003009070400500e03550b9018003a91a005a07006400000a102c5059814000c45c005440c0009082003258250085440007409292009000e4034003c21a0020307a406030b030010001f024210103a8807034210526044101446215846100c0e070000d44880c0c40b045020388c035161240b41d01160380c280712005d01003006119044140007040860301480080002030005400041040c4507108400090720b080c03070158281881600001081c03009402c03410010313910310100c002a0303016010005407198403800c1c40c5000032344030341240c2c4410007a048001612074000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 297942976 1250 297941726 297941729
    0x30507020603070810060513030602031b030403030204081b0f0d081e1315050706050a0216060e0c0910093c0c0207030b190b1201020c0f030406050304080c01090804030b01 75
    0x170030003005060321508192414018181e401966281d003000500005003607a0003142c003d8072815500d1500718040d0039040340c550080350220001794010030100301c0594200028645900c070304040341d000d1115100031410301c0b90710740e04c9035200b030712603858510500c0594421141d403441804025080c000740144280307290380c0800722460060b0012100003d00582c54040c1400101080e42c41925041151b01c40d40003400002e070603819002d508100c10f10702c66102c0e86042e07005520840000c903080203881a02420812141c5080e406210140c080080d0301c50264412000d40700c8194000403030740300160241c4039030840b0412000703408002880c0d00194280301000e144034040072880600001c1d0850000300d8580302c403840010500c080d4000801d09100080840e0321018400040005800145100043e8a0074194032000c8280e5400109200c04030018801c2d484c103403800c03034010340c0380a02e8000014140d1000500203003c0c450085940000d501c42034000d010f4550700b00c410303c0c3d1030300c0d201e05183e204c4100a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 297944226 1250 297942976 297942991
    0x41103030a17010f0b031f0b030406061805040201050409110c011409060108010c020714040e0a0b10060302030105061204020102070b0c01020436020c03130305010b040608030f0304020d0305070206030708 89
    0x42c00002041c800c184118800c1d101c0c1150400e042d525031851b030302e0400c5090307036030103c0148401714007055a01101c406180710342d000d400041030541c41d043e943d07100410800c03803c000d09800c050412000d070742c10a0455003140d41411000551262640c402c050900a060701c4100e40d500b46850840c0d020400f41110340551704080544680e6642e520705182201e82501d44034000d80c20409041003040303401e045400da0700c80301500201c0c900e101d000e1510704000342c2450440320f114000062203c0301d42c4030038004000d000c040c10704503c0c550401c0005500c41c010300089000078040c510014085910a02c151802004d1700038000361103801c3c881d0414044d400c24003c00d400454800c100149401c088800500f01d0144a905030040d00408001503010394041c08020100b031208118801c090f00000c07000c14000c60043c0000681070311584204000c2c6c2c0d4480d48a03400550040c841c0c82040c0581e442100e400603412500c5070107008403454181d40e1070095a1740039600400100810407a590403c4465224200 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 297945476 1250 297944226 297944267
    0x60a0f090e0c01020a03080c09010c06050a150609030c0506090315070c1b0b03040312060b070c1e1a0d0609020a0807020f030a12050c0f04030507081005040b0708041103030a 76
    0x2e040126503444900710050001480c0d000804c0e100310034503000f0f0010480c10324003450000c5280e154031094400580d00d004110b903031040840c08048003402801c0c06003440746802c01c0d0b00c9265807198484120a0300a003403050100040c0c0b074115640800c0124a00c410800c0050031a00c4c0c00c0401900fa001c44450580c2c410b2100503407049400b00010b015800e86144d4419181940c6503610126200d00e68080341c05130780ea6541c0c001013038aa070741c0c00c050420940b01e144810a46802d00d081d0181480d8280c80c102025200c6910501510851134542d1110004000409403614110800303d4082c0c07599500004105100107035222541c0d6110b0b000b60301c01e003810380071201c0e000b10000c042903903841840d0001002405a60f80060200c0c1d00e600085e400665540c1c2e03035070600340404220300b0700d0750007a8070440b2107511001c01001440018080d042004061010800c41c40c80d0544038000c0c0114001c00580801a1000005080011994044070848000340c21252289030061003d42061291500c0104001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 297946726 1250 297945476 297945493
    0x717010e07050d091406010b0a270b0a0203090d080903060709080c040c0c0c08010203090622080c0a1a06010e040911010c020a080105091c03150e060a0f090e 69
    0xe40c0c020110707000c0c0301c107a5038076464100301201c0c5000400c4100307821208001c1022072420002030400100c1c4c043c2919a8a0a0b0345085400c0050b0146012078614000104045446014100705440700012545654141ca40c2d84003281002c034254404d0000d195800341c80d0601d20b205100d05000078224510f01030302200c1107034540d0b4101762034880c0c40c0d205100440d031200000700b00e01c2c1840d400608500e00641001c07000001c050740d0745050741ca07041d000721903d690301008109078410f0400c0882d070028241d070000201c28444015000d554228000c0c0a00741032000504c2440320041080040b100e1900a407500c0095604510000200041520402d000450b803620140c8a8038281c8140d41d03e0070317804100d07d071000044400544000512440680c2c0c001079805001071f03066400c0c0500c91048220b42c0180560350302c400181a1400304101091013050b2a01c0400021003070468010340c00d1324203400e81344210343d48407000601c01c00c0440e00011940c0e00e1403080000c04c0c05d0950401e41c50402d10000307846590 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 297947976 1250 297946726 297946739
    0x4060e0114061b0a031b0b4204140403020a080a0912060c2705040c11030f040e0709080d08060303091302070b06041509020702060904051807080102340b071701 70
    0x34086e100040c180c0000380f80440e44141d11050040c2e540554401c05079400e523901c52440500584081c44d09111300743d00f400c0c518140c6014461800189240c80100c40c041c1000d0300c00039601c10586a00800d00d6800264070540240594503503c02400c4409001a00e0b10f001d00c0c004c4090031144040ca00815191000403500e60b02c0c007404071184289908002032400e18003c100401790012540301c0090100420030b110141c10140020300101081e20701255440d40340046104090b00f0003040700b001c00c01c04110038000580302081a1400710304500e02225151103140020303046108032070f005944050100034034414030000b42c01600c0002d0103512040780c580d64050034402a038000220089a030002d074541485190581c1e030141c01000c0c0050b08060504441c113010038103c441c16903111464100311003503012402030400480000d041035600130b50500070400d0f403000803121500d12000040c4442d00c02e0100104401030700d16012504000841c0040c1446000940018003080c0455a98180e150000c03614 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 297949226 1250 297947976 297948017
    0x60c0406020d1b021503041103070e070f021c091d01080307080304080d05010b0301030b0a0c051914040e0619050306010e04030315150e04060e0114061b0a03 69
    0x4603846034014020b51581c1401c203e6820f1806095803c4080c881d0318150096107881d1441c0b460310010010456903070501d82010b0139086c010119071882039201c0c04090021062a800705904000b03981130016000c001c1e10310a9040841c5100746202c40d0300e05000d000240340e44002039008546200140d0940500583d48070601000240030740a2158010002a00001e00310340c0156403141c000c80c007180c10f0140000300c44040e00d000381d22110b20100c0103c0144180300d400c0c41121f8000e103080204100c12120380501600500412614200c00384a42d198494480c2c0186002c103600a80c1c3c1c200340b552607448036111000090144d5810703016072604178600c2c01c62107a4500704d102707584004008110f281e1a01d900d40c84e141b80e00901c101c04258992105001640301d001400020304404091041801402d50b0000c1c4850b81b408841032080e41004410000214a200000e041d24520324070ac41e42014100040f070540c1c816601441314404100c99403400101000c51a038140c40e00c80d90f1460740c41070106064141 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 297950476 1250 297949226 297949229
    0x1b0111010b06070b040321060f050603130602030606070203060f0901060f030f150b1207030308060a032301020c19170307050a030c030b0d150506060f0a03020c03070605040311060c04 80
    0xc104104011070340106020064484d44a0f12a04d0038142941c0c04908403081f80e0303000da031024421515208280503012003c04400d01405003620454218034104e5103100042c81c1a080180009500101144090302c0352401c4035406074001c1c003200c00509025403540300400d01110185039551a2080119182107860303100000c03a504407090b00540c03c0780d5120120001135241c900d11285650f08820455511420803d201c0700c858400a40001483c43c2005005e06800400080c4a00c0044c0428000100100c0403040034659841500420b200e02c5007100c2c2c024402ca022810a5129219410402081303040c516a0401d20134100200544800070410f2454081030f03400f007020601c18081c0c002c0ba607200c0c1e4031210400807075250100c6d10701aa0000318195441c450000d8a0614802c900c112600d402c034050b00b5000001075920900c0c11803265030002040c0600d0300701c08101500000c071000511803c00540d2001c035000042000207042c030380340151800594103804001c60169000060405406d0000d540 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 297951726 1250 297950476 297950479
    0x3010c030c080a02090f09010b130e0720030d02040b0d06092c160803090f06040302090103020607080405060d05070807030524030f10091505061e03010b031b0111010b 73
    0x4002d444011010004e50410603001e60003280c1048810146e80da1554014000c0c0100d1990300c4e138404842841580824290704a5841034070300c00e05202c0c2c0030703902c03095401020620703924061480c40004805410361040419001d0708500105002c58440304031401000c3ca80440c1d40e08205e540e035a819614103554000c0c2442c280174280407100b1000c0210002005142a07810007a210310780c0c0c1041e03e000a50002d40c006c05803e61001c2810308450810940c0d03110311031011100e0381e003814070303650000350000750500009014a00101d540320170805840700b90360240c5002040346031a040b0000100c0000d00301280c1d1040060740280200e10300c14003901c00d103402070b503450080701d2050072035000000143d0400c8169981521800700c16107a100d80500090410ac00001c10115070b40c046c9041521240d0700c0814081c501600d44428400c040d51201480f0958006100030000c151100d003002a0042030b2200146400d130082682050040c26207180e01e101c0110240c13074034080d88040448481c200d138501c100c0ca0b03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 297952976 1250 297951726 297951737
    0x8030403050f280605071116080111030402090a0b06070c03030507061d060f0601020f1b1206090712020f04020307030605131424181918110a08070308030603010c030c 73
    0x40700852066044686d0207407060800da0b4034035050010b450302d09505d416490071070007861030f81804000000c0c0265410751068503101c50031401c007500080c880c8400600b54445040c0e6525203d01c0d07a0320746009880195401c11841c03000c0d40e03501c3c00d000d0501d5100c0c1c102203031500c0c0380c90080341c4850025000001100241401080c03d551042005d95040038054001419803049107900b90400004202684241c40140c200a4900908105000c081034890000c1d81d003d030444410083e255a00090120441c1d84811284100c9942400403030a280000100719400a0001040001c41501a0041400c844040d90007000c08410f40d16204102c4101c01c46444010b10f0340380108040000802d21340c07c02c1b0108003108000c0c2d000000c001141c00003e00d01841c0506200d030100315001d90908070000720303000700e100d052140c51b46104a50303c00380325089000345041900e034495015511880e2400d406007441500f2902c0658a030304042341150001c0b0b0705075110750300700600050618031a00130385410320b1468440 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 297954226 1250 297952976 297953053
    0xa080a052512020f0c01060f1403031905121602060105061e09040b0a030c1505210a060e070e030c0a050d0308151008180a0c0504020705010608030403050f 68
    0x1142c07084031000060a6081d004e1003080c00200e0424002d0042000e8000002403d034039064100c4000c141c540d12100b82512021034030403498070080308480c0790390b00c0d140210368241d0595405481d60f00840c000300d141c20b03124104008032400886001d0045111607001c441540e80c0e02d108003c45407050903100795520703202c6103160411000c0040a0300309050014808a040c60710040854808903c560064860608140042001c002c03003d505c0343d181040c40c680589080407285034201507400c403c07100407020341c1090001d20ba9a000394001c001a008406024100d03003801c1e0070040036190314420040c46402184402981031820000720380403580c000c0e14540800c012130b20182d80c00c01d00204100c406010392000c16120f95904070049044507075944901003282440d100b0030320084440c000c0c2285070382c415650070020620440341e81d01100d804840c056610711107450300764050b0038142d04c0030b8103c4c40045008800c00c84007041c030004c14000300701190255032245480c41c0048404c600c0304e01040014801c1d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 297955476 1250 297954226 297954301
    0x925090e0c0a0216271e141003080909040305090909010c0e090423031201152a1b0e090c010f0801060905010c08071209030c09020c030d0911060a080a05 67
    0x18141400800294002041e80c22104440f00b51b21111120b40000c0755900720307808400801001007a0419031080a0784806070440d65440a00d02c1080c50303103803003030400000003000c25214404503140200041c107100c20390b080c0f640e00036003c3c008115400012a841840704070f010b0a142c40e12921807608482295801a1006403561071105015401c0726180400c1024250891031403000c2070007050540404d0000c0808101c004010041c240c00052810110760560144944480c1b8036005441c0c0004110740594500010150b04060b581e120f050b540c0400b8003008602c100128545a642c40280c80341350b264180b241d002c44009509000d130340302180c1f0810341032080c1d510403900c041d4014800e140c02441e000c1c0c41d48440120001003044d01d000a42c44400501c100607481803544000c20024a00b5820f0182c81005e01d61617024002d030000103107903100104001d100184030703400040c8802070070240da03802500310006d241250484051450b10300780000b00300f030204017007940c1840003c11021003208900040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 297956726 1250 297955476 297955529
    0x300c060f0606210603030f040807050109050406030506040b0606041e0e0a180b06030304030c1502120f04060809100603050307050613031b0501060b040f050a050925090e0c0a0216 78
    0x13403032180c044c03109001402655101e000103001030011b980041030b040d80340900043c500030440c0c0149000c1c6083c40d00400000c1c40020f10aa001031740068916100e075940e002080c118011a40701548141910001a0203282081588402e503141441800700d159200442a01540d4055003007800c400c0100c020305c0c0c00704004c0c11856070002030040c02e40c6c0c900340e0b0700d0301d414600c8100e40c0c0149580304085230030b06203440d80400000c610441203040490400e01d90300000c009501a901c940703410b014105000545151080c84400d69a6008110400030309469060003540c940003040100c40520800c4041783d14009013140241c441039243d0f0721880244486882e078031524000c010101d58a64a07010085031140349400a04090700744400512031407450141040f440c5091030788124001e14010050107500382d10b614080c283c0c0e40a00002806000743c1c1542200d601081742c1c090f021090141c410b00c140015004014104103809500701c907482c454041c4000142e50547c03289451400c420440c0e039124540c40b5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 297957976 1250 297956726 297956731
    0x120b040b0405011107030e01021e06010b0d02090405132a06050a020102090904030e0325060c03091508100e0601020a060e0f030705011517300c060f060621 68
    0x740c2c00481e182c41402ca011186400c000710403408210380400910301c1c5c0d641008905610405810350000340c80074500103644035034040c000c81025100c0051134207011a03c50b01100e041e04000b600401c0f552520400b015200c0075180070850720000b01c81f100c4010b0030045004001051407100e480d038241803500c1c205540b030341e010100c08019550240030401080d650202c80c0d51145000313440368140c0424a0701003500700004008042c05101180001e00346110348146040241ca05c241010040d000700381c00d040e10115810384c0a80000c24090842412003580081003c2c06010715018040030161600c140070b413070400803245240142e10105c0c9c0000801c1e001c0c0c1069800b84124800d990b09000a0302c80e95007980e00ca844162801d81d1a8101c1340245500311109600800c0380d280c130200034000707039204540c580944a050f003e140080781758291103445a82c41c240c500d04585c8688665600d105102281c8821303044075002183c001500c001801d81c20310004855440303440b0b0860070340c20722201f0391004154201 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 297959226 1250 297957976 297957983
    0xb070609050109050105070816090e0402180c070201020d03060305030d090602040801020d020c0f0601270f0603030c060507020309010c080304050c150d05060a05090114190f0f120b040b04 82
    0x3900c00c0600821028401c280700a8028400407a46107000c0034080c0c00344002424400016221000c00c1c00642c0c4c0c80000712041d1010480400990b40302c50000980b540d00101e0889480d401410038401d190050270300811210340700fa0252404c0c020b002c00c05a003100c04c40d12025009070001c12400c0c8020390540d11000e0300c50f204550040c180703a00c440c242da08a030040c182c10641d10340c0c00200c802220302c0401c8020862000c40b0b00402541d03044c803030041d207000b11000fa52031412000840b00c05030300110360080d001603031200030104203041c2d59047c014100e0070050010354680d442d20001c40c40c071070b20200480d41c81540603100c0b084c800900d81d81d0381000e94030090095445000d020300e8034107507641d002c1840d000d0510040c0d1894a81ca0040c14440440b80c2c06041140326041004042005448410840341150310807241283d10300d01480c0829403482413003103d41101507240102050407103090200000b0b0b6030000d001240a01c1d01d03030030f0007241101501070103000c180020f000039001451411241e90320510 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 297960476 1250 297959226 297959231
    0xe07061e2a050f15010e0103030e090901060302030d0804211e02070302100c140118150b1f0f030908090405130f0605011d06090a0b0a0b030f060319030503010b0706 72
    0x442c0c5616041c541d1907440360f03090f60095070b81c100c040306030f40500340e014040001d203107822549142d81c040c14050010b0443d07401843d890000034130588080d4071503001141c001d03098403000580b07450700900403401101c08071140280340d90b0315164020822075000707170500262a9401d4481365102d1203d522507404003580c0031441050000310060304d468000410a00c1142c40c1c107049000180790030001d4240300d10840c8010380c94548109080700416444e80716442e00580091100ca15484101d00601030f00526650804903500c000100c0000002c1c007032045824070341d41ea110300e100500048050341c10000c40902401e1040c0034050161170503074007141e049850300d21450700031107450761034480c40010b24202792269070f5a40c004006901001074240642181d04035600c82a02e400d0000880150001c1c1c41d00012550340c03081c02c0c0c0c8a449801c078900180205841c0c8540328a440312861101c2241150464020700a103c948031206282d911980b0007503605840b01821030b820841d1441003034001c2c210076030f0441c2c1c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 297961726 1250 297960476 297960557
    0xe0a230a0c0b04090605120c040506040212091c0c0b1b19050d0c2609030c160302040c02060903040608130f03110105180c01030b12010e07061e 63
    0x10189485440244503446282d51103034a8a8400d038103c0b01c0603072005000f00040c0e00d404441850106001003880c0b0100c4000460b602d0301008580203000343c500c00c000171842c52041c000007410004004c025a514888821054500c81c2000c6a00060118005140d1040800819101440d0615488050064025007400c0440d0080c0320410300d06014403400210b000000c61902205042c00703101540341b014200412010030f002510307a0b40b250481c2c010050109403002145c2121010710869801d012203e0880e44130a50107a0f052006c9165848200c0c802c901c0c00650a0700729001088080c4500155800b850a051410704151100c400083c903d115a00c145103280c400101e10300d0f820f00c0507600980c0d0381c00301901100d0001c0d003144c40c0a05801c6100151881780380d20b080c80000c6e03215081d1030030b1030007240c0c1c2285400030404466070880404019400c01601e0b4080c0301c80024240220740315561113401050500b02c803500c04500c0c8034240c030001948000111075070b8003910050302400001c1068800c4a1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 297962976 1250 297961726 297961733
    0xc0301060e040b0a060e06040b040e0106060302040f090b0d03081b03010603020307110a110d080f0c0102190e0319030e03011104060201060501090806070f052b0e0a230a 74
    0x1100e00307400008450304550207000a100d400015250b1204400c3c1c01041001c2c104508020840c0300142a548079039243c40c032558080d20703150400306807600408000c1c0121500c900001d000394101d8003805940c07041c01c00300064007541c0c6001d8151101e9010380009818809a01c0485003010002e0800d011003140800c4a100d48103a43c0c01540280b03119500185c407810f00034402450088541c50690707035940100b00a5002c03c00900c40b03603180880488561644c8411840c0c010140d0007120040019450041120500756106400510800d1010040c0b61990000807400f540c02c2001071003940d425600554044c8041503c40c006210002e0003403c004c6400022a8000307402e44040394100c6214001c0420304001140e024010b12010380300c00d08003a82c8550624003601ea680200078415030401185051a8400798016000c40381c00d203c4001d1652062554103032007030704070b101003100c510185142030307a107540310340001c92160307032240d4010b46041030101c0000100400b5030101c0d2400c2214020f64801c039000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 297964226 1250 297962976 297962981
    0x1a0d0305130e0703020304020405010e040209010b2115090108060714131214060601020d020a080a110a0302030715020c0a240e060402030709020c33041b0f12030e030c0301 75
    0x8003d0740d61302603a6450302e40305000c1a81c0c81a801010129000301c20b0200603910414180e040d40e07403d41500d6101d19400f0010300d020000c1c04000c0c803038030182e20203005945094110751201c0c81802e585505080c0d030713241e1004d035955200301d42c090005010f00e4001c007180135441c001024400b10b070400d0a0314444e02c0c1c40d9820180f07030165404680c0004a13104501c80f03200b060003c154407500c240007501c40718400403070294542e800c00000400c40a00098501003150190300a0740d405811a801c45041071100e180181d605d40c040b14064a0300503030b041c4070002502980c022604c10a0150b80602004143d698a14001603540d108886413854070043c4000409040d11403071000c08010b00051000d407c103401410b04142d003c1d040b104419004104820904074006102c2840c007811540e1400c48402c5900341e481000032000700c10101e5101941440107000702d072181203909170407486201d00030715580d00620200d14050300c10a000c4034103080c448404a4003580c50b00c0d00e058006001d580302c02c003000001a08 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 297965476 1250 297964226 297964231
    0x1e010f14210a0e0d12020d1b020d09050d030504030b070c0b0a0f060e0f061c080f12100e0a09170705060702100b221b08010501031a0d0305130e 63
    0x70000c141c40d00b0005091558021154880c00080142101083c0340070300908000c0c000303400c052940e1300050841080315080e482a160085070b6544041e81a0b05420300a4840d44840021400075186200c085030915062651408203a03060320b038241740c246599181d420b040402001c00c010b010500814101041550800b02c4c07058801c003800040c000e135011203840c22245960070030b185030806101048a183c46032482c030340e00108211901075003031242c00c1d0910540a8900001844c0c0440072031841905000800030304403208030800719510a40c0e07001100ca4903001c4621555509603980c1e004281140a5a0b120546031402404580001240c15181d800d0580c031181044a2a600003010031203c0c0360b0500098040c0d1038681800e000000942c1c0c0000e03000030413204d5002130760038540c0981c51008070301d520035041d0750750200740c10b490100701e03540c040d107124030034483d40d804241004d0f51040c24401d04020b40154540040040340c800d40b042d1801c4031140c00018001070b2540381c0308400724404840d20081c51 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 297966726 1250 297965476 297965527
    0x6010828060819150506120a03030f0b06130306051512070906120506010b09040b09090105090d0c0530070609030e060705031b0106050d08091e010f14 66
    0x3211442c05a206141100000d0103c00c1e254801210400040c00703046440751a1071401c102107402e46402000034218001c03c41d0240b0340e40300d2441c0d40000c154041c2c000b41e184100105040000748094010b03c1124400e0381400300021000240034000120079920050b08001c00448680c01c81e8002000f207402d007004000380444036400314104100a044a0082c0790141a0010b44490700383d841d0b90f42c6503541c03801130043da080c1c60404a000800d03034446074410421004018180c0710f060a144002c14020a801d5030b450500f070080140441841d4080c07002144401d601c00c00500c120000784001c0c000d0030500010900409459020700905040114054900c0f240908000504d6440e0f43c5001341440340003034013075030080000344544030125101000359010006e44920110100403400342407401400795400c43d0380d110b01c0c100c0303120b418805004041c004000007518016460700d84000c82c5094600140700790350026440219202490344151017000c0d100402450003410001a041d001701d01194018508 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 297967976 1250 297966726 297966731
    0x804141606031d01020c03040306020702031207080a030c05090d021507060903020610081207030804020a05041b030e010204152001050a0b13060b0f07080702041406130e0606010828 79
    0x1841d50000030f8a4289240c22910001c6280c80442d54020f900da000d64030000d8543c43d40801c080707082d5207060054405002c081c50102d5507401451509080a420900e08040028070f09144220218000c1c1308a820030381000703240365121101e43d0700f00034201d41c0d0071300949500b132000d01c030000020f4507038024244410710a0300504817a00d8642200400c04d0700b00e600659155024000001200a440f000c8480e05901860250b10640e942c1c0085400c0c072005038803040c0c02c286000070002d80c1c0c0d580814164400b00780ca0780e0a00035805034040f030380d00b0b0b80100c1c0036441c1011000c011003440e5900604231440d804005d040d60466140300115520700b11034046035040200d40e00c1b007000e00010316000c4264080b41e5038050741002028141800320b1094003c289500a101500007401c0e401d20440c502910340a9034020403c0c40003c007108102c54000700c1c281c070324600440a090240340e1074a0305014099965091100400f40d0b81e8403c4011254501c01610748290703000e06094080705040d0b102d040c12900d400e1403602 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 297969226 1250 297967976 297967991
    0x507090602060702150a050c1b0606040b120c0d050f030307090e06091006080a020c01181103070b030402040c0e040e07061821021504060e1005030403080414160603 72
    0x103402c10310020424021508803c0c0d0100c8a0141c41c0070080e0081c800210008240c0d030394428001d1107110380c00c0c900d100468910074203840311400052480c801d10b01a10b040c000c803080442072007000c1c11031002c40b4110b0307049031100d40400d0820500f603402c16801502240d465141d041c117018119071003660310a0019160160a0014038800e641c4c81d90400029203c15203a41b5000410801c1070119000e01d608015085001c81c4107021035030180c0b05200e41600c02081403028507a46201340e48070040c01200c100c3c80306400441203140200d04681200c211341380300c82c550380d034030f070301704002810101504c90071321001c11402201134031035214040325070303101000802c0b010703060200203010141e554011000c80303101d1090074410f59003206019001c40241840d04030031510184006862010255111450400701040002c0d1003944455008085107003a5620007600702484012a0130740b1084401402091400c004540010200800c5141c07a0300084256001099008181141011a9844280040d480ea00d6 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 297970476 1250 297969226 297969239
    0x20906070501050f01172d030a050306090108010603020d06090f080a0c1a07020c010509031005250216140a050907050705070e011229070903030f0306060e0402130504050709 76
    0xc07050150030001c050030086011011b590b0f646440d00c0d102c80451002c42c4107618100f40714280c00c1359006450a090325110700b01c2d180d0040144d0000c40c0c031540b14081c2c2c0c200001322214184918400d40350050706028800392103807181e00240184190480e0700d1000703644500d0103d03107a400176007924221a0703540d618040f80c034180030521070300000c0802502c4c0c5051050203150b0360006031030f01300ea600a091240d26141080700103130514081c1d070700c5140a0360500c2c0800805180800c1c031101d10980794200203c0111141c44c0499075040794140b0f08000c030841841c140050007801201d5042030700010000c0e00501d49031004210110340030345103140401c0021502c20204481440300b003025040d0000c07002d010790f00d0203101d4041d54520260241c84001c03114010b0b5420607180c41190b508109a44c040200da080c401e1009140c4490f41c4410360020f64007243e40300d84c1a111f03000d035808407034190340c42086405a038010840290b21071011a400240684000100c0e41c9442c000e4503c6a4295129042a24074111 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 297971726 1250 297970476 297970501
    0x12020108060118060e0105090d0b0402030d320915042105060601050703021c051c0507080402100201020706060902030f07081e060d02120a030315030203030405040b030102090607050105 81
    0x41100c1d052040203490200f00012001c4520100c03281442d0040d101d00781c400c01aaa980300b40c0102d15005004000004188010201d002c4c0c0510f03c298220744864a10050843e01d5200101005000e48001101001086200781c00d4101d050b52040082d490486c6102c0001c1c1c814910f10340085288002180401c0043c0310f6508008500d50840841500b0012590740c403921688014105818400003060743d1051500c00c02030b16810030401803460094668908018205030042e400c50381141c2c0900600d040d250b2f0507400344502a10085c0c41e02007041e2955030030024905115200031003190350a01500002c2290790284100034081101e0059407420b00d500340d1003070130714010441c5080c0520708040c81003114a0202845503000c1041e0f90710020f4649070000f816071603007400043d50211509a034030008080c080b0b98503910318441d880800003600388548407444a005407102079403580041c13008011505150308202c00c04d00c0010300051820700c81d00e0001d11180c0120f101510203070364820802c00313140c8040c03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 297972976 1250 297971726 297971731
    0x601050406090605090c0d0902100806132a1115010f0801060f0b0c07030204020d1d06070c03140405040c09030c090902060304080901090905150a051f1808030412020108 74
    0x190b003803020034145000308400703003800342106810840026950380880c0565115964480d8000c002d101c4510103218002c04212054800e2403152240070384040f0740d88a03900c1000c1506800c0c217048404690300c1f071000c3c420f5180982e810001e100038407a039080307001800c0c08100c042407038070056842c26504241002c039420105400a200b5607140040c02d00909403510002011101c100b510071f0758603644010507070b0a200c503980c030086d0024004168004a502070f034215001440300074240001c1162064450390b681c00060312000040713920b44032240c011034400d801c1c100d4541405900d207407900750344001040071552a54112000200c40f85004e00403c00b024448038001c0209000901c04c0324902c0c0c00046803440080c0c80201140c40009034041582d02580c101c0d8024125400100714600c1c10001c0c4180d40384a0000f014420b41441102085510f072808400300c007400b40303d40304202c6860401068401070030400c0914041c0c02c03007001c0010420b100b00010070107405a08600f071040c004610000d065603402 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 297974226 1250 297972976 297972989
    0x80604050c03060d0809041401050111010b090c090a1a030402010f080106090510110a080903010c1d0613081f0c030203391603020606091e0403120c020601050406 71
    0x811003440041c05550003a00d412840803110440d540101c0e1511076554400e42003004e821500b000310b8142c25490070302036136040700e10030707210104860309140f03c0074200e40004c1d040a0b4401c50000c046124042900042c0580d1000a491110841e4072010500c00c0400041500700100c003001040004550380903a00e580707800c001d420304603004e5052550180440c07840e80038181c010948031400c8000c491041100035041ca070348505545290185040c000c500b50b110a0342076010f58200840325121034424025109003c500f2099441d40304120001c0002a62100c005505102403c0002080b51039040c02034804426010955038403442201160109466204981105040c814070030000401c102c0300c3d00120001c1c2c500d1400c4881c0220313225400070a901000036003840b80000c24502513810328021002091400b9808454490741c0321820081c404a0840d80d680d4490125035100e030701c80442601081e0000d119041005083d008051030340c08940006845000581c003020040081d41024820744024149 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 297975476 1250 297974226 297974231
    0xc050102010c090e011517090106140105070201080109050a140c0a020d0e01051903060909200a03031d0303090d06090b061005042d030f0b1e0a02030916080d080604 72
    0x2800a101c4e21441d81440355490110414603003034181c600c01d0000c0c0c0880b51182507009054180510044d000302458010030040950000c080d444540c00340c015101e402d58140e448a0080c0c5c00c3c4202c64001c2c041c098110705e002611880e0312412011201d612620071100307c0c80064507a00724041c024540215020800c06210280340450f00c06e9910104440c441e104042600803003032a1180100c0007005142d1122411a20700025038080150855008189845a00030344550704090000c2101c00c008a1000601141103611010209100004c00504c4108014150303401c0182120110f4402000d540003120251b030b840501c001005260010f00d5003240081d00c1c17908041d401284042c02d0f901c00e600882543d11842c945528075009440303102e504c0374415190303102d5040e42da490000310003050110215103400041c00050b40401846400718500024406822001d4481001c80d4000354070150461525000d0a10f002c2040d000311030700c040003804008010450408480d40c02800400e02a084520650 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 297976726 1250 297975476 297975479
    0xa080a0b04031215050f011709163602042c0901050123040e07090615030c050a0c0201051308060a0b060c06010501180e0a0b040b03010b030d0509060c06040c050102010c09 75
    0x1a02849042d040d1001501ca99803540f104000690702d00c8e80c50310000e04d40c40b030031030704201c045400030a00a002d07008101c60010341d29283e50b51a121008040c14800f0151035003107480c01d2281c401910344810100030078005141c69158003075540000c411a86854841e80c3c0c0070500781e80721510711105640715809000800c142d50514100043d208100403940082c10961403001c0d0213643d4035402007101030209011160005d6840032000c003e040c040c8079010072482104071003205540203000d112480d5900f83e403000d20f0032520b9901521803100d82841641000800c0c0012143c002c0401150701c003a10601d4020085482c0c104689002d5410301402c1340c0c000c050a00c00c0d562207001c001101410f4070400d0074005140d05490680101c5c00349198008060b070358030a41400000304503540000c0780401c0a5405008084103041814260b034201030007140c2540c0302e0304200c0d0440c0d200710040d04907041c0090016240c010f6441c0c0f803901c0c0c404103807001d8a0310040040204038640c3c0911905100e8903150a004402c0d9 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 297977976 1250 297976726 297976751
    0x190503010510021b040e150f0402010206070c0f0b0a0b0d050a0611091302030711100504030e10170c04050301020d0f06140a0b03130b090d02150c180a080a0b040312 72
    0x2044e01100034083e60300c0b5102450070140034420300c1c900001c0741001030803d00c1d0042d680e003550581a40c0990146c01075001080d106031142d001003800c43c1e00048420f01c85841965510003001c0000d0501c545950344041600da43d980d441428480d00380508010110581c40d81440d20842e803a240001c40003810410038121592a11590800c40d525603038401030720b941d201c0c01d05a0308001010903540c0c0070b0185001503e040701155020034000e5011782d8500d046880c07c00248082c44000d80001d81c08210807006000c50f0704800f03000741394403080c0c0000150800b969000820f09a030440e1003c102e01e03a4036411107884c0d18509205500041c641e503911450300c0310301240843d070120700c80e01039102c0e802c00010004504c000c940b2030881240703501c140407140916020030000c2c2c0303841d4504500d2005010f010002c003480780c002d810722801041304080a80c03400200031841c440000d0310041481e081f4102d04e00001c1c0b03004060204002050003100714641c01d140a04e0020403054141c68102d5000746401103c2400f07 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 297979226 1250 297977976 297978013
    0x60e0a030f2a06090f03051c0506150706090b0a0603200a030803090106030b0c090306070e0105181804051c0906080106050f0705100b040f200f19050301051002 70
    0x10480b141020368050202401c00b0b0016041c81400a000070f211500b000c410580d22200a207850500c01007040104858007841c202981e1040d6441a401840f1f106100c8805206400420305644180d1000903610640c0e0340d1604885004c8070b501d401159603070301c00c1040c04102000078403c4000244406103228201001511510844c0005043e546c1e000c000a010000c095014102843e08030301d511070300f07142c0081840c4d04c56025500c954001d00903180410ba0640c021300f22101800c4050315034509003207403601481070342c60410104592004d080f41d529260300202003841d500583c082c0028001c4c0c0140403614040c46001d000d00c000400170040420048903901c0300c002030640c2c4262070041c0d964200502c07900214003802c2400b9020b406400a24191964075074000402c0f10710580d004e05c0480941078801e4201c2e86000c010302c80e90038158411065a58891008100d51464414140c1c2400c00c500c2c80f120351846156008004200000b00601203458034440e8035800c031140e88000c000680b01078000098 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 297980476 1250 297979226 297979277
    0xb2e0e0601170402090c0703020f070305010b10020105133305090d050f0307031d0114040606050f060f0901050c15100905091009080f0d09060f020901050703110a060e0a030f 76
    0x6d0b001000c25040e003018803d1203660482c4113201c0480b007140d512414620700800701c54407c24030039907817041011505401809640d206030f80c00129415048400d844403400d81248081c154843c0d244003140d91200b003c1c0c120400c0c9040400c2c000081e2600d0050915441c08032504807180a002c030034010384184c0f07083c10b022030b54003144c50718010130140400c04030320080c8501610180d0940d42000000c0103040f1000f4000741c85980109400c1c04007990320b04c240400c1300c03540d000c43c0d50440000c004803110b408564000f804036074811306d042882d2000402d03c8a0030403520742603400c03140c241c000500c404540b10031907400c060b001c2004204000e007080c5076060740d19156030004400d003588811548061000b0380060701d808040038540c035640e0303001000c40640100310404040342c02d00e24205049032100c099109903501d01d001a10b840c0c1c509602a07c0540d40c4221050324440c031449613224550010340710303014444c0c89007d01b0340103018903030309860007400c40c0507000310701000c0007030300a100004103104151808 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 297981726 1250 297980476 297980491
    0x20a0e0910230f15030a0f020301080706030e0c1206010303110c0d0209090a0b0a0e01060f3005030d1d0c031c02010f020a0203130609030b2e0e060117040209 69
    0x184880002c0410714080e2010845039120301c56040301c01d0384810710001584a103080600c10400c0030704034a030381022404280102c04444d07022190600040340a54044001c00c07100001f1508100000340018034007682103520b083e2180c00c0b90703004204058004441501c3d61680e00c000e010540a948040b400706d45d442c5002a204201000c0827030b00c0300c4d0040c800d0040e450340000003603200d4a042140400501030402d4004010740c80d103080024503054a01628080c1d40468081c004850078600c4d4600103140c10a12101c4420400c0b444400060010402410b070035601c1d5601280765018a03658160700340383c0c6504054290004180c1210b00d69001c40c0c0000781052030b4009440741502c00c001280104000e102a060750341c400500580d02c0c0c1d40020190050030034424031800e40035290482104c00c203100e4480107012654150120b210042c01c2c229400544a81100c060408070070310382030107a2104580c0c800d0244803d458240706032544c1c03101000707460152216003e8010304260b408145c11543c001c0801 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 297982976 1250 297981726 297981779
    0x7051308062215090501020a020c03070305030d020903030d06090c0306061130070b0609010b0c0c15070206070f0201030509010e030f0c011b0207051f08060d15020a0e0910 75
    0x20040000010030300200040503d000c102980d01c5151090003903200071044409485126218016440e0000354402a264000051030501d42c066400c0e0f4065085505010792502050003c881c2081c0b1078031800740200030b542d0002c1407210380e60784c000d0203c5500b60410000c001c14190440e001d140005400040c032088241d4000c9107040c1400700c03000490404040d04101040090f00b801803102808903140140350896074030150347d0780c2e4003007900d981c4607481622ba01d80d003120b00701d010280343c41880246910007180a480c82d0240c41d0340082d25551000d81e0440d0340c001d14a8002e020740d64144503c40d0b0002e540002080b00440c004042a0340303010301c41c400c4e0445680084d0345070f101d080a401c00c41101f00b00300760030001141081800703501e0725558000c1034003079030340c0c06511302c07001c9080e00030003041c810035849546158a8048c2401090810f02105403640d104942d0220381d45000342c401090b6103035040d6203207002d202c00d000402101d00406885038104243c1c1a409200000c46914031101c00030800880 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 297984226 1250 297982976 297983041
    0x1030501051c021c080c0d0215040b0718080d02060603070501020a02040b060904020307121b080c070f081303050715020c0105030907090207150e010e030d0c050409050705130806 78
    0xd041113000402c2407421046000c000040218100141c60000c1100381994400c1071841c030102c2e9910459018441c2014540005c41c01240002619542100d0b684c540281482c4141422010a035013a602525103075011070600362600382d040c441150022411030290080300e14000000b50b42d9101c20802a2181d9607809074003104c0d540701003c40e582240c02800541d22403402c610042c0c0782c8190900c209840c03505100e0f0507001080b604075040341c803001507215446d260710b480442c0106a048107a0888954800c150340c900032413140b90103403100c1071072003410492040c1549050740c20024940c0c08049003802c1c520700104040e80110f03a8010b01403003032801c541c40fa514058040e28103c3c2c41d40c4180f22aa20005440e0180b000200c01c00903c0d960001051150981c002d05076400c0b82c85045000405400c20711100c4420500c035040780d66207583d035181080c200390300c8000102c00c590302916168085100082e0060302c00303011900c500010040080544800c0c507041000442c00b0183c6084a0445503904c4003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 297985476 1250 297984226 297984229
    0xe090f1018050a0c1a040b030c0309010f0e06010f06091508060d061107030e060307020a0303020c1005250f0203070303020f04030602070f050c15272d01030501051c02 73
    0x21a144241e070400103ca940e9407103030500600c06130141c0107208071102d054168480240c125401c0f1000c40d40720070175251555441c0c405540320364001508081c1d4a5480325000c03040100702c1c0c054420080c0290010306510b5141c126450f034104002e504c80c50034050b20380800c000c0106e90184070001c00006c2d0800040564030100018044890f13804014003484c604030030f40c1029250400602072080c800c3e142d201d00c00181c5020410f036400100d4840340141e00c60310b20300c0006807194014104c2040c01a003120320038040d000c114015168101c179450401d14042d0945542503c20400382541c0c04900d0610090180c035100000f5142e1040200140c113060300058400d40f10918801224001c0d034000c03100b1034661a0601c0c0c2a5864007140c00162114400d0b03c2416145290142c10a58084400080039203005810107030001d82c40100e48041c9825a0015440e40007a221041101c0490b00501c030301150151012200c2440d07105030440c02c80c10549400c0050042c0d440c0c0308201e852002c2c0d042102c000f084041c0c030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 297986726 1250 297985476 297985511
    0xf101d0f0307270b0904061109060c03091005040503071a070c060507050c0108011508090127030809120306011805130b0414040c0b0307021011040e090f10 68
    0x301080d014420300c080010610b05a82c0c50740300148414159000410054420380d056070056040a50f2202403000030500082c13940d070081c1420704a07070404d1400c021110001a030180c106110340c01068000140742e41161030443c00103100780c04213040c828207141c1008086943e43d01a8000c0150343c940c3c2e08605a0001a0a416107140c1e40d44420501e41160322404014001e402410003107405110b10904682150b02981d0544c0c16950b016006501e4039100041c2140e02020141c2001801d56032940c900d107416003180c1e8004014620040a10070001c403914006001d004003c0804801d50402d00041c04140400d6003125013040c82480c0c01d6020700e01c41701c10361000c40880d0307110781c0e40001034018000d513682c5c5030742141c0d080d11002c4500304203e46d500444100d00400884004040c0004010140f2030545200d010f1508031105204850034003010207003a904407251001400521180032800304030300482c41c00304a03440107808001d0704801c540140025a203440b5840701c1c007102519100031004201101 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 297987976 1250 297986726 297986749
    0x4090507031202030f210a050412030b06090a03050706080a090201090b0a110d02100f020f3a06090b1f05251202070503060103150504021302070b060f101d 68
    0x40045e1661813540c140307190034009501c8130b0842011041c0000030280419485050711680d000101d4200640c0ca914049000b481c0c5030703841c260f000d501404851007980714540d5a0000c0c500c510028070125040000241100c030000b0480c00c0c6c0f26061076100b20050360300165260440d88540001a15607080303440c00d0302e8410042802c2540c0c0e10500402038010b5a0018000b000c101c010002005040c02c104070242c00e900c00c0c3c581031079034401d00b000681d1061284c40413185d00c17510082000421b07800348018140010601560003200151100c4040c00002c15034810100011000c8545210a805a41d0100c030100e903c405450b06200010440041080c84404940940c080a2200002491f010f1501d2010b821400148000511440401103034505000480c0c9044c0c94010004500c10411802c140c2c0141100038030032a0481c02640030300850b0402c90014002051007200c561100349003030b20a100000e182265180d11aa8100c0c0c0e00b44101074002c440c0e503180701d15000b01c0d0801480302d000403803041c1e03010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 297989226 1250 297987976 297987997
    0xb0d080f030a1409061501170c07030201091a040302011a1309020a080a0501140601210c0513030302100b03010605011709120a05030a05090d120c0c050106060c020f0409050703120203 80
    0x1c20082104d0f003080441c017188180054002c03c0800c0d0120001102c603401d181c0345a0240d00818008030307403004010b102134407020303210703200129028451781d42c1d40300740350b2884038486075800b00e10f020302c001c158082c01340d0a0841031350703001d054240040720f00260b241c40030700343c40740100e0f55110800f00c10341d03d2708000c2c00003400745001181d202500c240b410600808040c1c06040401880001045144d807040124043c96900310100c0004060300c002c4600082c00030300d80807414013404101c0b0002d1444480c03c030200440c0203801800e00d5407517048810701034440c03041d00503120340d140c4081403000780e803c8100c121000407072404e0403a00790b440401251610400e819000c0c016a40030443c00c0d2040d90000046101c4c1c0c1c854581840140c1340c0400041e0782c1c0f0480807046021034002d00c160100c0b0201640020052512843c22450000d0b40e81c4034182102d1181e0041c1d00000c1400450b281035041444402807140c100f80d44c10408000d99031030f5a03171160060300005048003c0400204c421520820684001d10310 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 297990476 1250 297989226 297989261
    0x807020a0501181401060b04060f020c1005031905090304090c030b1806030f370b0103060f0b0303190e030a082107030203070905010f02030c0a060606030b0d080f030a 73
    0x8020109080f141c5002d1821030304052507026041c2181c030107004010440c5e9050800c01d061604150f0242d82c20385004503000114441c3c070354950015a44d08410b02140301c0e8680f50707695a81001140c010399008244e074003d001905003010321001400c00422171b0104c035507005000030b0680803504c04401400381421074076030107002220043d0400c41d0500f00640128411401c5403000150440038a4a0305112403142940c00d0808928840b0025110014400c02c142a102020458060740d10404561004c1e00240d402d140d440c551048002298030580d0f040c83c0c0b0460095080c101080c0006c0c5628400782886410040c00f4400300c0c4081d101000603071091a4455046911040e000d4000311802103800c0403440942840808950840e00030b1003220b0090030340340d6803c0c1607281480c0041d1341000c0243c0305101144010019a00c001c401070050050040c465030010900501d840b400400b5150011450ba100d240a4013803040060303010821144401d203642c20003038882d641e1a495600409511454559400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 297991726 1250 297990476 297990491
    0x40905010b0301080d0807020d050702040906020304050c03190203030409152601050c070201081311100201020d14010e0406150f0306020c15270a020409030c030e04090308070807020a0501 82
    0x10001c080c605070b5684000319220100455001c4440080030307615107001d030304014110712001d4403e00040803164009840400c10070483e03078070001240c0c002c88056642c0e4012141d1400705260500003403401400540e41c0807900c0c5d001c1d0300041c0d280d128610070001c41594800c03109032566440c2061030300501d606400032104071020500420344c0584004031031a103500e0000041c1140021009403500b01e601a135034803015a0318007001c10080080390310242c3d100b00889000749029030303e041c56503c0c074100c250300158483c450410303540c003078620151482800302005001400312021116aa07640940c00813804100c800b0712080b100d60184041d000a40002c09001c00801800f003260000d001000c2504102c0d01c210345e071a450080000c00507a000a0019010010442200510010b003641c0110780c40c283c500e40801da50004086500140c42100450740352403c0b001819045514509151025101440201d00b1541c0041100400400420a0010315800309220300e10030040900c580790f1002c000c004a8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 297992976 1250 297991726 297991739
    0x100323040b1801020307050703110f1e06011d1603470f040903030b1e100809060105090411101112040f0308030402060f030a0605040b060c0a031404090501 68
    0x8407400c584100c1601191502250340c4181442100d01c074660b02e070340e03036401c1c07040c80d40c1c08590b50400041c040c82c281c880d240d0b030400100020310110884001c1045080710b00180c0c00c4603142030100503406010701412003120f03c0c3e002c01c0040001c542c00030851124852001020b0000d80061003815000901242c0003084040c100c6200b40c00110381c0700017000148845010448007a8039160b5080400e0f820105608000320141000d4100061052080c14045010a40b80010038100c041800e80c000c0d00f124240e20340b22080c1841d4590401302070007840c124001d807030031104040d80c50006206490103050800d0000c2c050103800c1c8a041c0d003041001b04081c105071313003000004140020b0058045818001c0c100042981e1031004211403ca61058540f8007209203161205551600028020782c0c114500f04000000303920480c00842c41000c0300c1c100000c40d682444c0030f0004448a5010a03405010100700e844100d0308002482d1801c103500d46844149030000d510760240d0346c01079900c0401603d0900c000400c00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 297994226 1250 297992976 297992993
    0x2030405031e1918090b0f010f0509030f07031a15060d0222210b04110a0503100f0506010302090f0907050906070309031205030c0d02070204060b0301090f061410032304 74
    0x4115130400d059819103801004080750060440541d01040c190000351165001c1c00e1500c0c2a4582401d1103400c006c00b1001090411505480104854004030410700400a0029540e081c6200039001e0004a241580309100c21551007865144910320109240b401e401050b0111005050b07501054a0180403500301102c02d100e413409080000340703d1520f1030348511300d440b6100b418150002041032103900d90361074101c0035818590480e5040407207850081500e0b1030030803203e0f07600c8158140024003103801e00030308000c07188085c1c11541012300400130040d6650b901840342d10041d60484501a00b80c43d52001503c00c0c3c41101c0500703400003804226501495008480c2c0c40403030340118042c0c4143e00d9001e904886903c0200c40103100141c2c01c2c8006c030750490703042e8054031650b48040d00010312540ca4a4071041c0d103800981c40b504400780c6900e1001e0281c0002d000c0c0318024140c04162030103451000000414181c910340d8414201555031041c80070302c0c0c000315000601c1c03c4d000748840c00c02d4101030419158 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 297995476 1250 297994226 297994247
    0x70c05060703030203060312090d11150304080403030f0311091306180905211902030408060109020306031009081c200702010807020c1818060106090f0902030405031e19 74
    0x2007800340350782c03030403001c0d03081c80440f11041c0000300043c0300c4ac04656201c1c1c0501d003004a040360402c64400e505082c403040d0400450065001e420f4a5448901d14603004211000d40310300901054101008090310f800c0b400c042c2d03900e05000b101d200c0da88940f01c1e5801402801c641d482012000c1b00086101002c42c899480800814003403000e90301c2070703103112150b4040000750b044084032020040001d404c03c0000e218049502550f03520549107090303074a00c520b6142c08003e03000308100c1035000050040743e240801c00f1603c8038000d0b070001e00c128103150f120440540501d0401c0b40100f1001d03c007a04202400e80e000d0b009141740200d680600500d0303101c0d040e601d50041c000c12070106188001051290780000307010050454000c0c03a024000b004580529900d40025001c040310054090b10141c0b040340501805003c0c0c4103d41c2d500e100035142c102d0f1100340e1022940048502c510400611002c0382001c801c50344d04c3c843c11a1110480340030000025061300c1216512881c866204002700701e4140e00007007164 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 297996726 1250 297995476 297995479
    0xf1e0c10180b12010909020105070f0b01140d03090b130902070606140603011203030f0b0d060b090a02040e0a020702030f0d020a0b0109020f09010c050709060e040605070806030a08070c0506070303020306 89
    0x454240c1c0b42d0404240c1c5200b006500052401c03000d00400c050301817a08020300180c03040c9000c03418000e641d035410300040f50034401202c0f41c0540300c00600a00c80320f8550900607440442e03c008240c2800d44000d003c030141800b840302460000940102800f00b400324085c02010108000c540e150b1140c10640c00a110600481020300350142d8586202d241103010740b81680ea800d02c5007072802c5111355080d0b00034641288810f1296480d00c080c0c4110780d503a0900e004000e80503080200ea02407400040042102e8010040d20a07244107000c00c0c811040c070030b80030700e0780281100c4c0010b0347c0741824000203241c1000d2112603001c901c10000600b4816501085100c4103d01c01e0b641c1c6185030362280401c4003a4020314064108800c418458030b141507200b40410201203028906036003001c2c0e100c181c18025240103400c6080f00759800310500003005020704c500355200003185844c20450178030700002919100e060724050041280414030005210082c0662001007200510b80c507585d100c1440c001d0080d400849005 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 297997976 1250 297996726 297996767
    0xb03070b070618080d05070210050c030406050601030e0a2307081c03090f030f120c0c0b090703020d030c06020c37020616060e0d0e0a080f1e0c10 64
    0x10714400c0390840d90943c0f19600c180726070f06040d00e03000301070010078004004604504c941e034021391801c05184541802801301c016560799070714040c20002c05440d009001181011301d400d100d8541c0450104902071226448626407000c40074042da10404280c031134000088074003c880000504620018034122901b03150958009040940e0105404460283c5406822418060911070020344030b402c4d858400c0d902401d041d2444040d191050781242c5402c40380e0008500340b00ca0881c18004001c0d07002e540b046400e030003844d0560030755001c10340c9407051324001414400c024418004100d102d030142c0e40c1401907031044503d0352404805004510301d405000c0d4a11904c80a09081d0f1240795050f200c0c20f840e0042d21040ca0803e4401042078460108441602c180340e644110a080c0d020901c80d044c2d40d81c040d43d80d2400101e414008101d903421482c1d21400803944101000300000c000030030401010b0345038018a45c4c81c1c0b54201c0b165410300d01d41c01c12080c0c0c0812401c6500c600b1903045030020608940c0360204 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 297999226 1250 297997976 297997991
    0x1611031005070206070c0201090603110d09060509100b0d2306150109081507050309010b040203100906050a0f030b0a0e0d0f03050115020c10020a050a08030a0b0906090402090a0b03070b0706 83
    0x286c400785007010019000031402c140c01e10419020f500001ca0101703c3c1e034455460000c2e034440410407105200b03070481d41607072104203014039a1b404000704030700854250000c00c211100c40000030810b10005600802d8aa00d405003c0c0c88c0044500012410480100681e00c4610701101ca4040c0699961140d40c085140c4a502240f0488005408090041e889000c09030700e03107900390143c82076040149170074019902e03041c1d800d80d01c1e100d42c005103011310412004208010308040c5610b0a80e9545c0c1c000c1d41c00f401441304100074280f440c3c0080b0003202d40001c0c00b1000c50f141c0407101405881010341c402401c1c412008003008141e80006034040c8123199503420800380e42ca03000765040c00561103104400603401740f90003840c5894204448031007180f8034011604c1d40c8170156a04c0d41086800c15050358404004420064001968001c0b03121040341101d81303080c1840d0440008441d550302400203806442900000345c91580151312a140c0080c00030100d458040e03071500200075a034001f281c2103c0350390034040c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 298000476 1250 297999226 297999241
    0x3103080f0903060703051911091002160801090201080705070303060b0304110312030106021203251116030c120203121b100912050f1e07050f0a03051611031005070206 73
    0x2070754098901e003200e94141f0b064610800c0b02070241d00e04040c482d06400c00c01c54050f6510068080f0065101c0c0e005401c000c15040e01d1901440060380c4002d4841e4180030700080142c0c0e21020f411351081307050a1680d103d030468101100140b0b00341d0099801c07200008144401d000c0340e000d55000e240802c034100c0c0d01440f00110218140d000070b12941000da4411444c40441c4042900607641c020b9400a80761082188004072034020300f007036a01d450115001d8100722126074410b0100c00d01c42d124101c90a601e0703910307681d1446141103041c4110843c1582e01d000480c110f40e000d104035440000c4200e401ca0f181c10588510356807601c8600811003051294007940d14140c0d000303000c0d125210ba0403100401400201c2542034505612810f01000100010030210720741150b0140f0303400501400810040d10307215189041851b164220300c01034411f910102800300045d0f801021155044001c4040300000c01c658940400ca04024100c2d46038140210038801c582160103a10043032013110f056013281da854032800b1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 298001726 1250 298000476 298000481
    0x140a12020a0c1e0b061e0d0308010512070b0f0f07060903020c0f0405130210120e10050906100303110c03010f02030405070608010b07030c030e030307030801090506063103080f0903060703 82
    0x40d000b05884c41c0c44000506600c3c1550312042c5046050f80780c919440d9180703000950401070104224007064038000140803a00b0b0440d101240304001100902d070b840d041000008243c010752204481400e000075000300d100c3c0180041c2c0c4d0b60582d0081003031008103450714000e0b444180f901a0980224100c0400171210700e01030040074000e20300f0004c044031004e8030b90207000350303581800d03540300c24007000c0e5000309c405c3c60513486203029007201b0f034025104841501c011103040d0b84002c2d003c201039500600034065a81550402c0324101c3c6c2e49130810384400341118498504002c01107041540c15482d008104041c58241d070011449180309000340d818441d154001038074042c000f07000d414201d103024010440001c1c082d01d1106265030190400b102d050b0015800030385554071003e0201c0c0001c0c1181c00402c013051190007a00c1e040b1400311101410000408154081e071040031407000b001c52100078410094000100608000d10741083c840f555030303402c0e6541e0142d15440700c1c01c0d4a0280c85402c00241d10b80e40b00f031 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 298002976 1250 298001726 298001783
    0x61e15260906090d0e0f0126070f030605010219150e012a021b030313080c0f0301061802070606080f0a05070902030103111002070504051e1006140a12020a0c 69
    0x19295005030244040612180424072006c0c1814840800b41c21905000002114402d0070740ea447d00121301c0c5000c0b20020807002002c1109400c0c1070a001d4103205981e00410424100d18484454480c15929030900060401040704141000380c40c0c156003810b40d04041d0407502e075880f55188109440b4421000d041c00c1c0707203181c280e45030050300064200c07680000881c0c1c00355840a4010101c07070421140d0720340e00c0c4812680b47e1101501d644012000003a03401c01d840075800c0c800b000c5001300701c000c2c40c184442d81c6000d035900e424050b1682c002221810005280d005001901c0b1302c6048680c1440701000080e0b5541d04140241c13075a00c10500001170304904c0b402124144c076884106540c0445c0d40400348402580c035881010190b005010303001c555500c992003260300c0b4000c07600340e8021201e040da102c1605030401600694003c401c2c00b009002803074010320b90f808003081005a8603925a41050211404411031700d842c01e0303e0b400052102c1502da40075405a43e1203020701544c28007581142d28038051040c01 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 298004226 1250 298002976 298003003
    0xf130f32061f050f09190519061b0f0506091f0b0105040303051810091406070f08091909020403060e0d0905010e0f0a0801020c01061e1526090609 64
    0x99482c800c80e075803180010f408000c020311500c508140b6014002034141c4136408001241c2100303590b040240d442c100554540c6180d000c0d015640039400e01a00400115101044c19818491200b4150820400c50031110029401c10284ca019040004490b0b8803003035114450290701102150801d5030322428403030007060010503140c007481d151840e80d0569840e00008a01190500b50503010030b40c580742d4001e004884c1c80c00e5a1003201141c00c026900262141c1441d80500038035052240400180e00461141c48180e00f1041458071a14104000b803051805950072001d020361000000135004071079006407040d2403141d0810f008410b06d0510071907840c902809884002019641c080009501a00b110800d00c0307005006070b10401424004545040070aa11001c4a0f030b500140644d146038080c86a10094180b2030ac40e01904003d00e07d6588854030f407070041101140c0514040b001460069006008031044103944401c0400045400c0d9880310045440707200b079005250018140c0b841c0400d111142005 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 298005476 1250 298004226 298004269
    0x9020301261f060308030f1b0403030e0405040f0f050607021504150e010605062a030a1d0109051c0308010e0709060e04230403030b0f130f3206 63
    0x40902c01800c510030309211030101c0581c0c0b60030110205001400840c40b5004040c410b601c03070b0804c0040300c0a2058a10110105001c040c002400007075401640e180c0c008104031070101c0c0903299810b01206008a1030001400c05640520050030400d0118416103e41c0359034007070714000d6145c00c00c0a0340500d0101c4e0010300c1016a030703101c0c291144050340f1010107806040000240d142e00c65000c1081603101e00003101640c0400d1190340442503240104030303180c1d000c0700003031405c0101021014103200b69405000c08550000c181113011a403050108a0081c000100080c5880f03c034040ca41d41d116044100030341c0041e407124008101410030b405128003a842c3c6986010080b0300d804d0702241c40e150311580707855100c3d0316040e40003c0c4400c4801e034411440c515a00990b45400c042c42c01608880301102e91600401c02c1d91080c0f4001c0da05c0c40c1c00d81800050002d40401c501e5180c40401c0e000b8407160407002c20701031032041c92480c1003110302c1c089100c4843d86510406107450b204200308805000e19040181c900 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 298006726 1250 298005476 298005493
    0x1050c0409020304210e090a110306010c03111009060b0d020f010c1722060c0210141b0309010e011407030e0114040603140705071a070e0405010902030126 68
    0x1000c0c0c0d0700455025004440384d8445c64000d03520b1100007801c2000860024050400322110380c0741c101003a03070300407031042c1c0100244600710741c0707140d440c0c0001040241440038504000041c180680d280e100d09008600035280c200000c62000300090600700030070f45403c0c1c41d0003d02941030408190040c5a03607002000d0180924100c1300448070040c401c04200d840c60405800460741141250280103400c4c0c84000c00e0413001c0f50980803d40e20303005603002000b00803041e0058000360310755101031444c0401901e006040401002001d5200c0d01c0f444144141214144160040300c88000c0081c0c070107507000740e131081407112030840112440140c1c49419680c00c10100040b6000078010032000c00710090604100c840354001c0c0e52f00d000395810503403000c00440d441c0d50111200f160344803c510f501c000d01d8240142020740c50340b544200c01000c18080411103c0306008944610701a83c0d080d000040000c2c0140500d40c1c50307203112070217500284140c184021604a2583c20b040046091a01c040301a800030502c42 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 298007976 1250 298006726 298006739
    0x90b0a15030b0408030603010510030b010302061803030310180c08161103070b01060206180a0b09030903160e15220f0606080f01060207061d03190c030b060301050c04 73
    0x1003910314511055110205000030000d280110814495405481880c1d242d14001d007c0c107082d50001000c4100521010b482030000a100007402e80c1034030307010fa52080d00e0300341c80f060084c5071060104400703500d84070201c10040b01162034560507055480b000d80b242e100c218040042c900703540c401c2800c000410710540015000c49144451030221642c54074010150fa40d050f01401e05681c86404252404244080140840b540400c803454002010b28001410151f0406045450b80f000e083e004001e00e00d01c03800714440ea2020070940c0c0c6c0440c0c000303069034825002c0355050304200310140314000a0814050010700241a45003800c0c0c0d64501c050083c02481d40c42c07441c04640714400500000841d03070703180842c0f10100710b58400c0101604094070780e02e89a04044d0000c0d07560b25030581c404421540140d034240b00f00d90b4080c002c914202407059620150f880b0080020303003003007121001c4418a041d8941c5c010305100c000b01c0c08404481c018100300440d0381700e4500380350a841c411550840c120741e00300400c0001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 298009226 1250 298007976 298007981
    0x40b07031404030b0403050409061202060306060306040b060f0703021005070c020613030f0b040201030b0d03051b03040b0c030a0807050c03091e1201021917010501050f07050303131203090b0a 84
    0x70008446a140c582a101e07507600380d000106440c26070001e01c000c2000d124848141c420b0001801c3e1501485802030700d980c1c002002848014982c1d0301682003c804a11942c031a50003401c2c0d802c00c01000d4036282c507200c41e1200250313007140d00250014860400d0701007940c29640b103141e00808580d518a96a040988c00740318665000c10a20031000c011100000081810218404440c0717100c1c03550700c0080c3c2010700004080c0e61800c1c041c10f208084c3d228003900040d4103c0102c0d0078000480b40784501400032021000d041d80142c1d80314051100700012b401c081c603180880101051100c6403202059030721500c0741120390740a180050703c041d500805c07040d0628a010b00506000100c150642c9028076980c80125960aa072200d9207800c80e90046405000c40032200b0040c0308214041c901001c03100401da034103a0350540103108042c1030140018402600b00c0d050030483d50700582040450f681ca0504005403090301d0030a04041e9401c50314040c5a40c0250312038010303100c20300c0d00b040107483c0c00d44444824000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 298010476 1250 298009226 298009247
    0x9010f0608180607030209041b080406110403150504020a060503093c0c042318120c0a0203060109020f03070e01030f0c0201060323121c090b04050111040b0703 70
    0x242c110144240c400300c1c082042110310402090350096150500181800300307803817520346e51603d00c0c2030f40984420442e0f030004e02241d00c01c0d0080f0001c211200004a004643e1181d80c00c094200803191b80342a2070108950080d60241d0b20070f41d1840d904569507542140c0f903000076a500d84c00d54200444410164031301031643d8800c482d150020410140c2d00c08141400e10180c2940911260008055000b4600e09445805440700c0002020860409000050440940000c04210094114204040303011000300030358076051070703040b1225a50301c0701d00c100039a4450704480120f00c41c1c4508000031501c49968000d88070410074070b18015080d13441300207040e1000031030f0755001c60415640703558500c1001c1060080040c4501e0035000082c1c024110704041078000d81801e46c110060512100c0031105070000984c0190080091800380c6d207994042182e18124101c82c241e0000590406084200340716440b29524082ca105000030030421075003010a41841c0154031074080c00060900000300400d000345080036 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 298011726 1250 298010476 298010491
    0xf06030601080d0f090b041710050c071502070b271204120201020a0b16120c090b0318100b0102100506012f01050114010f030203010b070f02190303020c0f09010f0608 73
    0x141c1e8907883c1c0b2040d00994000b40c0c040c4407189050b55903402c40345030a000032745055100c58018002c2e458000400c9500c1e10901200500b001442800781c090303102c0c694190ac00c40d95001c02803011500b461110307090110407006541d0000c280f40e65111440085c005004d26000118803000780c10189480c6011000105e9080240e040d801340c1654100094400c003d000e2007500296a1240221002c2c90018000520007004400451030712501e1f07842c850b0000f041004541410300c038640c0e680c1d034040134251010484030701c0c000c680c41005c2c0f0807040a07140307801c410380a180a0b400c43e14900078409107201550001d581c0c2c9404a2114a03115160501c013032480c0040d050401b0b40480c054180660441c2120401d900c01c04103802e40261400941d0f9200d02e450811040c1442e040d4255414280e82802078410801b0040407560000b100c4421900d0343e14658201d80482d0210314036141d03a07802c01a450b0740407068000d220300c0010001c0812460301c50074050582e1840480348014504185050315101c20141049 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 298012976 1250 298011726 298011737
    0xf12060c0c150f141009051909210507020f0105030702150906070905060703090b09040902030d0206060103060b04030b06060d0b030a08070b0705040e0a090c090609050f06030601080d0f 81
    0x10340815000030000321a40e40d02000000d9800038200b180c1c04075080c400d030340440d84121344103002400604400c0281614003c005c001040d403550004a12400041c2c0561501c441c280f800c8002400100c1c070382c0c01020707400c4100607550995405012122807141181c02507000c0c03581070003529154407030400303141d01c080d845c0101c61004000c0e030399130001148100d8290401d44e210300c041290f01544421204024081500c2c01810480c150354003600d20034003802400500140031400000c41d9807103410103d801c40d00a000e5400e100495400291a83c2c0c042721840e021038100b050005202e80000c0071601103076041a505021130310381e002048584d50044070041c240b65110801c0c081195824050346446600c200c0b20103560b0340151404910101009014100344601400308002406440942c0c0e54030941c155800501540c0034a40340c2e4503064160400c00c44645056800300381c8800c103600ca02e0084407005900d4007641c2d80d503000c040c0e40300e20900421810360002c02c41520028020304640106000d0750801 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 298014226 1250 298012976 298012997
    0xb010c2114161101170103110f04020309060f150f0103050c0d020a0f0e01020d09260106090b041d070b0c010204030b071205090a030504050120070801090c0f12060c 72
    0xa0030704582000b103045411a48030300c0450708015092982007100c0d0800c0c240690703821122410301d900010140310142c20a000b0451042aa94802802a00c040b20050085449041c000b445075a03c0804954064212040c4400314440c0b101c0c0c49490742040e0002040005030608020045000d0100a455001858820f003d1032008880f40c0c000342144031045d0392171581c030f10f03000c28004000c40002156136040d034100344a1070700103545c05040340c1e00341c2d40485a200740031004050142403005448903100f03407652902c400030580b4039294020042c5814105d9083c4180c5c0005200405580040e03c11075000b54014402000340314188d401801c00d811700b58000605040e62070b2100746240b8003c988501c001920758101c031004649500c1210b07080424800204284101e03907038040c006200c0c0d40203050500c00900780483e003400e030344100380078140320040680c1c4103143c0d03885415001e4080c10004a40c0031041040204510210044150448030400c0500e111405036458110080079250003810811807075001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 298015476 1250 298014226 298014257
    0x20f100c050f0c06041b0305030336070639050f151e0402100e0301020408011814190f06020f1b0706030b030a06050a0e0601060c060b010c21 62
    0xf0b805160301010152142d49420300c0d103400d003003171021060503240307012210a0003ca040003042d2a44116480d00340a000c54600c02d444080c40300f5010b0342d90751400408001c1030080008108142160450f80740c0007402020a1207072043c0d280c200806c80600d0145100c80101c0a0034080c14070385550050007a240348a00c0c00d49860705004440011450000b241c0d1705010301182801c4081280d1102d84080102a0030942c5c0090448c0050464200c10030180301c841a1207a80e080d030448008000b410000c00c03900c0e0711101035420601c2c41c24001d4030f42002c5000011541e0a011550403074048520220786043c030300c20790762401c4801c50b92a007504c0d07a9a080c001c160415080c1030060100702865013004501c0d01c0c00e10a8680f0f444420f410001c201810040700c078401c0e40300010900d0410b41d21240202d074039070311101c150000749199900001c075882444000034080d40c11548040701d180c01003905000c41e542c0040151382c180079021000b000c0d05c4402e01034403140b001005071a0070302c0e0628a000c0409043c0f000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 298016726 1250 298015476 298015507
    0x318110d051501061206031101030506040e160503010b060310030b040602040902040920040617150a1203020c01020c090f150405010f050a0812091512180d020f100c05 73
    0x100715210710070b0100e0040c0580740d00040c0d200c2e0142c1011909005031421a91890b02d029107886030241815195400303e40b040d0395035000414003140080440e0f00340702803500708030314041d000c1c46458000d51908201010790300f407a000b240e02c50741c000500b90f0341991540e80c07801e490141c000e100342d8056600380400300b00c004090005100620194a005c61088521507020682012031440040040780402c020405681c00c00703070390039059540210f00c480c50769580110040c0c9100d599680d50340980030a4012564604980b85134458074002ea003190310b480d1034200166038032500d0440f09a8040c141c04006201c044404880d1f0398040c01c2100052140c0b000301c804102a12800c0c1c201005440040b0418401d41c20310020303140041096600402e0340200701d030511301483c81401c403858012440b060784030042d400b904007110340300740076480c80000382c0c6029a401820313062035441d10200d03400740340c850640117440041c81c4a8144c4003540944801c03030380d00034410000e004502600060080a00929150102a0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 298017976 1250 298016726 298016743
    0x90108180d0f0f0903050c0609061c05010f0803031314010b03331003140a050d2109031d01020c0d060203010801110f0a0815040203090705100318110d05 67
    0x2d0301e4100c2c4080e03003540050800d0311090f00b21420000b241c001040402c0000640e07100584040d903409036500c0400020484510454180701d03a010b0f0440300c840030824950340168103c030540c209900d0410b4032902c81a4a1740720a4070000b01c01020030441401090701c02c1e15141d1018844000001c0381c101c4000401c1c105036495031074801410a0b042801034162042e07075001820711240e55809180d01c6c1c01ca030340006440b039902000e0040306003480c14511940042108040d4070b500001120850050080001c1581e03900803c0300300801c6245c1d24010f52440c5600880404542c90340388c00314007030a80c0c3c46010507042070018050451049400d1001e05880303001403800d2842c002d03e000350752581440e001d81d003514140f2000c442c50740010403900019140010640da01c0895503d004002600c0721007048030985034100510b0b0380a8800410300246c032034001107401c11907105803541001c40740d2841d4260103d0305007142642110851070044000903070741100011849000a1541c56071042507101d06241c00ca98 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 298019226 1250 298017976 298018003
    0x21020c0a050c12150c0a021e0a120507030e01031505060f070506060a05010f1103090909030a080c09060d0b0402120907030605090d1202030709081c03050a0e0309010818 74
    0x1140590780ca050075440c000c00440704200401c9051031407089a08207680090940c100785c9008034008000c50700c2880302d001d080c0d01352005480e81142e01604181c444031203030782c2210b40050240b02600100e0084041d55000c9400d42c0712031022a0018005402814844580c98169544101d010038290b4810b40582021503000d140340e0384880c020b10f40185031803c041c2007584034040120081081f42e0340207100d04450201c81c60301d07100308081001c00300d107180508140306034070102c00c20400c468000008050b2401c204c3c1580d804403980c407211420141c034803e10741c0c0190000c0d41004240812040c2d40c0002c060413201410040c80d00d0400600f034410400c0036079603221141c0001c40f041060100a00603240c1200402c07019000d122904031000e00b519103139603800c08420307402100060714180201d148000414900082e100d900303484509001030304250070480c102003480c20300811a400c42610803030107205034040041d403500b0103a40054030003101c01031031504102008144200c041ca010700c0419010f1b00e0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 298020476 1250 298019226 298019233
    0xf060103062733050307080705060d090f080a1d030706031104120303020403051011070f020f090a2f0906070c09062606070c2307030c051f21020c0a05 66
    0x31201c483d0034002c079070085100c1c2e4061141072000e1a00420414200c4078100c07142070b81c40c4c3c114405a0040c0010200140007040342820050074403038028004c0807000c0c0e03a030795020b2405a40c1805c483c4010581e120060b0142e110840a02c840c9000380e03c1001601144078907030f800c0c0ba503504015800389212050480002e0340108040040000803c04e0360150452080306000111003508907205a001c0c00d00003801440303291000c1d8095442e800511a44c001001d0144035040c0b81491901d400b91504050403030041d804004200d40c0c1601c08a000044040d980001e1860081d00504114298024000544000001a0340040c0b66330103445940d009101c4141c1a1101da502c088848500700c2c40b501d60241250402c0c001c0105081c0e00940d10700c141c41e40302d07040c801c00e2039421425200d07806031104400514070030140080b0610140703841c84070859408466030b120075802040440010f1628906090215040100100400ba0402415200c08285240040c2004115035036540b51200d03004003554281c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 298021582 1106 298020476 298020551
    0x4180b0c0d0609090609140106060203190207080610081c08040f081605030c0106080304030b0c09030a15051b04080c1c02040509060f0601030627 64
    0x121081082001306034508480200315544060700ea00e03030300f5080c034050301005015220941d0030342d9004e0f600342103000e89205a01c2c820500440f040d4084c00c4030101d10340c40708100d031a00ca0170980900c1e150040c5442046414000b03d55503a0340c00b40116a2070054040e00702c1c000c190000c0d0b110404028000c014101540700e8043c1c13042d4030891042c07201965040c000b0000203004880d115200030007595941c0d41c4030320b0b96031040e80700003070414078410005000d04a020015100c0c049000c2c06446001070643d171411100c21441c134110a0082c1d884040c0b00c41150340c000401180e0446410303440c43c060402c0021542c03411041400752082c104900c1c81c800980d004800d12300748650140c014402800c04260030360b1640411240c04408043c9000015030644c8a40948421a0018511007284444003c0030300d49003d40103044817101900c031010800c25800100c200204042e007029400b0484 = true := by decide +kernel

theorem cover : BRFrame.Cov 297841726 298021582 := by
  have h0 := BRFrame.cov_init 297841726
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297841726 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 297841726 ≤ n) (h2 : n < 298021582) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
