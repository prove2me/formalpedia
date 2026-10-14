-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1039
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:57:37.885965+00:00
-- url     : https://prove2.me/submissions/0b1528f0-2c95-4fc6-a4d9-435e0fb1f8cd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 186690647 ≤ n < 186870503 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 186691897 1250 186690647 186690653
    0x7050705010605043201120b070215070302030106020705060903030d051012050c0a050f0d12110a060501060e0105070b0109020d0f2d0207080d020307021e0708061509060f03030c030a0903 82
    0x9200300000c2c1d09081c000c5180140407c0b10000000000641c00450707072040368840c9130b4120324001031600c0b40c854142c204420b101040d649030300114100c070710b01d030b080390f6909840790100b00e81391242075965503040d4810800c40b4400e41075604002e84c4465807400c01e082c0d040da14203028941c803040c1502100c50750403092407180710346842007821015150070307608043e200c0c0c000c00c0803070020740c50351001038503c0003540740208a0b28815811000c0320f00542c01510409000347c078105010341002c0c06540040f1351109015589075114030190350030a5001564001140d1a01d2003000095102002c40703100c1685554880041400c42d008202a02000f4049101c039051484654800c00c0a0100c050700c015004100900100b2440c9082d29200f52042d240160f49454104007640303007020403c221868a032502010804481c80030640b04c045404100c02e40e401560394a8005e5820062245502d41c84070f402008a9498105000604801d95014003100d14000c480090646560462510440080e4007506c0601c20 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 186693147 1250 186691897 186691961
    0x403080901110702030c0d050c0a180513021e030c060304051507030c09031707021c4808061303140703020c011142040201080705070501060504 63
    0x2078240c2511030300f4105282030b40001e8480825401c880d00c200015000748060110520807201001e10090802c000346983d0994008a2503405c80381c00151454000003034590400b1001350029103600038003646171303100c40083c4000c4600700c00346900d40600c20490089015183d01c0000d41c05580200020705501841c00381c2440d07070031801401c000400d0b040c6020450300076001480c0700c0c217681c0d000c3d884001d04400000000b044d40210742000e54806034a801c641880103506810b400b0050041030820800c407900011039594030180c10100002d0300c40c912020034a26420076082480b48014426082c0c8283e4a00415142490507030b203070071880b0149400c000426811174044081601ca00f41082c0c2002e8940d00e0194843e61250919414400310003248a0400e20501540c124031703140c021111908045d002010703004220010013000701c030313422044410411a4171031141d0f10880d4140c1d00c10500360798444040300d2540080c1d4045501d50b40b54070021505554501841141c1e070407403034401100c03a41000f01d0001e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 186694397 1250 186693147 186693161
    0x3031033030222181805160303021218010507080d06090c11061005040504020102150a020702090606121801021e120c13060311160b010e01090e25030503030403080901 73
    0x201032003004004010402d0700c4084800641007840001855154480d0710489210a00c0030062150103544074040a0401c42112036090301e004e5070032240c00f040bd03451211820b01c14501c0c690f40946a0050040c21907201c0c6d001002400d1188450341d04001c0003409060690f01203030800c1c070055403100340080f801580308200b146002c03171a0300100180d040c45160180349013458040c0302e024640b030303000207010f4be40208101410650265010304d03007481c24418410003500061402c0303105a94a0010940c02d14140080c1c41012603000c4480c822a00d4a04030341d107414141505c01042075400b80400741500c8101003007100000ca00302c452070703690038610444120804000b13000201d100304c10301090091b80d013001c07491010361351541070005030b980010842030b401d40140110066025601c5184104022910100604a80c91441305103a240d8a8011034410b8810700d5509031001d51150f448001070041240c40400309800044011010700d850b620750314119842101e0540120304100144040b0000900c103002d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 186695647 1250 186694397 186694447
    0x405090d030c030b06160221070906051813060f02130e060406030b040b04020a09050c090f0307051302070c05030601171b0f01030c0228060b03030310330302 69
    0x102407900000169103002d2103ca1169100344019040301f192610080c0c60b5007150386803401070400454620555481e4030310f0182d081564101200003689080520b200040200c20300c0790301c3c4080c0d0b58145e000c6940d106080c0162071254540f508030700755500f144020081c030343c0242e003400203150078528420740440016008500980c5468010400b08000c9031400383c001d42c1c031507150030658446000040c0c200080b5001f40703419034500f4051044036100b4034010507c08c003055811401c1680c1040070591210701510942ea041408002040301c03080147d0300130310105101d80d481c202c1d0103446002003450400240c020714506c0c02546646807030404100800c04c1c40d80303602d001d8401d220258801090070f402c050070215040c903469040c03141d4880d00a004000382001294034000c100c11020b0012207510707180c00820307602c040c504045a081424044203c0c0c0c8118030308048401103d20700300c08810b40c900d441e40100326044001328020030020065800b2021301039142d50140c0c80740c0c00455400000c600c1fa10000d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 186696897 1250 186695647 186695651
    0x306060219050a0206160b07030608150103053708030609010f061d0409050f0d030e0316170c060703021312150c020c09040b0103030905151603030b0405090d030c03 72
    0x4200010400a0303c1210b05606031005a196501070b403041c800c03007441502c0105201c20400421680980c140c1c000001c03910700b0b104507502e4440000b12140c0b40e080a0001800701c2c0c110312081400192660301c2540741d94007481840b01650002032013404034181d001e00448502c180003007400050319105032840d0140c0f0b0640c40050360700f40b52250250410500e000140d00c50b2558402d402403030f41d42c581c0000318254100c810741c0c00b4824001c0100d5260050140e503500401d1030202c5030494040001b0a0b01c0c21080c071200b0380c00d038240d001d0301d0304074280e00c0103000910401000c0090300c06a80c0c0500109001e81815140580c80d00340500b0508000c881701d07042821013400c9452440c022071000c43e40030344080f00551001403d01c83c0d1180482c203140410080c41e4200031358105202c1040382070303034580b4100c0b4060785e43e621080b45c403041005540701c050801074409603810f01208100000702242040346500c039080c000f0341050404007140035104102c9440d5075941002c51400351444d054001c08100500510301 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 186698147 1250 186696897 186696943
    0xa020a0b040602060603161a1605010b0102011a0901030b04060e07080102090a090b13050c0c01091109071103030106111606030209040506090106050f030408041205060a0e120706020901031b03060602 87
    0x40d031100151034231880301851100e0703066418481016085032005407588103001603228003410103d001c1d080389000e5600540c40c213180260500700c502500010050020821242d5904e1500c48803e00c0c0c501605c1560341d1136480034048030041040210030000c11108001603100e8070444200910702c6004e0340302041c83c508050507a41540c4e5510024374420500e40800601503c0355074003032380180a07845c181c0c1e440e0b40c03800c128141442400500d079070700303608119011480c5955003c01201c000040a280382e545600910050002a0080503107400741c1818030101d4075400301d8100d2580051055a0283c40482ea000031410365500b805d0041d582c3c090300c15145000f09500d480c3e001000d030721580403054207148000c030104e000c11080d00100c400400940e49100805076041c2031458450300d0583d00c00340214035254107203080201c08070f460060401c001c41e060b820070303c49842d110040c0d8459550141016540c11074450000d100c000503d07001c01c9170303075130000d040c6080640c0a49040d046180d0301880805d0015 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 186699397 1250 186698147 186698173
    0x30c03072006071716060e2811060a0201090203060f0702060f060303190c05060406050f0a0509060601050a11060702010c030b12030a0507030c0c0305010b1513060e030a020a0b040602060603 83
    0x180b2000a200c3d136402140d60f4842c0d0420942010b090000300814003800c1c050000040c1c040040c08816414100d2081c113101e03038028014014000008100804502e20900c44002d41d140842c054100c1000500021488800c190700080c2000c00880b1920480c0042030300340403c440e410800c599115011800d40e1040d400d0800019980e8018225081c4030710b00100ca004442071702c10100004469800800c50394141403902d08000501405c0f10100b10740122400040c41d141507500806009840c0400541041c0c0c44a40046a0b584d024032000030600c1042ea800316a8440b00b0043d8038440c591640c0006203429000344014183c03503000907420701c1032142d031551102c0498040300710b13100e01040741081c55030f58a040c54141d8a83c040000c02402104881d60004180601900b2039101c5031000c4940c090b1001c248c4056402501a01407444802205c400041c0070480c0601507828210304001e040325003403610b680c0004e0780d41c0c8003900201c04076400400e00300401c0d40c04224090b003011040b00503100074a4411 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 186700647 1250 186699397 186699413
    0x1008011802040902030c0702180c07060203100b0c2b021f0b0901150305072607110d05091002060702060408090a0504020c0d0f05030108071205030c0307200607 70
    0x80240c812003614004100344992480d07040301e00074a5003090940d22880c01601c021182e0b04000016400380005e20f424154016000325103d1007441c10300045801c200c601d0b2511802904018402242d0014090b0081031000000c0003900903035106800034103036004907500801e503841c506400c4107040c900303030801c44c50000d4004c51104250260807c100d15500a00c0103040701821880c4821500040d10800114a1019004070040b07000d85944080c03010f40c6442c20100c0b400c004403816540400f40841204000f03440c20a00550006e032546440302c0025080c5442c1c6041100e018800004140c0004511405051541c00c2c45101049800582001d140012000e521518020030013880300e440050096002e0380d4074913000c0d003c2c0201400031500e5150403000d0a94501c40150007001145003052518000391144042f80d058414000140c01c1d00740c138180038104c00b280030340012503d81c002848240a8102e040000c0c0010500403a4401d6007100c011040611088035080c109000d10000c00903800461010 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 186701897 1250 186700647 186700649
    0x60a030303020c0114100e010b18011d060f04030b010509040f020d030212030c0703181a0a0207050d0501090b0c070b240a080717150a051b030a050411100801 69
    0x141000340c0d8520251000030300404e154081e2140c0c1a00f90700c18070541504400714042038481f0b072608640e0998035514264454081c50505442145d000e038080c40c400d5208040324148141100da0f001084541c3d01c00040c8107030082b00d10003030b1050001c034007042030249081c001d0780181340c2030b5040c90190403e40c6540c0b0364003600d00406130081c4250b1600b141058400c1215060100301000312544030704003841b400285900c07562043d000150030307961207040d050708070454108032104d0183c0744105502d10180003030b00303402c006c110000394090f0310400186a03c4260404481611031000099540b45502c0c226000d03c001070003928400d030b0b050048100080141a031070717400030300400c4c541000007202e010039588541e07407416203500b003d000000001d070308000150f400b044e10190000761201d030040030103060b520b4442e51310100f52445d16102162101036580c2c0070a411031038100111300300c3c2c1c079403920b1514541e03c107907274002c100d0743e980741080b040c00b00b140d5014074810300c00c07104e84040c0664850010201c2c101 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 186703147 1250 186701897 186701903
    0xc04050f010504180c060509040501090e0a0b0730150b1606020910080a06050303070b0a0506010507050a080301031a09030a030f021b010e07050102070b0307030b041d0c0f0405060a03 80
    0x540e1075451038900c2c404600313066244d8402002040140c60740e000801c280c00c0450124000c605041c004190782020340252020140014020414007140e502e0302c048101c40540007009000c0b60f100030f00071000949a800000d44019600d003140200008925011070302c40a02002400c07400300340030700001200008441d450341248181d87c07400301c01410598000d1050b201d42503400160389204401c080d4014404510840282c3d904000c21a5228189500c0b4402c40e031001700904200d00005115021a50000e9005041850618104038041d41d44a16200c100c10781565003040c040300400c01c202040c54841100c003204004c03954107060018003e9981d000302c12204091584484140700d8030302440d03065404503101c4124000001c0c101c06403840c024220700800790100d0042d20400700302940002800c45c101c46031800410319503911000e04034028403501c0442d1754030030f480310694038402554100c0c25030b1a11001018110924a61041200340c1d48030892080c06503042c030f4200000340d59210003010450f50 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 186704397 1250 186703147 186703151
    0xe03030414040209130504020f0a05210a0b04050a0b100311040c12020d02040302040f051e040519080c01150311100c0804060f0219051908130608090c04050f010504 72
    0x550710300000e0207402501425070b000748900c41c400f01031503401e80000b406140240d4800030301001b440c0c14081002080d02595420100324221a450400344004584201c455002920211440c0340c0c0c0c0d50b110340c02c0c04e075415103c59001002c0740c8280f044024110390003c42016403c6403e52465a4200c0d00f02000070200340320356a40c0c580441c2d5280580c03048540030710320324411541c9100e00000751000b900140000ea014a14000e244030380c4080d20f205d0540220f040001168500042c0d030f120380e01064000340f0444540c081c1109222003540341d5807004403c14400da820544030b001a1078618212030049071510341540c9048c00410100c0c10300d07242d0381801a401c2d2514145022103101c2664048103403d00181200400540014860350100c61300908900c1030703007502e45002070001c1c0c400700c8951880c0701070f156812215559201003a0b000348030b498503220710309035401c2000d184118000d1b142c3d1a4081c00c0402c900400300320b800a1700f808100e6801108440401042c10170200303040302104140103207800340d9 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 186705647 1250 186704397 186704429
    0x20d3509010b0a0609060201140c03040f14030a0c0b070203091008220b010602010518070605030411040f090b06040c20010603020a1413020a08130305210103050d0e030304 75
    0x14401e4200070b5030300601801e961241e030350350100141001991300c1050019440c01e071002c4d203040941880f442c0168144d210b80781c01c1d41c4890301c824050200320903088071041d03404140400c2d504001c0c00940f552400d00e03101e858800444c0d090401100000421100c110b410420202303000c0c0c0c1d00c81081100c00182c5181400d259990402d40c1c0c43e200b4401c001030340803016054003400410581060b114180c81e07031640207014945840f01c01c81c2414000c1044100e051700200700602c141c622680107164010300984c0c1b441800301d540c2c0041400c0303c045080e45101541c462602400b40300708251810340025041d1400c0042041c250001004010514123400f020902c2503158000c1c2c060035042400515001030081c80140e6698042140102c40d80c950740340507211003010018901903070710a0b40c0503503100d170300c43d012141d98005a0584d40b00e0758a000314140300050201010001081c45041c0031a908412150460b504600380340385000700ea65051401c00021680500311618040240d40843d141c004130240c0c01 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 186706897 1250 186705647 186705661
    0x5040216061d07030606090b0d0203031905040b040b07020a060203090f0f0a0b0c0303011514070816050f0703231f062411011505010c06020903010606020d35 69
    0x8020a80b010482d02d109415000c418441d0316800394080381d001017810000e6001300c0702441450321418402950680040c840020360900310070345002040c0385c2d840c0852078203445510340d1001750040e03003040040050106e04c4a0450810745601005080b441c0011070a003070034100064031143c0581d41090103000c4a1140c2d04864842400220140c006404410745943c5844407641d41d035082403180c841d41e81e15043e940348440b409044129042c2031a60051460301054ad1074400d02030b07210110001400c190380b81020302180040c451000c500c0e8441001c0e00d125032642c100000516039503d002401201c248803662500b000000c1d10810110080e40d042641c1c11403050700000610195100c2000740b08090440d01e0152070100c04188120226180c070010030201c0c4680d14200c03103460175484010300282d07106009560142d40809803440c840c070f0340549401079000209003910142e501c6803015901000801e03040c65002415411304c1c80c0e11080d164916880b04400c03400d9540d01d140703d85032102d03e070000705082d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 186708147 1250 186706897 186706931
    0x130b06040b060d09050a03021902030a030302090d020d03091406040803090f15070c051c0b06010809011107080909010b0f031909140c030106090b011e1112070605010504021606 77
    0x300034000c43c000c201310300c0c40c0e0400507100c0407503880460041c000c542401895002d50700d0f00000154014004084810b1b103507600354000d40c080ca45c002d03400b804000d84c11006076039a00c105103540e40311f540d44071f1040c0d14020503d047d0000300c4400c540700c1d807020311083c042058008281d501c071407002c40b2070507620703035420000c2001507080152001c00101c00040490a11040c6e914202c21074205035070303040107190b40d6102400d04440080004000c03c0468002c00c006620036104950001d15100001580c100e958640411030ba000100c111860000802c40003070503c0e140441c24010403070881c5036454500f80291905841c40028001e86420714038028000c09203159074442035120307a201c01105c0d0343c0f140c42d03a440e0356200185035040d40300b9804c240380801c0811640c02032895000046e1034204190243c0c51204529680c4140c5c40b10801c003000006141c02e180802c4208450422950a595951002e08281080e80d805801540c06640100300361000c0c20b0300c10f0041070f4025007044001902c10801d0449050f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 186709397 1250 186708147 186708157
    0x50109030206160614130b0f0712150f060e030f01020f0406080403120f020d0b1f12020d0c0c030906020a030e0d020d060507050c010501050f01270503011a030105130b06040b06 77
    0x117050360900800c000d01032480c1c180c040190007105101220703a40e038010506165000c4541400181144001e000c0c030b0301c50368104254080b0503103c610401034580642183c044607550242d000241241d02c085401d0405000c2d020030f9440c000300079480d120140c00d4030411885148550000c004001c000141414854070403803034460343e046810f0040c410018120b0703000c0d401045080000c91315103582503a003484c226400d4207044085070341079841d01e42c0e420015142d2b800070b29000c007000c9400f0817850110a41911a408a10415890b520800320380c605000b450032441c0d8001e58203541c0000c03940700101e9004a0b0901c070380c0c18211049009080c9c280301280c49a20400f07001805181480203200300c043d040b0300505000c040260003000b0071303079903042002021486811514040b07040103425154a1040d0100c0c401c0c01ca0b412440b40c00300030768420120b42140d000e882800680307180094290b0844c5821701526400c40301c0c12407044800907494940307080300c50024049912903540c404101d081600c0d5842503403 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 186710647 1250 186709397 186709421
    0x10c03120b100c060f09022b0206030f091212010b030711010908041a180f03190b040b0f060f01030b0a031b030c12050303040323160303060501090302061606 69
    0xb0b150307407400001e003001c1544402210750703d0038208100011000d031320407042616001480280044580e001400200c5150031002002c800e01c0304618001d80c56000045014500c212010045444d03d55611810020b8441500a074260108120007a01c82c10a441c541561282e18005030b41c0e480d0820140c403070042e40390f40c1d0a642e50800500c0e80c140507000c1c01400c21154156410960b0b003d0704100082d461040c950110742e2a1281d40f540b184605140d03003076254440c0041e089607000e445502c404c041c0e200f203044045070007241080400c0108041c09035a660045c0c070012500c0004c0c24080005a400c01008500d5030405a58020110603030380c1d911419801181c105907400c00c0101d900284028130100c45c001079a65601d400c60029000d075690a041c000d007900280654103546407903808881d0346100d054895105100c0c40d00c0410312034180310040c00009189504045054550720380901500d5980e0301250600c06d030001c0400141c3c5506c5e0840d00810003c007000c3d0f400c68090b1810344020044045e4035 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 186711897 1250 186710647 186710659
    0x1c02030d0207170708190f05060f0a0b0603040f02010c1b0b04090c020304060c110301060b040e070f030b0307090207060f0203010b0c06060405070507060507090e0a060509011202010c03120b 83
    0x18059a00460090191003560005641070b0f51038010841c1e9905003880340d1241c0764051451800a000c2d0070080b9000036204000e0b0b01826203264550700d1801c082a00d0303010b450031401043c010b8005041c40352446020043d10518154a40f546031004880c0707600c138003c2d061040950103042009121413078103200c501051540c04407541c44600d8031032140c21030b0184030001841d003100584ca40d0300010039141103850700c0d0380d0211100516998150317420046001c0710f03050f44d00c40b440442c00c801414003601c00f07400c00e03c24820b002c1c9080000103205100e11071481c42810316004955100b41c4010882c078003070310026200580d90300203500e849802000c0d4011054684c51003c8008120742111500900b10348014200301c5010f600d900303081004032030b410340341817003c98010014400000d12540000d603101d0150b007815000190307281c254a0440e081292139810b6582c1c1c608090110b8900356003118094402c14003044940031007540040d140804090f0080c1c2800000183c010010809810481901c80003802c0c1e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 186713147 1250 186711897 186711913
    0x61d1308070311121305030f01050c030105010f14040b0702040f050906130206041d010f08030a0203160609020d0303020915041d25030504140f0c090601030207020a0b03071713021c0203 81
    0xc08480c2c5c040038043d5900c24001ca400001d21140305004040c09100402d41c0b45185074078182c01510000081000d18040c03080c002c01c80680000d030100540020606000d4180d83c4503501e2041008981c1c1c01241900701d80c3c40c002c1407007001400011059801a04140651108000c0d400024101c1c000c42c0c4c05041540031084145111a25030380320107048278103840e01e0f04000d60700e540c0c04d10780b40e00808107050700583c82408809580042c101c4901b4605018150000d000300e02354011070b50135548aa0141c0110b60001070400b07260500c030004503542c00e90000564207240c01c000d20545120b9154460220a1020b00041001c0071b007a200c0968859110740c4a64400418002020f0003500088900340c0e1002c41602c50404550400b00d20513098400000190248080322420440d20382c00280c4114101903007031040000580752031480c80c015010441c00079880c1c3c91300b510001c025015000c0044501381d114010300511b40703603405294080c982d0465120308802129407002c022941400d101a505100b01f100e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 186714397 1250 186713147 186713167
    0x7090509090c030d080906040206070c08060f15031501120c050a03051c0903030503070c06020910050c1603082b020706150e0105030d140706061d130807031112 70
    0x20340a050608181c0540d07411000c8184d00355a64241264810b6a82e040240002c0051401c0d40044c03e100e84504000e14015440700c98013071a008080b10f00b2a60700c1c006405109070785a0300c920210300707000c0440080594881414002c0100030040c402c00e8802d070f80b0060080f0400c401c99044802503c03001d0203800619540382030003075070748074001400d4030705905c811420040c0c00d01c55000301c0705880e0144c8a00e8903580791182d04450b00359580d03000f6200c0c1a1700380302c50704140d230f0388101d488c503d0820f0303542d184e4903947c29580d1a4209500300000c0440001072031420400a180b801c240c42c82c04c49000090800d01054000c0c00e10f1009500300310069140c4005600c0f010011035030300452030b1074054040c594502c0d80320500361683c0034082c024203900da4412624140f829220314403440728403101c0a08182014a00e80c2c0d160103a507010f42100d80c586251600c10110050200c101d2a40211450541010000c05413134000c25442040e070042c0c1000030f002d900c8940034004011012031500d01a00999031844004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 186715647 1250 186714397 186714403
    0x3020711060708040e0c0f03010302120a05010c09030501050108010e0c19050a06030e191e061803030207030f0905060703050c1f05011d04020a05040c090e040606180e150709050909 79
    0x401381103e420360210110306c40001103410ba40c00c2c401d01a0303065145900355020402c40c080c142000385c0e098801c560709503000030428000c0600300d0b40e590311151411811440c1103402d6401c140c002e000d041c0e02d07191343c0303610515000a450100c010150b5000d6044501c1c2c14150005400d1030f0495074009007c408006000c0340d00d6845144000c1c0c601e001d0301c1c02d003100110842d070807521010002c0d01807160303016410794200c503000044400b140305c0c400014414071180c0e2406c0241c0e01d42c10301030f804240c0c04580c070010305400c4400303003280032071901d00307950a1400c21000400da405080380140800c071001c0f903100034642c0100002d005c510800d0300c214000c0c09200d5496800b9140c02d0081c140c0b441e076171090701191400b400c80310038001da42c01805031000070f0604082c0002010864a1403040080c004400500580c400d410303a80282e0103113801049280c148503a114446510f0707510002014602032405a042202180b1810700d0030390290324078515110780c001110940361640103190321580e01c9041c41000e00f000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 186716897 1250 186715647 186715649
    0x312170c07030f0206040203100b030102210403020c0102070f060c080412141c09090b060702090906010608130f140705041404061109031203191d07080313060302071106070804 77
    0x1a0b034030a40f40f2610b840049856410a80c1c00070740541c800c444080001e02607030002821410040d00040c100510808614200d10841a6122a2111880607c014181c0c14040c04001150a00043c904140342142000c2541e070340d031064004001402d070142c01000280c6040b1001000c0300144800581080d041a1040b040703182c10200991140c64030440901c5211508501803c2107a215009454900580c0b00050164001c42541c0f20404110716001a0f840003c2d050103198840011f199560606001030403e28000d860f28030703148031507080d03d000100345201e50103c4950005000091a6854003442c0c605034042c0c118650150034000c103a494004144540e030700c65400f540050102545c3e01c01101082d21955101c5500750300038000d0744807165944402545c0100700c2950090944142d02c28030b00448000d846031030b80341c4410503100150b036803080201c41e02030240e640255190120100504000b1200d03413090340300b803540101d192020300400b203084070064032014003003540c0d034001440c21855a80c03007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 186718147 1250 186716897 186716903
    0xe0906101a09040b060c070315050702070308030c070606030c0b0a0e040905120f040306090606050f030c01081b0909040c050901060903030c06020708091302040612020c06010312170c07 81
    0x2440c400100405804205103102910702806407800607502c091001a101c0b914046030094010006500b98500411083c0c000350f0003990110900c1020041c4507003550b0b4050b21100441d80039900a00105005400b01c94010700008003180e66503900385061406000d07240e001801080b8521b80001c0d000c19203000074010110303d50340750038040c4100401c01003210328044c005171084c0d02c06032000d007900002500900c222608010b1040c1029602c1e0f54180507100081c038201e48043d1140c0b0300b040103003001400864100c0b07048016060a800c02d00008080b41c50081c0002c00002c3c10100c03903203d0410020403600e00c00300150030007800d441c080c00c0040c8080024410341c2c0c0206004000019950700c90f101c00401d80307074180d484001a59103a16002e02a40101c8030954040d4010000340703207955034407001c200c00c20644400258403985041c03401b40050071035072040d0121500400c484640e9020100d0141c2c1504d50111104209800742c0c5011691184105605101c0c40a00c105001180742c07130802811184e44 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 186719397 1250 186718147 186718171
    0x61f120608070e0406091401020403030513050402070f0209100b13050a050111030706020f0c0a0303060303020c0a08030702240a020616031a090601050c07030c0f0f03020a1503060e0906 81
    0x10765088240d42d68035141c400c4045004642c4080340c0050141e070803400e18140600341020280c0c0070038081a01726841580110045000001e203401c1c0c1444000410000f0001214110700708034183e121910400710b2460700905c40d0b80810001400b240200320740c90094035804030816240c03a003020350440080054080e040c4207a80c0e1140000e81c41d07100b50011908010300354090350500001340c1d6401c01941091400c01070245040c000c1c4507444100300306061208d0b009540c0800c4840ca0b5040190405a00071541802140c08100500100390b001084a94440c5d040d180150f600140320700748054641c2e08009140e1070759000031140e01159000541e140a47c2500416030081800c0c0d5138150121040c88490501a0811102c410206d14006058960004d81810b000b0301e8422284012400c12281d81c201f1205a158180c3c00c3c4509000e00c15940302a0482240c0c82c0f0300142140c0000d4031050152007516140006020780943d15480b942140b00145400c420000c1c6906285200c66164142190f03102c2203030b1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 186720647 1250 186719397 186719399
    0x809150304030f0e0a0e0712140106050729181014040210020708030d061e062102090d0f02040b0405060f01051b030d05041e02010512061f1206 63
    0x541018212030103581d00da11148120344541409031110690b90444560001000070b001480304482c9100d540300301c00c03655800383c1400d002140f40044071403550149036030001d07010060090035002801c0701c11145d045442240803401d600760302c420706600d90019090550581c81440329171002195020b40580e603000907a20000160b440c4001107c18808240c0c40d0312001c1030124001d400e001c200b6800c2e8842e0f51054031501500e45140d6840e42c0c0c0a954090a00caa5442c420800710001d007071a0100c0f940350b41840f180352403401000515483e44807490584c42c4100b86880c84a4002541c102c841010001c2e040b042c5840700c505000c2d9400544140580c05603040c01c030920020f240520910b8464807008122065510741200110380d80d4125144110003804100a0001102d9082001d4000d41500210204041c54180b130251a10707409494822441540c0201110040c0e03041016207c002e19295401d00c4240e0310140003800a141060b00303a18020540c07600e1100b056884000300422161102c003c0c0102 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 186721897 1250 186720647 186720679
    0xf03050d0210050f01120203010b0d030e03070e0103080304030503091e010204090f0e0622050709150e0c090621040302010c0e0604050a05040c02010603240501150206070c0314070809 80
    0x2482007142c1c4c0340624040c200041c00b0041244004c201110300183c0000b41c1100c484020446030382c4c4000c01a40820680c00007800c0d285030400104011b08072060b00d000c4194903641e122011408090401000d01c000880002c0701a41c040000805c40014103220701003249107548058000c0d40a80a114441c41c106a40c41c058000f8500801281181810003000300d03503250f400c2c9001d90301e1540300c9155a00d81c580010b0740411001c0040d140908200040054070043d00c1c074000c0310b00300c102d900129041c40d85100300008140000d042e5141e00d101038407825620200303080258030b41c080e00c80c6e010100280e41010300041c19170540c80021540e003c0c0d00c80803408810b800811146015901c02d0b1580550360036001d100d0780c01c05c3d400c05107041c146400080b074549c0e2659141e40e0a40c001070f00e962415801420400c51100b1039000f040c0c01080700030580610301417040802916004000d0060061240c0c050190081500c620702108040220800954840c042d52418800d203030701c011103541c842c20044510f5806 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 186723147 1250 186721897 186721901
    0x12060406080c010e130f020c07080c010233010b0c0105010b04050f1e0607050604050d080708070509010c050105160201140606070b0a02130306020901110d08060402130f03050d0210 79
    0x141c808540c014541400060011915102502d044503000701041031248442c9080b801443c5002c15060005601d0340030782d02150745800b815900c120b0003680a1140c101c0c1030798011503034001ea21010041d00c05c0d50001c004c2540d802a22424520b82d000030001c0000900c0ba6281001d800d1700c0031508024803469a075030751000054090b5000d2a075001c18002200303c1c05240c142040c0c42c6000040c0f40c1640c1e40e070311407000074050381c00c000070544081e00040200420400188102501d40480c0d0a01079083c0c140f0b104018504540201920305020f17001030f1a8056038021640214100e5101c0002d00c102d240909801c5071180440c81d0b4a00035608044810420b03089a490341c49c400c0d03002402c6241410200d88038402101405081344003a10703403c1013181c0d02c48030782c131200402441c00b0740405656a1406400188100c4580d03c172030311203410001042d61810743c019104c541000086401584844e0040540f280e01030590384942c2c01105400e500004001c00030800500700b10f1030390242e400da4044040c0c0c00d02 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 186724397 1250 186723147 186723149
    0x30506060a061e0903080408060f0a0e030d09050c1207060f020a0506130c0305030a090614030f0103030509030c120c0a1d040f0c0803070b010305100227030f0d0512060406 75
    0x1140a50f0b80c4058842241203941c040c42010b460500d008942ea81c46000843e8415080000290400e00c1001050f9540e0411a60001c40c00203040011592134103000b5124000c0c000c240c4505a203804445091040401540302c6500c5c0c020200c01e0a000c4407251141e60f84080d01c941d4000ca1104034640e40458004500040b0090f004805001150f031211903007881d00c0d4070040c1c11140b56071002408408124100f001e002c1030041d5480d0007885a042c00ca01801c41180740e1002e00e001503007042007200048000418a04595141c01c04540300c202440010781801c0640900c01e4004c19140c00302100c082d000030f100200c4030b00680d4060002621540b84e160b2441007081c00b044aa180c81d03003c100040c0d00154200c0d40c0a00910061034100d448213601c90460340300000642e000138451005200348003003481030390b00150303081c0021880c00c840420300c0f1402c64407214220849070208900c800c4291418020310314400901005e440000d0415000901075420400300500260301540004005040038400d0758 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 186725647 1250 186724397 186724409
    0x4110415030b150306010302150f0406020115230f010e10030501030213020306010f08100b03011815080c060306040e0102030c130e06090f270d020c03160b130b070b01030506060a 78
    0x81b40c1c01c580900c0841d071201094200081000c0040b101a032400801510280085500100304600d00700c0c2c1e00c00c441000c603002034071000400140b82d00b1010f8421011944c103001500c51140c2410740f080180c40000b070308400103810540c103184860080390b05510035810780c2e200721a103c5102e18442d00c600704070f002c121645808690701c044440e145038010b052041d4803054069808611503100c2c002202036400a034000841010404d4604502c1905030158001420000e154500e01c5490144031a82c1d440800070464050031000000c41c4954465030080e44615110600035560780c00c200300001c4090b44000500c0b861000c910b0070124481c944818483e00070080240100b0050702c1c0d800e240314801038094200000341600940c00d003004035810520300640d04924015000840411101a09207007101d0403240c800d4011001c0e10b042c0450b45446c1c0d0003035407401b400040c0c4440c3c4c2d4a02440d40d07022140c00240710000041004010420003500e558103aa1281e01542d00c42c1d05c48006001041010340162 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 186726897 1250 186725647 186725653
    0xb0c0d0c080c0a03080712050423010f0203040506012111100c0203010c0908070815070302090d0501021602040b04090b45060603060c07020904110415030b1503 70
    0x855200d00c28102040c00a01504406140c000c1e9100c01a10340341241d442100403039244400c02c590240c00c41c103c1010359400040c11f011504d050364607003130001c061001c01000e01191040d0110300050942c0070a85044100071300710740d81d042c2418000c0c3c3d5054240329074158400c81c1441003000c000c034402403400a40e07018a001051002d07a0007003017514403100c000c44e0204130702820981c2c00350340c0034010502c035030f03c2c81d840e922071450601400038203000307454000611640c404c440002c51a07000d0b042c21540714140e0300e4010384a44004001550b01d20210201600940c00030a1881c0c405100c3d40f07160103494400c440420460750600706000c00c0c4e0300c0741c0c0310113000c500002c0f002607143e82030680a41b10702c2403032407a07110550428006104c0c2c4001c5152184007036030009191441c103c0f01c208411038100d8022801080249000c403000d0103144a100303c001e010341646804a001c0148407880d82803a0368000713000f486080e00240410115203680d100030344500280340081103040d400014121101a006009 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 186728147 1250 186726897 186726913
    0x90b09010807030b060a0c030e010e150306010c0c09020921100b0f1804050c09010f0603200c03070309050108060618030307080f1e03060904030809010e1b0301060b0c 73
    0x159200c0e41c00030001014191202c00c80c407280c3e901e01008018840080e11145a002401d0600070080a40751983c54148240d10580300c119566082c1c0e8001c4104604200542d40c0d5681401290400c0c0054001003003001ca540b40403429124580185c41d000c03406441280d038217400402c05542040301c0701d044807039030380101c100c801c9034a60540101ca026000545140c8403050808013044401d440301985100045030403040c0410090103200c4030b02c07400822150310b5400c1d418201d0000c003850180c41030f40c061541e40c106111b180d00c2c01c042c50020300c403d0a140d07280c0301c0300d01c40c1c00c4580304e03070025004a0001d003200340c02081e10360190418600070b01c005000142413114540202c03818410011015a06120900c00100098032a60003014038402203542241c560141e00301000c4855a100c4c3d100c41400c00500400000303486da0b1000d00d91180e0503203001426a16000c04441c010f0400145802c01401801d21500f5800108038080000050076002004a81d580d90750759540c0c2d00030742c264007020340c101c207038 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 186729397 1250 186728147 186728149
    0xf0504050f04140901020a03050907140105030a0603052d0f030d0b030c04020d23010303051606092102072c0601090e0f040605070305070e0405070e030303010e16090b09 74
    0x801c1e110700340c02500025480308525400b48042c1030032a100282d03a034000410452481d031500803540c100b4a00310040c1441030814142c1e219440e98005514100000440050303a1101c154110b0001541c1000a54000030036680c40d110340081c906040002003116040b0404004d000000d44c2d500c406d0b01c6401035130400352206584006072012145072030b45842808005126980e40e4401071000301c0405200007405054040746818103070440c4400c07914601070900400c0440d0700041110b24100a03411140c2980c00503280c20002000e191101030942c0e415155040c00072410355904250290070f60f001c4030001a92050000c84500700460b515076190390380c0c21149284200d0b4214181c201d201410070303030011502c90303405040c0900b084566409082d171100034801070180511401c0d4100c40d8614041c4401d00c2c0c00030000c8c16890464140303500850b0303550002401e0500c03038240c54891000050a9a50307a5035112a0030180030741c184c0e03454030401100c150400e00c1d14051040d280456000095407400c02e60580 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 186730647 1250 186729397 186729409
    0x509011713030f14030a0c0e1504050f040e0a0f03030e1906231504150620010b0d05010e1207030f03020c010f23010e0907050409050a0b10150f050405 66
    0x6001c54180500c204d10307000c070032205a020707521480c900d103070020b410780d0701c02e00040400c2c04084110340510301400c2220441c6040c0401c640644a003545c2c0100109011004a00200701142000440c4d011f00c0880301c00700844250307180400d41c002d50782401034001c40404181c807180c0c0d40780b2407102c1555405000b0009180d6401c40800a08443e44410300b005454807480c07808401146c40c5044010700701406815842c2074401c0a50b40c003440032951840504103d0050f01820f41e0ba0702c02e480c18078149441c50380b958401d410032000f524000c0c041001c0704030140b4003203001e000d030f04000d00071038002c2d290103428001001c8240c0c0d010b130703406075a20400304001c03107070940086d4010642e00e2a555207900c1c0241c203140d0b29000d1036003c22031070111780246001d001e20840c101c2e00306801040c60000b046050001e41d0384000380c82000c0d6601203400184901c654506a0f19090750940000c240340c803214100b20b0035803994040c0301c0489030110318207500f07041c00c6081200d0340d03100c91200f040803c0041c002031045040031 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 186731897 1250 186730647 186730667
    0x3030910050a0b1002030301090c03020301270e01110909010b070f02130e0712030e010221090a053006070206133014040503070902090a0b0a050901171303 68
    0x1602c000849a00080210b10450402000c0700c0c05070307000000402c0040624440c02d540c03800d062030304500359414003114403100a1130780340003840c0010103150b0b0b28011205520101014080500800c412661146058500c1d040301d040a0311540c01d5000020b98030b4440030458101c96801002c045070240542d0030040e41c0c005403107015898580e2020001d103040301c108040d00103050b18800310581621145002004c004200e858681150070000403448251203252a4041d0300249004490300c800c4008040f030b40710b4065501880c5d0081d142800080007544908410310a480740706903400b01510082d40b05a41c1d401c0c15201c001c0186c0c40040000c00140455664001c807910401900200d40a0502030f40b0f00e4104518000c0b4040c20071150a402641e007200c100090036101900c0103081c281307007200007500c801c014403400e075416800141550040d40d0f420b0000f40948a0035000755151500d0079402030054001b04601408907070031120300c4698640e10341491b440341000c45010004192141d504884150003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 186733147 1250 186731897 186731911
    0x10c0b060607140714040b010e03120f0906041214120d050a060e0403030606090512030403080d020c0a0c0503010f06030f02040b0f31050106050a08070c020904030c0605090303091005 80
    0x1c0401d60f00c2802d80180f03c40700c02403101d070550070000c45c44207080100f11008403c1c894144400c0b25000b94003a02d001c9034181b000480880c050b515170b11660028000c610401c08081d61140c00000d01107203207001138135080309190080d00cd09048080000400f80e4401b541072000000e40402d00c182c00040c0c0594001d107622020071040424400e580e041589807403c800e0303d01702c01080d151103090103101d40c01b17520700006100859005201c0c4c250700402e80d032070303200c0c0340030150101d0350026425070002400d40494111440c410101d49030304056051414601201d800f42c2440795081601f0a41d03040d400d400361405030303a0030071042201c0400c2982003100400f0802640ea03003004455000d42016654401c880103400400080c802081c9071103203000c3c60801407450010f80b0646070000511040340d003c41540d17905074040c10305001c03e40340c5400541e000c0c14003000003584100b03158100800c06d607000c860010b0881c4100010301aa4840e00d81103a203e000c00c8856060a40c441403030b0302e103040420f03000543c20100c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 186734397 1250 186733147 186733163
    0x1021204060b0f0d080904050a060b0d05090a080c0a0c0501051305010804060623180412140d05070537030b0f0901081e03070308010311060c010f0b01030b010c0b060607 74
    0x2e01c00306142e099130803800d4034981d0011644c80024101070080c1c0e80d000700c8080d010803801d810301004130814010700b140c070041e180e40e0303400003005004100030350b0312941c0e00840c1890320780b6a0109040e0f036403400e40204441840881100050350350040b0203548401d1200400118818108401111400401002915a980c6581000071990b801070340155a481450240c41a075400c1002404402480d082c1410055902c0204100204140c5000038141001c103150840101c401c0f0100b0b401140107940c1401c40346441c200500903c2d94200c001007000415140c03a070480e03aa0a8448445d48266003140c40644500e40d038a9000c8a6100382d01c01020b04000800152044d0703c4080801c1c10610240c000122640c0007840c400391810031035002c0c1544400e0a03004500e00440741c0ea009184103418880201545951f44c029043c555665082d1b031188034410000300000f40c0c41c04500c0c009800b08500d103d012920300f150b50907855204825640c1c050b50401c078280e03d00d031960010b10500381d01401003920600 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 186735647 1250 186734397 186734419
    0x1080f04031704140d0e090f101e03140604020120010f02040803030105010e0a03110609010c0203060a0b1207030b16020a020909010c0e040207110409030e0d0506040b01060201021204060b 82
    0x41181e440b46004500603441409140380c0403000901d03100c4000080d4050107003641d5019001e40c1c0e007507801988940b240c502d1b00c00a032150b190340394100c1c03042e4100040c110b10300140c0c03010301e00010800e00200c03405016242c03174103100041c0c070344c0c0c0311042035030064001841c1400c01d00c82040c00800800581ca0b0f2080001091550342d0803480c102d81154201205a4000000401c102c0d0ba00070b044002c503900c112250810307545940c1d01c12046144c1b50181d5409500c0c081500c0b00780381c1c003440f00211185e4024081ea000791802403c0d0400030042420401d110b001c040241e64520840022841e080e40e03409a403801c82915030a02c042d0540c80c9140c240300c01c6100d00043c0c0c6005866001486001c1c5081c00b00205045098080107000f0310903406029000e603105008020100d802d524030b041e0071040a4500168001050a0480d021040103884641107032100c0450010400e00003071152065019071140b281d566243c20b022420b0b846a40181c803c2c9100f1100801d02084459106030340c1d201000380100016 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 186736897 1250 186735647 186735677
    0x1c051e040201020f0709060311100c03030e0a0204060b0705061b18030c0a0e0f060102030a14091503090f1b030c220507031a01140d0e10111308070501080f0403 70
    0x20311501b007401525120002002040703000c0c0d100c440821000c44080782d0320014110000c14080c100b50700517040585801c0c51800c0c54005108075851560040d000740440c68403090342460a1384494803c03521880b9407000038052009010030304440805124a0914054507096260020740100421580c90f026052403a05580c1c2c1d50b00901008054400103c1070340d2520880040f44202d0040c040c1c2e041d07401c20406000190b6004c00e0700c4101003058110300e40c8400305240030800d46240c9005003a00e9010000501c94410300000f028864100d00200300d4050078121003005440c01495100d40b6007503446403003124420715001520f10714040c00c684001c04143c6404800c0429550150b0360300c00460b0b502e0408a402c441440c40308072265400f0b0a082d41101c00b403d8642d9103030311601101c5c14040b0758074a202c0005a40600040030b080b601d5103014403604280c0125440a54010800000c1c10350013030600199542e000310b9841c0442d40c058440c4c1059a40341268603111802c000e0088080100f03d84000040c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 186738147 1250 186736897 186736903
    0xa0b010e24031f1d010b0d0207020409051f0209060a0534020a0506180906280e090a03020a02041d1506120c03070b0a03090f081c051e040201020f 64
    0x101d14840e82080c0705400342d0848068045003944c210320004142c15082c144666440f202050444a20b00e0301907070340b003c0410b9400000e00400741d0082d44641494040b00512000207001c0c4005140d84c0150312850000c1c1d03200c041240702e02c148042e040501032103c0c000d40e40c060400380026092000406102450000c1402420b01034601040ea444002406000a50601c100070708090314040e80c1d61481e01510030340101445014000407423240440d0000a80b0702d4442c8a03241c000c1c4218550300d0181d04400f4101110341d6000e80c0290200b08401030002003440000055008510750590068181c1200c507030240310117002c2c0c411019000000002c01c2c4002d5030000c00c4034005070003c0e02030418403030610740d04201c4284031080010505038806c0030201c1c03c41d580810004110780c0d0b9019280d64071100c90000303601038100050013500b01c1c00500b41d207200b48040c01008001d452001c00c000c60f0701680e221018400c58030183c80002e48940000b1444400122450006030042c3c0140116001d1940c22104189 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 186739397 1250 186738147 186738151
    0x5070c0b12010605070506060f0111010606120b030106050a0330030b15031b1c02030106091a2a0c1c060f1107030c140303010f0e0a0b010e2403 63
    0x4504100000c5541074500c030180c0d964007400c0b15190051400440d921250f5464001a01c058440c41400703410b88110ba0140200d0700527100c4940c000c0c011036170b6810010b41402a01c00741003140034288102e0102c42e140622404041c0c40340244061f00160954990180490802c0300c04001014a46902d00118191101c00144102290f50110743c05101805020008070a10104001d42000f482400185002c0c602074510303001c0b000c03200c10f80340c4c00110081410003a01c050404442440003001103000c503840300250042e10050f0300851607440c0340700070b0100e0600c519075054040d002484011403002c244620380d02c151651450032200303106010400202c0410207580042c3c041016000040c041110b81c1c041e65490b502d4103481080f8004000500850920034044004e041114850078102000240d100140d00710010400302c98036503854841901c50340340c1d03034001d070b8000b20b0010000030500c03000c60160075030986041e502c440e0401100380600a2000c403c0f0845a00117005005005c047c00c02c6402841c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 186740647 1250 186739397 186739409
    0x3070204060b0304291303211d0615040e0a02030d030b120304050a0e0603101104030c150e01110f06040c030c051e09070c050f0709050106090f030f0305070c 69
    0x10750340c0c3c1090f1804d841002480c444800102080c020794a0300c5240184030310f070340011414120b0704c02d0280c5107800c40d40300741c3c2d0b40900170142c01c0600e440a00c0e40c02e950b01c4030307110b9140100c2416412684271003540c1d450104444090030000888500c0041d818250400c82c580600c2404403112681b050340084d090003000070381d032400aa619100302c201c6162181d0301d130f4200c5202c1c9010758036042c144030225600000d24003c0c3e44407480c011001c5150340c2c408000c502c540700c003e05801c010f00291a001c0c1c2c43e50394004e200c180d545020105000c254030b00c1e141c0500400a286842c1d000f45840c048005446c510a9038101c0d81d564003a96001030354000c010310000380b0551081544100090071403904403158013540d0070142c0141e464403a00c0c1a60540601c500b04200c40848400030b0a940b101c0003100c0407420620014018000c41254420001c0300061031819181d4450042c4042d03a200c18089030780714098460140c0c1c06c054242c04002180851a4560146001e071400030702e490700e10b4a50b0800b8441940c80a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 186741897 1250 186740647 186740669
    0x140712030c0201050112030903060c0e060c0607410c01020a050c15060306070305091606080a0f05071205091213030303050c0918060a05090a0b030c03061608090307020406 75
    0x5600300307039420b1141030301401c0c2490078040c42c0080744d10004c00c25a11400300800780356540125061507405002c0b107040040c070041400c1e07a00d101e200e05207a1981c0c003d44083c0c0c0802e0b0036080d448401c3e0100b1904401c10a0410415018011100103189508250246507200103804000301c1103441400e000909004035591601c5039940306601150b0b140000701c281128200c0c03005400e000e000d40d004a01a41c01a00320b1030040746e60344038084102e00340981045a40080000000300240d0b00b07401c410990300c21983e140081041c442d50140390000d9a0301101d442c00024400343e1a041c282c2400d9110507041b070302017000c8601c103075010620b1032003c5d03015580101d031922804030b0400806034940103080e0311040001c0c08600b0041a5004201d1000002c101440140804000604c003521100722100c01410010900741542c1003425a9000506400e61154024013811001c40c000b41000076075a801404401c4006074120303448d001c1210310400181620710035010801448016039100c1c000c030f41c06001c0000301 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 186743147 1250 186741897 186741911
    0x610050d060b011e1701292503030b040f0c02120a02070906030f05061b0f180d0809040b010206040203190c0e010303080f0906070f030506030102090409050102130501050f040614071203 81
    0x11704407260592054a04030804031598100242c181404140400c2044103152298034034646020b5045400c6519481c1e0851050100300340b5070b05400c1200040003d880070498103c0d6400900b09403074a420b8a103016070b00c13210042010722020b400400d210816441954041e0b07407030302400019501168010381d0480d801841410612005100154100c59202c01c064a4040c83c80b074903103414000c19948220201010444079200207240394500c6514200030b020340690541131a01c074569410900b6080e000314904000c0c170381c0d00d50001820b0303402150018002d081032114154140210414140c04690307614001200040306050003a442e4082e600c20b488012003460440201d0021200003005100580d02c45024000860303000984280714142c00d25011440d9610382021070b0281c4075182c1200e4102b807a02ca400e80900030198050540c1070301c504200d00186076924011255801502614406c02c10100000c12032940901044071400c0ca042da2002e0034003505445904c50008100c081c0c030042915401 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 186744397 1250 186743147 186743177
    0x90605040506090412050f0f0c0d02010e120d022803020d0c0c030c060504050f1b04230a0519020304080a0f14042d03080403050610050d060b011e 64
    0x400758000403d496030383c800c1c54207446803102c4810102c0b400003070010004035a2804a003000440d910b000262006903503e28064500550301c29148621600551031b01184d00141c103004910400c08003d000c0342c41d8205a25010f10a00950081c20020304040008400100b95250726119a20600041c0c0340140c0350b10b95200a10181c41c03030a282d0a08008042108800103504040641070303094001d070b0000365660342c0d49085c529080d0080003903019403003070000c0404030ba4404212240306500c00d0b43c0500409586414000e0110f8001000f403280e0310740741c0002402c051583c1e005a0f84903c16111445d000a05208014100e9105880540d031103000000d80501d4190403440304500d059162410901c41c035010301005015001d18010000e02030244642c1403010070b0500604044012200333403a01016540b85880e20240d44a8803084a017409440c00007041c0c1d0080511510440d038014024001079035850740c500c2c0040448980f25414004400160807485d00150380319250312040742c13100307126124554 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 186745647 1250 186744397 186744401
    0xe04060317070c0504090b0703020c01140c0403140102090105070f060906052403070302030c01181a0c061b07030305040503210a0b091509130807060203061f02070e0a0204050a09060504 81
    0x138100d00c0c0220308210620001070000d00c403050744203140b4540140c507038400900c964003500e1071030134019540f040c40d0180b00440c001c5400400c02c0300e201e06460412894149001404d0380a500c40e1a03011500512103100411068900340a04d00d200c0c0e600010002c515680300000c0b584182c0350340d0341c0c920142c202194060f0400903c2c003561a130443c0102102031442d40029594500c550f40581004101c20042e44e04008200704075011b06845000c0c42241c4250111640c9c2d41e07009019130159a01c82d00b0041204140301c0b4910410201c000e1000c18070744a0251000d40c0505400703001155544000c0024849902d0030202d6012031040125102d40e10342004a07441d01030703942d603800c150320500082c8240895041005072414640c0c606a440d80b9141e45d0300b1180c06251030b2216800780040707900003804800c1020950041d480313480c08454503c62100c4500c02279400b42d084402c20340c00350340010401e002d860b00c032100381c9612101e13245e409403410341c9620119a2010581d1700901c19030385ca0350740c10300c140d141c14 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 186746897 1250 186745647 186745649
    0x7091503090224070812041b0b03131a09160602030a1d0f18040b010b030106020307150b030a050c04060b0c030406030504050a12020a02030f0303160e04060317070c 72
    0x80d16007400070400e160005480904070a4080314000709030000c0f009000901c01c20b44940380d800090041e03c5540407903205003051801c0754200c68502800c8032241ca01d003584030040040e070b580b020460f802d5560b0581c9009181d801114140c2c1d1a0b0a1200302045010300076885620400d0f20001609450380f141c800402442d000350012009d6400c02d000d54203015602c1100d1004104040800038920301040c00822080d0101c4114203801500b10b0a101d20507200002d030542c0194031540a1010703507aa6003446550178003085c060700c03005800070008031000c2000c90715241c0d100c040144002a4a408640003e8948200d0100442c0e1607000180000c44034034052140c000201102c05540c1d150070050703031100352240b00300c0c012001032560b103030302103418003078108400c552580d4010014104c2c1421814003139915688000f00b00c0c401e108900345900d41e41070100680740a016140c0c40d0000188850340140c92858280283c2904181d03201d1000011881c03c5900ea41c000a10400342c40e13440d07100d404c2000080c141 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 186748147 1250 186746897 186746939
    0x25030b04031205160c0807080408191109011212020c091305070504020405010507030c03030f0213090f11030610120c050307120b0f060f160302010b1903020a0e1e0709 73
    0x20075200c141c3c005400c502c2e108078555000900e1135551b100c41c03070308c00200d009640124407148102d001c000e114607104000406514090070002403040c1d00c480c1004040030090080c054003441400d02d00307000521803500b100740e040309401551030075007031540441d480820842d1100c0c0072721489a42c600074000c00b88080310150106079800d43c9000d04000001e002842800e400034204000c250400341850311a5110892040c41503109640c0c840e60f1017603000011003a03000c1c40000742d02d0002c40e1a0318890a100f0410b0150030f04180c181180c0d2041c08000740001804007150030320100e140303c240d40d10828485d011040381301d81c5403c1d45a040444006200e03920344560656002c2c0b410002503055a80d051b92801403500403980c0c0c0303035282c0f024080c51400340030340801143c03d44001c23500d00d4109601900002c03489032043e510784007500309886c0302c8001e01800b4403019400000d01c4c042807141608002216520070418900c2074800400e10317030100941c8508845000c0003804410046c003034001c0c3c24004944e8419 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 186749397 1250 186748147 186748171
    0x120609090209060904080c01050103060c0e03060f010512030c1212070813060b040603050d0309030f0c170c19030f0807050408190c050303040609090b06030925030b04031205 76
    0x3006901207501a0000f4250600c1502e481000400300441c00c8226400b280c64040240b2155a60f890320701e0181c0b0410000c0c0b00414042482c03600035003000516144030300c0c01041d40c004aa407814082c803c0000640c1c46100045c001040040346032141000b0410005103461040c03941c4000c1e80411081800015050310200314410b0140a800c140e50010b001f0201d40103d800202114040c2c0040c00601103580024110301a0b00028a0200c1c1c040e4054a8003500030b0b15142144618800100c81c10748000400030000303a002003060000c7c4040101034620880703070b401110160203405100324510700c901002100002d0740c1e40c80704c1c0780055212200c243c200e00716051507414581413048064441e4082c28121a21022140c004020301c00c0302d40f480c8001300000b4050782c1c1e5898840400138010401806480d280508001c40c03c07030380d0704081040ba48108480c6001e0301d581c074506501c90140c101a000c6001448a55841c080081010007041d14069440303910703201598455071080c14180c6000410090b6010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 186750647 1250 186749397 186749411
    0x40f0903020d2706020a0b060405060105070f061103010e01231f0903020a080d0219020303030c070c03050d05031801060608060f061201080601030507090207050d110307050d120609 79
    0x10390001886030300c540c8182080b5500c3e0060b4009604a03007101d05840500c09401c281c0041ca203600450070054441c0140164091561620103000c181d50055600d82e0000381c08100b024045003280b104c0841e100d00c14000800d41c041c0130105004150800c0c1c01c03001035017507a00300411034040748510200c01200e5a4000522500300400043d055480740c03584071211016107101d50303294134481c8428201441d4012300701c10286132510310155440001c4088400907100d0885011207403510590402d1705160f004008614507a00d001111015400014046424003c13140e00440001ca0074026844c1406407035031075030b40360b01d40004d12020303070703482c2c6812003071b070360740b41550038020300780d0117000d10b603004500781e5480004182e6807001c204a845079500f0303404141032210020966031008114903040328000d10803550210344400b1004128450050003c000d40e010ba0045076a15005540d2840039095000030b0f130b0306000c8a03403203040c00c240c1840c003000001454808192380044c220310402e0060006c0c210104490b03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 186751897 1250 186750647 186750653
    0x82401030206030408091005091e030d032f0901090e24030f070f061403010e161e36090905030c12040626070e030c04020a090302040f09 60
    0x50103000107070044500100080500c0584002c0361880701026000003031a11181074000c00707079000903001a01c20988911600c9400030400800300740241c00501509981405501c140c1c0284a00482d001d0f0901d8503040101050403c0080c00d652211118074880da5401d102000414000b070980142980500d00c50500800404520000c80e0400002421a01c004811000130340303491940d8546840e544280300d8046803050640351400308885043d120407003450200ca09804c80340c0400d004030505c003198240000c02882514030000300c845200d040c456616010030000b0498185280c003118003103026080421141d15807421040f030116105044d244011140303800d115040d19007481070043d40f036203c1c584e040500c0022f01c21508813008100480755604103806800c182c0c2d810911074400801c0050500082072a0312450f50807813560481300d10002a9204c0701c042da14603100741440c0d6050320440c0004038550301d451000b0840340182e07847e031000d014514030400c0140d4a2641c042c102c100d040c40060000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 186753147 1250 186751897 186751963
    0x90309090901060f0b1206010c080d0b060405090a0506011d030c0d0204110406020d03141017010f020c0106030c051c02010818030304060e0616080c0a09080d0908 71
    0x1614108540c0c200054542001081c0508400d800c10303e0000c852075070020b600100c0c00d0080084245480044001c0d41c2c8140042d54082e00c0c00d2005880b511040004d04280c4800b640304494a080007002e0300d086c603456401085c101001113422410055844040c40704a40c0c000071341001032038644090301044c0304202d000c20344801c00d42d8602402030724140c0c08501199600d400a8040d000c0301190507403160390700c000003540c0301041d89458000c20b1401100c01d04c04207103851b2181c0308156648245011915100c006621600010300600f180c0d50386201e540e11606e694001081410800e60010070240d007181005204a0015071003a48146c60010000e01c800124802400550313409081806455865100d08840001c980d07280a11a002c0041000704200f903560044d403a11a0780c074110f800755078500100030106a81c01c11a0780202d00c02c1c60000342c00504240081501404610700320181c43d5aa40d0300341c2c941003a000c2002c0104014040501c241d200c1000040e22404044851041440f51902c1d9410 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 186754397 1250 186753147 186753157
    0x703080f04120e0604180903140702031b19030506011419060309050307120513050f01120c05040317030117071401050904061214010b0a0302062a03030406020715050903 74
    0x400e0201c210100021030313071340b90252001003007401c040110340310f4010040700090000380000c41c08161641c07640c0400c03e1040e020b50300ca032a0f01a00405078645221483c2040303e0a44803031a5114581c0c0484104215001080100840c44fe80c0107122a5040900341010610b11100340c9008006a240e0038602c41102208041240c215041c00142600141000c1381144a242c81c0507043d48400c0c00c2c80c0311126071010081921100340c1005603542b03a218010840341502640e842400204180c1e842c0d5281140350340000c0015031282440d500d01582e036a21f00901c14010340f50240b003c90080010841e504400741c0c0c0303415903800f0303c2c0a44031081c185454280300c690000542ca04110020030040e45988840c3d10003070180004c0745d4082003611292070000e501000b02e0464030050350a01c0100c5411781000b08915058940c000c0c03066003080104c1a450801c0c40ca20086041c480c003510340042c1e0f241d8014001180254084c8901503aa4016400d11140f0400c1f40c64100301440d02e45801c00c05031a101200740c0d4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 186755647 1250 186754397 186754433
    0xc05130909020d050d1e051204020f01120c110f010c021209010201150b0a020c0105040f03030806030c0a060c0c050904150c1416020405010f0f1e08060c0703080f04 72
    0x1100700860022442c01d04070300d10004c0040c131441503654881504805e81c82202c508402c2c2c41d07070345440c54503000c03a064004c5450440d8a010000d021800510380710f42d40340404101813422196982d0640445000e4a40603400ca00100708543e480340e184090030b00a00303040d0f05204000707001001d80007400a43c0c42c9060751048007142000700d40580305a100b0b400400f003100c04040540765260b243c084041441d0720803c100405071144550045c00380d4021803c3d42c08840315103098488843ca15101940c544400a040300d906010310a5419141c4c0d0f16810340d0b402a0035150b5444901540718500500003009541000344a1a941410800003840c200c1d548545522940400329081000400658681455001150307080c000032481c2003815416148074107540d0f0081303a0600c035a903078541210058542c60301844848001803141800207150260b41e01c846410896800a0b55a985a0301e007410700100740d80c1034841b01400030310541807503441120690030811a2800011034103042c0e55541c45d00071030300c02c01 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 186756897 1250 186755647 186755651
    0x6030703020d020d0e19030816050409020301120218010312050706290a0b1603051605101a030f0a030809070503030708030406111e07020f041e0c051309 67
    0x6a02a1103501500c0007108801825515081d00750360201c050f10039600601702038455401007076240300c0905c420400980c4c05880c0d0600684a0300503a002080d842800c600c14441c04100c0018020300c40d100550081030038102e0105a01d00500c10400000b034610044001141148010320100d031060110000c1c1e180e180c1005541c6050525182007d4030b2095468000301034841550410444084410503213014121190750302c031501e031b62808955006940c0c1d003402ca041340101140c001f038090401071050641c807810045100d11726a681d145001820b09500c0c079515160740501e221240d10b044404000d02c02100907103042c120142e10241d907035140030805800c22002c3c6000c54464442488060083c1c48080c0a07070b55210a182480703501e81d4410b840841d00031386006603400c54a040c00c425203c94104030361503807072541640c1c210000a40c000e40c4050741c1c0503410317070b0008010f03503030314030801510003482c41d903500303034aa1411030384007c4a0010919400f800820440f019651002c40e00c07080035503040c4200 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 186758147 1250 186756897 186756901
    0xa1806050405100c060509060910272d05010b0d080706050a181103160b0301120507050a060201140109050c0405040911040236060f030718062304080303060603 70
    0x103d070440002134000d4503ea24000c00d1099000c4041213441c4115801c50450320021240c0e8040b60440381c108091000b8184010341c0038803501100541001d40d41d000300020149000c00c120705c880003402c84a11498005c4015000d001045001e00800c40d440750116408451012540c951080c00d105410300149000d40d01c03400941c00404e164026482e407500d18146a00d40d100516111652101d03074034040c1d01c688256150a064002c0341e01002050b2261224071030f0450b4278040e102488800254002c0368035001c0d00b88041030750b8852007424001044d190b40080b490ba00e22100507281d032541078100340301d5582484204080900034208880c112171055070300042151003414180e81d17004c102000903074010300004400c4440c6540303404070811a40c048148200201c0d401d8117074810032540e10001c0e60056002d0101a02604842c000355620012070b082c5440446d541e0b002d0440d41c1c001a40022020650300180c2c980d281802c40104110a6403400c4107900c2e05060600c00b0341ea034040144010701c503140001c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 186759397 1250 186758147 186758179
    0x60604031e02240901090e06011b03112e052203030608011107150509150402030c0307090507090e060a050f1302041214011a010f090314030a1806050405 67
    0x3c20b150b15184400509000002c070040036803a50b0000c40300600240c05000040b4058000207503003400340344140c544541c02034061001031741e10b900c540c90135828803400c4646100c100d2010f00c42e0000c014078801e044440b02e0440114001c2415002102916041c506400c22441410440b2001229405140c0e02c4e652002145011405820540c00a000e15401d002c285980d0840e000c000e080c010703100d00503508200e81c40304052000c81c0c00807111400d140d0300034840c99817030622001c0b01300d07041b90014041d65080150000801e00c0d1231030650081c0c2c015076440301001002980490701201900c00503d66031407a041c010001180d101c098000e092082d44a03040c42e034116500d03040b0300e40c0d800010075001d40d02d0301d80e07441100c401e9802000007a42c1e90707190100340101042040c0f148500d107070101d0481c14600c0c110b8500454181070b15a0b030346018804203034404804100517412011401c03010b8001142c1d1142c2c0c40e04000d020808001c4003209282921005001c1a5004000c2e00c055038025540d00a4204142d1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 186760647 1250 186759397 186759409
    0x1051813110a0306020c030a090510080c0f040306021206040b040e0c04020c0102091e0306060405240112020f13061107150c080a2c060405041a060a0207060206060604031e02 76
    0x80d0004000e144000b079801c1c0c0e660f0000c00542503208c051f840d4100c84913616014002c00a001c1503000c400075000b400014610405c04000d044508a000032190819480355155012640204900c104000702282002030b00d02d094040c50b1003132141640c0c1802520b0400107155170710782c002d0b400140304980205001074009006d50540d40d9a0324024446203245038004801e0400031290780165019004420001d10103007098052980210807001c0c65401d00d80040403540c0030b00d0219021503040000301c41c07822100a0140c0050300058140d09110303030f500c40e81c100c100303085108150f001c4001d20012440900c00c940c0e010410000b10342100f50140202244041c0c102d41e81005410010141d60000c6001d050032503103d00403085280503059176a0341040e0801c3e101d41c400711a401030780e41c00b0108000600890a20b07400085002c2010702401103503540c13941c0017807115045140340c8801680b007605c040082039030400185801c2001a560729141c01d007075440e020b04c02030f21a060f4026040300b06003030000719100c02c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 186761897 1250 186760647 186760649
    0xe031c0509030d0c080403090f0e070e010e1027032a0308030a060806060f22020f0304060902011706012c090a02030118060f030b0414100501051813110a 67
    0xf11404022620003c0400f4150010a840c194001042c203800403484281c0004c403d0280c4154000348000340e03496000c03c542020390b40c04024100590103503582c0007516444004403180b103154a85000c01c005e041c1803040101d10101d448100500c0b440310800100300b541d265215001500035809217184803900508620710707041e52000349007104c0003040000c140b506505c40030548214a043d141c2c9070302d40c0707410485260782c6002d6207680100032225900384c0392009021800078118554001d820104111011000d68004550540d00603480d400da4134115a80918243e14000c3c0300c2c25074805505107280020940c0b00344c42c1c1c0b5000141e1146c00240115140304070003e0388400b000309a0141880d000d031641010303400070311400810b00d0340e82c034001e0105070080c001c0c1402d841c0083c1c000c900301455520344500b80c4c5005801680c604240b100c0076007840000303008200c0c18102d4000003082c107514080078051034502d010340c1d498a4900e000c0c28400c1c0c1001810001001c207400c407503004514000c4100042a01c0c8017 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 186763147 1250 186761897 186761917
    0x40519080a0801050111060105040e0c091602010e03030106080c0a0c080304030f0905060703050711190f05030c040207020f040504140312091204030b070c0312050a0b040e031c050903 80
    0x2050000008010400005005142055540544907641c0f6401034502039841103d85966400c840014805410503074020b00707802d114001200c00040720031000c254024002e50309400300e00c1000601040003902401220f40c000310980040d461580342000041c00b40314081c1c02c0c5492000001081d075800340c0710342490040250801041c130f0360f0741040c1c0b03801780c4440c1d07900e803810700814004800010b140c41d0460540e070f00c081d00740c1c403000d00d440540d541701c0c0f50f60000821080d901c0404031114544a140f910000c00103086003c4440c1c1215080000300343c5803010020f0013600c1107004200c4000140c5030700042c004441016030700492151654030f494011404105810a9940300108602d86104203003c500307401034002030142c4055600f20307242c000a5104601002d0f0a40c022071010404083c41200100b0102d400383c50301900e030411070340204041d50760586000b2203041d20b801a001d4949454070444401d000706c0300c0114a04040308c641070385a408842002c1d00b0381c0703580f2070003d003070010180100c1e1035041d5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 186764397 1250 186763147 186763183
    0x7111c0c06020d14010b16030e03150405060a0f05010f030807060f0513060b0f031c020a02030a0c0503010f0b1309060b0d240b031b1f08190b0a0e0405 66
    0x50f030141c0c003004007005503298291105400001034180350500444202d80d00e00c0340501402c145d0360700c0680d1003900820403141c240c8a11101d000c1c104003c450528003440c8900c01500352404c2442e04201541d00510244603820701e484010400380440c0044d4000316079008081548600305418100300408000c40072070461414101000b20111500322210b04041c46202d04105021018082c884403c1a1103103541e0990f0000c001d8400703600142206041e0420144110703421007807a5804203007013201c800c004660640c500c017000d00680c5020f004a840101d1100002c01805a070074002403c2c002103404a8015a0381d6640090284441900640f204020140a02c0c2e011007040c9000b8200c00c0c50961240c0808100b1030039914100210300403460742c218001c000f0304580780c150680350031000020740050790000d100081900950340144d85448124429101c200701c81c039217041c25007110000c418039900c1e541d00e01520341c005951400c1c25803042c4e6160144160866585203405490105003a1042c0c41c900 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 186765647 1250 186764397 186764407
    0x31211010c052212080309030d090503041409040c0324060803120708040b1b1b0703022103220b040b0304030909060b03070309020102010b0d0c050907111c0c0602 71
    0x160444010020118400c4000341800302c01c07801c0d0f01040105004a1400d103100b03d15090200700328002071608200b01d1015245054036002c0c1c508112401500d0860702d6400201d400c103ca00e9070380001914585040d06c0c681d216292540d00d155607114107000040c000c1c1035621005403c07446000c071440d640302e01504200300d120b4840c2026544c0ba0040901c114100f421480041c80c20381c4100c0005004650140001c0400c1c1c071a884080300016000c40c0d9420602001c1c00303c0103207101c1c002002c0b1482780e41070f000f51040e1800c500500400340d4410b6a0101400136845074107014820000854640310712071074000d1015102c1c54000300a07a4515400500105030100c3d01181e0104044015402544251600d1140340e40d10801082603415078420800010018000505c050317000380c100700c1109205200005001d5542c00001d00c28200d0588103a50803040503105005505110303000d190881d08074103040c40c0181c03015100340e9440e10740403955005c1e100301c484850800340c003c071205002968854019500c7d6 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 186766897 1250 186765647 186765671
    0x1e060d02031b04061205040f150e0601080309060d0e100903120c030c0807030f1b12050c09030604081c020f0a0f0c03050414031006030602030906010e0105010903121101 74
    0x1a400c1581c031a031042c5070303416014600b0340700c62080310200d540c29110860b044090500300c1005040080080d95030001040c004d40004101c00280c071007500c100a40080c0307a51107020040e20b0000140c01048440d801017120100b59a2003005a425110300d51a01107440a8030f10551400d02c0e800c80da219841d41c1c28184400201a009280c1c030400100211302040096a03a2400720240c8990046150120304a0b002181c6498420b40000034450002900880c1400c04100c042ca60005940020380002da082980311828000f01d000381c1d034100345c1d440401804c060400340003139103842001d007008264800002d1800c0700f100441d90240d404010f400411900c81112280d00c9081380c0c13110740310400040b0310207120303101a80508510501c058140c0d54060410341000d4a0705d0420b0742140d0402c1d803501c25229600500007040c010350b00a0b5101d00d07030142e22420306122541c5481410381050030540e4a84006004590380f0040c83d10449402030302991451490703a100740c810300c01c140510096542030039040700d41 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 186768147 1250 186766897 186766901
    0x5151e12060402030d210b190807080118170c0f0a060504020f01170a05130501021c140c09040207060207050114010305100b060702060c010605060d050114090105030604021e060d 78
    0x481c030300035030a64190001a204c112140c04c010303038540030880c000c805a11100c15250340140840b8030048d00c2401103448400d8150710303031042a4411101648140780600808101780601c805030024084103028040042d80c80e0410101200c0a00101c4d0038082007140032140300300b040c0300313040c0d001c075050b100b0211050501401030541181c5c140e0041003c2101d080b0694800e8104652124100b1100304407030321183d02600103400040d0441c034942050084090100d18203100400041900000c4401380c3c2c0419460441591001801500c500100b5010851040e415008654401c03404540069644001d40303000e0000740030740070f0084c1c070641c070306902c1600c000301d00c0c0c1606050385e00402c11912701401c003589a10a0b5448045000d1300410184001030046c18420f000d82070909220780041249910b83c004034a407078000d010107041094440004010a00360b030444202941000d442c540c1456040c11b01081d40d90b040608001d001d01d90340e2180311403012447c5d003010059580103143c569500c9540744d401c00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 186769397 1250 186768147 186768151
    0x9060d1e060f120f260a05030f09030406080a02070c0b0c0102070317162d02100e060402060702010509030705040c0509090108190b0a06210b060405151e1206 69
    0x14842260310008202619040c00f0892404d9120340d0355501e211241e40c03803e204400b604c210101c10341802d2144040380c2e00d250082e0000100c0c2d9070710f00c1d0f00c0b454036440b039040300c20010300007009a810400085c001c0740ea02c050841da1200881d5805a5605018a00300380042d82690040030a500c000c500384a20034030640051007d40d000c2c2e56181c021074070b60410080441001e130349c0490303003c071000036100045015030460350308141c442d05800b0880590107038004d0403511941146006070004d01a030214485140304281040303030103000518141c42d0660105070588030301c038030103414003030042041c601c142c1e4208020406040094400d0010040a48004d41990041c8000c03a10034042c03e00007250358000041c094500481d010303101507808030940c6410f440500058010070440d45c0b80e00d004215541c00f21051a59100141c45009402c05241072100b500080913004030710031400c2c50140511800c41c8201039214240c101c0711a42e0141c18155030703041d0000280000c60b000482030b40d0341c01026001140c414 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 186770647 1250 186769397 186769409
    0x3010603050f0c19033201060c030207090b060d090507090e01110a0806191409090d090938030705030a030f080a0e1603030f0306050609060d1e06 64
    0x4402038542e1100c1420001084981c640091801e000840d80d400c0c803036403101d000c5282070500203031201070002001c50415244010308000a8a0b980342031780074400700c10300c41c01410300d49803c50110346140e030300944828081c81a03c0d1215214078114441d59a4041100c0b80d24030180d504120780d000a140980e1a50494881c4020341e600d001c044030b01c0d00e001030154500c4044040342d56850800c0c2194142c40202000c0d040da030700880302c1e0b00040c1c1c41281c0e1072601405820462048a0050405010072203003001c001c1c0000320301e0f00302d80c2c14490366171b0b003221048098480440e00403c840c0c140b002d444008000c4070111028950fa162031164148151001100c03801c04207805450070f5070f03168014503644e12280d10300280002d00705407801580c41d216800a5400c41401c00700807501e050003422079450444480005124160000400c2080641101d808407003010f1070f09040c850703280741400082e0140038101d510341c082c8600084184c804005580403502000100d00d59035589418591103400628140c0901 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 186771897 1250 186770647 186770651
    0x23101a030a02030715030e0a05010e0111160f020111010c050c1212010324020c0309120c0f1e2e020c0f10021c0e030c120607050c0703050102070803010603 68
    0x25140e060106100001a030040c0041c0095454070410501182032032000c02c04240c1e03140c035640c0d802c40062003055142809880003041c1d10380c0c1200c0550858251107080d40349880b00f0010b00c0541c10f10b00d9064055603800c4251103d210781d0030b00043c5c0300410b42e0001c030711565181c00c21440c0660307004000f0300031702c00da9001258004406200d040401d881260b0f500140705001c5c000400009a16064516400501040c1d150141c101c0306c05100590300810b00c008001c1d04041030030700850800400703440030040044020701005079070703c0105604420b642c910703030b028a88540254411710300303604d090f41400c5809041e44809034000030b6446143c407901c000c40700a0241041c41004800e10020320714455100084c4641d4a403a10941040390310b5400c03042500a600822142640300c03460807110f50501c03481900c0700b82c141841030f0300301400c2c0201c1164807840351803210880c15124200013100390784500309041040d5950281e915880c944169070707200070401d40c000900c020802006401441c100c40c09074500b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 186773147 1250 186771897 186771941
    0x8060103091e03080a110405090403020c03060c07110a2306070b1501080a0524010e130b040b011e2a06140f0403020a02090a09060e0604110d0f2310 65
    0x822081c2d8000303c1b809218040c003440244480e1400c2c80d1016045480b030b00484030b0384081c030000300b4104070342180c2c2500e0024000c40c048090200300005141d03100c1d01140c00d0313000343d400d064403160321078042054140501c0501c2443c0c0010f803103240880311450342000a0200e0346c40c086404e10707403101404200c02c1c006040701010524441c640e0103960b028000c503c60b40c100c3c0503a1841c4080f0100ea88110490401c00c042a0987c0d05d512a46020031034248454400304410345150240000c1d20070402565041041190105104000020608500c003500785403250036041d111042c03400d03040104c2507a001081c1a414410100329403580960105421b940705a20542e644480350f03101300108607000750168104007003800c014500120140e6220b046820300040400080d280d4000303e551081c114240c031342c0703c54180414029801c9195843c08021540480391120640e902000694032b0000103107407440724601000d50354241c0301c0590400401e0011a920240107010800c0544031a04042240000c4404 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 186774397 1250 186773147 186773161
    0x1e0a090b131d04030807050a05070b0a1514060f0f0702030601080105070e120c0d0c1503020903010b091b0c030706020304050c0a05010207050d03050c0c0307030311101b08060103091e0308 82
    0x80354402c94241e10380542c6980e94890940343c55100d5030034003040140c00c002b420300044040b1501c6005a040c070400203464070b030041c0054980388040d00f0080c41800c070717140070940c00d0391800d0481e100003d88040e01c40c2c0341c6036442d0103d92180158007000754140152400810140303015440300340b04040560395284010500340511404540190b000c00264010b41c103000c40506204200b403201604c140d500034015581d80800d031104000301202d54001917000105e541551a0901451003002d03411115143e150421b0021003079140b560a1304e243d0041c0c0040381400c9501010303c02e40d400c0a030010000c1d9940c0c03405140840e211480f0710900c1d40b1480380b600011481d941f00003140d2081d101c0c05400f403c4540c1113a00c0a96054000708890222803040c280001441d403030078040e0800031403007901c50104119a2441d181c0c203044220800c003240e2441c0c000f801d49210700000c54400b4401e95410081c11644070303440104e01030114440003401001c00d602090045075880000d82420a0090b0ba541c9641e48031382c0d13 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 186775647 1250 186774397 186774449
    0xa0609060f0303030203061f05070515060105030106140c070f0e07210218060d0204063506270601090501030e0303040b07120c020d11031e0a090b13 65
    0x101855070050182032050001a0095008680104000f80113401c000c0d031403503245800c01c07243c02c03114000807008215942000350400042c2050303000c0701030f0803000d0b02e0054002442400305110b40e90070002180d2481400e1900101110507420f240f4003550704c1e05855071107020b24070740e21303201792408980c01e42d001840d84d512078902009030a18480b9804002c007680c40f070800c003035002034001c0300042c5169011109960f40d480005d0503550400b820258aa900e44000540502d014130142c5520011070405074100900b5040c0003546441840014401500c5e23002c0421004031440d80101003030b21425070f00d241000f0f002601144151000d0ba02c0d4610261110011001c0c0d0b02c050170402d200742d00900110b000074070700a5a4540c00a40351400c0740d4145001c00b20401030304d400b80400300c05a040700d803150004a500048a0421030300c02070003146030900c1c030101003c0307020340310101010240703002c141d2581861042840400411303580317201c151a90301d50344121940300820310a010758141c0d15158404192000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 186776897 1250 186775647 186775649
    0x70f0507050705041524091a0a0c150f0e12040f0b030402041e050907120f1b080106080105011409011a030402210d020c0a14040e1c080a060906 63
    0x300300079001143c60b0006000160207090140124481814408248a94406403079090302040400d56070b0070403559840601201410740051022101c80003d500f030b22403034201221820011440e002404030514105071043c072007a103405203a42d5080c80050180c101040d00a04441c903611425182c0712180d070b41b42110103118601c2a00c10707010fa000713400c0140d0f145d190045c0d90701a002400200f00761200e011001b000d041c01d0f40650500740d50300c400344081c661080044c0000386c10032030080b100b0a4440c0d140d2031101e00304400014913a00559210004e0038441414200c01032001c03800901aaa44400340c03d8080c090901407405540043c4002907901d00c0d08100460403660302c00410350801011050840b5039a00041090740c01840316880d00c000709525415030210041450080d1002d4410385100a040ca130b101c080092151441c80c1040c850440c104101c50b04000c4210740001c2c0c0d0181030020391b8280461812003c000f00844501c0d0f0441d19007040e440307842084240410452951504c002d00215129 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 186778147 1250 186776897 186776903
    0x102120c07090e10110309120406050d180b010b0a0e0901061b1a0109021206030a03120b0f040e01020c070f1203030b01110a05100c02010b0d0b0408041805070f0507 72
    0x102580030008100164000500b20600f4410b0b00d032001c824030005415a0141408201c0311400041080b02d1100280010340d907074003903100c00da8507051420800030710a02a0800b0302083c2036403218000015148910b8910005900848a9086694403050110107070040c03a8140040f5200e0b072190b035000c3c131741003c00c0360503545207899000840780062404511940300a50442d0121181942c10b8800c807804d05100d80201007521000d6610041102850a08007020300131601903446681c446d00003c1c0c100ca2075070769898104d40009008090400000c00540490b03000a0b001803500c00002441d00040d002001800300d01e404031403050f560781480103080b001600c02c120110004c3c2d4850800240b1a400055500300c05140c41200b04007840c120038200050408226550350141c1d5561a26014501800035421601d0000304094001107001c02c1c000c100c090002071940c0703645400075041004040a80b130141c00c881000703a0303a0f034090300c1415004140030b59042003c501c04101841255100d4012140a01c2d4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 186779397 1250 186778147 186778153
    0x102c0a06111005040804060906020a0c0933050a080708060a11070219030c0504020705060f0601020a08040e060102120a020309190b07050a020414131106041d04020102120c 75
    0x450140101e94401d0001c200c000766001d0081d00484805540c080c40e4000c60007a44101c0d82c4d01d1a015001d801c180c1c0d954410740a540001c0100b130045504096020201c0e1070800020400051300c42618011220441c2c007980690849003440922582080008040e5003086da5580344291702d80700c2603591429644940314055011400140c00040c00e40c000b016001900c900860502d110b650006002c1c0c1200c801012914400281c01c0040c0301e9020079076401800c2c2580d04510700481c40c0ca07036a0329000c00410b200754108681d400304a091f48204482d60956030008005074846031200d102442015080d588a8014458041081d6a2001010031210301c800d031600210321302004401817141030250710f007290005001c43c080c00207201070100001c0207481d20407405805d0961240c41004120344080645140e0301403080108141a0313011284081080c0d08a80302001e504d83c41c400103107d61040740c12403a954080440c5e0003c0d00da01c244e210500070340c402d07000d56002080002c42940300340920600104594 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 186780647 1250 186779397 186779399
    0x60b1e19050702030c04061a2a1c0f09030308040f0b0c03090c0f01050a030b0f09010603200901090e0c0f0d1a030604020901050d0302070f0e01030201020d020706050904020c0a02102c0a 81
    0x19014014007441d501030110602068140841c10700e210070a8007141c094ad0030265a4420305547c03803083e150a800c05060040000a104400030070400e2640002428030000c0004a4280078003440340081c2558031950760740c19807404100049607508151212201803089103400281c0745000d04e011500d024040e5501420006440c1048002d843c0424423550400e5040b80da003291507d0b040d508601904990300d02003100c400039455888030354144040e001441005000000144e239200c100b450440d0100c03250035100d52070b0501401054032600e0b1064000c041d000a00e80300e05062500440004558107030038201c92203915040c035880d0030f01154001c0d84054580c00500140c501001404404c502030b01c125580c0c25201c1100c0012011180c0201d850410310000400456a04101d180f048c2052440030b07103a810b1515401802030300480c6402c038865030300403500f1800042c040103440c590740d4005100448450f12407001404000a24407030b001452400240b01101d4100c2904074071000c54003509041c251 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 186781897 1250 186780647 186780689
    0x306090703020702030f1c05030c0f0f0c0a0b0411180408030915010306141008030a030902060c0d030507030608070602060f070201141810060b1e19050702030c0406 72
    0x1180014045800e26609000301400b41e20708010040e80340e0b80c1d102c024094565421a1034000010065040301044420420410038810341c800366200c0c001042403542c2c55040020000059018445e0303124924840d907400d500501011030380240c001c4e8056540c00c60102c0082062085101c07402070b4410000c6801d0340850001a44040195808a4014140e0340a50315031455083c03c0d02c0c00303900a84c1d01644a565103551310740e41c24409500103186c031a940c1da803180350800550301c9008a03420a41032560340c0700c40000750340b41c4004641141c0e003c103060701c2c005414100c002e001400700784c43c4900002d10300700380031400f1100000d80c80203655490300144007641c1c5007290b048540400905450071952514802c94880d061100158000c1c0b00d0005102414481428028130b4540a403448188150415100700140707810a41107075903440e810f014245101c41e008880541c01e1040c2d5140c03c3d1078058603c1040b0352643e009000d00b1800b4400c40c1902c403501c0c894420002522203a0061040d058021620042d503 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 186783147 1250 186781897 186781909
    0x1206080a0209090304180b030606010503160e06071205030a05060111032203050102072a030314070c0f060e030c041401210605010b09011116060f0210020d09050708120306 75
    0xc03100380b036400c592a00391101c00409486c00303549a0301c2825038999658540c1803405116542d4881c0085c6031243c10762400141d020190404500c034034050060b103050100ea40d440d00400c880425820198080aa28074143d00422581c800c4400c640041c2c94a0041540ca62007803c526609000306d00086007004440302c4610608144484201400d154071040000090401c0c00589080341c05003611080d181190403091035a87d0440070b241001d140020400d00002e0f8100360601d0a9a4400c4180c588071082850324248a11454024490403d4511800901c05030700c040d00c0c565030482541a80c0320702254000340000d540d010120404405d6a070001844100c415a801c580140048940341e003e001131504c5100c120b810a03002242c0000000846054550f0040304054040713000c50300902250b1100b2600d0010800d96000d1139081000c6d10f288502c420f4420446c0f064450485c0d0421990342f00349240c900700400d074038582107030140a0b03150b0010728a0000b04018400b0105040e0b4189540e0b01c420400803 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 186784397 1250 186783147 186783151
    0x4020916030f15090c230f09030a0804050901092d0b03070e01080d030504080904050c0d05010b040e0f040f1203060905090a05120a1b020d0f0308010302130b0f0904020406080316031206080a0209 85
    0x480c150180501202649d04005020119000c0d40c0305555884c280002c0c44100c4005820408513a803c02201c1181050740c2c80510246145000c200300c00c1d441f001d0b50200c080c00300b405c0f0b603980c113200d148004200449600d07407180c12244007a044501d160001c6000350706030354040720040c0008a080c8220400b509154101507400b00c0900c005a2800c00c100c02c054007214002c0e0056400920081010300c01d41110259694004110a40d1510325203450390b134181c420f4001410003040e4403025038103202013a0003600050701604009106002c0d41ca0080c00240c0d40303c194031001d803094814401100d501c0ca040710b00b00c6010a080b40d03a841200c003000c5410628000c0c03801012030704404044101c80c0450184036510004522039a41d01c0d40303d51650041104410242c00c0700c600c40d601d4a8030040741595003114115144c45c007030300c2e2040c1c1541d4500014000f8407155008018902002542c040300c03482c50785406041e580319403039403d0404071286085048411038022040583e110b441c03043c0152a02c0ca251503 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 186785647 1250 186784397 186784417
    0xa0509100503070303080f060103020408101d030a020c040f0516080c190c0c08070501021009061103010b1209061b070c1e060806040504020916030f15090c23 69
    0xc000c0035500d2000c40e142c030040e60300a8000411800070310011070042c0c0d900541016091030154103207420800d00c281c031800903083d4940720541c0c0f8140034020b032132011860480100c598059030380700d0003003a2010f511900c014440a2107180751032262080d0610038841c15000e850105400741040c00b641000703407242e44001e0040d100511003480400302180a454007940054401d60314122640e2781490490601d5030140c1205003030341c10005080c001c80c0d900058900d40d00710340000100d00c3c107620b400c5c068000d040305c0240040590000001081040d0a94010002071030112042e619581da0900b0180d00c4510607182503007401507580d005550b40b400c11015001040c022403003000820794803d21400c030812030f903904558030b0a00c1107041280342d0304540c20607800301381920188a6071400e03600060b03c114000303000c15100041540034102c500e00c030382e20070121a8060310003082130449a0b025001215064815100c103075051079020740d0141d00c20300c0b542c801c03150a403034403011031407089010040c0703604814610 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 186786897 1250 186785647 186785671
    0x4051e040503160c03050c03010509030a0c030c1403041802030105100309150603110111010e070603020a1404030819020a050604140a05060a06080601050d030e040209310e0c0a0509 79
    0x1450500c00703501c0b0743c00580d1280c02d60007451403540c1340c0355007013120307159560388a07901d404100240d403040401250f0160009160205001c03c2602e0700f40d4945050100150000311640c0760018038040000003403054881c2c02c03c40c4a10540300d50403074070580c0b00034043e10341c10542019034071684a00940122500910403108400e1045602c5c101c8070444070b65501c1956600901030096995581001d28513102c62030140080c42a4a00c01c0040350341d074003d501c0703030608050f400240799038054030948105400c0940a034940395940d6880c1824605030700890101c9088210b2312502400440c00081d2581c001a4402c000e0701096403541c59000b0214040400300c41c55015008080f400504103008007446846c81c00c0c40000d00f182070100c1280341040581296015001240001010941041c40c141c00b403c0c0c104c03070160341e036810a408691000000301405199241e01d5440807405c3e0302c4841c500c1e5200c0900740082200702c80c0d1012156803108012069904500c03246000d1220b424480081a8019508141 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 186788147 1250 186786897 186786907
    0x11060c030a0e1509030c060318060903040305070e060102190602041d0a06080c01092c0c091003050705040905060a080f0d030608070f0b0901020c040c09090b04051e040503 75
    0x540e04660000c101800080c1a90102c20a103251940651103404042c18490303040004000101ea40c0e40034a0200520892000c4001800c40310350b0900c5483c40d40040d010303200740c0c0c1042c502160741c0c2c0d0081c0c00f04950300d000d0104040783ca400c0c2c0308440c5104030016030041140104030001003210f0a0a54026a041e54081002080b2141400f0140000c58504130660005140260032001112020307000701495070020351240c0c0c010303a0304c150620b0a0b10b9030080640000f5000350444280341c1481c0c0d402c02090280041040040f000c0c0802400f01c641c0107a464444007003c1c0e4408800711031040300e4032800700c4c030180420301850903568043c0d6804080a041d412007207803607041440c544002035031b07064000e50003043c600b03e0241d4140201402041c0880003083c4450900c0d8820801003d02d000f201880b81012038100c545a1007007110b4a140d180c068070030807a0416420000348521030074041c0440b03444c10b04000324010f042c584626480b405664003030907400e5500340b014129818003c1c03c1070f55240b000b0f01c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 186789397 1250 186788147 186788167
    0x20a030605010f050109080309010503010e180105010b21010513110c03220e0103021c0f02180907210b0601021e0601090f0507020c0f0a0824060604030503071106 71
    0x301e000e020340055007003800014940b90004128041903004030359560818001c000c0d599800c28207a03815500e401802074107a5803040b0f40c081c03484102841081566003040000101d01d440e01008042c00100012845a20801100011507490080c400c59030404010f0031b0031006442a648640c0707001011504c118170f00315200c1c0c081031071900541e44280300c009601c04036089000c2045000c4000b46111144284e4079032440e0000380c1074080300c0c9400c24001c100e8915400402182c1c1002d0540306a000b04803102003003080e101200c000608580c116814420010046991601213800b4035900e0703089041c21200c0d0101e030ba50003103490405003071a810362040002410155078810f803114003030804480200510b40c50b0600d898141c2c0c0f50441049035442c904800e000c40d4950100b0095801001601d40c1c012a221240114260030032540c0f020406000703038103062042030401c0121303e4080c40d00600b40c0340907031110020440107100b6880000c00350703481000fa500c00a203c640707541001000c014005030800d0a541 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 186790647 1250 186789397 186789401
    0x102030903090109050904121d0319020f0d050307080a1803030f1b02010e040e030f130e010602030918060418120f0e0604030b09030702060705150a0c0509010c020a0306 74
    0x9108406141c002049154180d64090201002042c0841e1841224141912000e081c454030549400c10400490b440186401040440c8680d600019044510301000d1020001402450100c2244903420141c03070301540b0b01c0d0030b80f0081c1e8406d4001000d10724104e107a0395002030641c420506c0105010302454003000138480080100003d40c0241c031046222402c80c1c04c01090004180e200c40d501c02d03a04001600513136800380c03888903500802d440004010b4a0411094658061f1514070800b58100184400420240741e2010040b03038030320401d0540700e98036010141d841e8028061000e030404141ca1803d544580d0b05490140c1004014100058181c00164402c40088210f042650890041c0050402d401d07400307500101d0040480c034004403214080d000043c1c5a12880c800648004180b10201c3d1001000b4400c07218002e500804444c7e8850051800d41c2e01c0d004c4903803000d1019165580050316202c2d0320b00598413040d503142d03034141ca0201e8110055172011b60b502c10680e0802c080d1100840002c811b4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 186791897 1250 186790647 186790651
    0x41e0806070206070305070f0504120606090203101a0f09091b030c07050c041509020a27061e080615070c09020903010b331210030605060613060e01020f010203 70
    0x2e0b80508514502407001074192030019001d035003040140340304c07038400540c444240c50a0f640b00a01106480d8810304111001d0465038111281c0d581c1300200713020603400e0b105c59140c02c44007070038a66030380d030003c600303802c20180240f194040d4041c00411a0b9415442c004a4a581c040c1c038490040018214000c8003506503041100c0c1c1d01c0d01c08030000342005c00e100007000142010002203c060101c0c0000c104d4110081250340f00386016250045060400c141c044c80c00d1100140e4000e113804150f08294000f65050000d0b403007440042050f0984580e060091400310003002001e5444829a42d00c84100b40071060300250301c21180c802c07040c0688800500c060708060010480020090780b150480c038109821550414035451140c3c034030f1003400405100c010f0804080c80e540c031080b000075013103d0140c007010384540d403c41082c12003810204a00c41800b846900107480c041d0b0300c200010754641043c05540e11070082081c00c003030403541c1d00b044100c0c440d07680f1f41c00b002e00600c1a1040010209000d500366002 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 186793147 1250 186791897 186791911
    0x506061b010b042702090a0b0603040c061103030c03041b0308030f060a120b041b15030e010c1419020c03010e0a44040e011203030f020301060203041e0806 68
    0x4440000c22946014003c04c107040b1040a0368801d0401a60800d01500c802c1c0580240200800e0001522640445d400a00c07190b002030122583e900c0c141c900080c0086884c00741c2c101084200c81102c00c400d000000740d030311a0040c440d00c0c5142d0f4a498942480c0c1c03848501d000d684041f03400e1000700005083c0000396010b60000030740b42800b03082c4842045569a41c641281c940f90700000d0340840400e014503207446d0003541081c01042c003c1031448515840314020380004401428224980507a143d050780031103842d4039080c00800180d414102c049900d03c0034030420181c1c811052003040c1501880c400e40c1920089680100c2e090788689401007070032342d2541001e400047e00208508402d10001d5809001c05450300b0803080e4040608440143d0250510788072007403003100c2203c3d0f0403050b520f01c03001c641c0546038510a100d080d40c1d661300311964241004800300c0009041402d9074203180e00300d00a8a0584000d9009035082c14100200b40d140940f01ca54045080c500c9050005180300b010310659006440b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 186794397 1250 186793147 186793151
    0x61d0a060c0c050f030a0f021203040816080102070309050402160212070806060607050303070807050c0105010306020a030b0d12050913020708040806150f09090f060a021801020a11040506061b01 85
    0x3507203041880c41d10580e81d1010340502c2e84110a601c00b0307900460008032541e44803c5c1854610001e00215a1860700305124040301d21000401281c03200c130025003000c224425000c154106a1164242820f0380601d40c002400b003000c00f44103000510b000d0b000341c400d0180c103401300300b8195803a4000404051681c0d003080c4103500300d0002444220014015540e001000765800c5140000aa039441d07524400104407108104014002c152958801c03000c40d0dc040801000074441561a824460020740c000d500c603101092402400070b016003482003000e0092030300300d100d1481c4086481d4040da025800250a6035000303c0395140300f103003d82684080c00401d07000c2e001880d1600e0074810420318128000c0e110a481c441046100d000079501c021400150100644800c02c8a40750394221618250995000c40c00340e02030030040201c02100780c5d0107444a459440645549a06480c00580c0c495403d6000548401c41080442d25a1304081d00002e420010191010349003034040c051107039040207c20000101c0e07075 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 186795647 1250 186794397 186794417
    0x50a0f06090b120615120a050f03030a06060e09040308060324040506010f0807120206070203100b09070521070e09010603050109050f0f0a09021c1b0816061d0a06 71
    0x3c1400c148607504072103100c005120354244410b4800203950100b204ca40300f605056002c5410042c103114409002c0d60003022151034403c85100c0301e0b1250070407130301b00b540e01d4030740300e00051001d03c2070421400071980a00426030f5512562401c41e080200180300710f4141c0300e2013000c106001921a15240ba4010201801c400340c101071a0180c141038060713202100070540c03030f0018803040c240803540c1021107015600e102c24641240c03001c211507001d0004041e41c140180d0315002903101d10794104805c402001c403880c2d045a51103102c16603c501034200c0340400a40320501c4103c4142051319865000321190400d08445403400c400075003064001d802c00c000007501c0e80010480030704680a1141c0000d003a030240c14152803c3c08036205408002404000c0c20fa4403440d494080d5250b0240e40441440505c8402002400c582000c000f0700400080800382920302140000d98140007103010191401450004554030780350003421660b14480d1025500c02801448110210355902900305e00101426101d803c600 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 186796897 1250 186795647 186795649
    0x10e1201150602062e290d1b03050723090a0303090603150b07020d1a01080f1209010903080a03020d020a09090b01030c02100906020702180f01170a06050a0f06090b 72
    0xb41003200c640d034480c000c41c401c0031760a00d20170340841c80948102210303c040710882c40c1000900104070898140e50b4034000640044803c025030803101544003031201d00c15041000305011000c85c0e0044520100042c003c55000050401e42100c07500d001c51000d00c800d09181d4000001403458080b98011800300b68040e03010424907405000c0c0001c820000502154110b16240d10f80c070301841555802031140000030001e008208003a28254141e680c200c000491568561101d02d40c0da4202d5504c65403244030b61002410f54040ca2821140da526040c2c0d580d000c40361a5941d085101d8010a008500b410380a21981480a003184054240c004681c0d6038604a64503103d044812529402203940c105418149400e60715a0006030290000c440e040c0300041e06040e90402d60000d02074100025442401e400031036014502c88507907107009102050b41c00b10166070380d5010b13401841503401d01e070306203800115820012800c0c0f80e1200743d020480140105451200c01004002c4401942014680e250307603946c0040b01d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 186798147 1250 186796897 186796921
    0x120105191211060d0608010605040b0f0a0506030402060c100b150a0e01050901030603050f0c120601030f02010305100509071e1403061c0803040303020306040506040209010e120115060206 82
    0x5103032089209420708207100140d030385903618400341541803405000c101e26141c49080ba0f40d5105800802c0000d5501c400c1e041e8043d110303502c80e15204509180e000c40700c7e450007000203000d81e100104103601607403800050080c1134100500990740702e1428407411403611010b00405003601c4810000143d00800c240420100244005881d01461000d00034541ca180c1c1001c20100c44080c242480c50710350008400490140c405500010454064805d90800c104c00000390020706060448070420400306200b44640e84000920024112416070585080594002c0d4840303a0040001c56810001980310000f045480100791034500c005040c0b40300410015900405808103600b5038070304808400281800d2031286d00014120b54810b00801e030082200031100000c14400031785c003a02b1140c076440c0c5401c001d0000e4204503981c600560030030001400c079142034803c0b509440c0d0140c58860488507a0b805001c80c02e0450840103845650701c0001c3d24500d4a00c0800030010f110703640c01020545070506002c18 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 186799397 1250 186798147 186798169
    0x90e040618050d0909050c07060905031303441303021503190605030c1207031b03060f090c06030506030c09150109170a1b050d060f180b1506040902120105 68
    0x45d00e850001803085049200702212040760300000017180301c0859040c401d042d8441c030360404645895007007000007000303104150321840c5500d03c9440c09180b140c164401a1420441c1c40d000320546c6c224884201d5000094041d0416101d074011483c5160713201d501040b40d034000b00c1702d448a8079501008100801b064024a60740b8a00c4d541800d2000314a40740c040703583d5842c0103201c0e81c415811214075907403800b003c10a100083d0b4104a17141109000324242240318159030205494242c10542c0011003040701c1e004080750540d0003c05c10b181e0340e02e002d500f18001c140c007403c0b0680c98040c2281d82c1c1751a030380b4209070b50b0058800c960f020350016000c00c0003420400781940078104001d040f42030b80021a10200d001a01250081200d040a005000c1505c50180c0280c0003290f1184010610606001e4a5400a08038803510f036010002c0880c01c0b1481c41a088000d0300041c6180b1641d0001181011004ca50038a443d4025142d2410b15440d43d44c25803c2ea08200300042d8000001001000a4580140181 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 186800647 1250 186799397 186799409
    0x1309050105071d0f0409201002070b0414040905010903032f0405040b0a1707060f110705011b05060c071b1208070c03050f0f07050102030406090e040618050d09 70
    0x1448444400145a490f202962160311503501d019081c079181e1116001083c5060344100813000503201000240d0f00c00080d11303e111701036040c41c1c1e80700c83d1560001490009036070303180051604040c074010880b0810203010300000e0b04240ca0f08032050019400f405010030841c42078a010424400126a940c14003002281c4200d8001002c0d00d0000c0c96215a01190191030b4280c4000c0740c9043c004001c90380d0107145610015005500780580940c101c0040384080560343c02e680d5518504298040031035202c401c240044815410520081140390300a610540687c0080c00281c4070640c2a51116030511a0840350381b1010400095800c0c2001000c98100c981410480180c40303803d030404568480c1e004800344010411000006c00710244401d0b901d01c0801551b01c50111940520010030040d140d041140c1070340c1e0103203e60100400c0c250700100517181a11031070782d10040024a820566181208050425074647d6510b1110301301c141c1c4040d0101c0a5075004000801081140c904010b05003200b41c1d20003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 186801897 1250 186800647 186800657
    0x606030307020f040507030e0a0f03080705090f09040215040806060a1502060a0b060f0304030309060e1b01120b030102070c061403010308030f1015020706170618090c130905010507 79
    0x7500181e440ca5030b43c80c40d011080d03030002096034900c5000c0d002440940003901c0d1601c206400c0fa801c000c00e01c2068043c851084e522018181c64903075003034a05004003031410364440300415034207449062411129030300c030703000500e003990510040741c50106c0ea520035003002c65290008410040d041c184001c0010040044140030001d190314403500070740300c2501500c124100303515195240d049640352010b0b5500280c01042c4d050742c9062070301d0080c00501c3d480400319a028108903014001000114405d0b15030060440741c1c01080412034011107c0c401c01d5000c8902c543d503031f5011203001c5e807002d101400d032452080003810382150030004c0c00342030b04100d030340c90f03540440040006100180b440c80544c0c0d00032015008449181e102c09000c041883d241d40c00c011050b03a4082c0c185c2c000950700040355003c444690b151142c0307480c5030b1189012140c0301190015000410241d9418200c80c040700d01e242d01400c40d07402c1e2002410844001005c0d001c0341010280041d0b00d421611082c44828031800c1d8110070076080c4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 186803147 1250 186801897 186801907
    0x306131a0118141c0c0b0a030f090b070c030207120c061103090d06181209090f0905030714151914130803070912050708010e0f030313140307050f06060303 68
    0x24440c00c3c0101c480014012806000701e00c002000c0d11340c0e407038201640701441142c03003502d4044042286d00f00c441d11000007407c10042e01c080c018284a2840899004092202c00d650f0710141070b42c5107000a1801c40451142984c00a00d8100d0508100715082c07051350550040303441c1100044c080c11036000604815042000009a03030b03039624030020a0581c0c4100042044c0daa0009107000c2e0003601600600303950400ca030000719684c2d00004001c00d035281c00d0010400110454800000c0f15402d4034005c00f582d0081080201007a05251900514404007040310f502400c90030f28200500b100f0307a615011031000045403040a101d90003408920002050303082d0041c1381202494102c0120ba00b0301600300c0c9000800320f181c0c2885082641c0142c0f04002c01840a100c0b2840c08541d140581c0c03240c940c065207811001c103d012800b08155002d00343c5a0015402c2d5200c03100c1c00c04d121b04960a08540c5c84003a4195003641c24800d0010301452409100a04041254040154208200140903501c260400c010b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 186804397 1250 186803147 186803159
    0x209090a030e010216060804021305070806030106060504060215060a08030d0509100c0f03051009060f0e06010c020607060f060e07121d0307080d090f0516050108040809060306131a0118 81
    0xf045034110740e01380c60301f04800d4540380003160441c2d43c4c1c1c500d442042c0d400d0204115100d500251094000c120030380003080101e80d00c100480c0d590085018000040c3c010705602d91003044400340f50f5402250007011114595902c00c1654511b905c959030325066151100c003000300b0080c05100440051741c2540c400d208501307620344d004003125001441507040c1a0744101040c40f01501e000c1c0c0b003024040307a40707080000340c0d2140ca081c01020f170684140c05034401c0400004415510825103071010781d0f405004d0707505242265031500c0c064501c0c0c6810f0051a9611440000c02c5190f6010309801503455840d144052032000c40304000b91582000c0c0d80c208541441c01a65142900004868406400084031070b00d46120041680c094a070150000c1c1c00b0700c112042c07140c14020041020001e81280c49409a01103075203000544070204d0445004e003201d80c0521982a0604040000f142d000130010b03c0b00e0012140b914040049600c40401290f92103400b00e42c8000c1541c0001181c040d40d6425405030300c003646000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 186805647 1250 186804397 186804433
    0x6031217010e180a020915030f0d0e0d1718040e060103050331030b100f030f0b042f011b0c050f01051315080a1b030203070504030209090a030e0102 65
    0xd0204540c90044902044070300c0814403034031300c60903802040a41c072814048504090621061f003414803a0003680c00844400c1c1e000140c2500e1411680c541d4000030b02080f040040c8842a0641601d840340cc04490307a00b422000c500403c6084031005e0011800886607051004503140b800c951034180d4403242c01031012501c00030a603030605c40003a559a500c207400644100b90240f9802d5250000c82c4490707404000c01024688151040c1484000007019961b94028040d405415100141856452200c00404152160307180c0e03900a02440f00c040b800c5034210104000718065080f00315141246007003c0301150381c488080d06020311081092a4a8a0b0944601440c92000d114241c440c080012104603664020303000c4d140740e0843c010016545964410000980e07520030100d103000500e19900007503003207042c1c1c03082103081012011001d0000c4a030700c500350020350000e410403043c040180070010041e40c0c4c5041403445100183c0241a1407a86440c0241491918240050642d00003464268a0030006 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 186806897 1250 186805647 186805651
    0xe0a0209010b0f0403020414060316033513050a050d03050d20032401080705071104020408010e0f01060e010b1c0209090a140901020c1902031006031217010e 69
    0x500d0080d9440408504110482c40f80b9480290006e0400312400c1c02904448ca10714030402e419800e40341c81203156030342e10138030101d50300000b400382e001c850905421001c01c58640001c1c00c01c419460620034802d40303c3c15000e8010940f80c40d14540154010700c81410868403d030300600e0191042c4241c490280d50180c0107006d00354009000340c2d960254184d08610186000307140c15020003200d962130038280d0180400c0091318a0054807a0b04011040f2404e502c030b065001c2c41a81c20781e0303c45043c035079165107204070b08681005160348203400b4040030415240078420a81003102110091290b500c9540006081d200706902607010022030b680104000d00344041240e82100e00440242400c00068060400034080c414000f40c000d04020300b080010121640000d007280c40000c500b6000e6503902c0c9080d4241c2c4121040800c2540160301141520a915404048000e01c000d083c0c0d0040c16000c0754039800c544082d032042e40c4c0754000307506d40c940c00750b0030207400904a526042280241e60600e9154035400b400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 186808147 1250 186806897 186806909
    0x50f1c03020f090405040c090c0806010516020301150b040303090f0308040303140d06090207051c0207060f021f1e020a020601060804031b03020607170f010506030601210c030e0a020901 81
    0x790030b032010a500c200302c41a0240050082006080c6400c0c034169045450060543c0c40c2d25101c07030399409500880c01c15110740016902d04e40f51507210980601c2041c10702c18200d030507649907512241c403030f0440e03982c080c080c201d0417190f10b03210340c5141402040802e1551100e242d50f84d64603014000320740c440f81282e0a50350035051284458526505c980d010340715035052002c01601d0500c0220300210150000c100c268021421950b54040540301460031005c0d000055001da848075a0030001c050080f207585000154038010358503d484010680602440c404076151555656651411032041081c20369140d184403260046040c000d1041c0040c3d503c0030113000f01c00c1406210b1380024105446560404007050130380208091010492801030340c2c507081070f20828085820711510244111707054048610070400c0062414a076446e01d000d220300f55001509240c108024035411481c0c0460029221003800300001d400101d003119660005e04841c8045100307249a0445951880580c1d00c03c0b44403410754030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 186809397 1250 186808147 186808151
    0x1409010c080c06010612060b0a091502120d0504030f140304150605180a0b04090c030803041b2d060f0305070201021603020115050d03080103110609120307050f1c03 72
    0x25081c444000e000d42c051290240c820040046070700380e88010703d004a20281c01003070094944a060005840c0a681001400a80b1111301003081204100d000e01600046005880c6040c109079480d0100390301c0601c540c0845030301e9405100401d5440805140036004c14038141c4c00d8500c441040300340c907220180000d440c0000d9101c031881c5114144d801000286401444030141020f5810740e212641401c444441c40795107020300781706180c00c16015140d80c0c6c80d40b1018500140f41035035219405a0009002038549811100c02800c2c10545003c08001410100701d17100501c600c1f5403504245021500d082104910348010200030958000d200c0c100c110340142404209551544000ca0080c041c1c11508031203002da001090080c1031b019844a04000c4400145804054440301807091402880d41e0013000031b0301d03940040012400c061f6500c00910070081c0070500d0021554005000d0005a01801c110343d0800122001000000c0001c0c0d0b5003030b80241e019002d43d500200700d0a9140f2152100141419 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 186810647 1250 186809397 186809417
    0x61026060a0e0406090506060603090c220213031527140d091e05060703050d150902190309050c061605010e010203100e04020a05041d0604080910140901 67
    0x241e180c200d220080d00d09545109002e10381410103a004c2e0211003001d0f5010301038000403c400f03043c0401103901c03e840c5039005203078991158003806908031001001411000303130300b280d00c5808079150005200780344000190152603421820700031401081d080114014918110090321715190b65003021902503001d000d02c550f8401141015068011030050015140c0184501c900500750019000001c5e03403050900900c00c07109042441c14004100e000341644088207100171070009205d080184045030a0040c0070a0007030241c8100c1b2503c4900b90403858070140c000c249042550052544444405003914050108100076110641c03130741c135501d4580d401628006000d00b801c2801240134481241d000c8001c10256071540c140c18000d400c19509155840c140070000502c8540200746103004980040010241502d0b0030300b000000c0841c00500b0006101d40891001180014043d05114078040c0390b41d60b5440200300704202110031007005190510450280700e0b203070310349103405480003100b080c24120700c96 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 186811897 1250 186810647 186810649
    0x9150903020a060e0d020106050109030f0825030e01030c03140c18061602012003090603060103060308030403020606130603050c0904080c07061101110a0e010e0f0301110306102606 79
    0x1044030900c0140030300c1e05040310841c0141c00001d030301746541c110740d008000d0291114011038501003944005801c40002483d000c000c1161103004000c440c0c4a0980c007000303d0854440c4c5440000305a600381c000c04c0d240380c1d070705c0c2255805010b0140102c52034a8108205601d100240010320405040b0100d410f0011a1110140301e603052b0b00e80850b80020021a2508802d2000700030200301801d04038001813104160b83d181200c082101c90080c40110302650900c41d0000a01c01c0c03d0708020705d21410107840d4440040030a5800c0e000f94012400790b8007400701880c207041407205010134841540c2038640344c2034041000c40e202159081554a0841d40300129842d81c0c1414022030240f500b01c030b800c0d80115540040e040d5082078004450199070002805490201c1d01540c01070701806210201181950a080d001580b044035221910a00100105131203071b4030030040703800c6a4008020488000340001800898984002045003240b464036108100c0000110f4901d100e8402c0d60620340310764040404a42c00d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 186813147 1250 186811897 186811903
    0x809031f02040e0708070f1d040e0a021804020303030403030c02150a0f20070b040c031b080f0606090601050d11031006091703040e0a0609090303020918250e060309010605030f010915090302 83
    0x500b040060040c0308ac650080340c041d490342c028601c200d22820050f001d190022040c10049032080c2d0700140558155a11604c090703010b4110304580204600985444581c11034100a0b80c6004591105d000941d12031000e4218045032904110704402c2d21046c188100e40c0038200007220210341c2d0114002400707840d545080e40250304103800041400c041c400b062031031922400c242208655a42c41291340100c000d10040343c0b034001c10f6a045030002c401800080729035026600034800300348080400903591221040c0e0001903041911f1006001c44000703810004564042c1494010303140c115a1117110301d8164030b90554900c65485002030321440c0c10006149101180c1c0400010003040030180442c9801e0719000340294070030300845100d02d14041161003c899103030201c5210b44a140350709030310314a600b100c3e4071a000d2500321800c20030603c0040000b86440f039001071809111007000100d42142044101418107210305003a85150f0701d840b61020218141044c040d80714405084009417a0340d880c207081742 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 186814397 1250 186813147 186813197
    0x207061d07091d030a0302031009020c030306010e13050114010908120306090606040f0906050a1401120f0204031e032a030f0909051f0f0b070809031f02040e0708070f 73
    0x250b10b004c081034002049401d41c000310711440c11020200311450f21809008100c0c0107002111055500900004043d54050303400c45410082c02071442441e580f00b200443e00341d800980010f407214524404210701941c010000a01a0000030b02421078200c20040c030003101c3c040103100c14401c00030386011940035124401114060000d014002212546903410130b8082c0005124090203901008400210405805581561400141d407080010380c4550100c0300602205400728808590800c00000002c07410b001180360006042c030014001203a03400c0180400394000c1e40002810a140000c0d20040080303803140800c1d640c542400065014402d404850000194120081c00c515000601594004a06224105460035600444901c1e15043c000b8058211441071640140c0180810400110100054070013044081c049a0300d16580d0010307185000f011040001c0c0580e800201400b6a8130303c20140382e4408414102030406040c8808002d00d10a61b049480c0100300440d84554006001455004 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 186815647 1250 186814397 186814451
    0x12030c1106220f05030919060e0d0611070b090606060a090e04030c06050c03150301020f0711031c0f0f0201090201080f100b0a0e0906041103011505040909060207061d0709 75
    0x51030340c43e407400c10399980c081d02d5007501c5080300f80151001c80c4a15100c040039140141d0301d400141e442c05003400b60400c0c128800b12801612880d8411019103080050500d40c0e000d080b1040103420300780340301d030f05144025040c503000342020842d400031250031024400803502c100b14003a5480d5254101145e2172210a40000c20060500090280b042d07100070155028500001558074084400d900301402c034421800814110344042c0242d40214000300540c080300d00d40079040e80e80e01c40080c8a203900e801c150030040703404121010705040398154052000c03150001c04d80001c00210790b4039000a41100c2005100204d229041c8001800444601a00b40000c01c02d030300f1025110484000041c003c0c01e44080c849020b103c0b0803002410070300d8240a00c03000c1c10785600300c417495a42005140048050301004007014402c3c10440018001110310888403464000d01c001038596403140380100c259a950f0702006400003000c81e00340d5004101041460860b1141c030b00000e14440382c00741e13000305d1500d0300c0084 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 186816897 1250 186815647 186815663
    0xb0a05070803070807020d020106030506060f030307080c0102030f09060108120c0a02041104050111010203011a09030316030905130221060127060f02060106091203170412030c110622 80
    0x1004016401c132040c0f81c00f4240980980f107298228010403400c130f45052001800da5809440411403e00b86280e9105403801c015060b00c4c500f50300303070320b401003590700c10280d03214240c1d80001004035200d081001550400c802130301405417545440e000300d0341c86101c40400741509000042282041c00704201e103414143e03003e0000d105200400500c0d10300d940042c80b55074042a05590502c90204c03040c403c8178141c6032449104812513031a08514a56500002e600d580c151004000740c0d0a02a1038940d10320365284690390300030031f032130509040c00143c03a0490104109940140140d60100c0305040b102408601e1840310012641c0c1c5210040300d00c4080134003181c2c0401400032000d017410507444149070075076616855480d00c00c90314500c1281c2e42d110901c1010f001030400030f010b0102c9140022030b207003100d000e0b150884004810403140020b6140690781100c8803c0229903003c40190140205944101c16007440410482da008078140c5400c80200180303402d42607030400c03072a596071144070640301d1900700c00b413 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 186818147 1250 186816897 186816901
    0x100504050403030618020c07140402040b130626060904150c050c0d080c0409050703020405100e0a080c01091a040905100603050f0103021f11101a04020403020a0b0a05070803 76
    0x40030307004002c0c41c0103c145e078075905607071515500d031079000325241c10440c10020040c141c503201c2e0312a505040d4124403035106400b040001041d03407201000d011410700c0b84000c2c14500703140104c060f01001030a01100d40c460002c0c0b0046131018101d41001e076005205451418496540380340c4511a008200c4042c0000340c038014640c8802d0760300c28040c01070078034008211240855100c4041c0c40c5200122807083c4521010403003880b68041a801458001c0604e04002d4105629a00050366520410980c3c50000e0141c0491182034601300c1c590340000d041400c0640090500800000c12449142c014440c48100c0801c410b891a0b0180d41143c0041c841c10800700550b050843c850528240c0740d1081c400001d040c500072a40c007044440001d41201e60040200c100c240495940c04050204444200140b10040c2c6025014503402e100c60003000f5243d45000a800d41126402d807410310340d91b8401809540705020034801604c42c0d000030743c291030102d58115110750b61110211403510501f00c0c020001440402 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 186819397 1250 186818147 186818153
    0xe0301020c16050d0b0402221404020405100b091504080d111204084912150314250f09020a0903030311040801050c04060e0321031005040504 62
    0x1e4229400c503640b6108000349541c61040180c94200c250001d080c034500302c80840d0061070b280010011515401003855922042c001c00002150032180c4032044001c06081008211310301131107141c0e03000e6145034501103050308007843c091080c06415809802503841c400500d000c1c0d1040800d4800a0020078125110a280d20b04018862041c520407181c2c6407040420000640c941002070f1000d5400d0900240302c0104002042207001140c400281007000c95010500b0450711550f141c41501c1100340000c1203007203a2894010441310b13496010540c0203241000d8000591b00c4100701c6011170790880703e444005200103240c60704107030000080a514010810700340108020401d1241c08a854040060b0a601c0d0b440039030354240e20805050b0030019900d02c2c01840064000c0d40440d40700c82c0b410005c0d0342459180c072138581c00c4440507698100305000101e8104001c5500846990306800d00340c0103400100c99449000300460380410110240700c002100190003c030b02081d2a0000b09001401130040d414542 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 186820647 1250 186819397 186819403
    0x408160609060f080403050906090405070c0c06020d051e270901050d150c141810170103030f021618050f150108180d0f0e1f030209010e0301020c 64
    0x880354002259441100290040c0102424121440303d500c400c900c075559998203d44640c000841180c1c001024440c00d140c0780c80e540301d4035129610381d0301da1903107100490811074026600b80c1d100b00110352040d1458a0200d034041c055501001100c803440c2201e10741d250b00c2c04410b0052a40c0044045030ba003000c242a030110240a02e0b00c01c40596200707000d0f0340ca1304140a808002944068190303401c01c00b00c021200b42580c0540c0030369a01e460304100904840c00e50340d040d40c0c003580c1084900c09280840c00f41c1440c180c60001d0840966007001d0303a110080c402614004401444007400344070200342c401c0c003044d0081c0b245103034080c0c140100021682e100c800000038403183c107440f01426860440095405854610024000c1480308604c4002c13000300001180d00c0800240680d00c102048902c07443d01c202c0c10031140b01c0e00346490700e03580c8808440300c000a040e0701c00c071120381c0d2040348003507080f00e000035012414000940702860007503941c3c090a4010f90306290110b000d076030590f100044c1600100004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 186821897 1250 186820647 186820649
    0xf090506180705010e0d0303090c12020a0906140603040c080625020106051c06140405011d011802100507050f0304050a06020109050607031805030309030a260402090a02040816 77
    0x80c0210003815a441c950b581d0724a01e0281c28081491520805550f00c1c0c50307000304149a110b4500822600d00c159501346008600b684410012170b02903900508600d4083d000c42d010b003161013800c10804c0e00d06001c18000503901c0007420300420f00040031405000011480801400c1d0750002c8942030305040270510070a81401c0003401f01c21501d90f50341900c09106006a20072594010580714121900c0d00c0011303202403200c0303000c84100b40d551490a61060020b02918813403402100005807001c8000d13000d10000200201c0038070b40340d1411080741403544060035504034103078040c1d420041e050400d800c190f0b8241700321040900f5521851034481c510110004c01803060b2441600d001c0c415a550f0300c401d07403c0c0c8e4405a070080560300314000041c21544658400340d000c10062070480c0c0d05480c2d9890b06c505581c801d4a0508094000048650115800400c00302c9480c110340c9026412460100325201400c80140000703205020080c003003a83d5800f2501940d0180c20400165081100d0b14a2294942501 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 186823147 1250 186821897 186821911
    0x1b0e04020901140a15031d03090301060b130b0d02091315080a0305030a050601140f030a181509030513060201091103030309060109051003120329060405010806040f090506 75
    0x281c0c90000c165150551400303500c112018244401d860f00341a54689980e01a01c0d1040070141e607022103402d6809180c42002107203070803e01540d41c4010800a06007034924a0304203100c1c1500801c00540032540c80c80303802c021280680c1c6074a44407215400c025001e0700c00e01010715481056502d0280486c0702c1540440760300c03041d105880c0d034100d44c0e030161613440310700c0f01d280a004607401f8800030300c200c0702d0754001c01d034091030515001c1220502459003150681140000300101403020042294007800303446925540050b0078440040c1228643d10100b0074094000c0e0040c43d2501c5c1c4880d8820503000da01a03a0110320501c002100450700c2c0e9100a0081c0400c9038203031403048405607110490304010007181d0081c10440c0140405a08107000c180160801500b42c1c8080d0aa0030780c0040858261001d240c0d00b904160350210340c4e07034002d12428000e801d69060380790150103001c100c1d640321b54952044400316042801c246c40c00f035440f540094010100300005101c0c280c20590490204600491020300c1424 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 186824397 1250 186823147 186823159
    0x70c0f180f0507020a02010507060e060c04030c050901030c0303030b01030b0a183605030702211b031c03020706090302070302210d2f0c030705060903191b0e0402 71
    0x101c0c25450006980058480e040560001002c4030099442440140500b0380601c001040b5000d000d148a4500307031044504521510340410b041c010809100d01d200010002290591170b41d504544410381d800f4114030008003499a6110300030700d280d000c0c4c1c00250380107000500c0600216524003110034545601c074082d03001903162032441622902240512034150342003d150320303c0c01500424080604080032011b81d1184010700039680140c0e00d103194041d202d0070603d0255402990b00d20114984003501c1d001c1c4004070a68003070780c1c1494070001981c40a04001900e841d2109905150690091040c42000f82c201c80c02d004010b0203050b00060000b040b2842030343c0b0010843c0e2100c002143c4414400e07072070b06035604408440c41c1c00741e204242250741251201031482c50150300f90740300c22100b198141d07020030540000300781c06100c0c0340c00e11040c0300529059920502c5c086c44440040d0720307184d1003017610b442d40f00c08603a090140511400c2c034002c545004410085074a031950382590341a1401c40c0c0880c0720714 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 186825647 1250 186824397 186824411
    0x150501080d0f14030a020306010207091113080c010804030819020f070b0601170105040c030b0d0c1511060612010902031009061a031518010606210c02030a05070c0f18 73
    0x90310078440b402c100c05040f04403500b103448032100c0070040d50000c0d00d0385046115841c40459200c0780d074890301c0010113024140759900c0790b143c0c048200bc0d05a50340f06a100d0b4000202e4903030141d03003280074160700c581d040c646007800760341d201850b025060004d40c0d600146840420b0307074464001108010007000d4000d100d8442e540d03a862004407182d008015900b0a0803c0c94001044103080c40e40110240c201c242c1000700d8401c40460114003890311010068441c0d0b02141400c10041c009a14041c89040c0180390a1480140142d40255142d0b4098100c030b0280102025180400e1420350050300c02030382c014203466545c1c070f100090001070700c4013942c04d44074a807422111800d43d01d0050b0038a050994064041d0242001410358400c00d5400204508040940e11011f106021028403c884c0507103502c1d00c4005c1c3c9021950030606401e4003281c501c0c13401b10310300610074525980000a544d810707011490a103540707800078a0b000b00b5002144d0700c05150300903c00001300e01c0300f900d200100e103d1454140d0401c059 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 186826897 1250 186825647 186825677
    0x507110708160509070c0305070804030204050a0207060b03010c021509070e090609071d07031a100c0b150d0b1306110c0d090b03060d0503070b01150f020a03080c07150501080d 77
    0x210107554400211b01840003081c0000c0c0120068040c103401008842d0402c0d50301c2d004501034032003c4605180c6598001130001c00c1222070711440d04025002e038000c0100b1841000040d58075039101c00e40d10b07078851401000807522141000b000b00903014146040d4254180034102541d60a402d5a102c2c2d124043e210b00442c952204150026510340d0000060071183c403810b04c2a40105200580d18102000451100f101a103d41345000c003088000d65690801604908010401000282c0040207a5046c0384200d4001d0b51811a5070f480c40d07400140982080e103072785026003a01208250001d11132400c00c54042c4030356446102505103c0700481c10b0b07414400001208458542c001d02400600781d0040c40411528104900a8200b1503c1401100d1500c4169110740020300400d900c144012100d04900048150748000d610310150058002080d11414640d8080d240d40d400508502100c8408501c040034844800c3d100e10703600811100402155840710906900d5401c0102004c0110b00643c420301d880c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 186828147 1250 186826897 186826909
    0x301020d06051f0906030e031306020606100e0d030e030a050a12080601050c06010b1605010e0714060310180b0907020a03031a150903010204030c12021807020a0605071107081605 78
    0x1402401d80e41e6120134900301003040c1c000b0222818001c45c2c512042c0200d40449078150b049901815050f0020141440c080d42000742c40c040302074411b4100852458040d140780c0b41d0303140243d95194182004811540b145000c00e00c4c2c1110307030001030304911908182405001041aa40362240550ba54408280d40c43d030005603624401d1000c051401d0b80541c0c0104800f40380140a000b146102c15840210800c4a458107420b41c4c100380c0e0200b86903042030f007003040f01c1801e2a003800e1340c008003602e445003103141000140600010030b01c03405990344c030800400c50800000703a1004c86c141d807004003105075030308146030700070750710040f44038120082803400c00c20382c424011400c910502440001c03c5c8096043d00e256107840c083d00000c06a54040d9001c6c00044001001207000c00043e1600e140d100110000382d00401c42c81200b00b803a003a2a1030580c00c14021007039400318400c3c004940151010489841d0710104031a05880500341901c1170159031408204003002141e080c00e4010404400e0401540b24020040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 186829397 1250 186828147 186828199
    0x806010507050a0b22050309040509070321030906090605061030060e07021006060806060405010813052d01060506090909072c1608060d0807020301020d0605 69
    0x1080e0710622411001652550742c49a00c5001700001c1640c0c42c5901d45041e812444098003180c00d600302084245103410540b1034103600400d00d5006000d2680395483d0742441040707040609880311500c040d02c070005402900f147d4109584568208540740745410148024102a11a1482030344003240c2c1e0380d122489090100340d009242280804c3c02400212060f4041c800c401c403040b0401e40b42c6c100042d504249c0d913402c51103681c0312303006060140180700c541030880700c0f241c010400380441c0720144441910f5203800c2ea0251002820501110713103a05902101c11100c1c8440280503209a450b00903d50304142030145841e949004010304440b60b1407011400e94803540585500244c041c09041544c0c0f403d04051600140340005540b08143c80f802d440340d00c420b444548214800814003400c49404c01d01c4407aa90008400c0c03850208115078200c020060317480940013611900350080104113021481c022110015402030007155600314014030080500725030311800c1d100fa4990b0300341d9580300781b0035110b880c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 186830647 1250 186829397 186829403
    0x9040506041b0318020901030501090203070b0a020606010309020f0904120318050a030507020109080f0309180f0402040c0314040c081c05030601120b030f0610060207061707020a0c030807030806010507 88
    0x81031207034811800ca004280c513001030b00b5032988401081e0056140c841030f0340d010314020b4001213110480307030040c14a000c8450340b007507c14201c10015403050560124a05420440034070303000c2034100b498000140c0010404025960124503030051004101003000201001c01c0c0e1a01e00340502c4010f1000424210340d40310001d40315401004145e4000b07840780e4010f00d2420b01c141800501c45446a640c03529000d03018001e02c3c4070758000102d0403c80e2900b40d130743c42a14080740c0c01010035882d000c40c50007080600900020700658581c04100000780c001d8018601c102c504220354400d0b49040d00f03080b07a10b0b218a1045007580e01071100e808001c900d000041d0302c000807890300c40b10724580b180401102c003000350a1800e0035080d075485810030140e80c00d018072202010850014441410902c1d8050f000f094203131320100c213551000000701300560b04000c880389208036400407002241c1d1250344c00da041012040c4000d00203070b8450408000c108882000c0c00300306000e50b880b90301a958010064900b0304c658440a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 186831897 1250 186830647 186830681
    0x51e1303080a02030406060f151b02030d0c031412010f0905010602060403052b02030f010f1a071401020301121101020d080103020904170a0e01030b0604150f021c03020904050604 78
    0x42d106a1107400540c1c02c503101d0600020055a5000e0b66100680c40c1e400c0701280c020b140d0000071310f032644554401d54001049503021b01c221100d41c00250303105040394104c000d201c10308400c9400c3c14050404418a10b0560102540d114800710030311112031424015505401461400401c5204081c4a824144d428a0300204a540c035640c809503241e0b00044400c1c10b003400d5440c01c405038030500c0c0f05a03008a640461000d030700c07401c04000c00c902c0e05a050308640811600c04604000e5588000806075061b00d510721201c0d80e07032180d41001000400e01214020301c03980000000640e004035584502c0f041c1e8020020450704070044c100490315007042642520018111000502c0507240400c07075541c110307126144030094040055403107461500312003c40d401048960400c5269075805020f1201c2e88501100e08c40d03d410304044643d0244580e04d4000e104003d0300c04465a0340c82c0c001c201020003182d0a15129070071442c1081c000b400b0798040d00d40c207401141410007141540c1428014596241c03958528 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 186833147 1250 186831897 186831901
    0x807050d0f0c0b030f0f040203060106110106120302030304030801060e0607110d0b150a1215050402010912080304060b060c0c120709020f0c0d02030307090324051e130308 75
    0x400c421480c0e00308094944040344294000024100c1400100030b0070400011501c0b441c0007000c21003000c1d4014110160381046208102c0141d80c0070403403d040d80c13214203041c1c110407440c48030300340145565080104042c03103c0303404c0c005250300000654401d500c80c0e540d01e10182e03241c80045400388990900180c0001090098034001201c205486010030000703045500b605c42551914070b040d41003500c1e280c41007400b07242c07000f20347d080419803100a09011003027010071032a01e42e21045809200c0c00141c000e82d9403000031508581c0304035059401028501440e0404820508000d42564030544049895914040450303665041900c10307980041c807a031014002c1684051f0038003200049038802001180941640032605054620141540000d50400a61142400d00b400b5180500d44c1c11401c06550050080101f09580705540a095952101003625007a100c8850012940d40300200041034600309010860030000441903220b40105101400750715407103d0505400e08484014003400044003000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 186834397 1250 186833147 186833149
    0x31b03120c0901140d0e010f18061a09010602010c0207061110050406020c03040f0f0b0403080f0c07050d0b1506130605090d0210021b060f310602150c04080705 70
    0x10142240c40d00604020007028024422103a0b00c0d030003243e011009964412142e40015000d104205e07850303429440410080000401009c002c1c2c0b0903480082809d515100c42d1034184d420920650302e11280945500d006584070384020340a0401c002658005114188001a909108171248446010510081d020f90000c05007024080c09006009a9150741c08015449028004000603c000e00030044000c1000f41414002d281e02c0744650700c41154100140400d10100308040c003201da00c41c2d040c11040d5078440041101d1810310070b40f80d0080758481100d60841c13050003011a82c452003000e00c1e0000c3c802d2203c6400030061a402040030f181c06551072004184039080c01034005002c07800d0000d180d180c0c0302e00154009104024004010340040e00400701610000b03c401c211140e40d0001207941500b011000385100038103010b00e0088205104421002c90b400029060000607103c8901d0440740d85030762a10800795031031018989540218400c500010f03100e180b2581981d00759100403001d8171716540707080 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 186835647 1250 186834397 186834421
    0x61107060c120c0b0c0904060b0301051c0c050d0605010302040c0804030206060d14030a17090c030c1e0d050c0a050303090d060c12140f060f0d0b27031b0312 69
    0xb05888144074020015402051030f65900501c2002403038999555250000c0901055038004c1d400001d9045052005001d141d4480441e2060001e81c1345445503005528140b90403110102d900482d008400844a5003e1110580240e416a802a5000e01460703600d000c0840d440a411030740640107810640c00b0804514200c000c01da0564000c5130418818007546954070700b154003402d0f14402241c501000940b08000300c0c1d406035403000e19580a450b4020740300c008243c59412164001c0e104240c0052000c0c0303158880300121202d6800078141d015110854a040b41e43c034048903075028481c000303007100000c40f03280020480d059400054003101c0440c00554501c00988007003822901400300e521900c0d10030005900c03a900840100112010103810a4544d8a1031028043c00c01c0c0e00514001c4680500d0b03840701c0c082c0c00020f030f50182e100c10320b035503070031a19030100c0920407242e40d4a40c00b590900038582800101425601c0c00d100752149101100c09030303040ea82d1041101c1c50030310740134441c0011a480243d07 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 186836897 1250 186835647 186835673
    0xf0b070b0402060f0913020702010e120303040b0414010509010b131107020607020f0d03020703060b120d0806031204030308150f100e030c120f0c0103050705090f04020903030403030207061107060c 86
    0x40203103042640010018904032603100925407242d80c08592314080d076034072030b01002c00702501380c0b070f0104508451422551a4800284058141111200800c0410603814070100086d41c10030000c001078180521590701801c1070840040c402c040481400390702c09000d00c2004961032203140b1092034402c0c0c650a109041e00710f1101a64001c0c01c032410001139444074000d40c00e50381e1181c0c0c0504506e606600d0420b084403080000c141c041c101840aa4005e03041c00070f020341c61480d840c1824129a41ca80c40000c0c42d1800b6540c0840e03032004c01243c00410141c0051200d80502d10340603041000710101028082142a840111607010060980c0407a03098001e81000d103191501038299005035024101040e48070144000b0380b482940404480030440a0a00100440440c24a001e01507400c0101d0300030300174013458040911a00720f04066040c90b950380d90441e0400000074065980361592410040c1d01c41615125103004252441e110f406e200d02c0200e00301094402d17a0b01d901003a882584c540000340300722 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 186838147 1250 186836897 186836917
    0xb010c0f020f0613180203041203090204110c030403050c060a2313030b0604180c05190305100b0907050f040b180a03140d050c060411180c040f0b070b040206 69
    0x841e40340b0700030719160764000b408805200c0e46120307061460034010104120030f051007001424414814000011035110080f18068028900854064020b0000800620a2003500311420300000f8014042c1040440580102d900038000d645034088007200344130003842180000c10000c1c148100c41c003e0501d46880710000c403c00c4c00c0209003000032820305000503c0c59904141d91100110080203c9890240105614440d005e071120030601c8540e513400e030710fa0b1a40e004003071181c001c0d03d814071540b4035904d2180d8004e42d08141110700c032041081c1480000c00741d18001500032100d94000403c4140600100c03030304414000f07080d600d003c1c540b00c00041c00d0f17003120b5070190100d2060594901c2d2652944101c20145014004161000c0d052022207890b01341402130781d00074080c051011008070880800c5095100350010307441014a030807180024011900800840112107400060010030400a40500266840004200405900c900c070003201d90103000320081c01c000384030000a0044c14824043c01100704 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 186839397 1250 186838147 186838159
    0x605011803080a020f0d030b0907051201031101141204020f0108040f17070204020712090609031505090c06130305152431050604020304020d060c021c051306030b010c0f02 75
    0x8211600d986c1051010010310001a4079000c0201c19882e0100c840c6400c80c3d02c0f410860301c0c2c161049800c0794041c03c14400545580c640707030492003981e405017034019401c01594040541c2d5086444010384284c030f0507501a4020640380c1d8903100c2031350041091600070364002007400c0c41303002e0f140d44002c20081a4180200c0a003003c0c4000703070060301e5900281101034429140c00c0082010070700020880c4505070702010400000400800c003040904240c50b4900e0b10b1044c000c6910707039600c0320551a03c500710710201e820880020300c1445203a141c0c1e00c2c60b42a24801d2080c1c5086c0d141c002135081302e800d0107403410700c81c550b0f4000c9150b00ca603607000a568017190001e800410010110345046060a40150b010025010342c1012400a02c61078803e14cd84070b030040382d04504604160300820b280c0d84400308001e00081e034880461a2160003049800746000209012585c20000034a005104e034101c0d4221910380d6490703510118405009028044140f1010303510440610100c4d1503140740207254010aa130004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 186840647 1250 186839397 186839413
    0xb0108031c0c031b0f03141e13081201090b0108100e070c0203070b04050301182402071b0603050a06061d040906051f0e04020a090b03011d010b03010605011803080a02 73
    0xd5001400c4102074801c0c1c17207403119a444034001400f941d8005e081c10340385100100c200f00102c0244002c0c5001240c002c84002e0a42d652042078035122240341401501c010000300700480080c00d807440c0300b41600c030007040c00c1c040c001c4244010341e4101c106544842010070318560a008800b900d0f00ca05500c9400f6142c04504502e031900428105211904001c4401000203801d01540c00c090043c06102c0407e010041e030584c449031242c4502002100012100341c0c400c1030115180080c58042e145d036190051039111105a500605500620b094070a54020a051000003000700f55584540713411100e260b00d50b090f0704450100044501c0c0615484030754019a10184a80400d911740301c1c413403040c013405c02980c0f4001c03207504c00c9071966800f5a01c1441800c02d07820030440103031112100c0204884040c60007040c210390607400a409410210360305081d685038003240d96601e0a0540003100c0b0307108180d00070000c294a9400441d0040d00303070443c440c1125462102080000d0303840c002400c0207100c0784141c2e1880 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 186841897 1250 186840647 186840671
    0x6090103020d050a150605040302060415051903050403030b011b0305031e0a060501020f0f0d03020f0c06041a0619050906010513060801030303050f0601020a060c050c15040b0108031c0c03 82
    0x4610a594a51115548071745514103020f074441c03040041e04480c20107a007031a00d16400151307184150700505505581c10401c6038103143c021010340d40c1d80740100903031544d40300190300300400404086505400082c00c4c40714072502c0d9402a01e5804400c425071054409141c095102583c850303001500303038140c0c58000f400d540c10156039a250203014154bea440428414070703217400245000009542040c2c2904030521045e00e051f0006041d1181a02c1818050785640c0c03040b40c411000d010707031040900d250282c40b00700403c00c05080310f810741511182150808540701c403024809500742000800c641d405592600f4042e0389400002705030b009405152551a04e0361111380c5800d48041d50f4011303000b007102d200042c020960140200ba51000f01041e0740c41a916081c40004e5490145a001529495a90302d98000d801d00c02c204036100001a0b0003120394407400078280e001c41220842d019a00c5901d02000815440808000c950005660700d1340340c82021714114090000345039600c0a1428141d0740c541203038071 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 186843147 1250 186841897 186841901
    0x102011b0512161e14040e010f060302160f0305091203091f0f12060503071d0f04020a0e0717011401020f0106030206030c13120b09100b13020a090e0903040302010f0503040206030606090103020d 85
    0x241c18400101c0c0c0b17482d4907021940f110348d1520340100ac02c0c0341c018045210885035540c110701c01c1540082c0c100390200000d04083d0307504d05c15001031070b800030941410010030b81800001803415100654006a4006803894004000740f4080c0b540c40001e00255480300c4418402c401c201c551400d03803040010b50315620b2000a28003601075000800700e41d8110070f101e20014002041c070380d001707120861048007860140e0014000c9000d0b4010100c000c07400d0008100c00904c82c3e84000340d42074070340504044175610f402141d80c00184d00d0304603900500c01c010240c020f08030180a0101100d03405001941075884d40ba02e00e04a0360440f8207040703400851400c00180403215041ca101130280503d40c0c078022130510700f902c942084c0081c80a5200ba41c02c00043d02030733076101c90b07100c0360405440140043c0c0310141a00100d400302c2542e8001c00d582c00003081803240c1c0603004802001100c0c802d80f11a8181800c04c50151035900040714042c1d072040301440090302c01d062000060400b080140350051030012640030283c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 186844397 1250 186843147 186843149
    0x180609120115120b070507031206030501050907081c110f0706031a0402070b041103100905030408010e0601120f150f060801060b090d020f0102011b0512161e1404 71
    0x99503034442440499a200b2070150b1009041e090081012400e60354903404100c040140101c1c042080001c0c4040030300d031084103151801d4107254001d1104941e039041c410302030441900c3c6e42041c2e001305180080c01143c0000e880c01e42e00b000301a02c041001c2124000e035203808041290500900803800d082891942c00e0103407030080c210584000079241c000b69401407800343c45140442c0a18410072041011a150040b42540540e2001c0055a20b640745030100e800e0940e1004401582401c0180072420480040090401c0d1000c0e00c00810404285606841e80d8a1085c4135a230380c00c5c00f2222804000c52721101c00049180d00a040040c99a0ac1071880300d804c59040b039005000640d0703501014004400c0c28090304d0010025030036618100800030340011180d81081200074400c40044400d01250390007900500e0840420708000340018000c414081d1071030707104c2929590250940000038101c0a21030703d02e041d220707a055583c2e032032810708440c440840300350a074165014814508010400c00f024140104 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 186845647 1250 186844397 186844429
    0x80a0b121c0905040903081506040b0406030e0f01060509070c0602190c02010212090303090108090a020603090d030b0301050c03162c0f0301200d0905010203070c1101020c0303180609 80
    0x14903411070410080ca01d021603084036105a040800810109600480c919003240c10080ea80c2610385041c170005505206a030710261a164001ca000207085405502201d404024001928111910541d82d1400c994050280356807101410000c40d02091041100c406180d11402c001868030300382c030304090103050143c0c0001000402d10800c0c9011540c0c1403012015030501d5503c540d041c1046100025102c0c0209e03103146040080034400942803800401220007021b802070810b5989051182e4225240c4140402581c0401d0801100e441582414032400d48140c3c0621007207420f603190360803402190001e41c038002c010040d24003044c41c8a50031402e450801d001041040102c407030001001d20214407043c07482c1e18442d03490080044652659444002c958510540d0101c1c5c0d18108503998200a017041c14001e0b140c1d45c404020804030a404c4007242100c2805040360680352001c3c0d400483e07441244d0441903400d600203000f41c2242e0b20090070403c4106200a00b190f01740742d240340110700c4410750b2140c0d003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 186846897 1250 186845647 186845683
    0x70c0515010618180c02030d090620030121030c051b030f010501080309010c0c080109030509090609060f04050a0b12010917040f060c0602070204020714120a080a0b12 73
    0x400c0050b4000600a1103540400b25052042d89040350302800c00003520704d1542041e48501034120780620a0088540035403c45008200c45c0d038090800b40010040d01180680e0211202d1507021503a0010f0140c80c101ca109030080144040d180301c050031403291082084040c005425050b00005100380445148a41c08411004803041c001003014a4812056803250813a4500350040c4440d080110840350b215000f0b0802000342c1d411494010031140507035200f039840e54a00350180040550240050900c42800c4a803100c0b15110441007015441007501c035160b01c0041e14500030f4040c01c05401c02c41e48452058000180071900304085901004143c0c840e21003a50b44003590010044200ca10301003210a6001c00c50919040c040003d502001074000c0f0018030000710021420019030b0b07012550656406401075488010500d000101c0b091001201d040ea40030f9140c0e042c0c03010015100307135a6114442e17610800d842c0c80302d1b000309000b00136904920341c00140d01d40c01c852402c0710400600c8902c40302a262 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 186848147 1250 186846897 186846899
    0x20403020d030e030c190b0a050c030a08062e0c0510060305030c0f0601030f15020415020d0906050313020f1305040302030a030b10090608060d290618010e070c051501 73
    0xc00d4107100078080000e00c10003281c408102c401c180384500c10103031113031440c150360b8417071481e08e05a40340d0003054400001d40c030000583c500d0103540041858000c00069809039294183d005941d11020b075800315940f10f6051041e80302c10154801d00040c0c08460058091303075071040403002084281c44858206950580c000510108801401c000c10500d01c1c1c2d50700f014142035410f503603600b01d64000d0480c3c0074181d40001c0400d10580211907040300d0003010003101c2400d4186d444003020b910380301c2114803000890300a107800216140240708030383c0304400002c1d0a201031041a400c00c0759030b00c08203031041d4002d00080e00d144084031a40c450b26014074026001182c0340c10a4110090641e4101304240b802120842c030380c28040c0d500206180e06840050500181c55520100030032045600d07040050b0812101d070f0550020007004407072130503c034207640043c140c1c10b607140b009000030207900768001c801840c031342c1d030040108040d14005a0340201d100e14240840280589680d4070b454075410800000403c0000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 186849397 1250 186848147 186848149
    0x5011a0a08030f030f0a020408010614040c020d050d0e0f03031f08010204030b0a05070c0f0b0a0c0305090304050607020d0602030a06050f04140a0e03070b010801140606070b150103020403020d030e 86
    0x80000c0c0140201401140380091581d00e0390707031038000582982c1d060b440c100e02040d94090203405490140810342c1c020840305030f40c0d4055030741180c010304070b1900445c500701500c2e5100d0b1001c103041c8540c1e1030039210306203003510b0210404000c02c0000d400002c03601480030284c0070310100380011030203005030342401400c000000858111090700f50740141c02030780c810401000090300840348140d02112111001030300d40d48100c011781c0c5c8441c04000c01402d086515038484200000c1401103802403828400800a0001e6400113078100c0d00250b032008440e50043c03104000c603240c140001c1c401c007880940b4211041c0b08a90341c0d9016a0400c0d1180206291604014802401c21b082281c0c00e400b000c5900b8840e10b101405442000400540306200c869140d4481400036002001140c8400e070707200c04000300542c1c2d52503816000b4030103c4000d9100c4841c3c040851300e18a4a40165500144c0107199440503840301c032048900c400d000da0a16040c96004e2200101507650740602d041814001e440340f00307454078040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 186850647 1250 186849397 186849409
    0x14070305070203030f04030e0301200a110d08040b190e0d1d010c1b05060d02120703050402060306040c1e1701150906050a031d030309060624091207080f0c09040803060405040c0305011a 81
    0xc0c2da42403050b13100030803815009078407010558102d50088012040c4b0f4888050748500c24810a4100740700d0b9003482c6c0c4000c885100003d40c0c6c0c0b0541501c1e9182d07c403c1c03200c0351020501e50710110101d8005018003201c40041040100d04042c00d03880179100c02e8589a07540041140d5070400003040c041c080d030209020369110700038021179500c145107240c1007204d480c1a0740090910300020349941e02a541d199170440146011300120401045500720022003c981180c2c000c02d40b0b09008404081101c001000081509904c0300209030754003213031a045502c6050100407981500110411401c150b10f031003424503040800501ea8990b490844041c582d079107030a600a624001024003244d0290004a42d1619440300000d802c01c1e64840720407101e50380e090000c00044482854455214083c042c9040005400e0400200125440f80c00000d41e20100241005c1103040501113801800780c03401000040c1403440c103a800310394060710542211000a80b079465850840f90320582194036540515441d20300d40c503080c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 186851897 1250 186850647 186850667
    0x703030c1203050c0d0b0102070305030d0204080715020a081e030703020a1d0f040b010c06180b010b03150418050d05030106021011040b090105040914070305070203030f04030e0301200a 81
    0xd08061182d03040400214082d4800c4c5c0308a030000941c0da26104c000703a8403e01c07040c001540c010040300c2c0c441d41e080243d18000d5016100d2180c0d41d00c28000c0000e40d8089408200310801030301d070060001c03c6200e072200111980002180c0b4440c0a0f024240d0590130108070103035000c2c0c0219a401078880212041c0909140b00d44514031045403542038113a40d2941e52580c00c0c80304d51300103a4010507100001e030016909644821801088a41000d41614188003030446050b8006d000313003200f00840c0d1b031b21850b11070248026079450061010500000301d850800e500000c03140e820210005442d10798603101e803801c10003498000c0000607070010041005950402001c0c0881c4088001003000c00c44011804c81e040c0310314821120409408140c6603060783c0100300740c800031f00b081d00b0140420040040c480c0c185103822950580860710f090b020404c039510000541e4450340d4454000e41d81d940303854800356043c2d4220240d959040d0740341d40c007146009940da40200401508504070315251100100084c0944c0c801c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 186853147 1250 186851897 186851933
    0x6120b010e090105150c07030f02040501211205071e02090601181712040f0e100302031b0609060a110c01020111120606093d021209030a02030703030c 66
    0x700d0000140c560303640c18215045036811111005105e02560004190b801001e1581c0700a0058080000500070ba82020494103803088078204000e0380c035403404824410128000e83c1c6241c9481001c00c00141c0d0f43c00b40e0200030001800d04500f130807050396070411550417002034001402c5401341c0701c208500304644600e420107000d080092000c003001d03450f028906580d105007a0302d080e9160b24002c0401040c0300c1700e104900d24a002d00d0b50703a5215014220010124801c50b00b05848000000d03440301500698902540d6004024150307207074140b05222200c2c1c598150703c0d54331140822008034665109001415418410b4a1348140c0c480103c20503402d0460b0301c00c00380e05590410002c555a4500380c02199461a661260941d071a191400031034158040c20a06075007000c500e00002c28048a0403082c64014085400c00c404030a0190740c0d41a85141d1113443c84015922864603080301a25081c040d1580f850040d0448101c01026000203103811150b51055000c40e906094100a0040d081001528100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 186854397 1250 186853147 186853157
    0x3080c060a050601020a26130303020c0d030e0f0a0e01080c1806010c12140409050105030d0c0b070f030f092405061e030115260703020a030f14010606120b01 69
    0x1e48540042d441b00b84005005012036424032400c03031060f400402e0071400c0c03182200410385940c0510001846039215000c1a0054403601c250007549152021504400c194103a0f1861510f8100c441404603145132480050303132242003010081483d05a000209000b003002c0401000742e48080400c2c4020210030900942c00b44543d01c00f081041d9030000c90600c0210313030118030031a203403241050480d101085501c4030700d04c000f80040c00184015080c2c104505072581107050b00d1400301c80c02002d44001c010b8540003003504072080e00241403d03005d1f6038810307240c2c0000e040200c3c0c075003401d5281c841101c941003004c60f030030905451100d4801100d4110303202d4100b01ca01042002c0e06080e0009802d40c2c0a1035035141400314041c02e4101076403070030341200d05010f11015901d8202d035240c80940404515040c0d8480304402c901500740d8101c0303c00520401280d80141510080c1419a01c4480d0b0361800510152942c1d14406100d00c603008007485400f004120b070740c0c0c0f0040310f030241000d00f00943d40e030565903904000d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 186855647 1250 186854397 186854401
    0x1006140f040314030f0c0c210a060e0c0301110705010c0503010f0509180a0f0b0903070b0a020c0c030d0e01080f0105102024090102040b0403030507020105040f03080c060a05 76
    0x80554200d0741500d4115000c0700310402500700d12031442c803520381d401c21001800310764400321200004400c80f0302181290b4244944103503680c5503042c5409140b80a1003907100c3c0c941040445c42d151f1000380030001041c00d81d032a0824030001300c1d0079580c50406412030900005810300c20302200380f003955080c0c0032601e4070b03c3c074652400324001c2c0000d103640200ca11403c6c08102040c403401100350340740038042014060303680d60700311400c2c9002d42c80c07040c10064807a01c1c510350011302c2c2010040304540300d541d80403070828255241c1c80001002500310340d142c6603c41c0706801541c21076a50810440031603400e2541e07820414000e4000051102102801600d061070380d150042c8225550100c0e00c6d141c0900c1450008143e460241d2010424015036401001c107000700058410564039042944155820f0b02202c50b559444411040d4205e2140e40f040c02038080040c031080c00003070f100d0b200800b403160051421504181c1c45207804118068150300c07c40701758a00146000d040c2505100c41c540c44841400100700b14 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 186856897 1250 186855647 186855667
    0xe2b05030601142212020111160e04050304030209010807061b0317071206090b010305090303040c050d060e03040e2205032b0c0f02100603020a030201080403030e06100614 75
    0x81c0007083c0d01e0307400d08000401d0030741c090034940f40180440011440c00c008840d80d11070203e0310007000441c003613002a00100900c03121900c001a10300e546811051615500d514012100182c0207019204440b2400104000800341e07542c014a075000c1c0017083c000d000c8961500b207010300030004050b20284c61051000c00700003c643c00c002d220940001030306282506603250325040301c10002c10407000303140b50f00d04200860042880c1e8840c2c004103400b03032402c002e20340ba6407100968a00080b500240b0f504510402030002c1d0030304076401781c81c941c824000070814200c07a400302400c40d00a9009214100500c1c0200084c00130813941a280741d50804654154541c5075403142134613441140c43c01c000c1c5e600b00f13541d006015181c0c003101d05140f91100a00b0803565200074002031000d49030b501c80300014070903515103148044043c0724180440754000e009050b428910b42c0152036100d401002a01856902c80700005102400e10106224000d403010122040303082800240c84038802c005401c0c06414180828010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 186858147 1250 186856897 186856907
    0x3030708091203042301141b03010806010506090607060203150913050607030b010908070e040b0f0106091406070f0f0b0a060807050402070501061518061d12010e2b05030601 76
    0x264005001205c40d40c1c862001c0b404800020201c1031082d0718224101d0b9004007050301050241040070f030380d503007081951401d4035650300007801000301d1030304448010012850044003c6c204a81d020b882e10341002c8280d1100400c80c4c10469032070700940052480c000d001c1c40c0200c60581c0c8100d034000300c04004000390316115540c00008003a8018036581d0311402e2841e0b070152510900506821040310b007200c3e210b41c500008100182c408075480000100420171141c2810101816540c0316500c40e1706180ca0311000c685222031451003280c200104011090200d1402014a600705014542881c01410640307003200005800030500b84001e840c00c1000d010246011449008440080f039000d07803142340c0c509040c0e00412255112140850b84160070032a400c0d000300d910301501d0410080c0d00c0c40269580c0050710300000c81c0c0d0060401a402c3d1a843c99035182110902082a0165000003001126809001d20703099030f41c415040c84461294801d1005844809205281003481c1f0703006040d400e01c4c50010385 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 186859397 1250 186858147 186858151
    0x11407060903110d050d06050103110a050304031403070c02090f091b031002042402030a0f0c0c0506030a0212060a0302010f0c0503130b041403012a050405030d0203030708091203 78
    0x221160700c0d1291081818030030000744003810b00800640740621601d500103809548450307a44025581082800165580240f28080c0e11480007071586180c400315000465007648020801c4042c415050320004503641104041c45c450030a5403075098040c0700c0380c010066500c00c010800d80b1800406d808020140d080460b8400b0f419454a60402200c084400040c2c1050704940c0800022880810b0026103030f181c50070003190024019400180050b10820103c0e02c6c0c0c800e110301c440201d240011406005489000c101070814000c146014025131200d0018219601c140e07924882c0035000b05d070030a40307021407621082e0800d000b02c488544803031840c0e002030040b81c0440700520504c5103481202090020610441e510b07031400c2d1040e401600e4540300c11131030300e4115004c0d6400f101241c4500c40240d00b414445c1401c0411065a1343c45502c0052030b0050142541291800801005100018450b00c0401c4215107645194020350303128a0400002000360000800d00d07025548003041c40b054070301d04941280c0e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 186860647 1250 186859397 186859403
    0x3120105031e1207141b0a08060f0609060105090411041403010204031a0709120309091a0f19090204030f060c0c1e0303090506130303061a0d0e1f050402040605011407 73
    0x140d00c0700114140b03201718501810142c40c1c1070191545280302d4a054a220303807000c480c12200144c407d0340366050540c0c2d0f91812140501c0070504940031401518119110b654010414904076241c0440400030a0548411081080c074642c000b2a0a00486524a20142c0100c0040c0c00850509143da261035407581d42c0390aa40d00205c4200000c900854450002d1501170030140780340c070725505c495103001030080c8024404d40800c00d161583d504002203000c0250140c1030402004900c030400d00c0f404010009001003140422000121400101e285c000c0c000743c002113000301031082800c95603040810503246890702c000d0400619042001c0081c10381c00f44000403a429403410500c6a803145010382c0140400c0c03101030058411101000b00c40040c095207490501d01c255000d120603555006081d00703840001a11004162003440788202c090903540c06900d8403070480d000c07642070501412030082e02d180100444464162160700700310075400c050190100404003803030f00b0800004140d0f034140403070007070103001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 186861897 1250 186860647 186860683
    0x10e0f0a03080411040e0a0c05031207030806092802031e01060801060c0606180b030c100c080d1803020a030e0306060a090504061d070504050c040b120a06030503120105031e 76
    0x585110f496541c89400c6c0c1ca03091004403415405141072003003050541d8450300e07119102d020107600000343c007281510740456040e11281e4240e00ca000820220310300040480407044040a9950010400c0c1c812009440b01400c100696a0400b410b01c0e142c21031148401c090030022a03001080210352006040d41100c486180000e0030464905c0d210300608031513400501060500c128003403803440e16500c40d028405e401c40c00c03a20740402d603030280608080100c00d1200450030201c041c2c40858802e03c010598a400720340009007500601860107560181ca2400754011b0307010b925072400301070b040b40c01c1014180040b4001c0c03080307103841000140c24160386d005900c00b45450304041303010812981c0005d0b8001012103a0710000440c2e0b900d150365180841e100e154412400d00703021500f440782281c122400e46400c011f40629000b51014400c80d0840060309510b00d0795910300002020a0042c0040e03c84003002000741d01c0c240d458072003007518104112442c030350650b042d4000b1020404000030b0504040301e0606403 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 186863147 1250 186861897 186861923
    0x91305070e0c1c1b0e0103050f061309020111071409010b1c0c03150303030b0a050906060a050702010c1a0403081503100b040b1503041208100603091e05010e0f0a030804 74
    0x1c034030302074140952411240c00080213030100103a080b1003030490b480c00070703a030401c00c80c0d440400d03081d00c01c0d01c16a075194000001ca00c0503014014503400c154412401814181401c000b00130078079140c803800758441c840100d00080402c2d40e81c60300803c414018148080070038101202941c01c7e22825101c5a001210980e4400a180b034030f0380070f5080b1000582c200d8440c042c21035070303c0c100900a0200c2d0503c1d02c6c480c02d03c844002c40e0360b01d4205003c90040002a10480c00c00c1c24281e01607c00c0c3c2c0c003401050b03042c0040c5160000c0000d1100c5501c125051711500107440900742031038090201d42c0b028080c00e00c1c2d10f40c0b59100a200b82c83c0055810360781304801d1b50201740c0d1039071b1402040040c0282c0f00500d8002c7c414100f000c103101c203040025805030784250101009840b81a40403916000150b8421102e40c00006007080003a00c0380d008000d1060041c2200c1410248000f0208a2060401412145a5103490f49040c010800b480340028401d8408054141e0350320b155001051032500810050044402400b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 186864397 1250 186863147 186863197
    0xa1d0f1504201512070f032007050703050a030c020307090603081c06080a110315040b131509030f020c0105211302120303010f1a03060f03010902091305070e0c 70
    0x100e00500440041500d075130329140d8820042d0070b882240c1c85000705032061214060141b1034401c080210100074140d4035910807612688030b007030b80b0001c001c0e16070b4880d024000c4003283d42440000e05040c400e0311821101d006a2042c5400c2c002c440c0e00940c0d8080c80c0c508100040388840301145d03d0540318501c0140e0300c81c080c15001d401400e6542141c61144244144407080005050794451840f808170211240607511044d000203a5604442c004c01608164012030103151034204140b480074412502d508d52a81411b4400003201d1592400340c00040c5500c40b264907054050064640c0307102d080c40c085242c0725242d0000c10645e80d42000c140b00b40d40d4030100150180c1002400e100d04194010642c0104036400311030030360380750401c0c0030300c062101454034001081c03090740c0f400008281400d1002070440d9914020040030300b070300c10f0485801d03540750600700c40182d07140344c812481480880f0b1350981c95000c90801600d0b2141c10b030400102d040743e01d01408000c101d48000d8410540b0500c441c500740c10031800d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 186865647 1250 186864397 186864409
    0xd0c06050903010e060c07021302040f031203020d0920010c0803070507110a15020607080907030b06060706060f060906111c11030d050711190206030a1d0f150420 71
    0x4ea5001050284500b44400d010740680105400c0f03008543e8082c1d5850710745013050881c4507922607404015441c4030100300145070401c620440c41c400e800e0050400d003048030400d090701d040920407100318125040441c1a80f0000c0a01c0b04400428070f060a601c3c07915698100707191201500500600c01c002c120001000306090700e9144042000d400c1908180d0703600c910119401c0c40130020009401200f000808140c86000d0052191855030700401045156482d00056140050002c80c0c20640400c101404950f450140c4402861080350944041d4a00040100603141540110301000040e1100e01c2c0900400a43ca406480b903e00d00d0010b5051030390b4040d1150125016210310500000c200041c44020790346c4001d00c50801c136114425200c41d44130a076a11681d60000194038105c101c0c400d9009401c0c07a4000d55802050b0a0001411100d006143d503041440c017012060507500034400b0300c010120078882d000c4170b012408506c00b01130809036600800c0300c017400c121120310400244a1b003031720b80c1c650f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 186866897 1250 186865647 186865661
    0x311040e01020d0f0b120709110d05040c09060801020424110609010204140901080607121118040606080903120a1404030809070605040b0405010507060f0e060708060d0c0605090301 79
    0x198000719030360300c0c0c0f040141c005002c07819030724500c00e403400814289a05040d02080c5403003417a0005061403c0c2403a0804000700244002c50036021018417440c3d1001d0300301c5c400d40f40101d0140fa0281c0400e8500401c203401c1e9085600b0040440e401030000300f0842c1541040c0c41007544085c4101100804920003c40710340702d036010500d04900c03600e030912104a1040d170040c000d590201d946070004001800501010000a108040d00c6502c864001000c50b0301c9422900798600c440741c03001c10301c08002015609507401c0a400401c596048075040d001c14605171091320010001801c108a41d40f81001c00c040d141d000d612104200072070800001200e144641e0301041c2658000007503a581810700b4100203024a908907003000d000c4c41602c20205910340900c0c1500c04541d85400c0c520301d0181800e0044038a500001c2c030444109850305104405c08074a400f880392124208002440e05181c00040200301d100040c060600842c0064095000303d10f502e0714600035100142012680c4081c02c0010138018051 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 186868147 1250 186866897 186866921
    0xe0c150f04030b0f0604020304080f0a03110301060f021b0d0f03020709020f0706051b041e0f0603020a0915020303010b03150306091c08160804030215010b04051513031104 75
    0x20000703010041150a201c011302a0710a00b00381801599548240000c0b440180d4015010303a0042c03000c419410484802440611000e10700400c2c94600c05680140d140c100b0781141340480c11b00e0b8004495281d0400401c00882029855429500306800120b9181502820040d040d0f4110890600c10b040c000c100710b000805003038504554502484010700c0b215041024210b410368104004a4030458540070403d0765500804401441d091520303800da0f0650552010007840141d4070600007680c000394030083c1d80103201541b005a52242c0c02e0304010100c4403550006001060508510509a40d00005490540c2e190041090752034031841040030341100d0542489501d88104000c0100c0080702040700750002d00349026444c104c0300716007404d5440c49402c452200640292581510905204a00580d00603010f0300665000c203800509108400c1c20076080b00c3c1c101040040c080000d03041681079400c40c4107840c0c000d40c2c1020125100700c8501420b0380f0001c2c01c0280851144c580d95915035100d041c210310 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 186869397 1250 186868147 186868177
    0x14040504090c150306030b150112020313060509010207060b10080703050c0d0c090905100b070f140601030b0105030606010504031e15020c06041b06120c1206080309090108010e0c15 79
    0x40f02d010020003500550008444c2c28501e0300c0841c1c2c07104000c00700124101c80503181d00385002302d80c10090000b504010001408100403002910101d0603030322405008910030800580d07522010f0400030305890380000038038000c20180a04031100c45e401482c098000300301c3c2c54082103a03240d07550500f540d405103587d0502c1c3c961a120000c03885a4110300241d0841d40e80c0e1a0601041d61201c14151b003200c0c45100d49400407004100d054006034040c008900400c0c4500c503040900c102d8011207500d0000241c008440308907480005200702c0c40c08000f80c0e03078031680034039011f40390500755a10720b1128400c022000b2440c445c4e82c58014104900007804803a140607000c0210f449030b040d0044560703652015a0203440000500d02d1102c10170100c0828042510034589404044010118a15000b8220564003104119903000300200146e014041c080041c5000d80080d516401c1110400c0201380045c0d2101d15540e241c036000c64001c40c00030402c0c07000300300110303221000c50180d035192013040c0c441c2c00100b00d5080 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 186870503 1106 186869397 186869429
    0x8160207090e0724080a05070507020f1807031d03070b0615071e03020d03200c0102070c09061703070201090e1806160e0114040504090c 60
    0x30b0040000c03140115070718004060f140e0008030202030010000103401c05400e62001e6880c2c0c12492541c020811801d1204010344984207034079009009800c1c19400b01d043e82e5032031b0f640026405038051894810320700460001c0082528150111071034080765044070600c04004140d8001d2944407094402ca9250034040240d0101c0d0354146006007601044030b0000200185810030b0111144140c14030fa0031018600641000c000320941e104142c604420080ea94104003429244181e11742c00c8265220728002d940e0b400b80c8551a406460150710040004401040e0780c4883d0845a0503503845000d6245010002d40b20721401d03002070300258401d601807050420845e031087d08640404810440c1ca22040b100a081400468100440d0b002462454619a82004000400400c2440c0c0451192082c04d41c030091070007103000300b5000d030390744a410404029981c000c2c01e003d0b01031112001458 = true := by decide +kernel

theorem cover : BRFrame.Cov 186690647 186870503 := by
  have h0 := BRFrame.cov_init 186690647
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 186690647 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 186690647 ≤ n) (h2 : n < 186870503) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
