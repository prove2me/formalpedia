-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2559
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:04:21.686024+00:00
-- url     : https://prove2.me/submissions/06fc4dd5-ab71-4731-9422-0683943c82b8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 460071942 ≤ n < 460251798 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 460073192 1250 460071942 460071991
    0x3060b011b0506010b160c0f03170903060a0b0f0d1a13030815010e03150f0c183a11010c030e090912041e050604030213090602040e0406050609 63
    0x220b040d25040700c5c0550340c1d00f0511146400b00300001c02c0103031100d1a00b9200040400c04c8101f40001c40744a0786640514108180d0350844070b000340d1041582541001c3d000400e00d254590107c201114002c2c842d074102d007008004607031504d24410084407290045c10078500300b4111500440e0f0300552400f100d0031140d095542c010649600038010113451444020400c0007680110a407108618004d811114107104200707100101070700556025645030500404504000703801c0c01119030070746540c0b540d80e428941240c1800000c1c00c1c014040c68054507035140c90030b14068540703034000303601c00008510800303c1e146040007044910000501c90520000c10000000241c000030b008007007010442d00301c08140d03510f030951401c1c8228500c0302c60f000c44000801003042d2203091038200b4484507801c40c000340d060701ea405000d03042c8940e0002039400b00810903480803d406a81014445c0307407117080050300305030760344801015982c0d0903181181e0241e1103100700052400c11008180c0e0180c07800c5a10320011001d640340 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 460074442 1250 460073192 460073203
    0x604060804060f050705030a0506010e0d080f0c0a05030c01051e0f0402030132010503160b180315040519081e19030501050907170a0b0d060603060b011b05 68
    0x45900340326112000034144101a48103031006840e51100380034500c1c14080003469079000326484c8402d1480d050200d8019440355460014005015000c00000c00741901d501c0e0141d0864010400160380401000c000c4042c21320444c40c00610440c011911096070038074113825144c00030b1401010500300701500401c010b64203541c94000000724103d10407038540d400801d025007240031035a4803c610400b15070f001c1d0802c00d20380380d01d111200501807809980356400c240d2200c003c4038102180c6a00c0c200c041c40181c1e0650024100c50484042070905108002d011900f000000101842d00d80080010030041c40343c1801150b94940c103066a80c5000700c02d81e80d5041040c05200050704154522002ca01241c0c0c80001c200d410811b480d80c4171481c030302126000180548000d015840c0039a41c2400803c3c1618004d06840320011010401ea0034140c0e03074440c001c802005030101d460342c40114031100c034002c2031851240d440031f10f0240350b010840341130020014206292019400b00d4806c00070301450040340b0003040 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 460075692 1250 460074442 460074449
    0x5060421061a0a090513021224060f042c15010b13060807120b13090f022e14090405091c141611060415020d0e010e0f011e0302030a0b0402090604 64
    0x125423104180800c212881c0840c0c1503c40780210206c81412200d100362411414800d00301240d00001400b88207062106450a211804005c501e50382c591104203540c1c94a91850200c004088900029510358104100f000030f03404243d019900040c0c0b18070b40d40400b5410400703450f29081c0501d4609020034014039000c1c2c00c1103040003990b03442007902e240366a0800003081c0d42241075028420400141043c1003c56040f070401ca208056054000405074001141010902c80004100d948200c40e1001034561f580a041d844981a4041180755010b03074543c880d29003c4e0f0b00314001454403042d00c0740c00020841d0708000301c2e414810364000346c200d4603090300201d8000c0d00030f24161190070b0042c2e20f07103400404841358030580e01210115006c0b5034910b0340031500090b0111035088500050991000741c4a000c03a80b0541c81c0042e03a80e42000080341402c0c42001240c40d41131501a0412209000d2403820448210304580026000400d004449005004018241c401101c0031403074a4074440025486104038407 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 460076942 1250 460075692 460075699
    0xb0409020609120f0111120714030f07020102040e0906040c0e19020f041205160b040e01061d03010509010b01090e0f06090c071502091905060421061a0a09051302 71
    0x84a072042880f06000250000507898000c5c021045c2c4807030b017400140c00110112554429510000d1036030307031180c04080860450010007e00c0c6480f6080e0010740c40c8402000001550b40804c0b000889100750f120b150320414885001e40200c0c00c0c54901812103607241c0d48940d0b81072041c00b050041c0903c3c1c0d200500f21858480200603550620000d803c020760045034084001c04000000400901a0210b41035111121941d13620364101c0d12003200441900541c000c980070100400018030003c0c0c0640e4285c400388040c03803030044003591031000281c00d5071000c407a6000e075030b5114001c00e00309503000b40c42040036003600745240700d543c50072103c0c100b010180185035a2003081d107240492086940c050846280d550803d04481104640140c100d010394041c41620b801040500e0000042a492803001400c0e41c0000702114075192070200484070090f01224424058020003448400182440c801c2c8203191510034038808403c401d4004200001055600000326581403104101c100160142c01121990307048 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 460078192 1250 460076942 460076959
    0x809101a06090d08390703020607021c111005071203051305070902280e0f0415080c041103100b031015090323060a020c011e090203010b0409020609 65
    0xc100142c40e00300070310400303018502d002603105c030080d445c2d2003001e1401c42c181407201d140c0c108840d894050420b2031143c4100c150403a520900c01071070440c00a1441038002064584160071801c825a0394845210088507180000030f081e101c1810460042c016074481818201d00f0844291100640d012804c801d1404055542c030005480750500c030461110541c1000444241c2d5440d1b17040350000f540803aa083c0003c0d40f91501d9084040c0610780c0c8040c041c5125900c00c0400906541840913600300d1250b0158055114500c3d0109a40500d0000000300303641002840703040c003400705001c00c0311041034118104100c20400c0005504902e0b006008070344103003510300e550350784540e00c818406e00c00d608000d40441009441a88a9a0003404e001c2542c1c01520400c1004811440d6007006411017140510941c11190000c0c074040640e50180008410381d0f00081a840c400c40b00c51070600381041c010711001c9542c1c201395025400d003417044080038241039504003d0341c08c0a4000804502884d1030140c03066450 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 460079442 1250 460078192 460078207
    0x60e0301270c0b0f22032015070c05090a020702030d050c150f151906030b0622090f1802090405011b090303020124031e0b070809101a06 60
    0x2c8900c001459880c40740d0b0b03111100c1c008110300316030061003e041502c4515044080301c407002440142120740c00644803000d91604415420a4160a50a543d0000c1c9405100c40c11b00d500e80d001f040110310a050500e0180d042074100000b402000d000b01c00303941d1051004c000103881c001401e013803409003414403030346030080141031601d0b00050b0600c3d402c0c00c0d007940003070001480a42d80560701a462440700d51001c0c03110003092054070700d903061006103078036203a270410031456000b40c2c003a030900c800191600b0720707142d8106501ca543c0c8000d5840180c00c2030480d00208180c2d941c44c41a004007954040d000c3c40440164482c03503d0907200058042c2c030600c3d03103002203000c1050075481034091000d8038403281d4a2813450000078000c42003910081c0e0142d401c0c0341405c1c2d01c145246202452a10031960000e0302c0c2c904680f40c40d03242d4610708680101c00598413102c840400c40300e442d094400d0810303558082c001d18028842d41d007010030381c28006001509002d40030843c16a07001c90f840c5120400d8828039214441c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 460080692 1250 460079442 460079453
    0x14130c050d0f0602040e060f0102011104060e0a0806090f0f0d02030702010f051c020423150a14040f05011b050a0803060d060f0504060b031b0907030f0213060e030127 73
    0x50b610004044501c001000115540551280f80c031403242101c107104d00c0c2d003001e4016404e954102a460103150010001030007824041c500d0036004207005803141804a44440480345000303400c1c0c804580a90002c000d501c440031080001e1030b04410001c001d000c1e28034005502a61300e010300320009050042c5135040c40c4c0a81c1c45007081c0e404900300b2407000e07030f9032140b5042d40800030341c003c0c0580d600410280700020303149151001c0850309140080d060803074001c0b4414030400e90350080d040410800907900803103e00c05041c1c1000d0006000285090700c52245890009400c1c03007042e0892844a8a44c00700a5010401c0407030781010503a005880e1503a80e90325600080c1c07400440d1031004080d41e2628920707484081c2294000ca1149200d081c04101c0f0120b680100359445100d42405a04030400d150241d0050903ca400681c2003041c0e410049110f81510b20310390241e801148804070b8560030301c4001c0003100c1c3d0203085460f080c0000da00070040888400c10276004484000070704024a210002c12008004 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 460081942 1250 460080692 460080713
    0xd020706080612030a0305010504050a0e06040b04080715060509010f03050c1e100513080a021507020418030507030305011401050403062004180f1a01030510150314130c050d 76
    0x10445044c0d81d641c24080002400411080c040c9c103005070b1030080090103044681c418206c2e280045030061409649503540c0e03040701d21005000b00c030010018403400c40010804201c007818031020010201b4140d0400c814400c500c44141c1c40b81002c0c0040360810404901c000c12224502c85095919040c4105020312031494684d0b8400010780217828140c02c200c0c00707648540500640b02c80d4110710502c2d2961501c505544208040003e54040b40c00d01240041c4c3c11060001c00b503c038800f80c0080b812402601225542203402c030f8065020030000140341c0101a4181300d4280509500d03e85030880c07500d01c1000074814040d90100074009503848030262404074010404003258029602c90b160b44d60f844102403091009861040c440b041d0070885040a0118207005d1017600580e00302030801c010945800441c00360001070503048032100c8020000c2405074008880c80564031241c6c80120b204501140d440a1205004160220074100240b0302d400180c0b65450700c1c022620112460307600400303141060304280703 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 460083192 1250 460081942 460081969
    0x2121909180605030c1002060f1e16030e0d020d0e06070b130309090c0806060d1b050c070509010b0a0305040c171e0a0c270e010f0e0d0207060806 64
    0x2a20800401515001c990045410b4540c1601070390108021042031140b0410302899103400750f00000c00040340f1244a03c9039641c0b101612108501c1112070b01e2064120041c00d0303800d0382c406404802e070020119014007030040305000d041c0c01071104010b1104000d4540e100c1e19901405c01242140103200d0380d9902055801303c41d040180c010407801d0100d2400c88004504c003045011980b2540c0009035080e8511850f4041d0701c01d500c406101d0303580e00702040390980c41540706844c0d41c1c1d270b00e0000e1400d41c0c0f0780c1040e6001e1401ca81e11070950710860000d1203451305040754042485000c402006000011441003960400211810302007450744440c80c0500c0c00300c0d4190415001da45026020b180b0b1510001070248035030001802d2030200480c910101621b541030424080c1090361020010003c804144800c003114201100491424078002480031040c0d03070101c80800038503911010a540c5200c09407107240b01c0b00803103800500c862007110320081d4443c6424030806040c80501c0c0002419030b2100c4110340b01c2c0c0c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 460084442 1250 460083192 460083209
    0x304121d03010501170c01050406051818090607030608010606020309040c020715020604020112291203161109060d030e031606050c01061a07020603040f0b0c03041202121909 76
    0x540d0784407140d1099441803030640c198207214902c0c90707818550140085034151505a56141e2038100c0d14081c0c04cd0380848121550341003000019040400711200d040540074414801c083c00450504000060641b809034000920341c0c3d1519401f007080b59000021186c5149041ea000308441c1c038003c00036030903c0e03000d511104c2207801c215001505150301141c6144a180700340c0301c04522180b02840d20b07049403560450010030ba03030440c1c03075a90044c2c18064020b0382c0640003402c0c10405011018140e0070764010780300048060600903120000c2203008068000d900500349c80c0141649000300c00600d04184114000c1c044c0092840c0c2d079061074406104004003201d0400b55440c42035a5541c0040c06a840031040307040c2035117001d00109882c04a0018010513699514100d07060005c0341e02000b40c2d550014200701c503203500400466001034021803546100344032100b9a6600e0345854140340005208404240c8115003003080e00c050002c203500181c648041c40e2400d0045c6088440000782d03000b455940140c1d15 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 460085692 1250 460084442 460084451
    0x409090218010303050a11031e2a0708010b06091012060503120a080f060a0b0c01020d0e0106030b10270209030f01020901020c030309060d05070c0f030519050304121d0301 75
    0xa15801170b008190108041c1d0310a1200c12845805544901800b0300c0041c8c1002c1c1c0f0b00380c154220041a0107003605220200d62280001240320740b81034820780302d43c0860000c2d0056807003080390303d00c00e100d210b241c0c000984050303150540315800181c1d0403920307200d0b0000380301c06500341f8034403211140c0c0480c0240070050100e801e2200c40d0007904990340c200142000c0020200070004030b1104007460118001c00340642404003c074103142c81f0808e280c20016554140759801c0c062200d141d0102d01030081c070441d1445c00010180d0550074148540d44004110980e002c0003190300b00b0181d10043d0301d010422000342c01314011312851000041c080d01c110001550b05200d28074100f0030102041d070003004200002d800f1a0100e21074007060544a016940b09254814410310040340f5a00d1983c101070f134082d060389041c441e04002076440b8220322150301010b8001480c040342c4024a16068014142000c032241000d0b419032a01c1c0c4d8814409032900101d0008005200080802561640044400d00b00c0c00400030b10 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 460086942 1250 460085692 460085699
    0x1609030506010b030a0614010e041d16081c020622020303070b160c1106030403020a050a0507090c030612020d1112010510050103090c0e04020609040207030e190b040909021801 77
    0x3101a0400c2d42c0d104010340c03408200250008140264500b4004182c440c4a21002540204070040000c2e42f42c403d10b1482003200301228240c00c1c0503245c0d158924401d5041030718180080180341002000b5024040e181613440701106980015070307603510108404c01c000c5106040410741c0c9400c40b84400007034142c4000306d0b6400400082c4c8038141c0c46581d800d50400c245115540c4201c0b2200303491040584800b088904444207400c02500455006000340100d40303506445698146c5800e01511082d1100c1c3c011070703401d00c182c505a018ad039601388100d1501344500d6041107010060051100720081c800c440c0c502e2071204110081400f5140307404010040010b1001c208203003400380000701c804040d00c40030001c0c042021740c081d1260710306664203c03262001207810982c8041000300082c000340c0e80000180712030b81250303881d40000d108441c403da0302c8049582168050107486110311400900b0542c0003281032041000441c1070710100d840c00380002c00c1c2c90700d00b400481c6921400b5054400050410070011 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 460088192 1250 460086942 460086959
    0x6060f0c0616030c0c03111608060403030b04050f0105011d0a080d12110f0309010609110705060601020a050607050a09120303020c06100f03021527190806160903050601 74
    0x703620035885403901060350450440c0c210101c8461007002d401140039200c044003c42d1041c00703000300c081c1e503c900321403080d2480c25000350307904a02d500115080d07105504100c101545400350f1154080f05807414031060038540c1e41000c0c1d9000500600c2d0401015001c3c2c1c003a032400e001030b41c0c48140307030280c02c40c50b046449500350360304c420113882c0800114010042000310188140b088880c00c00480c1d0549003080000c55448200d548047c000d40c83e01d64892101180c040e256106200403040c88128407a0b03540c100e454640d050284c000c2006066401c0b80088034041840400e00b1507001a540ca80180d0b1480710110503243c1d46d4580d0400008194035403c24000c142c1c041d4020701440c0c0c6c4100403030710180e862000700082c01030741e8040c00001c0c003040c000420060a106600207801c182c000030740385c10404503041458200c04400b041410504000c8581c12031800c02c000c07400302e40c400f142820170000d8141010f2a03541c070000b410b4180450904010000c4e240e105840000207103921100740c8245595500c40d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 460089442 1250 460088192 460088203
    0x30d0e030d11030907030303021b0102040b0909010b030906070f02151e010803070317071209060b01080a090804140609090c27180c0c0d050408010506042306060f0c 72
    0x140d1030052a0038550071910b00d4501c00c0c2c134861641c0000400d01c550443d90b00310040c4d00a501c0240b0609800341d0100c0b100042030016001500c4001c1d52991656100700c10005d4520042e4459540e072217007002448440c81c00410402d07408941418400c2c266055050201e07c0c010f00b03401480e100c4440700c0c040c4011288100e07090303500704c02001491180d86c0d03215010f030b03500ca1143d10002400b14001114550017010001038580d480130035401c19204003840c04003510107940c20508100d41d45035480b0410805580c0000055410140981d030800c0304041558400101d0300c154010401000011024440d040da1443c3c100ca00e00580640309910318140042003840e02c0d00400b413904c40c0c503180700070414034480a03d42c03516845640113001001040c4190700c084e6021901404070421005c04118040e480c00c0b04100400d2401000c0d51000c0e0740703d1078240210700716503000d441c0078420f50500303050508005107034130007080843d5030030301581060310760000164a62240c400d10710500c0c2e9020805c84c555000210300d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 460090692 1250 460089442 460089457
    0x309020303090a080610060905090f0a1103090a020a0f05010e130225031403190515030f21031e0c07020418120305040b0a0b0a030b09010c09080a020d14030d0e03 71
    0x40d9240c00398895005480f202030382c3c09803980000894000bd0081e046c06044181c0089600d0400981000f801169a03469801200d5121081d03009050440450505091600c002c1108419800320641040d00082105040c0c01015201c0c4020903982208014140d04450403c60050490120640c1c3c4100c03525150f6400038090b404250560031850700300c4400e1046034442c81480440ca8890390154820000512020b040101c400c8461401d00e2411748081140e101001d103808000c0003140822141c092250300c00d0040f11103900001c0c03080c01064480e541a440d86052100340300d00c0503584110360000c0a028080029520500304882c0940b800d10522081410320302442e4a00d400b03201c1440154203a8070151001013008007141c00140005405a0044418140081c40d04403204d90300d44502c0a605010b80d40500242d565200320505150010f0440c1c0041c15a640a000311a038503070001049141c0385c0f4000f9262145204140c0d010440600403512a2105600c0801141981d550620340d20b030131401 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 460091942 1250 460090692 460090711
    0x240603131505011401030525090801060503011b030e0a0c0b0403020108061009050f06040e1806070906090b030a0e0102070501060311010914280608091606050304030309020303090a0806 81
    0x14401208201800b6880c16640c207007452400b804035078001100241001001a032070034200080d4021209a0f582e00d00303000b140c06680c0e040480741000c0d0480c2c01c403074096000c14800da14102c210150780c0d0810180707880e0700c0c50604000416400c5200020308085020f24010b1014004000110b000b0701100d01400a5074002c0c1c5e02c1d400145d480c542030012407070700700c203c0e04042107102a0410003898141100d1103282c001412003803c0030390740d95022240c0c010070b9a082000c01c45400342e102091004000442d0302c40e00c185080840e003840c0c404040c1001d0003c1c01782602001000002810b0a402d94202c01103900014001315130740d400c14200300e40201a00d00003140c3e00d0425489040e81580720b80f402c00300750b5082c03540ba901d48410040c100101d01f803a0320401c0c0c58a15a501d8441c0000180b041850b004033000c0c0c640e520309150085419080c4054844a0091b40310502400e10000358842d003501e522035894100001c1c08049800000d01c0c1d4001c030f100c010342c8400d103080c4c04101401c1c0820036600810106 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 460093192 1250 460091942 460091963
    0x306050a020a12050603100207060905010c02121b032b1104150305130503070506010314030703050a030b15040909060e0105130f03030e06070519020c010824060313 72
    0xc1040c8160321905480d040010708840d59040150801d40c000341c2c02540007022504c0302600c0008180036600000c1c0140c4020383e031410701100740b10080c080c03401c0108581c4090304c0c00b000703a012290b40a000c1c0700b02d00650005580807160032075400b0006c5540c8800c1d040340c20b9400808ad0030036440301014510850700c00500704120745032202400410744050310403c000d00171001d200c46404074010080106a01c200310160300d84800032807810b000518045010310080d2081c0e60440c2410540d4044810303d01070290320801041011940c80800e45903668010302e004600501c069000520600308121503c5203400005400190a0a83e500071481503205108c14026040702011442c202d40085590443c84440400b00ca4009403d1380340c1c040405200341000552180400b80c0245000c0782141d20002180000509004140084000b105500228402030487d00079080009201100161070924501c11a40b401d1401c83e80402c0028007104028150030746a141400034811002e001c040141c0308817689 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 460094442 1250 460093192 460093201
    0x8100e0a0e0d03110a0c030201060b0f0406090e070504050d050c040f0b030706030204030209040813030f060b130203060307152003070c080712020f0a23010f0e0d15020c16030605 78
    0x13801118410f80000c08550300741008008103503286039035048200c04655803480c0c00700e0b50b0422107014210821013040c00545032400c101e0003500c0c00d42e040c0c1010490300e82070300402105603404000c0b41c040c1c030310a0344d0080d4000c41d1740c94043d140090452034207503c10f003040c400c80c07949280780d1b004084043c400c508035030680e80c1d2a0800c0c3d040303100c0d60002a40201e00b00d07000402040c0c0c1e40c8c00030400d10311074080260f83d1036545c2c0c48900040d4040d0000710f40e850389a20020b802440c001070018101c8000032411491400d10750002942c0c2e804c42d2084084c40b06441c02a060441d005041402c035012982036503400749030000e00c045849521480b012141d0140340f61010603099000204541a11506481303014141c445800304a1482e03006261142d1041c45a14041800c100d80b207800c8480f100c105a100d010810000009031200720038100910412840c415010540c0c2d907441511101143c1102140d0807403001588148042c0c40390000111080c41606100c0192520980100c0d080340d002c0d4000300550707100e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 460095692 1250 460094442 460094447
    0x4051e010f0834080703020312040e04020d02040f14010e09030f18031c0c2307060c15060308030f0912040504180b0c0c07050f01080708100e0a0e0d 65
    0x181c0d0007111180c0d807024902621580c00002c40c60182c0004000481030107411103072088010850f83c1000049400400c010011420100040c50780480c2250b0068109400c011031100380300c500a03c040d1003001030300001c50664485a100c5407401c84d00c89000d014594440e601072504480c2807141212481050740000c082440100035500e54503150b118251601c41e03101c1000540103568419243c1c54014203000840c282116107008441524544410f02d0302585424501e5140d4010180c1c3c0d46c01142c400e488000c1c51402180d60401d450840c00e19199107585420000c1507800500d20a00400b407512602105016420026511904440440101da9580e0725041d03911040c4558045228a0041c4010302151805402200e400364a00c0e40c8a022088a511640008842901c0382c0e02c46c1d2000082050303c107a011304c6500e001d4042694000d9108165000090111400030040c1080080400200e05090700d000a001c009100fa64034074612400c040100e0300081400c0c1101910700d1141031500d0700703010b0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 460096942 1250 460095692 460095719
    0x60f13120506160203040f0e0a200a0c030c0506070302120c04050904030503090a0501050c0d0f06150c050f0d0305070e04090308190e0304090c080601090b07150b04051e01 75
    0x307500001518641e200c0180b4060b070040501c0285044d400140808590411101c8600c001060700f035030392001174100017081c0700480b01c05079241d03540c0b0119004865881c01c04141210104902860b00b9450300311075040032200c02c0d0746580000e10a004001c203020b0502c2c4d040e0043c207041191304a00c100c09440320007450585102c0c0d4844c050708141e40400040c04240220003840e848601001a00c0791420665581c44c2151411612240400008980d122141c4a10700c10070040c00c000b41d104105c0581000c0d25541c0002401298004110b092140c4800b0043c1c00e10000c02c6005640e8116029104690b5018014100484440b0002110544a00740c0f03454207028181d0070580640f0394407640c0c1c90310068201014031040c080f0962646a100c4c0e50105041000240001c044403100004d450003800c1c80106807040190500d0304000e00d15406000c0e62600100b01c030141507100c01c161a4082c0c5540d64400035100005030030354403034904010846904518000108070090000a0603116030303d030b007001565813 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 460098192 1250 460096942 460096979
    0x9010e011a0d090813080c0109060909020a1b0326040206180f0d0302061806012d091802030c090705121005030f07090c0825090302060f13 61
    0x18040480c2149290508024650304800d010b02258429042e11050380a0380075030f00c0801e41009064003040f40b108244420660041c0900e410640c50f4603202c0c1c011f102464a0149215050707002820800c65405000341e0754103e55002c0c501c06018000381409070528110031050400c009605102081c0f001c0d2aa0820344038642c001c009600723060900040e58584004c10030f803944c210300c41d40240b419560380e40c8282e42405202e80e004001924081c2c8140c800c0c02c48264072004c06902c61001448004005880341100c45030802d1070480150741006540c1c001005036122030f410f286041c01c903445600b40705000845d80c5000354101c07610070400c00c050105103801101c6060000c1d01c240440c401030540c0c4115103400588400c201c3c2d9585440d480040d041c00040c098501c02940b121100f00900070b5035001d5a2690012402d01d20103070b15015441c0740303c41480840000e15441140701d5816058002d031225806150080c0400343c03125070520505c00b2550116240d0701041101e00000960303469200400d0305503 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 460099442 1250 460098192 460098209
    0x20d0c08040324052d0114060a0c060212010305011a090c0d020c0106080d2a06020705100c020d0e061e160f0609030f0c050a0b07051e03040209010e01 66
    0x9051454443d440050300040c00c0c2d203000682c0800c9140488218001c25002e50079103840d0160b116450300243d021403070744441e03d42074180180010003e501c4002041241300b0f41c1034400503601c0b0700c80392040399403400d0f45800030041480802d10b1070340900181000c80c140c1e842030000300895201000340c0a290070100008075072015000b00014110080103000c0c002402000c00058100407405240343d080d03801e5500200459800b1307510181165600c4103a032401c22044084065803800360340d00f8440c001014901c00344c0b00f6500000c1441c01c11030100a094006100b845040210410302e4400030344800ca140050340001d8200d01c500ca105241040440e10100c1075a0700200d40420420b01c00f0f10990051080681041003048900010070903001704485440d1007403000003220b42c0c141c540904a43c03461280041080740d2401400d0014030001485010725410610400869550010171640c0f485012580e0b408105043c8803920b0350034140010314012403003214003e103941c0c2c80d04060740450000744250480d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 460100692 1250 460099442 460099447
    0x20a05060a2a0b091c0f0c060603110a05100f03150801240b040806220203060712140906040f170c070807060806210114090a05010e062a09040504030f020d0c08 70
    0x10000e026081c4464980c0c03580c1000040d00c016508c40e1012a002e95005a48011070816040290700e000350b8800701910003210301078600c0041101c010990113250b42007034249552110185c0038078241030600030003028010000d101d840ea101c41400c884820076101c0128500d14844003081e600503142c00d503020344203504000e120998920310407510030140d0031701d20000c2c80801080400942c60030300403248202915203d042d0001070203695103040301c10301804409040303c1030081c00109440400d50701c0e0401e8025600c0413082c030a50a2040480c942000d80410481c40010740b840c0e4024041511011156480156505d00c1d544400c02e0703c4810049585135444052500d10a680300240d6010074243c488007000003a10380c0c00481d43d05600740b0152a000c0c0d640d0b0004c030328a01040b00c01d001e140c26034032640c4040c2c00c0324100f92800100100000c0d00e81a951004101d80c0d407590320741c01040e502c495100900500560900d800c0180c01c52601064a900602403c0c8450141c0c500502c1001c0106610204452 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 460101942 1250 460100692 460100743
    0xe0307080a02012105070914030606280503030d0f0501090903050f0c010209031e0f0a0b01050f0418030c05150106022a0301060b0a0219020a05060a2a0b09 68
    0x50302c407403072010204c0d603142181594410140461241c144a01c007507840301c000c550704042d4044035242350018451700c6580044104905c41c0c036031100c0e0381031000d100d641340d00c0401519aa040300c404010f40060760188000b1032503c0104142c2d4012124480d14610108102d1740c992861500391002c503100540400c1080203031041c0c02d0030200080c1151201c03080010f080038601c100203410140300e054222059980d2001884400f1828400c102d0341031400402040c100303803181d440d4184401c051040c075108603031182c94a1007c2c1c0700c540001651803a5840c8002c443d00143c5000707411ba00c00410203031424800d00e0a0742030207000300040d481c1aa0041e170010070744803c00d095454100c00c00d00c000c0e07a084541012842c011a00d0900072000a08100500c0d2074813282903c01c000c1c5041c80507403940040d50b071004003110150301c1300e6038604281d84d010748000c0c2d5180fa44010070307104841c60a01c05240303e00384011030030482c26082041303890b4500c100c110101c984c4030a546590742e5a070510010f8140081507492a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 460103192 1250 460101942 460101947
    0x10902030a1103030c1c030c0f0e0f0a0e01230904110904031b060501030302100204060c02090601091208091003020a1b0309090e0708060c0c06041506090906020a0e0307080a0201 78
    0xb015640041c200d904c1c0138007903a9154100f02d148a54210304100340d900d0912115014000d4004525883c508860070b507032040c0005007400c000300c21090280c0c80303c544150058039000d05c030714040c01d90101040080e503075418101030301c000c10301c41120403842101c0102040749010f418060040360841c00010501d58004100320229101600403810301010124150750502c0302410504a00d00440c0001425855414003a00745102c40703051034102807041105121080e0004040d0381169019600c6400e503035a1900140c0b142d000d5500b069881080001c110010007040c0c00084c202c007002981c080d07150342c000890941c1a4081c0395011030102c1e6003080c00041100e8000402d03c0e81500914100b008965180d5501085515100c0149829006a00c0c14005808108091900b00c1010401d8a10b00450107032410346035400944010107001c1c04490954442e80d882e0800c03806400b524030104200c024030324164000303600130624500455144240280d0034640464042c04440c904006031800b10202d5004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 460104442 1250 460103192 460103213
    0x20607110a020d05030909090106081509010209041509150b09100201092a08030306300d050306010215060913060f05011d0109060803040e04052e0b03010902030a 71
    0x1a4428410741c814800981c0d0396040700c15606000c4e1000e180e40720085401e0200c800c0004201004c0c0b0b80c14090308102c095000201c50701c40b900e4401242000d52640205140a48507611000780e009082011031907002405025110413105410800c2103804403c403898003e205140c4207400d411307102445080365a00304449820400c2d9810300c0002580b240300c2c0d40780041a0414107551141036481c0142c40e50241c0002c00d80405004c110000b075023145009400240d07020138044401c40f49950051200b4904030260040d04050300b410007d80e606030f103404034000c1c0142c20890b603d40c01482a24401c40f4000c002d4800d090041201902100c890394402c0c0c0c0329103210320b280d02e04403a42661120950300c1c1c50031034495036000c0e22051890112070902114414900030043e040f8a1106144c00410050b040c000402c90302110080c1c880201281c1d01d6007862410001002412142d00304018038404805500a07000d4129145a41e410030030903040c1c00a02d0f00300e5078144402501a4402d482e42d10108401116 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 460105692 1250 460104442 460104467
    0x21070603110d05150f0d05030d0c02070b0706050f0a0504030e0105030705040b120901140f040b0403090e100905070203040f1806080a030305070f08061e0103061d1503010c020607 78
    0x184030340b616922a150030115141212044115001140c01001c0c51526444c0c08078010401c41d4400180312060710b074962a407003600404003805540b4000908968000d008071001131070ba260469031039410074188000036110458503164007441c080c001902611440c0b2910707000e05e4066803402840450400191507030362002d818182030003c1840002004000341008000d1035441500340d4041c6e04218007018203441c0f6004080c00504103200410201117400d565443d4855001942c40505403620b060a48130a041a0400c604040f0a10108901003511101c08001c4550100d020002c0d5990320400720388a0007503004924180c05042001c04c1401c04041d140740848140074030004000e69640003083c40c0c082820400c07030100f6152400c215240380c04c030300784c100ca107032560400e140c05260240010300b040c042000b0f41e44500000c070341d6270b450036403180e441000908840d11b50629502d04581c28200c440c06c08407041840c003884030926145900f01802914220482e41d00103001e00c6d200c1c19019501505041c030f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 460106942 1250 460105692 460105721
    0x3003020f010c110339010e060c0a1b03050f1801020708030a1d03071716050d0c0303030c021002041d1b041a070204060f0501030f2a05070f03050921070603 68
    0x89005401102d80e4500c0d41004010b00010721107c3c18280203080900003402034076111401d000ca4418213811480900c0ba4a480941034201011545025919030041c032007400e800342c1010030029220012503003d9600320300c00b41c080301c010580c0e44480c0c0b41d0707902c50700c07240c0b40c0000d940b01c262103030004110343da550310444001c003070360907031030f00c4217060b04200c0b201e2410044182c0c4400420f9a09505003c09440035150980ea00990064661607918444001d48270050802d41d5500f2241d00b45882440302c003c20000840c4c040d5030b00e5035910980a900d9a0074042600d0b0608504042503c00c076410307001d40000041c4900c0d0030b042914202246124810089900d604a5020805000140d9a5200e010007410007030740d03176102e0241030400040444100b07401c0100340782c1c03900310190709991103110642d40070003030708414000000a240342100d150046601c0202841040b50103001056048406096061001e58040041d51100d02403440d820b40350317080c1e040054020200074402d8500c01d0b00414024491030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 460108192 1250 460106942 460107007
    0x40506040501052b021203030103120906020c0d060b12030a030c020f06040212070e010b300c090607060e0105010806070804120f050f160606050301153003020f010c1103 74
    0x50b00869140b8a06c03501c5015590000801403007000228200740f042c020180c0383c0240010b04044000e903440480050007031052044882d22001c0001c40e400c9400040d0300036041680a40c040b0040980c1c941090840d500460306110010000ca440065407941240d114030061103980c490350280022070882c16803c81c50f5000b25000860911000380ca0136000740040c41005580e00c0411a0601c2c1c400c4940400b403942030100c650381f000348038900801c150082d581d101c11a9032000c42e500000c07964811031030024541801d14034031155405041d07101c24102c641d1481035994a0ba280401140c00714030482d0010000140c4001000040c1d109c0c0060720591021410000d1915002c40020b158a4006448080f07c01e4401c0d0550020001e045c01840010441a0000e024130980d00309080310094582c0602480c03e0f4180c444a40c05064005448107030b4654002d4440007204181802501e4a003071035035500240d800c003024098070602c540c032084013007030181c006981092444a8404c1100281c18503440b041c3c40e0302c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 460109442 1250 460108192 460108279
    0xa0c06020903190803071706090f10050d03020102071e08030705030a1104030f030f0207081e010204050a0b1e030415020a02070f0f170f030406180902031504050604050105 75
    0x101c3c042903c0680a01412070312031601c4000100014440410100c60380600d00a11480303440e459175a1344c00140316480c260907076072121101a4a052964442540030904101134800e264066009200d043e02800364030754026440300d00050498200003004180c80000c20010799214424009150004403e04000c00c0d1604048180a6180c100d03410940d41c0740d404040890030560810701408940846001078507038640703840c080584a0394030850700c41018035036030a800990102035040301d001d020000c111408a54880003c11000d4200c110b102c2c44500d004a03244280341120702c15a803140740d0000858100030010b02618019410801204c0154400c6640c0890914104401c090242040c440e22142140c50700c441c80c12045200c8003225000d4008003062245c265000c0112415140345040048480e0843d04c0c01001c620311035440200b44510220901c0b181041e0415000202501124148182c0c0c40301070401040315070a104050f880f508030741c8429610400c0c041ca02c1040c585500da0240404c02c07 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 460110692 1250 460109442 460109473
    0xa11100e0a0b0c0c1f0c021f03050f0c3906070e01020c120c060703050f19090b0a08011703070c120b10060c0818030a050a0510020a0c06020903 63
    0x480d081080d401c0310104001c80160003c000c2d41300101e030216522881d401d5200f030314510b20311148201e5400c00080084040954960030400203a144d05d140e0215800700090710001d00a01741920500038141e0202c012071007140f00c403820f4075083c0c44130600d010405650076115038242c140b4100c094000e40c0c4038401c2462400b00500c5001c1c803030042511005410b00381c11000900706140300d80d000348101c0d80640c619132114000100d0f203460f460181d94160390340302c4504055440b070040200c0c000c24804c0c005100109070002442d04a2030002d03e465444102c0d49900100c00507020b403600c2d80c4005660280100312010405c1d1059070040d01c1d04086c3c3c0c1c5826050344415580100c4c41e000444d15240041b80341c0100300c1d8000c0c07100c1d80100f1082d5184811400e0480003004c807106c2041c090004d49003c0742c0c64203040400c614a16040d40010221000c01085151158079150161010354081c00ac005000340c80d990180210781c4e21200540d1104c842e110940c0c0c41e0b400035008802110781510032294007465000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 460111942 1250 460110692 460110709
    0x5061f030819021e060609040f020306070f09050a06020607030f180c0524030c0708210a0f020c071a040e07320a0e03010b03100c0806030a11100e 64
    0x5080c80c038040689810b000c0c0a03140208082d5203107a080c0c0009400b41c0302c0d0201150241d00031b01c0403600f42549032181e04004039184d44490019506001d4903080c440c00703540203481050b04003410b8990814456a0384208030490740144640c001580044000a41c0d55202e540019280c0c0010500054800e402c41100b455000b4442c90840c0c050010002c140158a0110b003030308640c00303400041440302c2800d980c40074030900001c1c2c200e0010840c00300c0d01c1403c211520082e00d6402469030004445a040394aa018041c072040d03e07186c00440c5024082c0790b040030103000316084200450010440145000300070b410015550030004038400d0244004200310742100d541a0007001c01b5034540480320011202c09000981d201e034180d203490a00e245000020f082141661482c107080e00709158850704003000301e40909020304c0c0f11945409a85043c401c401070a500044a2000d1503032020101d40e6803801703040e07030740740542c9014004c200744440260301c5280001143c2209102d61426038124400710021034a0359 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 460113192 1250 460111942 460111957
    0xe0904022d130c050a1b05150403030b0d0201020d2d020309010f02030901170c070501050403030e0d090807090e12070c050906060726090618010906090305061f0308 72
    0x20305605444440318505900c010412082040040001e0f40740002c0140c11031181d19031071000d005680c0041e5603a00d40c1c4440440e5401d4008042d40d403420651088465a1321046a044000c00d00d0207842e0325080c10442090740001c1d070306800074082e0512280d0305a500c5010305030740104501d003440079000c0c484403110103103280ea002c64004648401d80e240001d003003500301e20070702e40840d8001c0c040840140e900005040b60541d8240c0c84000640b01e6140c1d0340001c1c8503a240c007030529800c2400348000c0685c50342c030090032a0921401e40d210484101012100b0b101680310305031859010160a00c1030344040d17800014031030100c5c002c8a0a8621050388000300b6082000d0a482082d0b148004000c03600700407401a501075801c8610901c1c00300240d582c030f90707544a00c140c1000c0c0c3c01c05013084414080e02d21000c03191043e400900d00e0740c80700c00c40080320107400042c0703d0032800104688000900350340034102c1503040e40c2c1d01c0800380800d5960000c40d8a000e80401500d40401e940c071003000030224030604010030340c4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 460114442 1250 460113192 460113259
    0x90b131a210a180c0e010b030415020f0403081309060f05010c0b06032407020106060e100f11070f050a0e0c1902071a03070315140f06131d010e070e090402 68
    0x1c2c911700728680343c200324142d000000100d000c20402c000144590040b01e0030040318200181c80d1024465401c1c81c0b4052078100030411003001a000003240e850034004c80443e2203200060100c030303464203178003007840c1d20318498240480d00300680500014204882190b2181c2e0150172a44c1c0203c2401c04001404602c0409000041d451014440c1c03031503080c01600040e16541c14202c0780b0303410040108071042040400002004102d55020300518490401007112800c2001120361894a8501044101000d8400e4074859034080c3d000041012144282340c0c41019030b080e810782007414041050f2541440e4454001c11405018404a8070703041c6a40801020041100441e0f220b103401c800c040c04407001100007a02c03c2401080c20042290000e803142c05c852401d0310001e004400c448041803085c02095007c0c0d0710010002404036655001c003901c0c401160341c1c0d114a07110344e40e1303520001444000036581500020300b481c4400e1201d00b8158149600503102a008601e4a40e0340500180c00c441300c2c580c0c1052 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 460115692 1250 460114442 460114463
    0x60209150a0f0306030201081609030c06020f0c0907080402061b06010323060610230c0d1706060d0506010e13020a0f0203030f01060f090b131a210a18 66
    0x1107142d402600c00d200300c0c0306030508101032411600040c10308407000b058040481840c2e888010540d2150300c1d840001c40d0710414800b203007519482d02035150289583d40c580c80e031180c008100294607080b42494011011030310b460055840720380074440325900c9550024bc0c114410450910302e14030811500780214090b440645002209008100c03440040301e11101036644204244580c540d51580c4003107541c0344a090080800c501c505440b4503070024111100000301000c14400d0700041d0105501000302c50680d10f40554445014a40c040749030156451a004034080c0509a10300100340d00850300240d050406140e484003080000c0c903074655071890307402110380106030414140d403c83e00034084803106001560030340c0b510001c2c03c41c0e554014030400c2d04006403d000c041c0e03010b0185e000c2c03e0251210021140c1e8907071115103205e41d48540d0344200000b18240a0001c9048010314068801c4d6011076030241d80701d24900c250340003c070030018284000705682e480f000c00c076540482c81c1c1c00898900c114a84075 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 460116942 1250 460115692 460115707
    0x209011407110105030a150305030d0522170405031b0f040c021002030a0b120d0f0509030319051c1d15180703020901181a0a0e0406020915 61
    0x5211945944000341898801c0c01040c001500d60582403684030000c1c07a10584a959100c0c07040060580c40075202c54058a1440100c10b00c90040f0003030114910380c1e442400640c660004440403035030f0140142c00f17015180303410000011080140b07a4949842c60080350704041d2502c0000e130070689800300070650b10f84800000719090400144600003d6001c503410040e540d491203002e0b407140c01c0c801c500e8003441e6000001900103056a80b0050310040080d0000a0000d99058426911000024850007140d4041c0d48030b11030b20302c05c3c411034070240c3d8060007841c00c060b0011401400d6031944108401808014002c00114061000c40803080701003500b03000c66400b4102d03c860807203880f40a01c10300e1517000051078080316150031142c0c0f80c00040d81840c91114400116066051140d203030802940311035628000200e0311800d254040314486006010031403208410f440c6681407900c40b181c1a003003c0b11a6040002c1d2144100d82ea52040c0544005803030400c6250009004043c6206020705902c1c0209148 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 460118192 1250 460116942 460116947
    0xd05010e0717060307030f0f23070905130209091203070c0b10050a1e030503130e1315020c030405130504030207090b0a0504020a030e0a0524010e06040903050c0709020901 75
    0x740d0808030280ba42c240700e4100344000c00d48407070721400050450a01c09503c48100403100740061038090700b142c07441d5402032991444075480718012201e0541489101d47c0814803101501c54540101c103480c02807210525542e0030b01960420040405c0020b00440d803002440018900c0107500c07c420595501500c1b001c640b0b0034002c2c2140207005c18444010200040c007251300c0d42c5a2034000c4c4d86a4029015042900c1086000300e803002e508028101e000200c2e906124080e035070301260581d58003000d1158140d031482030421007100340f882c0280042c1c0c02c7c81810b0043d0200381c0e008105031514a4107591174140c81c1c101050110070420000300c42c031a514810407003031603414080140a400510002e12108101c60001880d4201c9801124450355000540031003003402035001c40401c0032a2401d0382c501714024104541c550b491420000003041c28a190341809804e5a54100c0c10b03a24180803484103502c03020180300081400080c00c030b040c04400c2080311011801000a01c00829182d04c003d41c0e90300c00740000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 460119442 1250 460118192 460118207
    0x40f06090c033f0c0f0c0303031b08060d020108060406080601290a090e0a090609051c170109090804030503031503210a0309061d060f060603040c0b0c030d05010e07 72
    0x180100601c41001c4401c01c40103c02e1039504095480c070f000e0400700c0150410020b03450a100b0010510f11242200200309609030300101d610502e078820b103c00150f00d100055843c1b80b4200d0301d00d6400121209007000542c09051856080724010300b0000d0456159007a182c0742104c2030700314040d000000341c40000002c440042c0301c0c480c10f2151080703c0c00c004448001409c554494000e10680e003000c0c80c00640240000d03409044070942151040c13080f90064180a0f8581e40c0420a203820070049042d14140329008045500210300044890141a0318280c0b00b000142544103040310082000c000000102c0c1040002d14016280c4507011070003c00d00c03a081510b409a031100300c5000812840c50100d6662008058841c0741a603401e0200e980500d600d031103402800c00d05c80486a00348207902c0d05801010001d40580700d00710034606602c60792505810400b05000c102e5000b4002c4a00440601c800014140640022504c40c0b00b2a41842070040070f07803007501d5090300004154401e040030400344580c003208 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 460120692 1250 460119442 460119503
    0x102041a07051b10051809070f02160b0d020c0705031608010e1c0f0e100905041404050304060c06090f060e190b060f06040803030c121608040f06090c03 67
    0x400c581d0f440010000b2408682039501c95005000c00070804c154406242519912a294000c20104035032824804c041c2080303100b043c1c0440144210350103813418002e5011548180d401c48401e00d4100030b8909100c80103940100350314a02409010780008294500704141c681d01c2035104d01c402c1e01c0c1c40c2041206801c54098210f00d03ca50392041c28403e003a031203181108000d1182038a0800400c0034904000c1d510f1808021040790495407081c00307500290b6101242c0810340d01d080300c051104160301d1101c21040030050728040c0858200700010000d69005000718900207205078004a07501803603440341400c008201070306685580c0c03205041c101c08101441030400c0700709440180340c1240340b192507212480c0c4004002c103004203407102e01c0d2103859449009481c0140401d0003265034a1411062001541d08001c4091ba0407654142c0400d1b0b440b54001c9038400200250b94588801e507466031180e40380456024410b40d0000c0d546c0c00c8030404903400c1800880614040e4248443d0700e020803e000c0d90207601c165 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 460121942 1250 460120692 460120723
    0x14060909010c0c060c031b0503010602070b0c1b1302130e01080102030f01060e010207090e070e01050303160305070c0806040b2707050d0602120a0501030c050604060e010804050102041a0705 83
    0x75000c58541d0b0700201d0406003d41c10520015481d130846030190010440480f41c0616480041e04a0740103d61001c01981611019800d80d80c40aa4940c4001c43c01d02500070b40d030a4642000310050030003240ba900f102d400e000020300740d508807007200112804aa0001134820030071030602100780000c2515a00310f600511400c0001c40c518509452450310b103000c180035800401c02012919403d030f80c42000000e0203003094220801c89080f42d84c1c81c03c4e81d65010740c0315540c90584000000580d0386800302c2070340e043d0b500040030030900700004c0e07500310b0f2281d0282c02c0844071407540040105402030b00b007100ca40716a00c550822642400c0014014001503281c9a100340e90200350f000c40aa4034102044610444400f6120782843e41070300e2800300080e0080c038442c030522207254410072000d01281e401c9181200d000c5c2c00d40c1b0715040c1c0c482003440503034841d43c040d01010640d12524400a07511802135243d01c50700480c0010704294541c4499003449000f842c03803445084003c00c9402c10320000b1302007a5802c41c0c809 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 460123192 1250 460121942 460121951
    0xa060806010c0b060f120a060c0c02060d0e0307060f330b0306030a02060c160509071418100c02040b040501031a04031101090309080d030e031c0207061406090901 71
    0x50000308071190700b000042410420740c012422a40b655001c0e0308080c41c4c01810414640710a81401e0350381c400c4002e098502d1030a1144041c00c46004000701043c854006d0200c9240204103001c1070301406007141d042846103c03c02c1808041035291003900200d119041002c60700141048880181000da5450401481d802e0105824000400d44660080340d0b5000d48081d00c80d510200001d00b412450000650826000240311624001c040760f04242d031403000314a401d1840e20344040c40500030381226000c0c02b049500c4440e400051400b070282094000241c025640e41d4801004a5128101c0300d03070400110b001c191024045180a0080120860051f102040a0340c90740d00c2c1c10f9042003103129098113011a40c4042014140300f0b200c0411040e9066009100f00ca0302494000c0c08440903200754141401204440c18005201c0d008120300c10105400860604a4108190402443d040f00d4140b25950800c10100015901c0c060322281122a401c450010319207181840064a402001503241d41d140 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 460124442 1250 460123192 460123201
    0x5151608070305010b180303040f0b090a120f060e0a0204060605031801090b01030209070507050f0d0e061201060e030307050105190e12031f0509040b0a060830041502010b0a0608 78
    0x402040c0e40c4e01c1b1050f082c280001000302c3c40442d040d88a5074001d103a0b102c46c64034020400100c42c100a00340701c00180c611042e420360ba03072940460000c8016008141840c40d08c0003501091098124120805011050341c3c400240c07540000c046403450f134003250100e1004000c00030511986008003070440d02003c0240418080c0382d80300d40e0b040005001c001c1c4112495408981541d1041d4182d42030150b0060860700d190043e8100a84d80f80e0f800c2000000050340c2200c40d010380c1c1410010344140c1c03840920502a00e03420000e003a01d500410190094040c4014488140454030074042d15000e004215201c2030717604a007a02c0b040a44030910061401030f400021340c814000c08250460303034028003150200c58410040c2d403a80c012007100703600080d40b00908000303020a0100c4480fa0714000d0442c804100401541c85070000d40320041c2c41140e04800000301e0300e5494000c559003503080201c20402c641c40c5040d4070751101003101c2e0310a505910040c0c4d0358025508150a0018283c1c000c1d05a908040851703282 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 460125692 1250 460124442 460124459
    0x110a0507120e03030f040306050c040b0702130e150411030607120f090212010c03050906010803120613060b041a09090109020c07050915131b05070515160807030501 72
    0x21000e009100e0400701e00501403072442107041101c0d00074028240c0b5600c0c0711488048405800c10701056072100c0c600130105007500d81c081c00300c0381292403940300c0e141020555001c100d8001c00704e4042a01913a1109444003c40a0a01c84603c0380c0d103611002c0d607020f00f1300781803080b54404ca038640540a42d20031400c4c0048107811001d5581002d42541001c2460300c002480c0348040e09000600a41000d50021404c422041c1034211000c41c4c61513076030400a03651241c507000d070340e000203214140958100704044202d43c8580c8200962124010300400d06c8141c054986030101c40180d03102e400e0112001c10203100210082d0600304450194007140d034180420b00c0d001580f411010300c0380e501d26035400603017a904a1000d0082c50010b1800420381c02d0207203000c51034000c0d0b011501c040303648504440c0b151080041814441c502246251051110041101043c159040c1d40a40307000e032020701c1141c829401544042c3c4000d441140480d11940c0190011400581151405007961060505201c01845101d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 460126942 1250 460125692 460125697
    0x50f1608060406051f111b1c0c15020d0c0c0b0a0302040f060306031203230405210d0606030e03160c030501060810050702060402240f1b0705010c1104020711090708040501110a05 78
    0x10400c44440c86800180440d0801801384450014270103144200001420680c0c40c020b48040c000703e800380d07486045091421504080c400c0790080206c03501d21420f1141c02c40790400b43c501c0c1502030400525090f102d130761075884001c40c1e0703014000103a103036003040c010012843c022141090590809010b03030446051111800300d00c8601e44074003802035000190500c50100184a005100c0c0c03e00c40206003402c15244000d9400308880c01c456605100c070024115210f40700360601e42e0315400245080c49420034070801100d4a0300c40546101c0d01c19031010000c07540a20464000704171000040807100c01c908140c0e0b00351440203000d8025904040200700140c0c8a940c0070742e8080c0c0e41218448010102078094903001d010301c8843d03003038082000c14858800007854080c64482c0c1000d104a94106655100444041901010081c190b48111240c0d0380e041c10310350003030802e482c49070859075011602000400e6018808803140700000314118280300500c10284954080c0b581c0002c61240380a504150182452 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 460128192 1250 460126942 460126993
    0x50c0d080d0b0d0b04030305100609061205071806080709050d02030c01030e01020d2c010b13020a03020409020f0d05010b0421050a0506090a06050f1608060406051f11 73
    0x40d00c0b40c036800d80340e6451030000407805600c400a00e5913400c0508004004050481c0d00520350309050401140b00c0e40101001021030b01c0b6983c401d18081d0010900002600d0050081c40501204401510100a81d400d008001e0615643c42644a140c1401d000b0b01400a40c0e0059000e003880c2031041d0003503200070805287c101000e080c081040d03404019000d0083c440e40e2a90300100e450714640c80c0403140e8040b0384800b69514841a07031001051072540e14221000304040300d07806080c00480c8142c20120340c01411281c1c88909005007016950050700090364400000b86040900001e942e400749507031840303028090400580c00600b0700341080e0182103105104200039408942c1007504e5000c10004112280515a01c001521310b2410840d05c2e4540d1940d003141c003165610304150010701480d5201000d14440c01022403500e0006480c0242a105090098546500709489940c0440c4603150310300d242c0d42c0184d12054840c1c000e02543c034020689208070007981c0558114841940300d84001c7d40040705407 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 460129442 1250 460128192 460128217
    0x112812020a2606010609050906040b090f0712060f060314060109060318020303040915060e0603070309030e0907120f02090d230609151609090e010e0a050a050c0d08 72
    0x200c1e040c0b080072040962040c0209038103106900002c10a50390005051044820684924105440b1441084207032200e4070720942d005940000021504804420780d10340044850a0039450580c200a0080581e00c15030001c8a8142d018081005150340c144102c110890032020724400604052000030120120740c0300c0c1204040e2504104040328842404e01001c00354001e088a54550b0713a240603d016002030310764002e40342294440020010f0084400480500b0003d111074919174608500390004e2810380410f4040081c00c95011401d0340f40c1102890142210b0744a60100300c00d0708403031074142c0f2400750100060790b0040c005148075448925040c860503a2103654000003424818285080c100c0300c401c00d40c840e06c00c01007407203c01d00000c10003c2080d54100c51004880d0b5404d501d00d0202d01d0014109400900000410030036199a075100e01000d60307806d000402e40c103407503000c103618100d080e180aa80380d4001220440400504020000e8400000d58240d100b00042c0e444442c0e45018407440e80d1003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 460130692 1250 460129442 460129469
    0xb0717090606060f130306090c1e050913060513121d040914150f07080105060d0902031609020d05090705030a0b07090504050414010501060201050c040909112812020a 73
    0xb54030740e40050b11200403020313a6002017599241041c1c8054140038105031001c10131284041140400c02c0900001e020399001a0512107140c0b1081c0500d01000615490311108810742100006595008941c0034405507003030480d560445d0b040c15054003419242a006006030401c20900c40e0b036404403541c5034090100e500041061a034148220512280c0c241000c039406040840c400c01201140030b9401034403404142c0c1059600e911040e103580a0a0088a81c00380c0b06100e81c030790940c1103811886450340f010b0260354070342e02c0440c02c40d010060720381c004501d8640c000c41d20841c0b001862003201d80c003e114000518245140201180e04c8008029020b401c01c0000400540411301411180006002c0a07000300840d00d020709000084000c0c1074001c0c2d40d154200400003840303a01c140140360207030400d039081a2505240014034001444000d104070b40703052a00040200755036882c446001d140d4101d00d40c40d4040da666810700400c0034050303000f070100d0fa6101e000b04800760b203a410000d801d841d1724960522 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 460131942 1250 460130692 460130707
    0x15020406170907031208070e090402150d0e0d030c0327080a05041203030605010e010206010f05130f0c0305060909030304150f020702031b01030b0402041206090f050a0b071709060606 80
    0x3e04204480c0c0000d0499600d44c42130040065010072528415000c0340d440e80c100850721002c00507600300c2076902940c883e1190030700c2c030090b400d8a00200040c14400d800010149480506282000d0160080700003003076558222814030780d01400b075140503c034100107001c0458229803d0000758000307107201502010b00030130482c503200d000b40111806042d0402d03c1c8080e0540030315001f4041c000d18054180003a0300e8010049013540005440c0303050b90000711a02c14034034181b50600074003000304080c200550391661090340f100e04c11803044450310000c542e40440c40340382c12800d1101e0400040e02000c0941d00070410000810f00c00c400300628419801008258095918050300281c0194034010f0f5050150b5802c0804903480c406060601c40020b032002c1c024503000000b04002c9020b5445a2684180c1d0b8a8900303000420503444104194483c5885048040141c1c40e45450030042e62801c885130b01500302031111154000741219983d500405a680107840d024910f680c5400c409003502e4003030a008500302303 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 460133192 1250 460131942 460131961
    0x3011505070b09070312030b1f05040b1204060612080a081e190c090302211e01091104050903090d050c15090f0303040f061b0c06020a1502040617 64
    0x1c1d00c0781038020010b01c078142000490140c035204e242c44211015000c6849040c03980c6d0082c0030f07400407290001e00e10401100080b28032601144045803040030400104004541800b21a02821002490902260b09460b191602c54100c80d0f00743c1101c0040e0107440000300004020030b00320340d0030380e10382d203070042560f112100300007190002c0d44240744102c8000380070400302124901c0d001100790b625001c10700a584403180700740d46c005128000a504424440c038081c40903044c4100400c2e0000c2e1003030031940301001c049a05440354500800c212070a94540345900d0522451a802511400c2c088400f041107090400320300e6581c0c032036100014007a4056010000c1403080078001282c603044003a000e003844040c0030144024581c082ca480b00d01c00c605412914026080c000107a8056640c1000c2d00b003d21400c050054a04e20510145008030907492020705000804106490000380100d40051407903c01e1440d00310408204950007546081c03060008000751584160101e20020b074403171074240c1c2c540340c80146 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 460134442 1250 460133192 460133197
    0x3090d031b110c090c03091c090302040908040b07050709050105062106010210020c0c0910060207170f0703150507140f0c160e0106020609070305030910110d0f0e0405040803011505 79
    0x10f03075600a90000410161031030781001144a00350001c20f07204030b410141c040421401042d2000400a2803c910600050800327601501c1d08601614506e0700f0580e943d4070000e07072940700c9542141c240e04560130401485c9164061a40504000c80c0c140341060084804803020076030001807a51180706090120700035034002e1001d0300d0402c1d050761044d0f50350401100569540c034043c0010754020746418000074203201681c6000c4060744d40950103005460f02d0205c0807111460114070700c80103400b60345240d88501e0005c201c0c00b8015031085004003042140e0f1014441103c0004205000b030084601d0320902110001080300d141c2810180100c1c1c58080d134208051a00340002507510b9a8080000302084080f0a01d044504032412942141d105aa5020820313444190b1440010aa070380b0511002c0301178544604070115540b1203181a80742c2c050444011440c01d01200d005d0001b2541214074160a141d010400c1c40303120710240e805000c9410180e69010041c4414410458a9080c02c0d4004203160311400c00c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 460135692 1250 460134442 460134463
    0x36100c0c0506070e030c032404031b120e09090705012106030818060c0d0e12010c090602010b03150105040207061d070905060d02010836010203090d031b11 68
    0x120b0304540307040743c0c0191040948a5499220384600f8900d41038901d000503940d1342054440794030f012680c140404c0d00c264800d01170021002d00c0030800014000d28810a404c401c40f07030044c061001940040c0c00054500d2030340742d1080340070340071000800c0f10580300012a0012036070203103031021030074014807100e50058a0fa1186184800c0c107103070001080c0040b0b18068084081c0000100240c44070329420400548036128000126420001c107503c41070f402090340104031840980703060b01c442070a0b103140342180c035a000d0990100c0c06268040c03140035824840c00c2002e15082c0c0003422880442c0500c0c4448504c14401c0a204580003c2c520741002140e801180406400c0002c059203c002c1c1c1210391f80301c600f10f00840054514203000243d507440c0c0080403000060301a140c005003134503400001130901442e081219200e150307084240c2085100c800e40001012220400184c60703082004080d4200b4030405029010141043c400c0d84000d0100c1d080b4000d01c04141c24961403081c1200080380c2003c00e141d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 460136942 1250 460135692 460135703
    0x10b030111090a0b120a0b010e0907030c020c090c1c060536060d020105071a1006110a0b0601110c0406180f0c1b0501060e36100c0c 58
    0x551120751a0401d00140c40042411030300214190346913888214103019121502c1112070003403021070407900700c95010104643d01850110901030050000c145c15040542d500790001380d98180a440580d4103000c10078401404541401182c01c01e15201d000d00e01171010524108216107080300d02600311980b065000b040c025002c8000c0e100c114148010400c1407910502c80f801e106140040107200191035507220f1f10009003d49038031180354004441300e40000b070b030456921420070600b007104074260407010700c9111800d00c207501d00c908003030b4000c0441042d1801030040d0351100004800259424100c230740c0c01002840e0110002d41400c60340c42c902a4001c0402760007520707050780494080e2440f4030050b110300c4481c100340300e00314031070440c2011110303c402410300040524000001c1100c0400c01300030078034041c0d400400c0c01c0741c030303078000446991040d90740049040e01c3c07400c035420801c0301d01140000d0300300c082400d0210004107542e0903100d50b042d182c203908441d40c0d0180c1d00582c03030044400361441900701 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 460138192 1250 460136942 460136951
    0x20c0106080a030903050d050c0a08070510110a0f0314060f06070c03030906030509030c0d140c0f060402030c120601120804080d080105040612050a0b06060c030f22030221010b0301 79
    0xf820082c10202550006545038080c0a0740450414081c0044440403c00900201200b6410381c441e20303003507040348000300da5a0217140c1d000d105c1805140610006000c007030b802c00380d680100c213001500440c058000c9005060414113032520040e4950070065001d0030944000d0f8109912a001550f035219000340106034114902c2c000c810306610000c4042501c245440030000342e16421090b45d0303213024256940c2144e9000c200040516841084649101105180c00c0350429560131103060821180c0001029168003080802c0103504d000c203d43c40da003540c240c440301c2d520440c0c04403241e100c5005014803005080c0c0f031180c0c0003c00c51101c04440040c4580710585d585040c01c1540200002400c0c425a48034a0a211001c512400601001e55010740c0c001c0040502c2030190b51081c0081900500840d0f00c28014840540340e180180001d000548100003050351b6003140b243c1843c42d400500c0050380790081e89010620058440f5913a03604007012403492a100d003418100b4113070150070403c0400342c065081 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 460139442 1250 460138192 460138213
    0x209071704061a011403150a080d0e0f151b0a020904061e0e1005060411030c0a09080604030914030c0a0b0903070803090906100e0904030518091504020c010608 70
    0x42c0e00040f40c002e00c04030040864141d4400448907010344040035030905000700085131070140b04062901000740c0c045c1289002e950349900f41420406025200e2000c59010180801c0b1494685a00c05d4000412102079800441d0103066443d94059006180c0c40c900300300d4100303544440c003044a8403007113500500c03100301460203140c10b0000c2c2488400340c9151051040032360700d0b07640180c081c06c0440d41818005040c02d80c1c0e00b04022001e0080600a25007143c0d0718800891401b01e020300a510500100203520f9a5544502000300034102d07540c0f00f040560024414030001035401460780c81141c070303069424118084000700081c2040600020301d580101c5c2488001100e003152300140440c0d900032019034a18644e6a0429600ea2090340f038055407100c03080c00016224540f131141140d80b07a54914224400b210b8040c082066840d080d00d050b0003040000c46d078850300440a201d244d5403c9416985614a41455401d20310340302c1580764440e01c07442d00030480c40c980d034009500580040c6040c00c21035440c10003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 460140692 1250 460139442 460139453
    0xb1302090102060a1103060f13050108010212180309210105162c0126070903061d0606015708040504020a050408030a030606080912070209071704 64
    0x4000c1140303001d400b0300740c00914018451322401c0032422940c200c079883d5a65040030403910000c4403044c00e03032210103019203181258140c4039090103019030000060b61980a4440c940101c100102006ca0039508007210149205001c82a218094420344c2e00b10041c8007100300702030100e021401201201c2d0720300400c100c00002d100345802c16000350741e214070034203d403200c804080b00c1509511492034100c0400c080b061951081c500f0481900000241e03001d94050300010320410704059a849000904000060003408010310a1a41340d0800030007001e90022007544494407410020080340c1486440e50329100c035009046c0b0741e411a01d0a01448a030b4228955200e0b14495141e04c0d42c602e015013a0014800c0010001d82c00c03008015040360585040c40d140030108406035001c0d490150410000f44030014044800300041d0400c00c007262030100d20141080d000030240100180461000c1e03018602e810302c4418035204035640290162507000380b555480074281c503507005c0c04542200d07402041007003006102 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 460141942 1250 460140692 460140697
    0xf0c06150a030b0103120507080a0c1704031a091009051011030708040807050c0901060e040f15140a1d040b0108010b060d0213030b010801020d050a060b040b07060b1302 74
    0x3400410350500301122402070040100c018080282914042401840030661724415241d0104180c54068903080c0d036551390009075007040503030901092850180b103040102000304d00b1050034100002604203461504c031300c01c45050342c0c0c1c01610068002d0012840214080c0003901014004060a00c0600407038a40181c4e1403880310285400b262038000e9050500c803407441103a020711a00d0351407021540b81d64035000c0c050790001104888a10a40f0a140d0464980c908520b008040071f8844002903080b1030305200986207200c8002400d10703c0e0001c0c54140c0c110042c8a141582c0d41211034070443c2d18508081440005250000b000400c4c012940440d520350701d0151501ca54802c1c1d50b40d080310390760390075060309071000e40301007642c00304040c0001e03204000340b07038007a0080200000b140070a8981e00d03110001c80c1c5c1000e80210300c0f03a940000ea08544601035003c0c7c66084140d0034401c2004c10700c0c0443e50551805280580903559a00285a1b4280185504404100c940c0282402c00d40e0f1840b0340c6400096 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 460143192 1250 460141942 460141951
    0x501080708100204050f0907050909041514010e181501080a03021506090c03040503070b1503010c110a030807020709020a09050a090c090e0a060801020f071124030c0f0c06 75
    0x288a50b81c1a01000340d40d5000340c40403541c025002d401e85202410402440350802032200c420000148420155a0b0340c01d041c103400340b0b015001c00c00304d00c00c050030703080d0641f40d80142c4200d0f104d01c07100040001b15070710030946502915090600f810070b401d0000050404d43c04102e0091403404000010541c004040740c1c415920f0300c41c2c1c088074960366403102c0d900c208100440d4074682c45120100044d520720a010011607000d8825015070f03203416026540c03116030110503101814130401c50303004504241024400c24002481c503003040600c1c207a0000385180d8a04400c0e900400300060f5502007104c0600800c0700030041c000b02d04042d034a800540e0310084c00c14040f44100d03403040c6a000c00000d2034101905c99021085151355070000c00d541496940001510040c260561071551900009180003003840a4650103100c8500303180c2c0c54126003080202c14070b200074603604c030319980092803940c504403a00c05d010820403107000644130707540c2c80301110090240350714030050320303400240304c0c0e060400c0030414a124 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 460144442 1250 460143192 460143209
    0x10050307030e01060e0f1f090908090607260708030103151401120c090506060d0c050c0703030908070b03222306040501290d080d0908070c090507081f0905010807 71
    0x355540c10100c02207c00d40c0c6036082c015440040c05110303038102c1d90084c0c9d08882c003c584031864491101d000c140c0720b0b44801400d40320450340169160440390520a05800c04a5100d2540d0a224094581c04400e1106100090003c51344980603080c0406030b4014070460301a02108441961303550484182e03004845004940408074120701140c5141c440c4101c0b400307207001900f080e091141c910b019800801c2d02001007000d0001c00c0c4980070444004114100c080c1d4407a5941e11303100d03868407400619218440c0c020075410302042c07080150000f0b01d418400c0c1011107601c17082e8100701030390810300c1407901e4006141400440c2e110f803c3d018658000b51050003144614000c00050350f491600300c8100149420551078010b21807403444852415008020301355019140507071500140318101d00807185001c2d400c403820140070031400207201c880c2a40c413004103021441405940b6002c0001045204003c010740c0103a030031500e15440760f1074200c0081001e401400303c200820752710380040a98840301885040740 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 460145692 1250 460144442 460144471
    0x60e04030f0504030308040308041505100614040b0730030902010e0d0b0a021305090114030f0c06090d05010f2a020c060a0e01051303030e0f01080610050307030e01060e 74
    0x1141e200b0350881d070072130341c0580d140c041d5034580717603001c6408007006030090b42d010800c4e1590351054500c42c420b840c0101213030080d00390000d18008024003840345c180c6400c0289102440200001c8000108036190103511100748a074106c0152150b200054016501c1c40056400c18000302409070141c0c4066011030003601d61103164810f100030056013200c1031400820b00c4035050040f800c80f180c1c6402401c0c0040003161410001034660011500c003060907804200c5159405804415504051081040d1000208041d00554001c403001c074102d0b00c1586da0407030080c90001e952906010080d848407003c030425920074003400c038884040307528409000036a40c0400401864072200c19000042206d4151b802800680c24903402d40d2041d55281c8141c4030141c144a02045103c400c01c02000d50303840a10708c40d0308c6907504c45100b481400a81c040c1098101e050022210901900e40d992105070301001c0c2c51454003130354035903402c00b0803000b400380c40f034180a0700d40c00c0c41e00204200d044400001d100b10740780c1c1040c84 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 460146942 1250 460145692 460145717
    0x2040e0105070c11060403051c090605040803340b0615090d080a170903040815130f03090b04030c03061a0105030a05100b0406030e010b030c030d050913060e0403 71
    0x500321402600d1610100faa0015610001004422841340d00d40340101141e041954a46070581030240aa1040c05041075040c1030002e0070360494100c401800184c0343c00340c20213081c644929643e22454251901441c004015400c44040004401042c542440d02080c022241440d18125841d0140c0b1a1449002d81701c000703210001440f820750b070260500801d03208502c1e06035150201641d01440c0300e1030401900e01a50300e003000c841e03404070740180d5006006507550f51030141c6090074400f14070300e85240c09005905201141301c044080880450704501b0700310080c0000e1805407207507c82c0740d0290850b00c002103400801e101d00c9090400441e40194414481d1160103c841d80b00c1b560707980ca81a000c114184040740180440d031380042c0d03014808022021926840380c0c41100584c226070300040020f5100c01505070310403800e00502481450940080a009148100207034642d144c1114a10800602052405a0303503603002d60318808010144040054640b5505d01505c1c42c9403c840507404030f00011000c2 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 460148192 1250 460146942 460146971
    0x1110a0e01020c040b011205090f010e031c06060804032627060c03040807030c06020d050618190c1206060201050603160b09060a0507061505031e030d02031b04030507030204 76
    0x34801c40d40169107e8252100c5000042c0050601814a184a1043d16850780141d8024402c8407034904000e4000d41d00c1e210580150010310705400c80d003518190411000b04180c0e600007582d00d8020703601d070405004a50214507040b6010000e4030b0406401c40d00c040503c42e0861000e4412036a8449030140c2840c1b100300b040b10320742c1e035510565040380301803020000180800d00c6440584141842440d10000924958591000ba40c1100d15000050750f512070a004d00f603d0100014003201c8100c1a40d41060718280051905552009036000a02d079211380e09520800e100f66030385a02c50403018010031000b52500b00090013844104c0d0010301070311590151510038a00624200201c4041d07583d4240380260b00414003000d500300040b004144a401d03c440000100e082c00303804128000b42403006a0540740c8020145880b40d4030855101700e00b0450b0341850009008421180c4c0c0130b0750041c1c00f6075a40c0700c410350030440d05001e201a100c8108003007000720030440013113003150450f402100d0a01c401d0303070000c454 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 460149442 1250 460148192 460148201
    0x81806060a0909030908010504060605100e2b02030f0f010e0307081c02041706060103061e210b180c0f0d030819020f09100e010f0e0301110a0e01020c04 67
    0x540d9014588030700410880415800c5059114481c0c82c1458100350340324109401e42d80152422641075840312414005810700702c105c005080711900d0070b441600d69030004a100c082c00f814400710319200c6084640d840c0e01c001041c1032165a800f03011216004d041c070301110380320b01002c840c2c80303840e500744605000321882c0041614072a603000051a0b240441140c074074040b0440c030303d402c20350164091000080414010812103041342c424406040303a0314240c00010100c600d6500200011000701c0e841840a240a042d508240e94186401c80b82c03103400c04a1b500301c010030b1208014060b1a0f400200a1b008c1985800c0701d0309040d00c00f040342e000c01504420043d80a8514041a80010a012222001c68401d450884d0030000524111400311a502200000c3e03034048580d803480e0200005041401f414410354003000d070f2807140f4011000b0100c0400003420138021909103002c0201421848038503640030341c00b80c0585c4a80c94183e0780e440c0701c00039010f8010000c40e40c040b800340c0500c1c401d5201d80d0500f40103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 460150692 1250 460149442 460149451
    0x10503060405061f1206150602030f0904180821010509040b0f1003080a050405010e0a030506040f031407030e120f060a02070f0c062a05100b0d050706081806 69
    0x140000703542d00020075000c1c18407460000280762010308002048105201c0c5c0160b898010740d0042038900408400c030000300c0907a400703401154030422502501c0d0104500707403001e03540221404100e07549903d20320440300005d82c0014002d02030010f15201801441501030400740813100720140079a99450401c04400c80c00c64024000008500008800d1200741c035590f81d2105052102114491305d03a00c80d1040b94000320708210100e100000d041c449903801140040c0e055500f20365420b81941107603940ca40314200600002c0110020300c00ba40100350054a05140310391649030419110002c134140140318441d00e040c080e02640001d01001e40c200da000ca020344002d201c0400a103140e03200d01030340340000d5200920603980300d000711000307100050040c95410010030b0f0b55500c418280805034040141074845100d0420891a01d00000001640110b07401e50010030840c0005040580500450404880307554010f010340105c548c003041c290f41010382c1134000c0d045c4600609c0d80051001401da9540780507213 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 460151942 1250 460150692 460150703
    0x304120510061d011401021f090f03052203050d0305060102150906040218060306061012060e010614070308010b070c0902120a1d1b0111032d04050f120c0a0e0f0105030604 75
    0x80c40d00100c08103000b200c01c0c088c2c06000c40081c4082ca1901c40d94070b0750800c20021000210009408480600c3c00181c046885000a4809050a207903503603032540c808185000c0703000d254443c2d0009015a0091140d0b50058051060a40b0313203142042010352140d0302141c04034828106500e6004070464000b80e0309200c0c180280043c00030341c03900000c06c0074008605061408010400200c040091594015034008004a030340129441d4101b040280c03e205098085500045050103100c0201c0e40c000300d214111055038410030307640c90541c20004801145604901c5039940001809555400e8001d0214851034440004008000e501d0303940744c5282420404103005544620701018000340503402840542405041c403443c80e03070559040360b056400180c2070b0030010440d1001c1c3c0040318005050007031554100c5151626003814840003640c01d07442e408686008910703d90018215501c100403020b486a0010001c034406956110940c8600710111103140b01c0b850700e00700025642c100003486500071603114 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 460153192 1250 460151942 460151953
    0xb0105070f140d050306040c0e010207180204050604030f05060c2a0f0f15090604123b1f09031b0302091302011e020304120510061d01140102 62
    0x280c98209a0220790503054411406054030311410340030800401c205620783c0d8a03415181c0c0340071810801100c500c0b06004060040c20b400c114800d0380d01080780c01c15104001203686030500d070760034050001d029035001103820000c002000b2050008102000035500e01c10f40c101d0300a544d40c42c0400c07001d030080314201a1007480110746507448542d081c6403918001100d5003120f03900f0413110702e1b85240008003001d89102c2e410000498000011a1100740ea0080e50007004107664101690703508542c504200c1d00e503082148482c0d090550354150320700c921001d815203000d2151380383c03071114258100f040143c6480c420040a079032162544070f14514900b107a8410307150707030402030300e5034540007584990300c0d0340705001ca03420103008001a500c00034400d0040d00c60195084a51051b840050614440c0c9a85604000c035803241c181c515540c004100e60a03681a030007030743c51104651504901c0d114241d48404200e900380071001c50034044040004a0a0203031601c620450790740c03600c10000b4040d00d0b42025005030040e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 460154442 1250 460153192 460153207
    0xf0d050c010b06030f061c020d021017160908070302090a0c1206180509060603060415020c01020d0504030f0503191a03010f0902010e151c0b03030301091b030b0105 72
    0x144050900404004000b050a01c10710b03000844a52045503007407102c8514805206090910b10200c111000400102102079140d9130000f52811182d282c00911a4400b400050754084c40f458944003d03019070a0710390300600f052403088018451056000000514000c0005080100003a1020890750081d24528440c2c603102444c6010300240c00000701800280c509003034210f241e5219600080c00110082d0f084506584900e0741a9100038014501c940d202c4c40030300c50940c1c0c1c00304030a03800036840ad55800c24a000491148041e00076011828802e510100310701da40c044080c0c203c1d51080748696201400c0e00c20151381a14580015103014407042e80f80e10710011201c010340d10040c61308403002d241c4035030102000300282c02c0d0790504407144007182e00d41c502c0b6400c658000801942c1d541c82140c5108204e01c490150601501402d500407a2075503c507041417000c504070b82d0240a5040000c0c00390b943d40d40e10f42d2042c07406464580c0610220102d101c1b1030113061807180c401e030166014141c2d03840749440c0c0d4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 460155692 1250 460154442 460154447
    0x2703080d0b060f0a12050a0b1f18170606030f120d0b04020307180504020901270906030c080607031503110a09020a121107021f090f09020403140f0d 65
    0x984118564104104200241d980e250000113420307001126a2401c0041c4074940102007610720141504007601e05000da040d50aa55440070900c40c00d049040458140c0a06d03201240c0c5d80c00d0100300200070400001001c110b441030241026000d10a1108444807601c81c03400345035460306115120039568205442e4601e2040640c8010440b00028201c04038400800d800010101d0740192120340c003154400003466000380b41d402140e001840e0444c1c046050070b40600c0040d01c0650260424111004a9070510200d03d5801c000c402c040e111815081201c81d03100e203024203900c0300b41e01070f102d40c91141000050781c2c54820b010b103e1060007100703001841d0324a1a13441d0980010101d404540c070403da00c0000ca05020148007416484080361f4510400b03042c0b100d125801c4076802100b1442c00c140c200006c9000d03071a001b89030848140c40d81c1001c21400d681c03010480d8540300a422408440c0008400010000741c19005001a00e0184501d0f10910003031004540ea01c51a08903c10b202c0c0c1c01101b000c0c59040e0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 460156942 1250 460155692 460155701
    0x309010915050408150a0b030d0801181407050c06101406070521090a0605040e0106140706020406030c030f050f010e07030e120a0e060f03040807212703080d 69
    0x95a0600300e043c82c1c1c40b2502c890900b1611010700741c0000c040420000ca03280c1500901e54481005e0f4054040b0090242e4014081001400340740c01100854100c01d1840505901034400e0404007207841d006030416001c01002c1d90b00114000c0250311076070b0045820901c911000c02c0403101c0001501002c1d40c0c032001442419049104180d9060089040c0b10654002420024408803d0340e820307680c0e80d01c100800c02c000080c954100c80c04205041c002807007040d4031128200d040d10fa003030400d000c020a510030303014900c0c440c400c0300400180c00842c0000300d550705500300c1d80c00381840d901c050100e65143c54080044844c00c68000c4066540040100840050074440c7d541000b41440c02044500b1021509841e0400010845400d0000000e00100240c6d2005900c006405e044a070180b90180070321203040d26000c0504041c00d071400008588003040b0810b50411841814034450081c501c0418801410143d1074070f103c040c1d0312003000821160034815110390000d40e5400f5190600301400040d0020090 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 460158192 1250 460156942 460156979
    0xe01090f020c01150602100e0c09130c0b030709051008071202041d060a080102190315090c051e0301060f180506130627092c0d030e03090109 62
    0x340e82000b04200c0b060080c02070081c920500c1d903c640445150100c02454801c0c60403003441c842e450f103404c0c140d0102c000b00e0002104641252195001d40715030441c902272000b081070080c501014040d000038494036210145100e010725413188440c45503103805221440180408240020340d0070f10015107414010744c3c1d0b424442200090042c18a034a842407204541c0b15107210b11180700e0310740e042202c940ba00c840000c000d045400000d604240110065071403141120040b0000d058682c1440b14081400300100001081021001d115100d1000310141682c2d00289180c03d150441210000400c0c4a2004690495099944008949031401d5040790400c84400b586500740c0c000e090006066628000a405c034500070040c002e43e0301e4034040c009080655240ea80000001c5240d0300b004405140741004d50450305036440c00329102801c0c0d11107082c00c2d0101800301c0d080c10340190074540e441500140400c41812180c80070001c00c5e044008a503540d001d0b500509000989070700003446001c0140b0b1600700c82 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 460159442 1250 460158192 460158221
    0x50f0304030c02040c0c110d0b010b07081c0207021207050a05060f0c060406051e070f030218030f0714060310050f0604030501050903030a06060806010212030601020a0807080a090b040e0109 83
    0x164030b0a940068150f502c4240e100e00001d6002e41250140f0141f16400401c0f940202c500f4000070215940705003425005118041104401003052018840800c0c122082241007928811181c1c01d0b0520650094110078420f902030180070079104100540040c00800340e40000b810325901c43d28100411500758845085c45090301d0051180503541c003070810402e0b0282c1c1c03080c46d0118aa140104103080c0303c0100809142280c1c14031424481e001ea00310b407511849021902d005641c0f2030083d000010207104441e40b440d054440c2040705401c603680030511809a40c401503880b0808200641080080d00059411001d0b102040d54208a42c3c5416a034418040c5005412503091658a48038142100e400b116120550f4100004000410394113120b900054619818980b03501d00304640000e5503445140c800060f29030000011550681c000c124011441d0341c031403140d03031703407282c15150898841e0444070007a00854442207000c640c852030a015242520040e00300c211041e0310341450030001c0c3c040003051030f40c0d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 460160692 1250 460159442 460159457
    0x120c010204030f0f020f09010605180d0b130201020d0e03190f0506100801061203050702010309020f130906060806130b040623040215091008090f01060f090e010c050f030403 76
    0x20fa040c503200380d851401440c0e04228400306005014592100c0b05d090741c031900140c4010300ca10f581080941d25100d1200d80861001031258001c209000a42900034048084010801c140440070301383c080380b110b100303a081d1010011480001e880031060f903405030790b158105584191010581c118019440390003407403008a4988651106401d08a0956080c06220310900301482100001d00900f07001f4408101c02c1e0350030419030740f802403080c0103108000741016102c2560a00755034440c2c0c2e00402411004115070380401443d940302c0014103100c502143c0c3c190070305000180040001c100580314061003213180d12004042eaa80c1d0340d902c480100200c81665440d01219000784030a41c1e0300421000c1540c120001e42820300400914000c52100100c2e0710b10304000d1241c3c00c1d20790540f00c840240c0d450030030b5541c5407941e001450074070241041000700c940c03030408001182c4803aa0400002c4510651080201444400b0a00d00340e43c140441c000c01f0500403c01482440a010001c40e0b115000e45407508 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 460161942 1250 460160692 460160699
    0x2070e09010f061502070f03170306040608030d020a1101090812071407080a1806050f0c030c060f070f0c0b0408090613061229010f021f050709080a05120c010204 71
    0x5080f150f2039040b800d00500c0c86524040703415010001a806080c0c5074048001552455036071030306039180c3c079518402c61000400464030b280ca55030800d4000e825800c0580b81c644044208d84002900900540c0c00080d60881c40050485010b12400f420305812240f443c0c61300d0700719050b84007175441c0544403404102c1e031a1110095540d00c1030203400c0d5180318000c0c1c2580c3d01c4866070002d01030340b2102040686001c20890400080d0b800004031a03844c1d1440c2003582c0c43d62008001e05065000320700900c00305000e0b010402507442c000c0030b0841e01c03032ba080e070701c5d101585900c05004440c1c103002c15600074400da401c00c01090100301d0b140c000d13141c403600c0101160300d01111044803080310509544803101240c40701000003526071660042c03940340c8501c8400c104080e21a10310014401c200340c205103052141306800c41024030300c03d01a00c003444240414540704248000c103090000c00045400e07800080340c400e4081030305c1c02e000ca82986155007101c01015089010040e0b98800d034061462003400b590f0801001 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 460163192 1250 460161942 460161971
    0x240e06091906030b01030c081b01030b0a12060b041803050a1815030504050705060f070b06180c03090d1106070807121509050610020d050307050706110915030702070e0901 75
    0x3d14410031140c40e6a51440c40c00e401a8011a003120203039801c100411842c040e11164460500d01d02440c000c01d0031144040400e8100401d50041004840702500034020710950742c005140c0040252020482014000f100301e411142034240180010010050796440c10320410740418030408a24490328050798920030791003595548000103003c01d4503401000240001031000c20000c050650300149061042055031081c1e10428800070300031928840440d5203510303056050f80e150000041c0422460404e002c60a02c10b4204888142851144110040b6045d10401048203001d84a100420494851010555a03031b0401031545013001018a070b002e240d007035117004030464454111071200c015400c01410400b42d840090185004101c1c1d00c0c0c01071046507000900032000512490180d4507501c407000b003199a48181c45000d4801c605010b040c0c1c08042010006066040b021654040803000c49505211b03d4042220810090381248400300402d00e1414140c0d03078800e02c140e00014981100301000c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 460164442 1250 460163192 460163201
    0xe06060904140403090609080a03120609060f15050f03010e07140d0b0f030309030a12020a080f0903010c0e0616060b041d060108071503180213240e060919 68
    0x3030b103080c4020340040c803040c9504044d401c0c01030326052030264401400c01c002191751f8400014001c0c1001240750100c1c01c035944030b5100101820100d441803011036603801015800484a009880c0c5100d24280141041d80c001d82c100c880802030100706608603880e2420341408001c00804a009015042d0894800f411180000b031261102e4030100049000d06282400842e40d41000c265000703501c00c0000007160741d40002c11031358030796000c0c141c9095000703903d900706d04017004404014024070000c43c06200481c5c0b0000940030b070300300036402007064584d1412300700c80c0d13448100303061600581c0410200340780300014202214080e00031840801d4107100e000c0400c0031a0180b030212543e0020051508843d01c03800d0101d1401030400b0b5006002d410b04043c19800c0205005000c40f0a01d60354044160281e10318503000703e26130780c0017040e1480e403415001210020304a40700044c04d10304001a0182c842119030600442980d00075501550380da682d08040c02400e100c00f40aa04192024030511210001d05014 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 460165692 1250 460164442 460164461
    0x209040b011806050612130507270b010e04021809160f02030316230703090e280504020f03060109020702101d10032003100602030301030201090e06060904 68
    0x4903a2038540c03402110701c0c000000c84108140250074000100010b0759058140e4452903035003038901805844035600b9041c1100509030040ca2801000d01c0045c100c001d0800400321002003051504100c14010b20a100304c070b1450708a580400e1184408681d5814198090408020030a100007049814034000071000d22049034209400e4203a00c0214041d1a031240c01c9800710041e0b17000071425402e000c0b8036150300040c5e01d00050100903c541968621054446006680d034a44042d1a65036038aa403c000b0142d014502130380081a40d400081500c001381c401c500802a100656011740d80340c0381075108005810050010f80c4c5c01186143c1c074851a90b01404014002e10308200010303610803047c414410021031610600c001d00c40303504407074881d02c207880041601b012021580741d0072002c00320070180c00400d100d84404245080385040310b540342c2c6050004600801044001c11080760b6592800c0317130b4a10007400000e00054140d0350030000000364a10450b080f0800808081c01c24101d04080350464100782d9 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 460166942 1250 460165692 460165703
    0x1503050705030c061c02070804090c030f0506060f040303211d210306131407030c021911061303080310051206010e15040603050d020f1c080c16020904 66
    0x40100124030301003000c507910030703400e484040c280000403401c00d03100715001c00903000460700007c4000c20032802d0030844002d04020002000142a6480c2c02001031031031003d5001418a0900826081c2c5040002d4030f40c1054086112481c00b41195011507480d4035540b001d14a048400c00d6400c661481c41c0540381142504042c00c416071506420064940000f0040b80040c14502150540c42020048100c9511a10680d0051901c0c3e050991401c010418030f400400c00d1010001401155981500280c0100100c2d40c200c51019030414500c031072400041300d0060554484021b000b6803800c0c1000075081a00146500c920155503a4840c0b68040d0720031100710402818458041c4404d01e0260f480003030205010009204940c14600d00700500400502142541144100300c202c1e966501d41142014652140070b4170390310303102040302a5036100c141802d500d160042c040d040103081000a2440e140c2899a40c0751b106517240c0c1d10300349885a0191001c0d0503a60020b080d460007503160000b4070f50060703100740d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 460168192 1250 460166942 460166953
    0x1d06030106020d090b041206110d05041b05010311030a0c0903050a080a1119060213050a081b090f041101050f0a0c0c0f0602070e150904030c050705121c03150305 71
    0x4004102032899085800712600038002485021f148500f1481c499034050000103e601ca04803000185008806540103c5030814041004000c0c583c21117410030300d401c641581500f5101c00064003640c0300080500107802c8213000003007a0907019000564440028141a402c8030b40b0382d00c40a060200c0c11406540c3c06100007006c00a9a42c410414071005001501412a50995141103915070b845030740003800345a0041522680e2203031b841003510040030b0003400d88100c140c0d0b4944164444d00e04000c2411548208041c400c3c607801d10b202528424801048401c20691301c035518803010601c812080e41c108002030143c80074950100c001400c0b100c2a1341c891000400480c41c02200b00083c50700060780d0600c014000708a41600040c140040d140900d081483e40d40c0c521031464211900c0341c0401e68040a000c040c0014141c1003001003009502a80944417140d0303c941c00c1c0800e080300e55408414542c8030101150100c0c0314112203d584040e64500807d1111400d4102c9529404030f82007900d254011 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 460169442 1250 460168192 460168213
    0x607200306040b1e0f160917151b04030305072409050607050f090f041404081335100e0c030708072702090301050c03041401090b071d0603010602 64
    0x403154140003188004e0b071200c1c00b510344400c0103414004040c100844106420b000e58044074000c4440c44054100c0301c08410003031100d81100f03a5100007000b86003411450300d0000c214246641070002d241e80032117074001e038030306031440c1d40480342c5034482c1c8015204000300c142034022810315500300005010706041d0115241f207a5042050411001a01440500c00d08010240349158a003050356001c0c035040300d82540302c4001e031003c82c0250a1011042c41c4d28010072017000708010164014000740101c0c8400c100704070b601e42015001c9021206240302018001d000760403e407946030209040300400d0b1000307031030003600c10700700c0b000035119240940b40040d0000817180416003170800610008124201c02002c00e03074501440040c200c052040d00341952404d06040c080b05a0703442c2c045490f039803070280c003c210500c0c00d901a9501c50f01b0070760342102c6110140040601e100b2050141c098250781220071101c85171035610303064a82031b025032003a0030440c0403480304403440e60b10a40a54020711041d0040c1c88644203 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 460170692 1250 460169442 460169461
    0xa12052109011b080711030d020c0f120a080a1e0e0f010c0512161716030b10120203060a17030d06050307030b16110a110a06020c0607200306040b 64
    0x70443e5a48000210703464800d8000d0354401003864002000782800098100421000b80c190b210308503185594500000d4001401c0e0303800a110210b403072580040e207044030091440d01f4a03e1007600c083c03100144004020604940207940400a05081104080e01d096042074249040c0c070300d09800c6018542004610b24090142801034000a040c0c40c80c0551a000d20300c0e0a0721000c403000340046442c20942011b006403680102c0e403d08030182003487d0810103141100146403140c03180b00c00324002078108100c10900c1d0a00c103001d034410a06549803400e260994082c00002900002c004a6203c00150000140324020207846803040070950301440e656009500340344c1c1503079101d43c000d5001e03500528040012444154215802110003404a030400400800841d8a1240c01c0328034010b0380107980b0002d08103c4100c402203007218003500c000c00c04035507400060303031102c0c0904001c4d60021010402d05000644903442101c0d000e200d03d00c0800940740003008a80342c0307141110112080303025541401800b6a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 460171942 1250 460170692 460170701
    0x30a0f091a060915090423150103051009050c090a0b04020d050105041512030503040602130620060106020d11070e011d0a020703050f030a0b030d090e06040203090a1205210901 77
    0x20070a50301e0b84040d00b8100c01141c84124001c0c409414072403e07d0341000e03510250040f10030710924410413204102100b0545005502c42803000b05d03203902c14401580000c4001d80a46183e5940100c0034008252141c01030040c1410700400343c00c1502d40c1e5622040d2969601d102400010007203010018541d810300d014802250043c0300340c100301c107407206010410140c02280e004503941c1e251400c1900da03112450040c019010f0404d40a0f540d020f0200702150403580000d6001001110805c20200241c085046980381d030030a003c1c1d5001a00803149a0000078000c160f0108085103080c112621241d80c0d00d1400c1d24500280c1040f0012554459551000d06501c0f1089401084119086281c042c280d900a004d911811840610075000880007410241155111022184011381540d0754915020030091000d540383c0500082010254045031172414540309591164491900616034540c0c0c1d40c4074460344644030918101004410801d0b40403100454220039001c01c0046010300c8542090007845080d02c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 460173192 1250 460171942 460171951
    0x1020d150504090b0601050d060b03070305040203011514060f0c010204170d0509030606090406140108030307030c020c062a070b04141e120304030204090f0215030705030a0f091a0609 80
    0xa900700b503c1440480c08050645401044c24201710341d9030610240110003801c200d07480f058002030b0210400003600d416402091159108034000c109a8440460101c0d0200d564040d0101444803100b0102003030405100501c03103018200030071410310019810107420390780282c0080c1d00c216090401c800c1020020424900c0003201030420701d0070401c0310400319690300700081c800c5104520304000305061085590000110a00207a0b140a0f10368460340d41d10390342d510540e40140000d1610020091080c8081981c00c91403000034550b91425600a8414102805625a0a1080d81d00c0510540710b0701c4100503101c014070900e040e03252100c1c80c0c9041b0a40f020b0402c1c240c079024094005014002112581000c14180f0040742c1e0111200d40250821b07285d0b01a681001303400a280841f04400e108003003820400c001e102301c03907400440c142c070003000e1320701d00040d28502d01044060010074089030039608000c41c511496000000c1c500c0c00780d116440e645540c61480d4503092289030500525061041c1d900d80d00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 460174442 1250 460173192 460173199
    0x31106120129190e100e040518250b0403110909030c07060f170106050304060c110304060822031218170c06060105090105070b042a0929010e011101020d1505 69
    0x17885c0c0d44000107088080b0805489215565070030018080e01c11441415801000d202e040720034800300c52444c10050036a842c0039030340c4e10740a4000083c0304144a011181602e602c00788402103c0c07895810701480100142c400202c40c0800e1011a0b942c40e42000082c00510055698101d507414001d405800030f200d010000c60348040682c0103105068005c0122034200750b020000003128860400100c401b809161400405400001030002c2c043d80d1140c0c81c2e5005084080c1c90711400c0c0940d42061100e0898408010085143e07091301806003032299100108072000c0c1561030100c40140e0791084448a4103c04c5a1603044c004907140c00006420001d06a01c05028200a07203010700400010304903002c0c490000300a118404001410842240d1100721410304140084c01000c0b02c100155400c20280c1c09030041c00742c034001c500c0d845000d20780607003a410f5010051400384400300074011946032071655200d60502030f280d4594011450300744002c1c5401c2900e42e00000740040d6255a81d5030010041e40890710 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 460175692 1250 460174442 460174459
    0x307120509150912010501090b0406080607020604030c060225120c0803130c1502150f060a140f0907020106060f05040f060f090b13031106120129190e 66
    0x1182d0700c1d101d40b040c054aa00c80b000c0e9880d41c00840000703070ba65081a5103100e4a509000c00020403000d107400a000c090350490f03003808284e403215441552000c04440590050340802e0116020a0203103044100060207840007514100b0f51081090f0100d80440600c401d914100d6060010300407030081d030007410003103444d0143e103440c07054072141c8050102500002c8011802e840150821110100303000050100080f20b00d050003400c4c0001e9200c0100b2507009100c9000c17000050b00c0301450107803252140b40006c0c1151309245c14044900741e0b01c110121000e42007541421091499a207042401e13126403040c0c0e00224030749d4140500200300c6e00d1809400c40501c50103010034400b01001d8070030381080d1010382c600040d42e20b01000080321511941d5100c1103003590009418014058581022003d41b0702132800e403022070a1700424400349205103012900840c158400600c00340c013042506034000051030840b015111000720320780034143d100c0c031101c28102180a580020305504441c000c16480411600d181 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 460176942 1250 460175692 460175707
    0x203090909030a0f0f020708010e0606010807090e0a1805011802100306240201150306020a180815060f0a1206050601050c0a060c050d020415030b060418050408040305060903071205 79
    0x10011004c031292038081c4000e990280c03003424405c001000044c080c03c0000e20030746003072030580e54031960141c55040c0010311100020f16100c0c01040e1410031103101c80c0b000c114a580b03c05498004159444002500310062005503010620034080c0304540302c14681d4400d6007480520421400c0d2080c16681000c0c10300b00b00c400c000910211910124020704088a031580030700018089005115100201d1200100c190700441440010f5001d490480c03400d0715800300000d4140440c6581c10520310400000d548042c1c0064035405c20002c4040e005030011f010040504414000900c030020310f500301103440d4004904100c00d102090162940003803081c02d2944c0390420b00c286c401d480b01c040c0440034090b1600c0f03014015442d88140201c1d02886005601103440d991183c400c1c20080c04482c0c3d51200113400d14802c2c480c3c5123408002c580854002407800e018801900030030340c1c0500801442035401001c1032100001192060084a2140c903036040559a40c0702d291503c60a5140c030b904504003000700900104 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 460178192 1250 460176942 460176947
    0xb0a08090d030b06090d05010905030f1201060e1f120c0e010e3a02030d030504200105040915120305071505010f0603091415060f031b0118090c0203090909030a 70
    0x11a8000c04c2513842940a1b207183c14650f02500e100c01c1d00905511000400765200c8800754040e000c052661500280036076601c007400c0b503003060f151124540c00003c1917611080319010281d0700e01440c0d5030b400c159292a06110b54034040b1a40b442805005c42c0350405198681d613400400300c0005103003251224401d0245462185a032405840c00441040e46642c01e07140340c0703143c107100100d400e0380201110401451380000a0150109690444a048d154500c880300724080600d140e42004060b510306051038a400c8011020b0000c108085a89544004020030610404405c0b801c41078000e40350141c0c0d81c1010314202c5000c40860724060b50b09860080181310100c00c407003e90003268040c0c900803c070741e070003800c1c40b008054140cbd00312950b80c480c59500380d02c245118407206110f0300b000c56400c01484005400d2585445842d00b45003c0031240e60480c5003558003035007408500350500790401166a0302c2d241700100712a807604540001d40d00100e00d1001c1c519081c51701c10360140101001c1e60400070000d901 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 460179442 1250 460178192 460178197
    0x120c020606041d030307180f0303230a17070e06040b07170c030d021c020c0714030c1f020f0d181706070f050f07030507050d0905010207030b07090b0a08090d030b06 72
    0xa4100503495107000150407211f4030300c001404003201007030717216540c4e854064501c40003000c0101c030340c1d071118a40114140c8040c0c142c8680800c2074942215082220b50b600000340002009942445001c0344003604648906000e40701614122185581d0b8240758181050003c50421480240640130820350a03004004015115101c50040300940c07221020080e02c400900780b2021b0781c00161000c81c105805e035400003600001c4440c02c0000c8507400481505240d00c3d2602c162000c2e4000d07286d02181008009032103029000d0030b00620507a180301d43d0328661075040c820424101d6001070852160400940140c3d4101e00c010041d0501c21120b88040c62040c68039814003d2480342070095840c0e00480f2940a0700c21900d01d0501800d040e0380c5c42c820351034080c01a800449040e14184162070200042c180550b1548043e508160001c3ca811495652000801c00740107000c00c080203400711000641400e124050302c0000842c3c0c544002c1843c06040d00751606800c0c0ca503030420503040815902654588404 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 460180692 1250 460179442 460179451
    0x40b03070b0f0715050a0b15130b0f0f22080a0312020306040605150c100b06070b040317161e0f120e03030c1e0c03040e0403120c020606041d0303 64
    0x2e916441d072895007000c000400c0383c0c00c400d0800f14105010415107422960005a200340103ca00c1001440c2c180001c400a004003e001d102d42d50b443d520900001d07119101500521100c1e25185d440d01080000140030b542090040b94000380d44940102d1541411488020103403200d00024450065a40c80091080d400d4124030300700c80b5800408104d09854940056010304070140014220b040c1c40e03240311240b07500500c0100c0c0309004948100c0c040303000c140907112502000402c0e0608000c8a41c644008004001e402142400103006113001c000c0510600c2074400d015102020020144072480038000308040f2218610701250040101000c40d00040200b0b9006218500b40c1d5100c50701c01c0d02c030401000741c580c2c0491144800305c02c01100c001004001d00c8461241c1015420000d8841c0c00b5034070a0240c02040d4036160018003052100842100e80070358414060303e0710310140252030105908a0b000c0580046c0140c000d6020800d140c14280034842e6104005020114119460585541c43c0d010151 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 460181942 1250 460180692 460180717
    0x122104050c030d090f0806060f061309051e0a1b0806030309030303190e07030c060c150207050c030111070c0e10030503040902070516060804030e130608010b040b03070b 74
    0x1040601104000365050788801604860f54407414101c050072000f414480c02800c00e940500206103a800400c0c04e5019400c050030760601810200d08011240e00250044152206000e100140c411018003a02c1d01440d941d0010054640e203105490b20032640c000d181c01c1016007045c0d0049900f0b4550011811806c09600c2c00e4645c0d43c0315000001d082d403046864080d498400070040c81401500440041e202d0394051104001080f07200c000c8607218003240c0300c0503000080809040006e20b004041d01d019031485107003550f010a075100c1901381242c000f40c00c20b682030b9000302e00c0c1140f01e04003449402721025490007094200301180e52143d00e0002c2c9030090380050401c01c0086140402a0171100024580c041d0590351900d4590110340025001000240c519129032500b031442c1281c600042d0083c0c0e030b101e998001c0345a642da2000c4d03a2450344440800d0f00440ea00300b2a42c21800d940c400c0c803015160340800450798904c2d10341000291880e50101d41c4c401d41000000308a60080b003411140700e140c040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 460183192 1250 460181942 460182007
    0x180a03152003190b120601051e06040b0a02011d0c01030b060405030d03020702030c120604030905060f0a030b0109050a0b04141503061c050d0c030f110d0e030a0501020a050c12 77
    0x103103c180b000c0c007400c040007500400c26000d100c0402a001c00c1050580341c0903107152000000c803400d404401203042940d160003403410003040c4205141c85000704280551b500001c64841400038140210511000104e0b041d5004503190000d19a07041c01354505a600c2192034038245418803001030b07114a241801c403004c0c59030000d00319045440c24001254101d10040460141a404107a100d07125441140c00302c00182c1c1c0c9000100b030b54039140060300c80c102805424031742003c0c9000700680c02007428003049414406041c10009072556034455003405050044101511540360540b942c541048065442d842082a0b410704984903d605043d00d0303200c03008858400812540103010041c080d501c0c00050441e000307810b10300070540c0d00020300c480103510944d1758403540c640841c0704459002d51041c004001c1d800c10300b11034598520070b0ba40012000001819900c40c1401917840c1c0c0e003280e1210080401082002c2142c51040d00c0074880300c0c048460b60140180b5050b020503a030350130610741d10001c00f4402e006 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 460184442 1250 460183192 460183231
    0x10f0506091332070c30030608100b060d0b01051b010c0807020c0a030b1806180c0a080705011229092208180a03152003 53
    0x9010064102e450112010031254460a05403d0381030040150300c01044440c3c4140d4072480903c43c000c51240c1c1d41e60b070713036400c000f91203a0f1034001003010201e40f0802001d0480301c13000304c5051005002019101c45d20002000340c50102c4880c20304040580c1c81070050314142400c4066140c010444013000502078000a81c03a03511001a40d50780115500560f4a181c511038500c1000415031200441203070f2034491080c0c3c4e03a14944120b81c0c50b010183c0c2c40740c100d04c40c800108001444901c025030000d48040e01200b0b285140711815260000403604c01c4100d0100c25290407282c84103000d041650701050380d0303900d00181800c445076030303d4211b07209150420003402008503d80e22540c0c0a161003200040e613040402440406040f420840204010700c50420300b4003042d4100f006032594810800400d1f098407038489191564407883d0400c0c5181c0340034a200f05039070281695001c0c1000c02440c03056080c00c41d40002480e10500f1074a035002400340140f072100c0301014640d40b076800d50707034402d04089848100312507 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 460185692 1250 460184442 460184449
    0x504120b10121101030b0405010513050c1603032c1c0e04050109020702090a0b0307030204110c1204030c0806010f0506090d08031317040b0901110705030d1d09010f050609 75
    0x1240c2c04800c01d20016555401002071019020040b60b0090360184103030740c1c8000c2008201d510030b104490744104550a4801011040d40066610101440105040036500c81440750741345840d802c2100042d980d03900110a03507030440305c00c81181c0a5210050f0102076040300306580c0324180c1d007801c01c940800c02c1e00d0407001449507503801c14100006e8001e05c00c039651602c1c06406900852812486a400c000c00500000300e503100700300083c04024000e00003140307103800380401014490b440410311481000350380115441000030303402c000f251200d82d035a610300c0d40c109035907034640503008044c140e00004010401c604070321104405481c0100c81c616940d40858000440e8516411070082c000c81010041001950501208180190081e00403902200b094920700e8511f200e14054681c40020070310070320005501c94050301d0b803907070041c100315180d25481c1d800180c90301204005400c002a1200d4210420300c030007071248a207401054030303c07801c04d506101c0b94189990040c010b0901496000c50000240e80d03 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 460186942 1250 460185692 460185721
    0x606040509190f0506090a0e060613090816031106161b0c080309011205010503060a0b1809010506010912030c032616031401120b0411040c0201050a0501060504120b 72
    0x744000020401054020103250181c40e040710000c6c0300e03100c1d0100090310b041e51801106200900c40014210302d6480008105529861600c811510b640c1c03011a403000658860003800301d034a00c00e14091441c40350340b03002800076128009007095500048144072002e1500c443c0800310203001d09041d902c0450081807040001d000c0c103006010004103501c000341c17580c400f00043c86003510aa803000214450700207100300340ca00a2145580507845100000c4810000c1d500900c0346001c010858100d4014171203c20300203403001d655135202c0da551791051090365a0821440d5000705a404080640c05503984c4014100102c650000303400d0144a0525114890b541081510001e0601074180c425042600e046e05205a580003d400480d1801c0044031003802083c94590481c0c07001500783c243d0513125682c05c0c82c0e00ea0058400c58a042c084403c0c40c01e1a40d680c01020b1030401d041e07000043c2c0340340c810141d50903150180d01840c24800108000e1100310100c201036160705800c0501141240c84a406004042c03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 460188192 1250 460186942 460186981
    0x60308250f060f020906070f0b09010c021e030705060108030319060510030e010b0d080408060912040603020c1f02070213050106200a080a120c091d0406060308040b040503010e03030606040509 84
    0x2c480011f210042100c2004028200340c000e01d10701d0345d00d66410300800e01302d4800035128400f590081a01102c15201d081d001c9000c1d114070810341e401e190031a580c1078a000401e07000200f03950000710400a10350000c00030302d41407407044002448542c0c640f0700803a681203105000c1408040c0c0754181c42ca00b0000940200d00e6096000c0c01282c403106141c103141305641c01034000c800e034900485001c074801150020308911541e610350701c07051034145000c1c2c080d8000d5020460351500d601410069243c15022214031041407210b003c80540d8840c280c0c8104464a201b483c1601c6129203040014060742d5440781111649500e044c10106485001d03280c803c7c5400780c0c01d80010469440003811b40300c00c0381c0c8481034500c206020342c424030541301d090310244e030391403d10b000e014402c031800340108004010144440b0340090107050005602926a26090065880390b0400380d00c00304009420041d60500340300b5180554491000b85041d03041620009913144503500c80c1522900d04200840d004404012821246 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 460189442 1250 460188192 460188199
    0x121c0b031c230a030609050c03091207240c020d03111608120115020d0e030c090717010b04060905010c0c1a120403031506021609020d09020301060308250f060f0209 72
    0x1110400f0000030050161030041400b501d08150108066031007000560b4040c244000c040c15107001d240050f1580c84e003003c60151458440c1c02c846120305e001c0c014508a100e1440c20020030440b01e000c501a14000c1c401d08114101842c110848004504010960742c0030041c0c400503010303036a05070512420038043e4103020b0f240d80e0404070000070704140440310306d41e101d045a003c1c0d40b941102c91109641c01000c3d16100c0340c240d0811a1a401e41d80f400035074a503809a242d080c88030b04209002c084158801d0260803208007514009800e104054201405000a10003480c100034803141a584401c51000c90344a1000002000140590a038540c2000e4458000302e048555040d80b500d420f00078003a20030380c0c00b2250035420514010030342510101d1640841c10021201e16000740c030b49540d4000a60080c80e4a4064030364500c1d0185c0140c3c1c0070b02860f130082d8000c04804d5242c1d107181d138480001507481c000390207180d204030410340002201c0ca0128071107560400390000700742000040c0b13140030707100d070a01e003961 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 460190692 1250 460189442 460189447
    0x140904140f0106080c0a0203030c0702011106070c140106061b0314120a0b0609180417040e04060509010c1d13060305010c03060501111905121c0b031c23 67
    0x103500d04014828100c5010341d0351060161645c13400e04802d44618081000103810410004450a181d10f00070303c5520320600d0461030714078480b00441d0900c0804d0301c201d00003c2c03c8100c00b006204403000e010f110b54460000070807009160800142c061142102440030b2500b080103058241030050003448201d017412200c0b255108100710b001c00c00f0040840d808050b180c5030080c0b0310702c242014421381d104000040c03c0030441c01e402c0f01d0f07803103803070b06c401007007221000010302002c95a00c1c0b0a134040d1000380324886d02d0000314245480c0000c1628402400d03060305130714060240c03d800d40e110380d0f2030440d9140c0e80f0f02d01c035000f100744005c10300d51050b00350001c1c010340c00c0101c0007040090561010082c5030003036404000303442c2c0700c3c0011140088032140510035030b400352280d2180e071341050103a815920311410403103800800c005800d4000b50032040e1308242502c07560344400c01860241c064030300c10490840191070680039920207a020710048201d0142040032894024a4000041201c81c1c0e00c001c2e104c5210f038 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 460191942 1250 460190692 460190701
    0x80a021207200a0c03060203180d0f020f160509090f010617010e072d051002030c070b042702160813050d0c060f0203070c060e0f01050a14090414 64
    0x244030345261041072400110052005000c1e010100320b00490680c8100740b03100e813030301e10b4680b8030280d000074010020001002400c41c00c0240100440425007849440e0f1407110042d20401904003200d540070213400c2d40001d0500100c554010410343c00351901200c0542098460318030341e900e49074200c9561941d0b9883c10b800400c07014590f0b0a13401020501034024440204001c2d07c036601d410b41c40c03042401c00c82d030070314100700b0740014101c100e50303031101003d0561000d90b9038a0001c0d20001c000603402c00075810018083d00802000d00c06c134006000943c0420307140078a03241701c5034501d00154445aa958400481d800a0181c0340e8044a074a104040c029100074400c40c1000c1c8001c0d40141e03d03001c96502549c0c000a41c904000240c070101070f4001d4052100700707160030425a1750ba26000b20401c02c500003044031200003503141585402424803039550414500886090020301682000f10506221080c000d480305036910080e01e00387c1d88001240c041d1113480b04004100540304a402c0c100032001180b0401 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 460193192 1250 460191942 460191947
    0x609061526090a0c0b13030618080d020910050313020f0a032a140a090b010315120201020606180735161b0b1f0b070203010b030d090303080a021207 65
    0x1e01c1600410000c0030240d60381240082510501c900c00e5411b4444036820004030b1500e9210410500180d101303814000c4c403664421b95250b00040d20442c0c00c0d540800d92030300e02e08010406034405229400e015285051104c0e01305900903070850000d101e140180003000998440742c507144002c540c81148600d80182c0014407200308400480c2c003d14030002003900045155050040340b4441c1000f51219101900701411304e03001d0240452001c0c10f150b19030307600919101d02c2c08000001070203901c805604107001032000a04045001d84028441c0882d071160001c80e4080321940398012019040c5038032000303a520404501c20300290780030941e21074000b01080c207030081c04041c180f00c0c10f1490350459902200c0401034544100007960340042c850071440c80400207458096440c1c101080300b0004405c584100129101d004503500086a0a140426442c4c2181002d008444041c00d04602402d0092411040201541c2c12888042c08000034103002c1841d003803466048030100341840605101526215202 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 460194442 1250 460193192 460193203
    0x6040b0a03090203100b0112023a05340207080d0c0b091615030608010204090615081b0f090907090e0108030a050313030203090a0305060a060906152609 67
    0x5071300038020f01014a201840d94819014103e005071a440203041e90300740c0481c020f403c0410f0121031007461151118094050780c94010b00c0d500300d8045442060104841d41055600240034029240b50800c00916020261306030b26004105130490010311060100049161400d280d11510f036900811007800006a40410a50012401031000700c409440e00114140d8403403856902402130150150140f05800c909032610b141c010192030041000c0c0e8aa15549089a001c1c1c0c0c40860240c1d0364480400007007030040207810143d07010381401826450520f070050881010720110300100d840010b00300310348006400540e01856005066040b003441e0901c1d01402ea14460b000d40d00482824200001d1107040001c01c030382e80f40310540ea40700e05680354100b80c15407006015200700c080d408280808542526031b007400c480214010401000e00f030800d0849402110119044050f040781001802c2c4042c00c81d00a40014540261901e442e625442c85070f51581030f0130050450030186880700a201030003000055 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 460195692 1250 460194442 460194461
    0x160303090906080703050607030b12030310060314040201120c1803080a200d14071a01051005040303090b0d180b0a151d0c190216080703080409020906040b0a03 70
    0x104102c01c0c1d8407058026075400d00c038803006104e50b10a8001504e2640b0071f8104164564020f041602000e54200c49070703080d50401c44520452403185e031010801a03926000d000c621207102000b803411400c0c47d800003401d8144c041c04030104280c403a0043c1041910464442149000081d5201440d42d240d04e81811581d22041d180400a210072041004800a2200711540d011841000307156041240d44140c0da076401d80740c124074404005000101c080b910024100e0300d042601e10b088041581042c04020300300d80c3c0480601b007000070521040c00001d40240140c000d46081614107619803080c0700e1404090014008101c80403800c846010b020400b40070f042c24040c0707044400900541c0400c021000c14000c0e02e10800c1e61141022102003070405290444907003042403210003501d002c80300d28120889000203003419006a00c42180c000c01c040d00e01c0d0100c0060f0400c5c1025000151860b12070b00c00361300550080600c070300d60010f4500392550714102210020912102c10380e48400703a460018005110300d0a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 460196942 1250 460195692 460195709
    0x120e19140f03090405070306050105251a0702010c090503030a0e030307050a0f1205090604090216140c0a0803031e10050d0f020103050f04050717010209150702100810061116030309 79
    0x1801b08484500901544065800c180e42e0700c0d0401ea040d001c014140340004943e90780000b114548a40811205120b1941c181184407103140c0904284100030308560031341d2699030030041c441c0c030306010b03e0794044211400514503252907800d041c174140000741035201d0188014030138410000b040d01003107814980603842900601c03d030705200102c9a0b054032180305181d8150b50000f0200b100744914446a03001d806a28420300011003565015614080b52020703452080d46103900010150f1114980580c0300009001003001071411801c1c2000c05c2e0400c201e503060000c403940818400103846003040f900703c600030100146500e0004842d42001090218150004e03400281440300103242c03403220354424bd000f517034414010404a40343c00902000054401c8901445540802c500200381e51030310580b0b44034040301440e055561a00d0300c1080704966100201c0d40902010004115141c415809524100c0b8650300305000500da036240e00d0790800380001c000e9040c05140241c00720925030f22040a105840004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 460198192 1250 460196942 460196951
    0x60a090c09090201091a370e0315180a150f140115030f1d0c01020a051b0d14070315200c12040b030403120e19140f030904 54
    0x1101060240d5040242c06804200100004c01920078401806100381e442c03118414104031203003860069800c3c40290350f40901c503012421041918014060f440048814145024540004004a519100701d028491100481040001e140b0802d00c00a0705810a11800780c0f2800581c031700d4840040c235501d048860329140f8181c041090b07080136215002d03405011107004080d0760f28000310460281c0c0c0300d9008004040e124100e1800707241c2540540c12407401010f818580e1640341440140c80c0c20a900f00090455102c494042e020440c007103600c503484840c01f641c0c1c121b114110004588841c000328401010451012902c608210003c40c1d51020390340700307c43c65131101d18002a26070940d01c40c0b003a098400382d1010100307030400c0510801400c048950406075201200c04542c0e40c44a13400651000307540000010410040652100140400c60f240700c40420940703191b00c400c25644c40200030700807204440420508180a100c0054a80052181c0c003150388000844808235201e17044001e95a0060382030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 460199442 1250 460198192 460198199
    0x20408060f04051c12021804150e0f060415291c150302030d08040308060a030809010815030f100e060c031b12181b030c10030e060a090c 60
    0x140e29070300850f0001c0c01040c1c0740007071180b0f0408090f01a0320030004c5c0a124940182100c2c90b90020b010a9000284158038013101d907410310003035510600c2d05002c0d1700c0d0750400c03e20031803500015498200502d010f4007811603840c18040782c001c0c90340202c0b02040305401c010004880d87c543c1c24061303015000d5151200c0c50800b84000740c1d164001d103041b100c040000c602100080c0285503100d440903080d202004c00741150340b5000300e030815500104050016104400301b0080c180c20907245d6402402c155a01d00b5a9071658417030180c2409a01040c6040141071400300d26903411000300c4192110300201074949200c2c030458803d940f88440c2c401c01c000700d424001d418034811741c0469190303c1150302c80317801c5186a0b50780001222582c44403042c00aa104140310104546511080d014418400f08045000e1000c0e1202c0c40c0e4904502d0110700d29985018509002041d01c0118400c6000d550903103e20110184068090b4090040828903440902c00c0c5002c006441c0c02513008540b00da4042d07245010b0300c0780c030b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 460200692 1250 460199442 460199461
    0xf0906040b1903090308070f02030403150b01090602071a0a110f060712061d09030403200f06092b060207080a0917030a1211070501060f060c0c03140a050d0302040806 73
    0x4015005d00400e80b40070002d51002d0050015465200291050740d103071549075698900d260b000000252080340c3c0d6281d69285558220104102034540d60005101c10303032500b21020b40d040d1205d80c01401c40c540c08a1207283c4140140130440800714044c095410100405080540c1c620b012070320540041c1100000d10400400c510070407040ea00000d080d44084600801150203c04000d0141c80c9c140c40108400008130b00207410b0054029403030301c0041c003206010010040c20032803040303040744a58010885c4251a564031507203043c6080b4940d031450540260250004007600d40303100080e11311400020713481e00308003464008008040454660076541902c9030b6111040350600350340001e9581c02001941080d50003501d06200c1c12885a00c0401c5001c00c462200c07a240e006040e007201d85a440300d0091000b1004101040301500144c40c01104842d16134980710381c0c4400a01c03003d0719450301001c11040058091010340300c215005402c0350f6403036291001c0280294441d00c2209428050310010825509 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 460201942 1250 460200692 460200701
    0x1050406030c0905280c08101404090212070603050402090c031b09130606110f03190e040f020a080a0c020c090f0a1506180b040302150f0906040b1903 66
    0xe812501c030810042c03c01e08400001c0001429000013100500d1003010800c055420400380310b80c2022006c038810103a184013030601e403805804070000c0c920000b4240840091122443e42103101240d02003907007120b03400446c402170715241c2103410314000c0d01c0002c0341d096090307045240500e2003a1040c0b80785564182502d94030f800203031001c2c0d490f40302c2506040421154400070303010360140184855810001200540304403040c0d6030010303021584100c502650620b0601000601c3e40c40d00d00510714203d1018948080ca541c56200719060110034405d5104030703100c60780158101c0d0b5500f00110750303441000701c000d000340c0301c200d50000c4c000d42000700107401544080f440000c6103001400c01121516615842c01d00840700038440c2200d1a5240c610300880d01402e000e8034010702c05900c0e2120b08031165407020100210a800040040c103082000308010707264500d880400c440142c0b00355850f07900507900c081c8039100e50000968000404140801c40c640380c4c500911800b04008a10b8020102802c0203a0a59 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 460203192 1250 460201942 460201949
    0x9070509092814150f09010b0a05010f0908060925060c1e0606090e070806011202060a02070816060e18060f0f1302030403020d09080307110d140f010501050406 70
    0x1074201c0c1101c2c50032290203407400030440c8948540200d202d6842d64051424401c00b40c45818a002e20091008413003856114680007070240c0d0003402161042004110000e425200d010704200e01c1d940d4030754501d44995003290180c10a00f080e1000d40c100054080d030f44045980b141022035400700d03000300040095201c0407048400c103494071001c801290f00c51415500320300402030900740910030f40100185681c440ea8000d0312106400195280050980905c0c00c18150002242a03110310010701c6040303400d440c80160990704443d41d664410007440e04900704002c40e40040b4491007902e4540084094001d00d00c41641c05907a076064800f800802004603500c08042104024680762010a0550034004001c1040300c101510000c0c2d40c000980115048000311101070001d01da0203c140010550b0520500c2145000b5244c4801243d040042460b2a1301c100304004213005d200601070350203500c94410307625005030400b5948100e20344131130320700f42c13541b4410084240d15403802c4d0000c10701c1d01e018880d85094 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 460204442 1250 460203192 460203223
    0xa14070501082a0c0303040c14030a150e0705030a08120c16030e0102012310090c0f11010b0d031205070828020f03010f03030f0206060d060c0e090907050909 69
    0xa141100301c2ca05040340415000381600d000400943c131302c0c200d00b08003c6010700c0c0b140300802480f074a85007803c4120690706281d248203421140401000c614036020100703860404020014000402000f040d240c00280e45c41b03590140148041c2c1c8041c080b0560203442601820303c40c03a010f69a603048900e0360380c0b103000518800d881c04070040102191140c2c82203966000d06000004211a062220290300348501c02d002d17004c18800010450090401d404110080c580c0c00c4007403103049603804c0081c03c11017000e000d101c108440503901d6015000c0075005103010000151480c00c1c08800360400a010241116003889600d00709004034420b01e1203104014814824a510700528041070346610320400784034210307501c00747d0b001d0280c07089800c007003001140200629818a00c1161442c50040c050521081c00701d01907400040c20880a0784030811102031355a4400400540c81000c10000d4951103e03003002d054120441804004960740c1c001680001d48404a0320751011742c2e2034001942d917803d010311641c81c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 460205692 1250 460204442 460204471
    0x82a030a0309080c19060c0c1e08120f030f100f0b0c0c0909191109010f0e010b03040b04060b0414161106100608060d150b0906040b1e04020c0a1407050108 68
    0x1403441f075580004583d118520071303811240d5411801e00300780c00d1075010142402107000308100e0101e0401000900f8001012150b00304104681902064000103110290002c2c00d403000459083c1031181d148050000c141d41c21861603142c032800741e07a540011440000520500740032401ea49803c0d51114030415203403005088881c0e07011051a00301c080345404844407004050300450990360400154041c01c2101d00c180d905a2400790109080207042e030241448500410500010540170103c0d01d07440350f00032001007060604000468014550b48050107442070103c0b040c0b10008107a0084c3e03030055a6141c1d0b03911480450044800c2d1505000e5880c07104010103444100105402080d0040d030103180104131680b0241551038042c411320f081648503241e9070740d50142d0140c03864440845a049081a1410011006a01c01140f8030450380029003010b100c92800201c0165500d80454415441502c1a07035618036051514810160048001d02c0c4280540b10001c107103948210f010350300c500308003040c51070b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 460206942 1250 460205692 460205699
    0xa0914091312030b1804060c050f0a051c0f1a01110c0f0316030c031a0105010e09091e01060f050603060a3b0f0a06082a030a0309080c19 60
    0x800c42c040b544088400e05480d03004c03040e01691070000c071503902c03044c04204981d20700d0a85020001c0700c01c4800041e090040510039140c1d203852000541d40c13140000e080503035032980c3c1010400c0250301003640ea402c040b810311001c0400150300b038211308010f000c80350014400c000088019204203150841c01c41c1a81c1c0701f13a843e0b1038140780641003284080c0e006800c0e62804500124084e640304445d810a0303032061048503040040020f1000084203407150580c1010f07807941003a00003454204010301d10303803145660101054071001c060003c00c24822111001d4091001482d0b402c45c0602000d10072804851414003000400e8202082203a204180042c50800000c0c1003611400964000401c1031016803e91f0310102d1410087c9a0f04203212551a21000142d02c0c040d803a00705018001440100f4260900c1c100300600c2400080081550782400311052441d0800d80c01406d86265883d400c540c580b160485a005140d0042203900071b40f403107c0700355281c0d80c04000510551070759600c1c1c2a2940040c00380b042 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 460208192 1250 460206942 460206953
    0x109050c0114071e12050703090e0103150c0e030d0f14030103031b05010e060f180a0c090c120609090c2129090105010f05270402030307080a09140913 66
    0x400b402160744030401e0f00003619610022039a117401c0c1800b150001940d0014560440d800c00d008050840c16050290304555502c41555101610070b42e03c1e07a290031160582ca40280d10007400700c000a4115450440c840c40b005203003048803074141c07011034072032201040280740d01c40c110780c140c0e42c0503118842805540c515080d6042022082543d9556030f80d03c0a05600030203002042c0202c000742d015801c141401005103e000e02c0c2d9020240c40daa2015180b000003500700342c411412503e8080000841d09503440e003d54015560f0100d041000d131034501c001c29948041c1e03101d40d400c01d01507286c40c080e03075864440f1080d102113001c0302d48244600001104001030000c50107503550003604020010b60200725004044032000c01d40d1903510700c2e5154001031002000c4546000001c102c11245100c1c00c91a00403a5102c00c0c511089504954000714000740940d10200111010a617014035182d549440c960b00080c201c456500802c0c03000c082c0350a030049285400c050442c0100c064884c6400c2c00c400c26983d1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 460209442 1250 460208192 460208213
    0x919090c14160f0c06030f0509031801301a01020a050709020915070605160c020d0f03020307020303040306020c0d030905031c0e0a0602031801020a080c070203070e090109050c011407 80
    0x100c541804003c42c041c00140400a003800810a989000c948002c0107108542900d40052014071035a1040c0700000060300c0412000311503410a0038504004004141104100b1900c081444405120002c0d45140b221b034581c040b10142e0401e038188800c1c11040c02c01261903880d401406400380d40a0030050003180129401009112002031480916103913002503000940c20000048c0c603150b640310708124044801c50801c0f1200340061424502140f4140c0c0007881100001c4d070041c101d0113480070442c0030180200f00311125a60002d04898846549181103400395110859000c000d0040455484282c4d003e0f00411090301c0c2c1c0700740510b0401d61a80004401c0e0f103144401c0703510351a2110344020381c110382446000d00c954003400000d03960386800b407000c0050000c1e248058205070f10400c50940d40a0b84242e0254220041250301ca6654541d800043c1c9409000e800c4004426169018407841840c150711942d030081c0b141c0251030302c60031118010f449403480c40810b41c4004000b0030030b941c00102030418 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 460210692 1250 460209442 460209487
    0x30803160e040504081206010504050a030818060705060108070509060a0b0a030615170f040215030406140f060f09071b1502120f0c03040c0e060103020919090c14 71
    0x101a25003007500000541503500c00d45003520074620005542c8900c03007111030b0841c0c0c000d80a0900390314040c582000705111500501c006003e42c10045154030b100c040c1c01e20701d08001c400c02440192500c000381006a142c6100f8401c0362075501c1101c0c0c000820b400c0c01c07100b480c801c00d8000c180c00e2034546014011040c550100c0003640c101a660500820b0825011408004c50b60655a030802d868850902d1080c00d901c000d00a00401ea130040100030050340c1c0c1c080d040c8600440320715140c0d22902c5619110025291f04861000502e0126040007004a1401300007071260000f00d881a019160340c0e403c0c4924414244c40b29400501040001c1000b200c0c05142c02c2c00f0303107101c0c0d071040800c8240c0803a10801ca800010345006002c803490306000701599400c000c145c002c240b00030481c0c40e504040c1d0790391010010901c624001c4031011b10002d8142d0f8003a905444502501410030041080c14100880340c08007913004010b002d43c94256481043c1e4030070701c1d3350350920202c04003481c90007e5862105503601144907 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 460211942 1250 460210692 460210697
    0x4030e03160e0a14091216081612050304021f0e040204080708211204020a0308121918020d170d020d0c0c050309040b15211003080316 59
    0xd4a140300c40e41c003510444010030b400d0440c1910380c01e1100c5100150340301101591540b9540e4024041c4242000c503c003284044004031856440071800340b01c2c15400382010b8083c10040006c100c2c01811020003201a05151081001c1040400c05d50016074441c003050310041e41103041008010005880301a4170f1400d4140e81c10000d04641815000070140c0e4015008102076810002041081d047c2c00c000007480041c0d510500c2c10210300e00a4950141e001d540c2c040300785c10011902007400e64541c0c20215000d503030002e13900c0e9920002241e9101c0c10800503640d900e001601e800110848040030301c140e07041200070085d00d14003009640c08204880300c0c500c0e025940400000500784050201c3c2000f060054140c03d0b015032160840f5080c0f200702c45c00ea41684080c88040107160000410201c221000b00c030044600184042600c0c0c007080e01400e4407845610784c2030000500540d510382400c113460071680010056915a5180d00c00890200d40c0e910000b030000c3c1c0306001103090381c08001c107501d08010491 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 460213192 1250 460211942 460211953
    0x20307091a1509040218030105010e0c030a020901120c02030715050c09150904090b010e06010507080d02030a140a151a0412030e1c0b0a0c0503060f0301020408030f0c210304030e03 79
    0xd400184c201d07448005604070b10f560040010741103080c20302070305005089440d141c51048c500ac8441035a1032100a01c1200c00c12350000d45500c180c2e02940707141d038000e015150304020110710410065505c2d0700464043d1000c0304e4040031401000d07054003c0d6807080c4451404103040c0b07541c080902210300341d1002230041190080c0b18545460f212889282d002c64040c2044031300c554234000d07805091841c0684140c0c10483e0410021000c2054601110700c1e80c04081c6005940c0e41e10140150000c1042d00b110f130407100d100340148115201c0c2a000801c0c2000c3c058000700e42c682d40e402405d4182c94800d0b601440040d014002000350200342c0315421050340c001d003040324411038a140040d072034540c540d40c030720400e40c1c0408011041c0800c51a02ca9480101c0c0101040282e0003c14007408502000700024855400071411850380d440c203405450080031070604507522003c505e2108900d5412090100b1074900c204810343c21142a9400021102803100012070701e11780700c1d520112000401e0b40c00c0c103501031080c07 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 460214442 1250 460213192 460213207
    0x6030c0c02040509030703110102191d030d11070501030e0d080705070803190b0102010e06041e05010f02090f0109030c06050906040b0315030601060e010210020a0e0a0b07020307091a15 81
    0x264003c481c41411640c003c0c41e0390751150314024100b14042c080800c40c0b60310501c002e44c00311501c09a400280c0e070090415001081c41842e0503030545e90115403c507054040e071010707113070389540001411b24018080801d4600c6140c48000441c01c03a205840d1302d0503190301c070030049024580581c812503049035961600038a400102c1c1c440c41da1980c0300b940c2d6141071465003a1114136002d0188648042004244000d000406003e90000c4c0c0d50303100504003800041414040c0c1894402803c2a0031403164420000e0211000c50202d0320000d42051000d00d0240d50509441c001643c45a000340080d2030303001480c0380296042980c00c60f81500010000741d009601004042030903071908010314440e242c03021001c2c0034036a400051504000040c0d1100c020b002007050b00c5115a0f80200e0802d00c0c4200c04000140c548407480c6084940b015460300854111100500128580360000000c020503402607040f0b0700481d6854420008172a41c0403500c501d44840c00c01010030b0b52800000303070b00072210441c0784142030504 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 460215692 1250 460214442 460214449
    0x2031b0304050d050d0f080c1b011b031a01020105091b010306230a0801020a050f0c0102070b0702070801150b181201021c0f09050c1c1a04060b030606030706030c0c02 73
    0xb04240c0582d241d41c000c0c0c0408103080d60007460b061b9141d0341c900e40408a400c052040804038000c00781d104500003e082140e040e401007d601003000692103000c180103410111a01034014882220f104003078154413400080386500500850703009002c0b40700102044032000505045618000f20310034101a10ba480c0040c2000414070341c4091a00200c141040b0001007500f0821041e145070701c250702c030307900620000e8070041d00081651074801918001d5661481c0b0b44580d14020310402c0740040251031140180129141c0c00180c05054400420080004101c02c5044100600d0144a00c00003560f040165800d05041caa10b0303003d5044e4090b20581e0350140303d00f810703426030708055400c0c600d43c01d07540c02c440540f40e60b600941ca1500c0196800b040740981b00d4035210780303c070300301d481c414010040011050344050407100e059076100e8000458bc00b41e0043c1c8003075521502400e031819540c0340c4c105110700e0301524000c01d501707001d130390000c2c01441a58a80380003038000c1c2c000402000140300b1425410300160702c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 460216942 1250 460215692 460215709
    0x11d040903051c090c1406130b190309260706060b0d0b04020f03011202150d0b0108090f060403030509100e0304061806080f130222051602031b030405 66
    0x500c02c0d01c2d9542c0350000001034418065a842c8007411076810100590301081c04808a03c0035036002030107103415080d51002090309032160408c841c0744420002d000240c1080034001610307003c810000b920002d103440540460a8808564019007950b90003d08000030300e04c8480460044130780c0500b0f2a08210752510303140221000c5078030084070a0000114a0015006441486074901c0c1c100c81c01c6003024100c0d000c021142c0414001d5550889010b15250159504c90715424601403510f0703250340d0340d44140c0142034040c04505d0300c0d40740800d20000104615810104010440c11304d4200140b031070395265202140500000350100f94103005d00020704148000d94068640400c2d800001550340c6c2d0310b0b00800030100e8089034580c42032110403210034815641e00018081c0c2002c410a603514032900c454030082c1c030742d400a140085d8409080380b01d40181011050350070000c2801d0f01c00c2001a69202c03105c40086424045403030005800c10000d41a00441010600c3d008207058821242441e0325030780400c83c0e06 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 460218192 1250 460216942 460216961
    0xc09040b120607020d031401050d06021204030c020f09090a06050a0b04060308190806091501090b12060301050906060d06200301031a06040c0f030b0301110d0b0103060e070e011d04 79
    0xc0d0050010029540d4041100701d17180700d25441c003040301c0501e200071380110110600075184602498140301d4181b0910303805840c0d1011b44c14902a9560030f1070f1070060400100356200300e0140100203204040761400c099200d2050212002824210225507070344002007800404c0c5103265903032246504059203881c49400061440b808800d551034030403241d061030392551001580104030a8104200b46911b030001c220b60080c00e601e209160003550480160780c0710b80560065422002e0100381071822442031840940100d42c294003c00c101d860707a001180e19103001320740c026000001c404c07404c2e0004a80383e22841500002c1c0d000c0080c5030012001e200d0440d40203a006a505c6840c81c545c26040007640b0300d440342c1101d802c46040001940802c00900410652070300f40c800d1595400800003562001c1d040190128000804940d5440880701d84100402200d03003841d0010785040d402041ca103020b043d0040c01840341340c440e5030101408100459106030f004170845110000d007104050181c96501070400b40 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 460219442 1250 460218192 460218229
    0x3112b0f020711040b030a0311070e0736060e030a0b0408070b15030715030b0907021e01051902070804080a05071a0304030c060e0a020a030c15080c030c09040b 70
    0xba140715040c5080c03042103600156100701e18203d1103170001d650000e5101e0110754142081c030780c485d03500f03004a42003200c650b01c06d8034841c00f02d000b00070350f26510120401480082000c070724001810304452982954007003050004145464506011490160350140741e0801c000703007124100707807140c1c2d0741505c12681600c0c01c48030801c0c0400c411041194803081c03d0341c403904a45166400c01c03000b0000a0340c40ea014800d442a040001c840e85030f10501c81d4111400188014000484608000340c1c020f580f6040494170380c2d13420407520704040710910306000d014000e001c4100003040129101800301c1c000d520142c41243c2007241007000080c035090901a140505002d04080c010302c4c0c0c0f8003c40d44181040072102c0e1b0300e58180800030400025040007820003512b4000800041444014040c580740c00325502000c1d5000344540800010000030500c41025550764101c42040c0c401421800c0d0346e055025507440018500600028004210340c0020f4042c403a0001c201040c161a00000700300e581d03100c6048201c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 460220692 1250 460219442 460219447
    0x408070801020d0e0d090b0a260a051f1806030f060e0705090708040f020a0816031b030302102004141f02101d1509060703112b0f02 58
    0x3d80300103442001d042c0042c040c00b800104000703c400405440f81e80c002d0064007900403510041c4a0310a02d00e1101180b019140755044001078403168813241c000b1507420107030ba41090000383d29440c60f0500d440c3d01025892214002c90b08140c0d5400c03000303030f00c1100800c030344e6580d40000011800c41008119074600940b0000b8100704800c00950078603c0c5134004500810304101030001013a03000181d41d5006801c440b040c0005e404a02c0041c002101a62010400740720720f8450780059041080b824089030700c12101030300c04e4031101101d001c0c408901d110103405604001c440c10b500380915004030700c1e032900c0610000d0035500841610103960b042500080030781c0401280e2200d05080403c20050388491503030001c0d04010700c105e17000355140508a4601c03096034880f052418408411b103144540103c90000780c9020840e44606103c003041c00310341484091080e0b002040c0c0c024001e114809559941c1d0004916010703408203070861034110b10344208803030180b84140180d041018030400d041e800c0d0880c40581d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 460221942 1250 460220692 460220707
    0x30408070c0e0a0c02030a1d04150b0d060909051c03020c0a030c03030506040b09011223032709010320100f0e06090609040b0d0c0603060e0106050c0c06090303040807080102 76
    0x804a908800202080d51b01c00c00031065403030740100c4202031108004800c0c2d90481c03040e00205014048110a450008038988004107801c00584050140440d402004100490391107502c10240e070403020000c0c103d50001d0701854011152a85151106683c600f4094a000b2038245010700c2c0c500012001d50010700303c194801c04042e8503010306504810300311000c0c460f0351000340000d105110107121304000c0d11282d00003001006001c3c040d42c2d140440001003040030044504d0740e19202d5000d0b82070f03400b40c0205140800120b0300c0290010f55221805004101541e0841c0d4628080101c01d103c1d07490010740000d501102d0343c0e42c0113800c2100f2000c0e60340e03298a412800c0d002410001000c2d005a21601040c0614010750703d40c04c00ba51005c08d0101d6000c03440d034140b200411509140d41c0009403000b0b401382c0e00814182d4160300710f00b0803284103a00c103145581c0d984000f101c2500503690500c609401020501105140c240d028146280c0c005080c0c0380b4150351240301c6881c012041d80b00031850f94000c908032 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 460223192 1250 460221942 460221961
    0x10f030b01080d0e21060a1a060412060c030608060403020d0f0203041202240408010509060606070b161b0b090d02030903250b1815040812030408070c0e 67
    0x1074010950980100881c00203501d014103004011905680100c40d03111901285c403416040b0030421001d03607800d4074241c2c01e0a904100c064215250803001d0014060313207582041c1803400480c0d048031101070000c00988501d0362440098824500184101038a4100c08036a6440034414180958465002004180e60b1078074003500e4544296030038015134006010400080324085150910709a0465200f0400030002c408100a08580078400e100100c1c049801310384170405611141c0900407003004c80341140c1e58602005418481c000c0c00030203030320301000401c9841c40c505104a0700102c5a00b0703c0d4584041100d00c03c88200225402034035038a25100500ca481c020603c030403004071119101861810713540d440825910310200c03200030680c0c034041000300c90204005803090050061003d500e80e07a0003564401100c1440080d1a5034411a48094241001c0719440c00712801c44044e5405016164150318000c011908010000d6030080410004030001410140071000a420544c1020800e8205007511 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 460224442 1250 460223192 460223213
    0x120b0106020606060702090c12161b0c05061c021804140402060a080703090821061905042703030507020609030708040909080d06060801090f11071712010f03 69
    0x8602590490403e022003602d8070b5084610507a01a40d411809072030744071140005103c0c1341101c441c1c0d50b0050080c80b50b8150b0709503e1290b050312551380c3d040c1842411560b001250080c603030042440e0000c0b2010491820280003418441c001801c8007030f40107090f114500140d03480039a0411075003540c0721412266140c940b194041401003205a50020319065000c02c00b14855000c201090100c2c0c5d000042d4880c0c800c2d000516650b030301c01c3c0300c10f403280500401d407184000d945900810084240c0c0003e001c0741000c0501d840507480031610689013629080c1800020040312900004900080e83c1c0303000e0302583d4030701c00440d2a200e940d000816240002d0b009050002c080c14182e620b0300100311000102e00d40c2403d46e030039a04901d5000800042d1450440003901c00c0e82145a00c003410b00c0400101190440d000038100c5003500020321600129030207050840f1040c0300000702140b018800b07540421040c0003c44402403a80b038400f03251111610901e5100e038000da1201301001d50045040c010400351001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 460225692 1250 460224442 460224449
    0x19020307021e0a080c0d06181707140606130c0c2102010b1207050f010509040c1107061103180f0a1403010c0305090d0f0203040b040f030c0510080a0902030c0a120b01 73
    0x117464500c002c0c50000e284031507203a001502168983c49840310201c2000c101c40c80c00e9134002000283c140d180c0007240e205801050302034400c00081522030450361808540c0610800000300040240d01c1140c2001c030003000c01c4030340c02c01080004120303c0c0c0051480c541c02c45040c800c118111048038100c4000900752890800c805d4040c030b42034100642d0b450b030300085200c143c5200301d400c40703445408007004850328040c14040070303841400c10842e0006550003480f001e80408984003684c007115240c03001500e9440702800c00d12856170042140e04040741092069281703002c40148405200c81e0321700c0c0000d040c002c540e00240c1d242c040541c1d0340a03940c42c09104410003192642020301c0540740001050307455122500828050012030b2011280c00f034404e004540151540c04411a125a11100e03104500ae00c94001114400c055200104076450442100c1e4559585030350707070070140e66135009940c01074940282c0c201d8251084507582800d50388c82041903005441003d48100055046007001c1d10f103083c0603030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 460226942 1250 460225692 460225709
    0x1002040b1b010207211e0f08090307020d29060f060c16090606170f0718180507080f07050301052803080c070807080319020307021e0a 59
    0x220401240d8040401d03120310981c01800000c800e07026410480c064491144010030356010380c0403c0303959960713484941102210950750801d0303815500242c80b05c913000050744d003800b1480c1c41020509107071003010159072180c1d8100660f41440c030180d01254410203400382c220f500a1103c0025603103012203181c405183e11400d0701c1c50a803414494040b614480207a40424024a0001487c041040c0b0410a0584030545d5400c01c00303185a81d44154002041140100400100444542e1200d041c44450160003042d60760160003c0d511840340681f110f006c04000c0c00400106200c00282c103d0f208005003040c20120031011988d4541076200030580c2d20020900031034050618140704007641d022050320f0541d20203407090121200c0011000e5003484005024051f8909410710120030440f013680685007011a010071240120303200d646482d100e10242c02000c0065005001c2d808446010188201d444106030050324a844019008034030250080600b0041448070840c082249091040e0b1903c02801e010 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 460228192 1250 460226942 460226947
    0x80d0c020d02010c090e090102220515070507050108040203100507081006051602060a170c04062604150204210c050d0b0f04051501030f0308070f020c011d0a06111002 73
    0x2e00c03001e0106400760203642d594510034000900d1f201001d5040315034044000110070480103c21507880b44100351802081c3c01010200c100035400300c8034900f0346990692101c0682407150400c1c004540d014002032080c1d074140314000c900d070b102c09080d01c91140501e405070741d0f400b4545064003810404409a034000410001d040004510743e040180c41c0d01c035901e60441e100c99440180c1e40c000c82e044245c00c030010302018029410701c14250010801402100c00503129403104280c1e02d022450f500c020540094130f0b4540c403400081c00100050460240800e00610050a103074560842419402a5010b0a080d0710080c450716401e002030098514014802210303024200c141d181e44841d00080d014000c0e500008a2500ac41c04101051040d80d04016030a161080305603900c3c101946000842807080e4045140a004101500d00c5245201c00002042e00285800c5106400442c0c3d90b166020700d429504000c0d44102340c0559400e84404000d04407a6160003502202a6080d03003441402c5088415440c1304 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 460229442 1250 460228192 460228211
    0x8040b070c1509181d16080601090501120f05030f1812030a09090207140105070503070915080609040303060515040302030f011512140d1d030106062109080d0c020d0201 74
    0xa103034100e41d0344ca15907004a481d4200e0007207000b450900007690075042c06020741120b170002c00c00d00110304032803248046840c666a03400303105084a030280500e4080d1014100401c0108400088144c0c55a20410440f850a0f205200700030707440e001001c030305c5940520042c160006141c11000d550b40981224051403400412480250a2041d02d1040646458010502405000d460550039080b03c0d0650000e105030711700a10010021fa0003212a840071551001020462544044000c03103544038a807280c0500741c03a56003c20a500d88018821001c06458a00c0401c69403111012200e0f90301ca01d40f0090b880e1411407042600f0100d1a00709103005030324054950280c50301d4400c861044408420744411050340c1c40c20100c0e01c5079266052044a031003a084104103ca038400c403408950031003410102c038002d0083c0105402c0e5039583c8940f400181c038041160603007006901c0b0022001c44080790008040c8615519003181e5003007081e0f50103030070380d88503100044a40c06000c84400340601d84003c020000c2c3c1c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 460230692 1250 460229442 460229459
    0x81905130b07111b030a0c0305070806090c01050703120f060b091002011a010804050f0102030708040c090902010f14071406070306080a0308010b030a2c01061508010e0408040b070c1509 81
    0x882100781380c20000e0010b401a000d03142440003240103a000b92104200d1030f100c1c10700541e40c200500c0b032480d03184201c10009510610100d500d02d001c12059403040e01d40031240c1c508642040701c0c40f4400c0000f5503917090710310b420742d40c0e48148801400000341c80358680b070200c001c011104814410314410340e418040b000301041011480c090011009081500560b1560b0400303515101c0f0000503134001d50310004c180806a5001600035124600c626141030003961a0000001030314134485009010416040d0b1140940e401540484490090180340e45d0408007913417104003041400b42125034158001d05e06000030240e041c0121400f5000c20380042019034015074000342591814400d48180f10000304c0413800503030540c0c201d0b00f5107120740401000801010038803040c03021144200000d5179880e013640001c1035200c1021018404441c0d84440030079a20344102111004030042040b20300f494100404103145408501078244a40164485c14095003410007052440c11010344050a011007614200403044 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 460231942 1250 460230692 460230703
    0xc03060501090b04081c1403131214030a0c030e030d02070b01080601080706050f13080303060301140603190f0206070305041809230c1309150e030901081905130b0711 73
    0x401a1030401b07801c54110030201d03001d10801d020a10403e200109015031441400c11160341d00380500d014500c000c0c69070100782c81e1b0901c803070140301c54502d081c40050300b0121241d2003140c0155603401d02207410700c00320400a05503440208d2001c0001e50205484060210b031600e20b45c00341189400400441d4104000c4c1540d48105100e48401c001c40041c107c244505800191001e005100c0740c0f0100303c540756410152641c00450f500c80c0130358a040203403404104080a4140507000103070241c81c080c1c41c080020410400a0002034032030301c140492403001602c13240d000300790341d1b4041c0d901e8030741780ca04110441c400810442c2c1c8000340c2c0b40c14811440040340d101c3c0601c201842c40e0b462036140c003810f02100715080640b00341d507181d8004016039030b1071000107054002e200b91f04d00c550104401e00c02024800011201c00700049c0c004c41d401070003400303c55401409620382082c403c6002c010544095041c1c00d060703e0085450a01e844081c0901004000405403100d4000382d203800e08800c0228180b1130710365500b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 460233192 1250 460231942 460231963
    0xb0d1412030c1b03070b0103170904181104092a080304120210020c030607110a061407030b0301110d02130e01081f05040b0a050703060b1306080612030307030213090c03060501090b0408 81
    0xc1150507507180e27103014908115095154040c10501181c198080361a0316400c40310300503541e00c988950034440c5440c01e8499070410360707030001c1491811a1522403805013881d0110105000c280c40100c0825807001c100040c000a0005820000446407144144100000c09940c543e0640d030040d42d6800780d41d5004220141e08c4101458140e04901140a000d850b101d14200d002e804503180c10040f04420100b800a207204102c01d40341408034607032000600d4200d640f9004d500035403000a010a07015000d41e070300140440c40d43c5d60b20380c400e0140ca880c42d41010040aa004014903400081f418a611250781c13084143e003008608200702c9441d0030b494104213204d0050160f81c01c0c650f1200040d6a182c041e6000d90090001c1030501c070b448160030260800c03107040b140208030119112030000365142c035005c000d440b51305812101850031901d403148150060341280c4040c085800080d0720100d20300e5540d11805145d2100c5660104813140342c50700141418100360081800700c2010401889a07000c0040d00c1d5804 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 460234442 1250 460233192 460233203
    0xb070c0909030504031e03110f1f27020307060f1e0203041203110c30120d020315010504120201050d110f03070207090b0d1412030c1b03070b0103 64
    0x2100007030301c0e0840e22441a0f40004094050300e201c0e03103581882d5611a5140684240c07140030307900c000c50351007a03030b00c54026440302015401039907502c0301440e900100600390812610003140e1b83c0c40e01e4011480d0b03041c400e54100c805100540d201400d41c42e0401502c0e00034026400c20b000305540021005260b03000070110001c504446c42c50040c0c0c0135200b002142c0003070801700c03942c03405039110749030003440c81c0b050340c290000b144680c400140d050314045042c0c0701d0b0780424440f121680c00020ac1c1000000e46003544008280c01400d000518400a100003030010300ba90704d10041e583d141002c0700d4405840050305481c10014140000e01040e0710740100004120340900300b1944410b4040b50700005482c2144540700680d001186400e50302c0fa1f2480554080d03807882d003c0e2202c29440d0400c0408441d07940d80a1a88850b80701d03120004180842c2a901c03404003080c043c1c4950079101d1464a03c10341c400d9a0401c2d9a0000046090f85028524540c03c444411b0b80d024520706142501e81845200060101402 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 460235692 1250 460234442 460234451
    0x405042d120f02070b0a050915040f0608040515010e06030f1b0d1b030c03120c0305120a0e16050a17070b0306061902010c080604140a020a11070305160b070c09 70
    0xb405000700000c00050a44c141c08a070741354210300c8010529002075030f082d4010040c00986515209424094806030f8078642c90b00c460a6107000000c541d8410050301c10b49040c021038400c039600e150844400c0e4080d21400f001d5802a0901c0c2c0705242c50280384001e403640d03035000803400195026140e08407003c4044120b510407011021403d003c240f880c00c011929242001342c0000004006404c44207c08580c010700d04510002110303101511034405d280c40c002c00145041101a03050030b0790101341500805c05502c0064554294011107140620301c1c291400230240c0d080040200e03207010b8202c44040c101034259044c2034404242415914005405100b10140c0044001051622403034161620703040b6421005505440c400c0001e402400e10005c0c40c80001c1c4590001501030605001d49060300c1c40008101c0081e581e101c120100a4000d04290f038200014250600c140c5503082000501460281002e804c0580c0f00c2c1c070382190305c803d4661007038a21100030b00c25440840e001710900c6080741e204c51000328 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 460236942 1250 460235692 460235717
    0x50a0902030f060f01120e10110a020c040f02090301050f060a05010507021f020f06041202070f140103150f080303160e061605161805060a05130b0f0405042d12 70
    0x25000110306100349035887c5012032116404030002448805c0c556460030030050502240c8060669100d1042e580380964482d034241081418541e00c84036506103114801403c08241c10300090a441c0c023a61910315149032507043c0301c071038070744040041c005040908046241511603070115807111842618014034202c0381e100c16050a000f440819100c468440a480280c6040c0c60110580f2240d4061940107114401c00890034181ca00e064500340d40c01006000302e082c21a42c0110090a0b552420080c3e82c10312000010f0140c40c000c4150313010b0004032000e180c4030301d40000714083c1060350352880780400480d803904e030001341c45510171180c05000c06850b4411084540c00c00c1440c000180300d00d1541c1104007400060348104180c1151744981c2d090000788120f482d07001c200901c0400c0c500444d0307400401c00c9000fa06448840c2c0c008207520380f01078007004a1405000024007150001c5900f030340c0203804810724202041c2021480d241390380a0100503204089036441d4050b05c8041c2c510b040007070000020300f81d03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 460238192 1250 460236942 460236947
    0x80a020327010909090c09180b01060306063e0d02190f0f080403120503070f111c03090c0f08070e0c03010b0a020a0b100819200105041509050a0902030f060f01 70
    0x480500f0a00c41c09108004010741e1802042380003a400313071540c0c5040000400c88501ca401604101c485d00e64070310070384411ba9800800e0101d0300030311410428901c0c0715002c00f01c00c20410304200780382c0b0320009014400e541600207400c014444118003100240311580400144028440b4048260005041c292607407040c50302040510651b040580055800c07980c410f02c03150710800841c8107002c180d4400c400044104419903811040166140c0a6000f2600980c5c02d1011048000e51002072850b000c501003030350340c03101905204140c118204220000b0024040ca100c1002004001c2403500360481c00c903d000b1000701542e00060007141c41c854800030781c8030040f0744200030018019400002540703d078100106400444005803045141c1806219480c0035600340044030b000540b50881802c00450f03146003100c007400201a031340a4140801484007040e1010701c0b40110690020700e49448402500388010020503941c95840220701500400400041e0f01c01c050030150080c4003582c48812120724900103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 460239442 1250 460238192 460238213
    0x7020708120301061b05120409060e1302091f1206060b0a0207120305070b1302040e19060507140307230403030e0d02040b03030c0714010e1e030a080a02032701090909 73
    0x11b0650300c2a90713868103510400c880180104c9405040070041607a654001503045c6008407900c2da44185104100409400c0a0b148568041c01440b845d202c0200141c2c019007102030a07800250800c0b10a46106040010501c1441c01a02c040c00005040c40b80c801c0d0300955880e0203008003840017000c0020081054007840035240d100c0d900c40c0920034103182c020b0181880c2c1003c0c0c83c3c03ea10543c20000c0791044400301045108081010110900e6242e40946442d0041e240181959003007107810301000c3e0130704900c600035500a14003962030030046420200705014008003600e20180034a01084108000f03500903c50030380900040e2003e01222005000041c021306c5600036558260000207140c1f009601e0102d2102c00f40c820300010440700301c0e2414011160009462401d640002e401c034140c0303082404600804210b10001000c0328111101179503100c2090b008144400007691020600e140c00300320614101a1102000c02038500c22030011000070080c201500c2200201d950b9440c00a00f400081d289 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 460240692 1250 460239442 460239497
    0xe0127020f040b090118050f0f0d0b090a030207060e0a03061d0319090b04050901061409100917280317130c0806010b071205090a0e0702070812030106 66
    0x200c01d444590303c41c0d03400310a0b84140003c0f40040e400340d032100b809102c80d4950006581020b481462a0003801e0180300f06000603108451303100b841420308a0000c2c814440710382c070404910019200030f8185240180c9080802d0704200c040c01604950b900650b1030b45808031045a40090b80810000c880140b041d40f04082014454042c1c000003e60508007049071615103200c40d8681c1d600296582c1e100c040401e28048e50180c01d50000c1d081004105d028030801c0148c80320115801907074030300507a610011f0303020b008410601c004982082c804000603046142c0c0324191503950f60241c0301c140384081c0102940700c0042404c0d8840103010552506062103100e0082903d84100205440ca0a1180a4003007002003450111101c10301d41d90080703601c0401150140c101c410401c15036091015682e51036103901e00d484103074000c010061103612055614801ea5000030180f08c100a00c80707040480c4000d040103e150003404856100c203580002c12412042104d044983e2403500b0118a110403003895541c040d46103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 460241942 1250 460240692 460240717
    0xd03030e06011509300c0f0f0e06041404140a0209100905090a050a031b12110f070501080c09041e230603100906020d090609050105010e012702 63
    0x8004640c0c0603d0400a0410300d5068460812141d55004101480d2160f003a13805c0e80d5440c10000c0c0c004442900e41a103091520030b004081849448010840b2880c041e80d03c100d8800c0ca5070f130000c0000e01050012181c01c90340a8409102d80315200088013038000e00038000414910a5038801052030409004a050007680148500401d040c0b0200c01160000a0301441070450f14140c08581806800590240c20540c01400b4100c4c0980c82d0300c1c140c0e03503d00005a00d8103015501081e41c0700141309030100103240115030322540304c541803034107089151024800c541a4a6440804284002da80002255034401c0d64040754964400584002c00c01070715501c45900705d07160482002001c00d009980050640f070b280158030010301c0031000500701a41400f035854a4154000d16001b00104066401c0407203a94068200546020442040c410456030351645c191000c598034455042009420b00a5900416000f0381701c10243d4103084c08040040c0e00021503035600303034880301c41640034001501510205045103 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 460243192 1250 460241942 460241953
    0x20f040b061b01050106020d020a0312090602070f0510050c09090a021201060f02060c04180e150a090c080f0303011814040326010602030f0a030e010903050c061012020d03030e 77
    0x304a59002da0106540d00a0550a0000100f906071000800701001d50407a8014000840c00c0e4a041e507403030f100c902840d220310343c03074500000115025000804c0018440d100903000e043c3c450a016003000d080300844800c40e81000c0c2071149500880058a6012404449841c00c030703142c48008000911940c40707160850784414000180081d00003040300c4d540340f80c680a0321201e0b035460080741c20030310a40c0601610204107407003250780d54155500c003804202180c0c0032503506181c0a0328130b50058bc0c048880e588821744071174500c42000300009c1d802d4000d1000000070b261501d007c262046e00c80c001401003417075a07040742c404250409a542c00c444c600c0c40201340e07000503604113400d00402d0b580030090103051114044d4a01c8040000c1051018101c4503603501135420700464508030b0b82294440c00e5014209a12252603c0b0281c00038454065001d1203616852b60b00da801500c0c1505040004243d1070b52254860740c10001c210240e40501010360f41117505102c603800914003a4000d00340d51800031a80d1290 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 460244442 1250 460243192 460243207
    0x60906030f090f0f0c0902090d0f0203030d11040807060c02030c01082206021206101d061308060103140304060801051507050f0c040609060311060d06051507030f08060d020f040b06 79
    0x24010304c4640134082e20011107a6a00d80400005905c80d544080d50060800904030000c1505001a003a006100600f41d078500410f40341003500b44c84200150403041e010000c2d040041c4a4204854030041517a41044120101d16400283e1550940740b425410b2015000000c2c0454003e5520a090700c50b10042c80f030740e0404141484002900190030103811844054040b802629002c00c5005181c1c0d01d540d40c4040b610b16101c0d00c0082c44203820b01c015007242d01030229034484004e04a030f13440901441801449550f2650401082c00311300d501004001d60070400c4140300507588035110b6410742c1e20948107110300a100c990b01c48160320500707401421340d020f807440301c0c0845280801c8601c40580c080300e05010386504c80d40c01c601155580d1100802d410f502ea240c1041504084015104c0340949041c009902640c41c004a181d003809609010710070b0400295501c105900100018500c0c034207850607030340b03914081d804039080c01000e400192184298030200e460541d202d80089071144405032401e03854020 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 460245692 1250 460244442 460244453
    0xb1207080c0114040509040204090201030f020d150504051e0402010e06040308120612030403020d0219030c030303050f06010903030531052d0909070b03010b22060906030f090f 77
    0xc03600d6803540000c0980c0b00c105410700d100f80990b03060321002005502c26440c1c0d0340c01c200060416003012070600d600e45d10040d54031902440508488a0b02210219121044100d03c2648454640220344500c4c42d1400740551001161034090b48502100058102611a8001030701e074030080301002c940c03103000007030040200406d40024000ca51074410001010b502c59400b00405190001a007492070b90040c001080545041d82ca0410001d00250503c000e0f05007001a10101a40790b800a940c800c03600d075004c00070140c0c18801c1650110100d003460a4508012000034500166403001074104000843d903203010030a80032080c07000314087c0d190003820039044401e040c04003007180310303840c880e40340340480c00c104500001010320103441501c802c1d41010004810056501c0000e070400382503100b0080041030400700d41e0011070107429507400d06904c61141205d0043c000183c1400b1003000c4c40c240908106083d003200c1c5600075201581804600141846079060041c09948070190002e20f80212000c203120 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 460246942 1250 460245692 460245703
    0x3060f06051f02030f09010c320102031003020904150519060605030606040b0c07030f06090204060801200c120715140c160309030503031501030b01090302060d0b120708 74
    0x40042c1d8580c503198180300707201ea001d40e045034100c2001d03810800c40c000841040d6401889032090506045c0c9001907a0740342c1c850b5a54055640152414020440d0508602407002c00d039084a2100025461440d20800c00c059217461403000078081c0350350340082020003401e0070b032098224500100800c8035140c201c9411084c990400c0e18490aa45840703c04138078030f8411812a0300c01c0304040d1a2902e4149817110002d075550111140780028002d464011000130160b0144030704080c00b172500460200e0342801044100e440d56480000c840c1e01d0300a220b40001c00411084108080060134507441d00b248624107403d0508036008900292030000e101020449601d00032101d60042d94020807a43d01c0001e90903105400c04d403a01e105da43c0b0705010042101e0600191a40000d11a04e001c1001545d40d90b151441e5410644800e1304944e81c0031001c0c5020b5900d403150403e812001d10b0a850b01520307640109031940700303011100307215030b40341c5501a1454a80411400b040071280c811603220541c1d4462003502c80 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 460248192 1250 460246942 460246949
    0x18050114160201060e0118090c0807030c050a0e0a0506040b03070602100e01021e070317010b0d0b010801140616051e0d020705061b070e130209060d03020c010f0903060f06 75
    0xc01c0d80c070104070708292051180c0c3d420f0710350521200000d40d00301089800c3d40c3c4070921130780d44107585070b980c000006243e081c0020000e00c1c11800400d9410300310719102d8031400191700120700a142181c2c3c10810380800d00c050b990070104207100080d898640d04040340c080c0001084064044c07103400000a0041c1c0e0000750b040000095200030400c1c402030030a014207034450070500c000c1c00703040e08101c16075070800b83e030080070b9084c46410b08080c00d82c0203842e040301d0660241e10040030ba031004980004450002d001d8241d00f070409103462500c560410002d90540e01106000c280148000300d02101c10b40d00d03040c03910803800c0d005400c6803500c001a02248198501c000c800d00030300c0c000c036004040102d00000d80081903420080540c1e06055003d462126203c40c044550819841242d10020f45c28a0030812207008015040068134046060300602c0b07882440035241d03c1c01814842c103c60040b80c3e01188401401034246007000140e2248c0004544c0c0e40750382d03080079040c240384c84d0509800001a42c480401c8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 460249442 1250 460248192 460248211
    0x120c03120e070b0a11010501060e121f09140714120a03050301050409080d0c0e150304080d0902030a060e0606040509031e03280e0c0604030f030318050114 68
    0xa020410100415110010314a61860b44151420b1000c040c81d82c2c05881141c01900d000714228040d0442c0c0c0e800c2d5032007030740090081603441c01e0140c80c5040c40507048201e024004020300c621850994148440e5088009500d9070955444100c020060300c0202c100d00d407000c1404613007406445240100c080a00a035080f48505000040081080d002203050500503415848043c2107a10300310a203c060b124006c2c04070755658003004040c100d110948900c00030802c2e180d80710345441e17840c40701303100443c01d941204001682d404e108001c0002d4070b81048601c1116100703000304040146101092802d00343d000020059420850411514100098000c0c03180d03c04440500076a100c1025407607c91044404060310b10122aa282c2003056444000f15000a0b810900180c0410000d0620401c103041402c403804913515000c4282402004100000112000729900b52800b072035540d4901c22003504180090625444d91201035031031071103401500509400034000d00c1040040900c1d000100d13006c0380c1300c120 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 460250692 1250 460249442 460249457
    0x1528170a0c030c170d020a0308070306031b0303261302061e0c072403050403021c030203010e01050616031202270909010507120b0f06070c080d0309030c0209040f120c03 74
    0x42d5807030004650801c020281c020700610f1f40e0544003221807030401400c1905068584500100240c13811100601465841c010fa050791800d40c9402000c51007500c01d030a6528440c4c120314034240c1201612a6044a24001d410480700b01c24408a4030030f010780502422040f1006503401c4080e48180000e0a4044225041d20015a15556081c2600c41485908005a101010720a0409029501c45500b0078003d0044542c042082150906200481824000002e4003c4010085541d00b070164030701429046642c0350401244112078030390080e05140c007500300000544400b585c1d07403040c0d04540390703440401e001d514031805483e4582455426100902d00403c10003000481c03880301840340300c0c000d00c00c1e80c1c2c2c0e01490644494880d4080d1051000f0298821340500c01e40da0181c1da15801004607500c40e044401e503191900d60558103003810140720405040c01d104145000a502c074000401881e4110380b0019a515603080000d540b207400200140b483c03001001c0e5030140303500b044a000c407992090f9030f4400c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 460251798 1106 460250692 460250729
    0xa03060503150a2309150a060305030f0721030207020306060901030803010b0f090907080f160c0b09012c010b060f030f1e1528170a0c030c 61
    0x5c1c850750146601c0005a840304980d95403200c0506400c0000718a10f8803081d40781e1080d02c2410900c1030001403682c041222045458600d060028022500342080240107402548801c2c4140c0c40b0b881003200051481c5420307001d850690790b00071601402e6928060041c40580c00902403254600320034000141d454941c003441d20310418450f40c41e104241403d210040c3c04d81070180104107030030030900c22123100d07540041c030707081550794040400d9140307588507400c050061082c00d19880c40b6440440400d005c3d281003080031024900480000c01c03190042000f0420340e071168603842c0030141024400103640540010800d40c4c08242e1502600042561040910f01e18070221084066030703486c00040c0d5407078100340505050346041e607204445c420441c0120704200c0146031062150700c14400322040394468052140014499108940701216070320b0b85415041800d02e03020f400c03400d140da00c4140 = true := by decide +kernel

theorem cover : BRFrame.Cov 460071942 460251798 := by
  have h0 := BRFrame.cov_init 460071942
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460071942 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 460071942 ≤ n) (h2 : n < 460251798) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
