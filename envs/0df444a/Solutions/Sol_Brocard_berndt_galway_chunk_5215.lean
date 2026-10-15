-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5215
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:07:31.50183+00:00
-- url     : https://prove2.me/submissions/2c0faac9-abca-488e-92a8-61f4bf1c6c8e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 937769784 ≤ n < 937949640 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 937771034 1250 937769784 937769851
    0xd030b120d0905040608070602030a080703090b0c0d0f02251112070f050312121b0a170606070809060a0c050a08030f060307030201020c100c05010507210203040b 71
    0x4a000e6240c803032031038035406900d0b48140d9070101c41c200996510781169a80e02c8100c0e02641016900030411050894004e2000d180e108001d4034000c01c00781010341c2da0080092050f1070000b400407020500d102c03d07403c0d034040c0040b50b40310b000d030031801c101c03a08031f00c10f44901c1902d10a60005101d00040c50900c0014014100b07904c601404030440144601d00c460396440d9942b042c180301140504012a031380c5000305009040800089880f800c0030000c901e4503155945c00340000c50b800d548000038803d000414005810070700102d46480000e03031406984038590200092206100305010800032000a06034010340342051801d58400f41c981100240544030b14a1000000d0040d208140d03a02c0f00308030b9103000451042d07080400824464403400d05059031030003d03001c000e01580141c1020041400c01184941c16142c07240780c4003140500741d40b541400c440d002c3c3c443c0c5000840051070300081742607410b881556450845011451850070b038980c4402410060302d95901c8522045a1501040b8800b10b48801e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 937772284 1250 937771034 937771069
    0xe0301050103110901090b0603060f011e030605030106060809031206060408070306050402010f0314010e0933070c150209010306090507080601090f0305070302210a030e09010f0501020d030b 83
    0x40395840e0b05284002c100e40c000220f114105078000801d00c6481806a00d090b040060b1800d400c45e22810104404160414172032410005426460b04c1c00181d6111800d00c81d23522a00c00107030290504080c5800c2d07407007981010080c840e10340c040c494000e000008460b200c030f4409010350041d4860400003030880c49194400406841001008820f10007650f21850046100b41c072650815589840c081d0161982040004041104d80300104002c0c0000080b180e48001101d0544900301c01c0c1c5402c2c084c42440550410f15071592009180c0020b580c5441c0031a0490480d081040124a60f070350345006a060340c5000e101402d40100320148640d000341c00241c00350450780418810b920341110018120481100c0c014001400c4003000503000c807003030323104070166500580502540c03400c2d0f40038050303800340c00d08002d21a000ca61403ca00075a2050040c100c0e810311950351990505c90345020001141c4046e08070600035005128100105c3c4e800185003038008500b42000304030341094000080080103084031044 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 937773534 1250 937772284 937772291
    0x1202042c01150f050102030702010804110402072609061603230a0801060509032a0d140609060f0103031110020a050703030f0504030207030b09120403030314130203070b0a0e0301 78
    0x100500c81904000c25110198102c031400a0303484030780414011541c4070b11405038000300449000343d4807440103981e100340540f482501c4080e80001141c200da001250544d00060405408035442505503071800200303051b004071a0600040c6800102181309541080c801c0c41d00c0741090204050059400d0641c0611604d2840545a13003480800c40660000b41005c001810403c0040b661f68012010740f9040c05020b0010030840110074815064440481c1820703005810380d80000300c5581e40c440c41c10321001d00c10310b02825020682030f02140b50910180c4483c205400100130003120340a07000d209411250586001d0728100c1504a0090800c1929206948000d00019010017910b8100004200f0103100b90b400700085204a03480404554081e10010016007201d081040462260500d00d0b0700300b2201815903542c00d0b003000d00003244c0d03409980114046503d1f80f112590181202242940c010000500b100030451a40c0c0001c0e1038127000d00808035074603030100d4000381d454495110816002c034050000c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 937774784 1250 937773534 937773611
    0x20705090a0504110d0b0a0c05220509130215280e030c04050c09060a110f0c1f02071e0e010e1f06121d0a06050a05070207120204 57
    0x310090141160280c900300740180303880a250030116180c014071074100104003690b407120a00070001d40b44108080702042418400f403c15562b42e1102450302c603c20403c45074071a441e02c0248009810001c060754501e40c006404e04000d6180e034980c0c1941c100c1a00c2c021540c3e94440c03540c01100c4098a0034081140a44c0034142c4000c5800c01600254070508500b181c103241c8108040100799002110301007200c0d0b50900015a840c10000f000c0c207881556801d2543e0400304c9070003440d1401c4850b44001d0407541c0080100350381130404006070000c0c80310700d8429030a94540d015000c0d580d00114465113580640402c0401c081580b141c50100107003210103a40c0ea0556034034504501c01c1d40041d100c1c0a81003119400103405141900c2c00c1c1d01c11070b4501d0b10786440d44000c5460820081c04504e81403c443c50320346410201086040c096004c42600c40c0500040a040034024601128401005041036500c40441404404191600d02e40e81c1613040300c01084803a0100c8180c500405145100001083e011084 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 937776034 1250 937774784 937774801
    0x60209011b0606080f030a0903120203070f080d05010504140f06010e03010c030902040c03090b0c0309281115070b0903130b0a020d0903080433090f1e0b070302070509 73
    0x2c481192084c104507203502c100c1e0780b5403075206c2c40380702d1000c0081501c013882040060b059500c5440303074070000c1c0166414040d1680f0b076030002c55000301c0d0880326a100081d0030405610b140c070a09000d00070566082058100c43c1c08540b0200c100a40345d42484400c0c030700000d51326172061ba464851404060024001d540d100c40c0c000c1d000d003e030030310300303d1290303040050140d1664820b03c02c412025030000741036115034031283d030b005074154005800001b180c0100c84c02140a10024001070407103480d201000c41c3d020680b400e010911900e0300a80901c20b091a10503210650501d0042c0d030401a08098855600e85a10128901d50300c43c0700d07480350f8203d40040000504900d040040c1c210000d8607020388020f03102004040300c07000d049000c01001c2c0031090000340300d42418540851151001142c1c0d104442c103850302294806100c0c2015200041d485c188240202111804980c3c000c00074003484452201c0725012114644003036004001d58104041484002d00d80b080010100400010b00707418440c2c1041c000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 937777284 1250 937776034 937776041
    0x1b060509071707230609131b0804140a051f0915050f0f09060106050a1101151707080a080f120411040605091306020a03061e060306050603090a060209011b06 69
    0x85800c150b00740302c030824540b0104c2604900b0903600401d02441c101c803440401c03040205000d00f079442659a8a13581058080407440c1c03c05d200d40c2600c940019203410324008504140b400c125031400e8000c0188400020400100000f5400d039a0f00c1c141a0080d17840705400003000d031000e0180042501803801c0030180c01580c03004c0d0046000700c010050b2607542c1d0481c00f07150344041c0c800d0b15007076010b0700c01013140e01d114a01070025000c90b0300d8048095214000c00a09640e07580d40300c2204096444070801600d8601a03403c03007610407500140900500c0d04807a651200070181b405403523003c00023868100c0500301d0040f175910700421042c0c1d510754200350a041c100c24a40781034441c0070394900700012996180081d03146100d0b01c45e03020340300c0c0f440b9161b542c0c0c3c40294000f10f071501c042c1a140c110101e10b00c1204140781c1103000c803950080b0b42c2d8501e403800040968103030b903010380d00801041040c0006c0c20004a01b01503e5a080200541e94400c54001203031801400c2c0c080036502e11002d00c400042180307540 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 937778534 1250 937777284 937777289
    0xf0105100f06020f0604030f0302040302451602070305100b130608030a1d0301230601090e0406150906080f070b1318140c03090d1b060509071707 64
    0x6a4081e007541e2200020ba03a03801a11400000c2c55010000140c006072050700c9522101c0020700c1c02508059895001c80c440004055022030003503940002c110000403000820711150204041c00d42e18103220314902d052906015000d0502201440a4200194001c001a0006540c40400c503a81042c1c001c0541c00100507502034a8402d6214119035840364955015007415a40039101451a14080c0c140586201149140b2110601110080c1402a40c0c0a2081c1500301541c070140c000f44101c80c4842d0105071300c00a00e100e040c496910b0043c800440c01c5020315a106501131000221640b800821452600240d0302111503103050580101d0180c40225043d02500b107d0021180d54070b072035007103900b070394040c00c4098041307015140020072900d103400c0c1e600c12081a824100148070401000001c1301804121003c40c50b80d1380c00824440100c8042041030b480110601c1c04e00c041c05103e800811056499900c09800700d80c5480c01700e034400805000010007800141c60307c1e0ba000781d088130b00d96268680751 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 937779784 1250 937778534 937778549
    0x2110060206060d03050d0222060e0f03030a0f050f07020907050a02061b03071404050307120506010b03040302060403030e0f0f1c092d030804030b0103020a0605090a14030f010510 78
    0x10703004219141000888940c815074140c46403400d010314681a280290403030880c0040403140158901e0f030034210328458002030a400c4e500c082409010364148020620b0318250140a507100704032000d02542e02c0001181030f0340403850003665a25901031403007418051410f000e076002d5500e0007030001450300907006048001403030b000e40c0c51560b00e50903a0146020394031070b400d120010410004e17520500c070712545420185001480760a058440020078585a015007001103803281e4206240140101044403a0051078402c0b0350520f1440d19560003511a84090001800e00d0349404190800602c1404125542104407040b600400340c010005950341100442c0c0382c0494a020140c3c840d99846002c070301c0250f03070064104c0e0104865410210800c846440c0a11200d0f060b145008000070b0380c0c12000f040250b0164095080c81e50440c010061901001e50045081c0101007080750342985509020b60115150402c01031141e1005034007107400c080c3d8414440e8107551910003004000f24080c0255001e49011 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 937781034 1250 937779784 937779793
    0x7090e070e010f17042301020d0507030e0a0c0501050f090405130308010603060528051908120909041103030d0c170106050f04090b0406150206060411090604050621100602 75
    0x11881070381c4140b00102034000b200400d0000034041003009660444c206603031000d80407a2000c03130071181d08982209c141c910110b030b00c80090000d001da2600481c8052040070000d020481c2a555520505c0c01c035030b201c1d0354103011020400c80c00e00141c40c030035145041c4010703206121510305603540b1600c40801c600c04038041401c000011079101d100c1c1c0301d644180c4002a00080010300c2c180711600c610381c0c200e400341c41c8106030041d0100c0d040e243c04a600058405a6480b501031a080250041c10301034494900340070400e080c030040e8040da0725030703007400d80250b04403a2590300506c081c00440d042d0300c60305d08540c07030080c00c00444401c80703640401980400000c0f42426000b507601c411080714507100310910340c0042c81c400d000a00007009207a00002440200400004e6a0350341d84075044540f00c0401c4484000d40c100d142000381c981001e0048854003108403804602d40b0124a00140300ca0165024a40c0a403c0c0828440d110188a0844007034014100301c0d140030525103825001e107890454003900005001c4d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 937782284 1250 937781034 937781057
    0x207140606090c04230613060c050f160b09040b040507111b18070e100504091803050a0c0507091803112406010c02121006050d05070b0307090e070e01 66
    0x101d00c04e850075180041d4420300b0261041e034041507000343c410003580d0302041c200a20000780702d054201030300074807480d241c440245106060450400440b031a1015030751b08001d0501c41c0301c0b01c038074201d1001d48052154454603810b100e400b04004000000c05d45800a240805003c1404c2d084100901c0c1b091a0504484101e8036041d09014010020032180fa0412070b8030241781c06a40c4402c402503032000180ca498500c40803281e000514030025070b2803003808140001003c1c04201218010824120042086c4040850142d03a0003000c0d40309100c138a90812080d00e8092081000510100b402450301c0e650500c4920b81160880b400310800702d00840108040c00c5a5201070900800c0c480e12403000c60405402141540d1110340c19294024122810400310003400c200503a21070a909541c510f915000700318542c15006908200c03001c64214520a00c01c00303000c540000d01c0083d0b0b0700701390380003c0511a10307511110740550301c000040d0403001141d90303a007082200300b503408225080010402d0740e88031124030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 937783534 1250 937782284 937782301
    0xe07090b100e06070605180d0c0b130c060809100603050c010206060a06170c07240501050a121b0f18180b0a0e1c031a01091512020714060609 62
    0x30034030790f40040082c0702401c04504294015a032050110a032890405408945113083c03001c1c016030314010680b43c007201400e202d1130121392680184030f40b006403840c2da021340310003401c2c008512480d41040a000009410024203002c200c02c25040341c80140303c1d10740c6034604140c5401002e09054010b1081030001030092070060071a01c119605a00c4921764000705003554a07225900030300b07141400b03004000050003e5102c030001c2d1141c1282010390b840d60012450820281e0307006901c90707403095450740c1081c0200302c5500c50204a180d130010118086030784030700c00304110800c9540400c1c03a0400c0c0200000d002c0900600150648003045020069920300c8009010314410f0076002801e800d010000040d112802e03139100c11240c0501800b21060140b00c400c4080526101e80100030010351500004c2100700481e8003543c003e4882402c0030324215082108881a60000000e0741c42000403203111400a910941d0450342c0054101603d0131203021051842da81d01c070425101c3c0c0f03006841030800109202d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 937784784 1250 937783534 937783547
    0x503011505092d041b0806010602030d05131b0306060f0b07060b1503090109170a020a17070501020a050421200112090609030f020106061b03030e07090b10 68
    0x160001810b40702c96480b401e0b81c600c60706441404a8014200740c1070820003001c1490811440303148252040e0300d034512094410301110003150300208050307001ca0014401c003500401540d500100c41c1000058680d2a80441c80c881c8000341d401422903403032089800b1590048000042c04c0c2c07401000cac1400900c0cbd03a40c15a040851452161154040c01400a507002803482c0d00254490400280381c4134821400003954034207541300342e6450005030741d5180712504002c480340f80c200c6520307e1041200d040a43c0c405000c3d4440060701c1340284000e4203140c00c50318580d040c00c2079070b2407540c0003030003151070340181c10001e0301f141e000f0b0040e003042c0c3d0440f00d40420301d88000b0340805622540102c10626800700c000c046010745d4900320318ae034180f001000041c4458042440b0b40340c2d03c9030103040013040c840d2080c2005082d15400c0b03000d503821641400c80508c01035030080f0022200070040c0d2122400c0140b40e0904030010071090034084468001c1e00e5000400755950b070480506ca42084881310b0000500d40002e4500 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 937786034 1250 937784784 937784789
    0x2c04030203070311031c06140f06090f011b0501021b06070903081e121f08030f0d140a050f0c07050613050f0d05071703130f0206041a030105030115 65
    0x181e1080010000003845200c032102c0351071420381103e0412552024a843c07400d6004690160955560000c20030f600188000825440c015280303171003004070442c0861140d10900c18118080c844200394404164811107103500104804030749204003030304514205010313501542240d8801d01004400805078070020a05070f0144801d44c03500e8400600d1540c4182d0107401101500c81a01c0c011343d446402413180034010080c00c08010003030381d814a401e0b02408281c40d18a07942c4096201c1d1040c007031002d6400041120520001424690384138408048607002922080000f0800c190380c0e0b90900c80900700c950401401201c100d000c45403d076680d503038024924003602c4006003c42d4485c1d0042510a801096461003060140c0d041d034070a142c00356507051408600c0e14801d0002100026102c080c00b0041c605041c01d412640d02d81c500d1418503066aa0704a000844084e0410814550690440d40c50601302c1d4000c0814003024541c20401140291654200340b00d91070284d42081c0c1c0300c0448001c04045c5009 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 937787284 1250 937786034 937786037
    0x209090f04170d2705100e0c1309020103111602190b0705061618092301090b03011b14030a0609020d060810050903032e2c0403 56
    0x6940c500640c40000000684280d88400141042d03402060391a00103203540d0751424004104150b140700b0014014569a801100101c003016944001510124005a206640030400706070400c0f61203003281000401400d0541c007810801d68407164000b0f44d00b051082c24000d03201045607a00c1e54440303503501d1240d405101c60b0342000c20b01c1c00703005150811a00c5003000880c1d0000b2901c03074a420364010795500c00380007035503036500c030004111701e00c1008482840003100c14506800c0780c5010441000003813a4034010780c03a14036103810005c56040895190070b00750140c50303d44e44042d542e64890441c000c200200d00180a9400e00c940707402400c1011014203418410741d5500311641d0b4070305045c5000c1c0e402c090f0601c410b40741c4441c2c00240c2040300d4000f51120380c00c440d90019240303282c070b22424901401406c680024600700003c001000002106880c0d00803400b00100c5800b0545950004503d0005d03041315100304400d14020489600703002c030400b16169080448208030b1034690b42c280400c6402c0720000c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 937788534 1250 937787284 937787299
    0x40507080c0708040312200c03100f020d140a0b091303081801050f22050c0609030a080f130f0b091003021b06040b0c12010b07030212161101030209 65
    0x24014801e01d4001c0580900078403025050544a9603041d401003904602a0001078021402c0103070340c0d03200c034a40c03103480614500500a03104000e0203c2d0701c8803a4400c8001d80e040d034aa010252008880c1c0450700000c00f14042003084a60313040c1e4040b908242641d4070b804080c54200b000025080c8080818052480300c0c3c100a80071500c1c1d07804079800180140041000c03050b2200024180f442401400c0c0a00142503400645140501005562071003503643c40c1c4000c0c51900d00ca02c00305102041001c91580180d82480e070350443e07400400e1400084040c0140041c4d00007691000303541c0d0610242a07100311300c0098070a070517034510001800040a0296104035070003040860700034502182c1004500314103090240c14018aa664481c00074441803131001d06810100030801000307994050ba030b034032212106202d410046a0102d07550307040c4050240e003020003400a00f407007d25008022003154050380c003014960f66611000f00c04815403506000700e60350b080402440c1c0d600d40c000c0c0240c61202c2c00150504 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 937789784 1250 937788534 937788541
    0x305071203210507080606070308040b15060d0e0c040c02071e03060207140c0a080705011419050706060b0301060c020d06110a020c01020708070e060904030e10030906050604050708 79
    0x2010354658000101c0034003040d4810b0511070000000e40c0065114481400181880c14013400f61690340001c0034a48180c601308054000250420320242d0002e0304110011200e5992001c2c403040510802e2101d40c3c45400400e41c41c030742d03028039000f01e24220003020694590020800c00d04c401d4400007000200940c00c40c41c004e0140d0461070450070301240240a0b00843d080d565101e500490b40410b405494071031720b411110007112410068003e4640d4143d8000d1202842c2400e06e83e118007050055604008400d004d414242c1030040544140440580c9880900307128001d0241c401d03403040d28203c4440f810300c0b600084038007205c0184c0e4103c40070b523260a0407960a56082204140b06103004445942c2d44507030b036400380e0b06d035007000d400c2c881c1c840d8004140c010f110400283c50003130720307601480c22507100c01010322840c280040f1140c1c002e0340c1034610036180c0c0c440785401d89550407100b2144d5089480c081c4059071441c1d058015490490203602c0c20003050f2510414071054403070031070350500070071400b1020 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 937791034 1250 937789784 937789799
    0x4030209011a091512150604060c0809030d0f0206010801020f090108190609060504140405120a090e09030706060602030c210c061f0f0311040b0d0807120f09030507 72
    0x4a50b1809000c1440c54900c0d1000080c24454008004468041c00031840b02103950440b034400342c00c001c0d000d10418403c148000001d03003d200d54083c50003084a0307031580c1801c2110b040c1c140c40075458000c0942c0c0c002c00c0d600c10002c15003140c61155200500c110400001c5101061080318200c2e020094213903d00003481c4019188508054010a1101c40c505842490401c891080300c0c090106890045400d40c40c11080200f0385161000c4007103224007040600000440c0050320341503003011800450b4640320108800e5400d0041584881c5541c0b048108020410790f0110003410007520904040142c2919154201c0e540e0107036805424159100240849100c1c002501002d00c11104030340c100e15004c003240c0074905001003521409914001c481c400c0500d4040000e0740f078040d100d0f10b0b41070050030b89151264410039032060702843c040d9580304512043e0740c0300e4481210700b240c2c1240007103542c1c00240c5002c1c0480700345030008000003000c030072403040040e200f500c070001102c0d0410000c0000c1c0d41010364 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 937792284 1250 937791034 937791059
    0x1b0206070c020f04050f07030e012d090503040b190807021908041e05040e01090510020313140c1e0109170309120312070318110a080f0717030403020901 67
    0x20183e920040c02500390b61295601e018041c402e0301c000030031081ca418511005015074101040d1480e5a90402c0380000a4041b0104880e070b1a14604140010002c4503481c884000e0003003010141c030074000020045145010140240300b6143c142c524003c1c481122601225004021359084005820039020420060b4060301e803044214081c402d0b8a00e800d1356a01d9200c0820794231140800f000c3c921031010401440c0600c580314901c00303403000a001003c01d075522503031a0802800d1050400d5070110100f01d5100e11070346003146440e80310f45003002c50418072407016510104e046402d803003860800807100d204240707a00010880340042e155141e0306810403500d01c1409050120442e4103200901103040156136002140025803c0100034542d04d603001c40501c4280d0500030294418141030100205071030145c43c82c100c0740b0b190018040000c1181900000d44904059800421248600c09400010780408070b20202141c00500004100e070303280c0d183c050303140d0040d03110107580010424010045401400c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 937793534 1250 937792284 937792307
    0xd09050d022415041b2001050f0708040c0503150105091006050301060e0d0605070c0215090603011404021303082a0c042003190b0103020c1c090b0d0b041b020607 71
    0x200003191414005c000600c140c034120001c40d000890f000c09010340304a440b6000c44000074154028017140c03170b011400b040d5010010345a4001c10205400240600090b0204007018040c0241610b40301e00c031041c03e94403880b0b000e000c2e181c80341d042600881d480d0440c0c0b40241080319403d48440703065a103001c4003030b541004800300d600e070061307007071029540050141d200c0c440c401d01301da8039a2407010440b40144503183c031040071484610102000312240c1c0e83c0d00c0c002680d04460a680d820707500e0605000100c0c01a005d04001152a08440d1102104001350a0302404540103038490310104501c04000f0454440072208004032650000e0310700040f0b90a098210101c1d020003509104000082c400c0020000d5108840502c0503014032208400d09260300c0c0981301680509190a40c280441001410380b42e1740b610750220248071540c4040e40403d070045a02d1030040c10841c981c0d80d140d408408201029240c0d07800094451440c0c00e2443c00180c4d68255403107261a480e5000b050301c0d0b901c000c0d0a03106121001c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 937794784 1250 937793534 937793539
    0xc04050a020906070821010e0103080304060204090e0c030d02071211041803080405101437060503070603020f180402040b16052b140d09050d022415 65
    0x30841103000e42c03207010080528a125000707840c1c6e130b00000414500151403070030b01c46c04490180001004403807840143d26044d241c00991140d83d9071601d190940017072085a0004415074181401d40518450120303d401da50320f0150207565160b5241041281c48143c0c0380070308504145107007160350120f0148440102180710140000401c682d050005140c6016441411000508007000f084104007081c0030301004603a09103000c0c410b40b91a07409412030035100402d00709606080b02c00c01c2a10341c3c4448145e94404503001f0001c88541d805400c0c0320054645400349034028070541000140c0c5078400d1088401d03640c11542c440d03041c5680c4014204180100355840c0c2e500c29024400854070600360401040c880c0b00c0090410555189490581d080c02080c00b030910309000709406000c2c800e00d4481001611b41030900c0d14000c0026050140d00e0031b4003038031640b145418500500141002800145030390440030030f4007120040041009a058800c02d00f1211083d44820180031908071800d1017180042d00e0f000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 937796034 1250 937794784 937794787
    0x1b09040608150121080313030e090c07140f03190507120c0203010b042c120301080322030807030c020609120c0a050618150d0212070e01020f0c04050a02 67
    0x440081c01e00e4071080805001c1c00442800041044501021150007240142d980308544008a5100c18600c0d010080000c00000e00e880d483d041018420004030801e0f140081c480681818400300342c820391380000c0c00803984481000e400744400000091070001d81d51001d4019031a1405420400b02500c44001c0130b401444000c0c806000054603001c01000f45040555070881003820b1401014203458182a1060003a403402c199240641c071142d071414440750320b2040000003003c419000504d03101e024002c0742d4001001000100741260f005c00204951003400c8003c00340019000f21114601d0003507c001081d81c079040100d0b90000e40144040e0390b10310b000401039424120144080703405410480880d81440c0c0052103080749a1820714100c03005040305a41b0305003040c8001e81c05d030444840c43e8000d184901e2100341c07031006101e0b070101281c005100c55542591940d01500101846503001d58a040c049182940c000306030354400124104241d071110b0040040e00d012009110080c200544403850b070741d40 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 937797284 1250 937796034 937796039
    0x10b1207171c0822020a050906240c010c1403011e08160812040302010c02040b0a030218220302030d0b0303040906030b0103052119030f0e1c0302031b090406 69
    0x800201091095940d01d5007042850444c05203007003840c0410741c0c08800200b580b00100583c0304c00e84640e00b9600140c800495907126070740002c1c0000103250030404503c811000151a00e041c00019000c1c0320a188001d201400c2510426107643c5c45041c41c40c142c8250610040102850700400030205201e90842c140c1c80d2915001414140050707032081d440e140a1300c11007049000e078100b042d06103658844410508080c1194002881d0680449019110302e80314006a029559000e02c40e030000c650003402c0340f10032410740c003e071300390000100d403135038000c0c0308503d546210700c10814100420f881d455400b9500e0004806c81e07401c000c2030500410350301844180700c0480d40842c42d200c2e10019600481c0c94680c65071651400380d00d0811f800301116841c81240501a9034201c0040554104a07151080100400383e60f0000f02d00400782080c207800400d0414002a600607030103e8500e116640d040002c0d400c1402d1404203400341d00c4107450240620301020080d2410b00e101c44040c0510280080000c15020b5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 937798534 1250 937797284 937797313
    0x308031302040929010609060e0d08090402030403110607030204120f05120f0d06090c0c030f0302130f03020f04050c092202070813080c010905061c05040302030309010b120717 77
    0x1061054509604100180c0e5500104c15002524014a03c0745807007007403103040c5035005148100c0d14010a01807000301d2210b40421040a064410300390000d00b0031504d0f0301e41420300414819045501c00c0940c0900808684610b100f8003c540c160b444421901c64007000c07503580d91100c6c2e000408151018054030040c41c0c0c2d40890741d001841000603102485403128403000d1000308544250303004501c814588442c00d141940c21a079000340960305400c01041880740d01c50107030060b21402d1901030240414450100303202c01c503800da8406490003135600c0c011040e011000e205c06c443d001d81d85a003d54205000d0084940f5000203c4120007011400c0f80c0d40d10800f90380e2100581c1c014810480307900c0e03c041806815402040b04010082c0480401410f40e40c41eaa40080c0c101d017104d000d810300075080000d0b190400d0740d20701d80c08503114103501d42c200010302c0d01d410020348940040e500c0c003900b035091454600b054a4540c07240b01d0040700c4030014226091605d00c070340200050900b903010160089154141d00307078 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 937799784 1250 937798534 937798553
    0x10503040b2d100524030c0d05010602101811130902040e1e03030f01030b060f0d1518240902060a0c0c05060403030e100908031c05060a03080313020409 67
    0x142c00a444904541002e41c6911080c1906410a6026117080c1005082c404001940841786490180b032066407a2688012980e082c03055042400341b09050400002d2000e50002d000904030070b480804211090502021142c4a160080c02409034121848402c000e4609580075500d0503940c0b240000320000c00b5800319059800010f10843d0036080101c101d42052280314001d0000840c45010310315510f44444464481d031010300002d0440d5241c1341c00030310140c440e12003841e10624020000c055003802032030807004e506000d07000c3d1103501d4180480300341ea14030b10807000e82c801940001c092408050916225101030016005100d559417600b44400150b100c030401403103401c2d041d5540801104013418064102481035004a0084c4402c00c070400c08642e100800c04402c5800312201014a404620211400c0d6615005901c01d03010001d0045508007952806c01c1400703400340720034019607031107404200040c02a840090b00701c0c50300300006600e1034803404030101214402840010710796039a03102c42990 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 937801034 1250 937799784 937799851
    0xa03110d2115082406030606090a0c0e0a23040b0109090b0a0f0e07030e0a081602131a01030f06050a03170f030403122405010528031b020c010503040b 66
    0x1205107203085429084c4a40d5103a03100a013034005041e0303030030301d907000c2441c0031703402800d03003042d80d5803014100000c074414420702d003881400408032043c094980301c001043c640d1365250000140780c2e1340f0105049050502408000307500503140c20360542d2070070800300094989550100d41c0510740c41c0c40414040c6500c511070307014001d8064848818907240c1c43c06401c0395000f6100500f954081840c0d280013800301070440b280c030700d084130181c06000203910100f5141c45003642a0b995041c20200700d44d650250410300824980c00903030702403181c0041003030070a0440e0401d01a06400c1005441c052002c40c2400d0b81c0c2c2c10f0051040e008452801046101d0141550400da60440000340002c403a001c1016003402082818003c01110104040c003030135142056100307521829040c018041001c8581041401c1e1408200051882a482031811044001c1c028015205d4405881801d41010442c00d80b000031294483c61040e110189191240d4542d800d8101c00101000b02020a51400300701d200745401280f5030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 937802284 1250 937801034 937801063
    0x50904020711010f0801030b01030f06090203150912090d060b0121060905070518010e060d090c170303090303010605031b0c0a0c051c06020a020c030a03110d211508 72
    0x110015260300044c00440342401003010400c0d454010f0000c10302c14218241101d502600eaa00d06034114079101010b400d00d100065854061038500c0039401d084502c44900c29480300c0d01342d4003d0b038216801690140503080300c082d0400491b031141c000184403648068480c1405061100d6180c10743c00d040b2007030b0703946451001200d6444005c200035041240c05011380001e0030742482420800100b551015050481d1030017410400040303c5041d07a0b4032640101e54042c401c41e0400d00c000f08403414078081180c00d520503d8001d500c00315a0480c1c1d10780200a59001c3d0450380302842c40d592805008603180c1c3c00103001000402e0034400c118821036481001800344404141c080c0502540324145044100d10325444070b8051500e2807000342110a0103003032080d0301e90b4449001a26520011000c0303203071140f01c001d89501882080f04001c103040c0c22443d4481c0f001e0f0414102c9948688044007180c0c0c0d1200581980c1c2d03c450711101081814009400c210350104a010050881c103079140c401c83d203030010340424000d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 937803534 1250 937802284 937802303
    0x80714120f0d020f1005040827040906020705070b033c15010f050a02031204170412140c09040b130804090e10020c06061504081203070f0903050d030c0509040207 71
    0x20351324a0700f8000c444805240c6482040146072607254131903280f04609812140b10040200f80440420344682407201c0d12018100b001325038400d14062000f07510108040d21b0300e12554000141600b5142c046912a1403400e107000c10780c0001c08000b8441d042841d62603c17180d15103041c4810083c803003a841d28402c1c113045c07000d280c600302c291340007609500305840540d0030048100020b281141d000401ca03100200e0f01a0285426500c40c180040e118030424081c1d044250002800101d000c00b40343d01070680b6002e05560440c119064201030307503521039a28071320f80245500d00040c000c80c048101c000d41c17089803010751003c2ca00c03090b9070b404080e038000d420075032070141e131481010700440040010b5078041c5d0003410214681040204825600c1000801e054441e510042c613144003440c92805440c005d2103c20121000c01c010340b0390603501b980080300e2080014002c0d100c00c41c0400e2240100b0811203030004c01034008400a40c0040300038100c40c11058042c80303002c2145001c01c0d101c41c03006012041c000c0a901 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 937804784 1250 937803534 937803553
    0x152203151d07030c0b0903031303060b0a1418061306060206071103030c09040903090914010e090a0b22020a031a0c0c03090415052206080714120f0d02 66
    0x41002200c80310340d4003041d402202c043c070004844c110500103441024254a498201c4040041e265100b201d0100c84411407464000082084a070404d00340d070101251044416929184070b070080d2001c0701d004560010f5a10780303501400f100e1000340b680250300513041003440d81d200ca40020581e4203030b82c4441c0060f481001005a419031041502001c4543c2e100558918100030b075240210f80144039105204c1c030b94955070074003050b01a928081c02020230078010700140403103120030144580309104844c2503920190004001c0403011a071040d925074440d0344260142c8420362550381ea59148601400d5043d0340c00d1b41800940d8072a0039020085110710b0184802c40c0c0d042040c01c80ca500c000d040340307860400174040d034141540040140c490180003580c001034801c02400c0701800d400269840142c2020400c200200c0010b15640740d00f0117507165610501c12603070748201d015660031142c41a1101c482d01d0b14100b85281c07400740c4e91804100d440d4000c50700c00e030070120042401c0c505c020a4030409030b407200c0d009 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 937806034 1250 937804784 937804811
    0x90e090a060e010c0512060604170d0810030201020a1209090e010f0c09270603060509030d0b0111030f09040e030a050a0201050a180f0512041202090615220315 70
    0x49290300b0841c50024081d000d00190041c080303014011b00303010b142ea40301001807519110b032400e0380e0080c4000d0b20300742c0b0f1141013401302c40e40302c2c544181070380000740009000510740c05096040200f2a507042c0d00800903282c040d1110984d40301794003150803c20a002c1d000044094081c091088103046e0340b0000180410100c0c030f12400c42da1401e81150030701501402c1041401c0b039215a085103210302c03038014503410700c0303100320381d40140304030b0708000c6c1418079010600c50400400006455400f01c0414100105880b400040d54146507414192030141d204001c00e583c5038403488003400f4010409480403030301d0804c4d80c0e00300d411608120101400544045509001150f09000342500000742a80800100a160315004844100d005015107614821b42c08074040010803c0210041103541d000c4c00d803500d0b220400c1c0745440c402d0f07071016880b07040d0150128140f0300d00111900c03441a20b9551081c50550f1b40c00c000942440d540d507820300740d40080ca50000200704845031480310b40d00d06640004100404448 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 937807284 1250 937806034 937806041
    0xa0e0a09020a03020c30160c12030f0810150c02060304060b180708180c0307060f0207080106080606010e0d06060b090a0e040b0c0d1e02030a14100b0307090e090a06 72
    0x244003150301c03140946c103408a92124507000c0d0202e0203811683c3d4901080c090306070f0002840e00014140d040c0f1080010703815178080145004180b0960316400c0c5416498001c888034502600c000e400d1042d18007041009410403c2108403401540c1800410102c00740c0010740a908116410350b9030340c0c1c40b49200ea44501d03001c02610443e190201c510301c020300303003020010b05103000104040343c2a6528070002c2d05c0000100545c0d40a01e00040c1116040e83e140c1b04010b10701007a1120480140c894400c022801e52010b01508007951004001031480e565207078011500b05080b04000d9810040320841580812490301804004e0201c208031182d45110000510204095660004500b10312807000d020004101903a4160000120340d43c4075110307100b1200c500014212107110300000000d4981008004e402c503000b551003078034680c50421041c2c0344039002a46681d0115420a040c0320418001e1140d00401d102070f64100d06d5a1604400a50b02c505056959010559840340c03681e110002100810503a0300 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 937808534 1250 937807284 937807303
    0x51e07020a0c0f08010c0f0c0b150301150503120403020d0f17040803250b070c230609060109200703050409090f0b0105030d1b050a0f0b1602030901050a0e0a09020a03020c 75
    0x900b410203413800782e00083c00c03010074403c0100001400008aa99a00140ad400c81e1100c0e008000b0000c4501004000441606500c2818020300810a0354004d43c40003070292030482c9d030003030510800d1030410340d141c020241da00711089904002000b00040442040c9000e8005003001c14019507884020500022045003904c44e5040c035906236074031300c0707001903070322034005400c075000342482c0381008983e24184040d03a0700b001080c0e030300c00120120100c0b04a00024614001d64807441034925590704c40e11070105407022510200e0b80810003580b103498180280d070080c2192400780c5801402c0c03070f0712004111f05a80ca0758400791340c02514001c000c018484100302c85801844210000c124240401d44041e000e000c0340010402541c3c2d20003140000d100707090101d00501c43e4803901450400b40f0914141c25429019140d010380d142408980c0c0c220b02d07000004440711410705855050074940902402c48800e18803175440c80c2c01142458000942c90300c14006003440300c071140c03409078441c201c0618070703480e128544 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 937809784 1250 937808534 937808537
    0x10815040c0b0309010b10050403170a0f0507030e03060f010611010507081f03021503090d0302030103050303221403040614040302130e120c150604051e07020a0c0f08010c 75
    0x60003400001000001d00034102c0d65201c19880d165a299082a40103101c416241074000003001038082045034000e00070816030784201040d02d900d0805181680290280442140111381c4414003141c5842c004c50281161511070314288e030780c9018580200b8207001c008d58458452003000700040c4042c0b50815544d00218161070002c010034580109c0003450391101401e42014a4060f006100e0090801807280c009180c000d400c03407101000c403042ea0a2250f004560761340351400703415001c01c240c034440d0003268100c82e0408011800c544810038184600003d01003004500303003034800a0f0001a50750041c030483d180b800c4000c0e68445181c040080e20203248840102d0005100b0002800140d45203070100c06510b02441c0000350300b803100d10f14685084507218541120700d42c0450680c195200024000b4044506845406403944410082c4400d07a03801b0b0f6400f5580e020b1126041c0d081c12246d01d01740b5801000d910444601020030b85886500c0c401c3c6400c03030501d400703640c0c40511524109014040781c0d14644d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 937811034 1250 937809784 937809823
    0x516031703070f08130803010b0a0f1407020411160605060307060311070b0a0b030f0a11220e0102090d050115080d09032006040602100c0302040f0b0f0f120108 70
    0xb03103070018092420014240700f03100001c8040b0f01030002c49050781000b51b13480124680d880d6101c09407001c85820803050030300042c0c82400c00c80c0809125400d80298a850940c12500303100855080101400001c2440d40182d50180401249090109a00e500c1c05026604c0042c040c10017009040c1010b0240d0040030030705091a03002400c102d03c0208480402d50806034001c00c2e03487e4014400c0c007a24003c09403617410700c90040013641e0904042016540d40b8410401102e6184007003081c4000c0001a0f40654070039294100c18021f515843e400c03031403650134550001850300c0300b6000040c1c0424500760094030a41c1d0740300002c005a0a84d558030340c000e80041002890000d0700c4000041c104045400014082443c107001c08898407a420015405101c0041c961034503580c40c0c460081d030f14144c003240d9507005401d0016045103180030b403007154140c0340c1d00c079400707242e060074401c10308030b5944802c3c0300d804462000c00c10100d1203401103001d88261161914019100d501d4641d001c0e1074840c0c00250071654264 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 937812284 1250 937811034 937811041
    0x315020f190512010e0c0d1d1f06060e150901121503170705030a0c1b1d10080c0d230d12050c0a0804020118080606030d02070b040603090206070516031703 68
    0x410b4425941f80742e1210b0000b00d08541c0e4031507411a0005010120041ca20031032880d003240c45080e000346d5007580c230285000c200d000e90b80c139400c032541022440aa80c101c114002c108504064000c024500f0640604101c50440504504807046650303084155004c105210010b0042101031850080004250308115042442075150541c0f64400c62a069090000440c140d40c1000600b4100e60584041000d0310001c0e281d07244179512101068000301000c00d00c00100158040714a204078030103494020000f041e404032004c090100e04150940143d0b5040e5180c00c0349e10f10741002d1055411500e25403401340107009014580a0140038002150040d0a4140420806014203407401c0d114070320082d00e440c02c15910f030390005a50b4402c00d2126540d03541e0b500e003808159000b0024049010784016004c441c84a0707480003040361070343e10364003c800a40f00200402c1100d240b0a4012554030780c0024210752928459580300b600d4400c048540c201c01c040345201c2041072140c0000203010b6400c0e0a19550701d90318 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 937813534 1250 937812284 937812301
    0x90106050f06040e1f06032307141b011503122105040201030e19020a15080a0c0315170607030b03060613020c0a0c050306100315020f190512010e 64
    0x9503010b50802034188034001000c2121017005444e8102c442c00c01070100a0302c81c00c004000c1d1074407040c901c1a002800d550101d1841010030300602c210200c1d650700b404a001b2506506950780145030b400d118403005521951400028424014480715403054201028078624004241181ca00d2411040c4009483c0341c1c4840040c200d6000b0926070486e200007541c3c0d480d8401a00105081040c4803001e04c1031100e81000c0509881c0c1c03401c3d0183c000c0320b403200c0041d03035001440c1c0d0749003001500800040c0b508012541700d1031650022409809281400304805216200c00d6100c00b50907801134900380c58400c00c0d03007001e803428000540c000e02a8501405a4802200801e43e120000340200c1c1c0142c100c0d00d003a805004e5594165015544004143c500b0b001ca02d040804140301c00d03000d8140f0074014140401c0040d5421020b2204899008041c4802c4011a401c5070b002500041042c8406003010003407504400e40c410b4602984071403545a442e29401c0d000c034400c0418078160000704000070f45c00140040c00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 937814784 1250 937813534 937813537
    0x2d0310060803090a06110a2d0807020f041109010e0a0e0c191e0509180c040501170f0103031409090403110c01090f150c020a09050f090601050916031d010203090106050f06 75
    0x54110300c8910711390070b5018561102215403000a103030b5038503d0050781c8c10411054003c0c528240225441c4484c65508030410044400c0768500c0141e02d101001840c1e1594045c03451080780070001800401071320303540e45010040d100101d13010011401c000628038404c0c114030104010391580d600d0504450f800110004c81541c1e40c08410f11f081c403401041e030314025502e040f03c20300b083c007a014850b040f90800c2500d84c009a0890b01603280401c0d2a4079010150400782503616100d80100744c0c0481c10342e441d546051310002442d15450006030820440649582c40d9840701078052440303903036035a40d01010720220034100300d591020281002001d0703034100f0a4412441c0e4502c191020b0442e0040d0007044a10141d4144011078002900208025800600c0e00c6c0345501880c8100140411446650390706002c05440301804d0195560220100c0c4c0420000c15040c10401d0345c0755101c0c00c00240c86020b41ca00000c01f00340d500811407032070307400004101240400f8003860000b004162000c1002c60390303020000d03409 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 937816034 1250 937814784 937814803
    0x130e0304060819060609090608120409090c081b041a0307090c020304120b0916150804032d0917060a020c1f020a09052d0310060803090a0611 62
    0x700442d000105848540341c040801144407189400c1264580e5480b0141c01d00180384166100145044000140040d002c00c101000a80066603140f9241c104040c103402040740d03a10a07150300a02c184007182c03c2d1750400c041004031301003280c540003610460703040200307541c050f200c0c0c03000c0352000180044190328000b40c2001910302081c1e000c0307401a12480c00720702d5070040d0b13800005001034101700e035024071801d202168020000641a504880d445024506200132144100144400b10040d5054050300c24008982c04c64803900d4520f415901c50312103040354080c82c2c0d12561a41c1c040901c09450720f500449607900900914811135241d4032140b85558545070001e14420420f40c0008040390840410301c1401c0c0076103a00c0700c030140b401c1c0140062a000f50019900c000114070700c503801048920b048031005c00101099122589800009441e101d441003d41900c00d4241c41590f0040c5140d001d68011200038203600c600441c1c072070800030100135030011540d0003c01481100c1403260980540070441219 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 937817284 1250 937816034 937816037
    0xd150501050714120d33030f15060e070306061d0d050f03070506151e010c02010315230a2d03060f020703030f1505150423130e030406 59
    0x43d0100104085030411100c0003d85885500c000b424101e000f405a225010b07448059440e54400030780c0b000d50f003100703144404503a0315240c1c410608000180700d0946c42c1248610401c658034804c4402d2103400e040d9280c03030308440e49200107a010403e410f45d040c03183c2070080c0700d1407422070903101d201040f400400c82c1000701240140306510700130080c800104490012981200c0403030703640b25210f081c01c4d41c0350401501c0c0050581070801480285260251084604c9542c1030b0b04039030484000d00055880001c552004c9041c140c03aa00011441c2005640800c02418404d240121205124180740d1250030112050341c07068103030940174030062400259841c1c0300c81c0400d000b10143c000500400060002c0303540b000340024100001e94030400e00d40d070050410343d84281c40900800044000300c0069903c02d001a03501c07840c50700c8040003686800c1440c000c170104529021450700351541041e41c10220740f450860060003004080303164905001d54031507032129a02078100145000390118a4891049114900 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 937818534 1250 937817284 937817303
    0xb0a0207051c020d260a0e0c040e0303010810050f04021212030901091104020703021f110c06060906030715032714011b02060604090c0e04080d1505010507 68
    0x1010030600300a501c40c001001d0302c00060411070b03000003d41d6034400c0000040042c00c003108000404102540500e610300034885c8240641c0c0e82da011000c01041d05400c141030510030110078440c1074446114080002d0341c480003650352036050511862401c85440a800c1802d072a010801500b100e0003054981c000303504460107000140c10b40700b820300c0c003c1c20015041180800005014001105500c0303000da00f44141c03010301800f0000e000f08400c83c0a207542c041d025030402d0a848800311914042e6254446481c20006410100032104014070380044c010400c16901001c14005c0920f444076200b94448401c8004003956810805585401d0681d85141004d2545a001002e043c00500c08103820140c8072503800501c16040d410040200c00104441d840c1c0c41d443c0091034185c6c200c00fa0491841d4100680003064586c8500003030100400d00040269900c25111f4008580360480202c90ad0045000c1c21805485605d08504141104e449042002032400000c070b00300b08c180d80240580310030700d030020b1615 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 937819784 1250 937818534 937818547
    0x912020109120f150e060601110d030b120a05100605030111070b044103190804020409050d05040614030402211509012702010206040b0a1b030c1206030b0a02 69
    0x203c040c1c002c20040080280c45618034144c1403641c040c20358503450404a038466102c050054038100031a140b5a103240d08141303506130640b0f01a80100c059a080a48101191000302c19850306180562008a47d40e80000512012a031214002c0e90050b041c110000c10a5030498007500890b0311407242d00800c52404500010103004095200c400740c5803601c0110030034070310007080c464442c040b05c1d10080c011609800d6080503503800001552050b0640c6a1420180380000e541a20100b1000300100d90107915448240c0c0011800e00892404210b607848031510355040c20303005840325510350040c0c01400c106104000160751400c24840f501c0314054201e000c0781d9003800d0350a05207030f41440d940d000303114110280940c280c0150702c240710304044003442503c040c0e021180d108071b10040e8517002e80103900030004280880d03680c4030490f400070346e00100020010070b030103a041c694040400b050000300f079a500e0600300054020055851400c94180204a01801c43d038600c0d406140207440300d040d00f94080382d40f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 937821034 1250 937819784 937819793
    0x6070203070c050906060316091208030703051509190905010903081e07080a0f231005090103080d050c13120212010e0604140f10061502030c060c130302060c0105010303091202010912 80
    0x4902070900d0b801017000000d512f082c810b101e5070003590a6400a4034100000c1c880840c842e241c03c1701044018a4104c40b6103c0c004103020b00414103400e187c00035030703585401c00090030902c10f031040b4603c65200c05940c1c0c60545202145411209030b048091041c100402c0401e82d80700207460b03402180c201c00000d12694210009004200c00c00707498090207240120442c82150442d420362041c190341c00c0765052180c8803c00d101d1515820311000f0000803051003050750310903103608810380c407200900f1a14182802000c07212a001b1140d40011585180b0800c0003042d4207080c0d40a030b01d02c000f000001c0c46030019204209580d03e40c001e02c09000d44010390382401900200380017400226005408450311000340300c0144000b441a4424188052030400d5034680300c0303001006440d0415800701c05040c4507550f1115144039907100d040e402d01c45407203981c0040700582d2454080c0102d41c615500014a0703605519000d4141e40041d040076007002c2c030ba0f01c407000c0140c4c1c1c09003071030301518900605644443e50780d182 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 937822284 1250 937821034 937821047
    0xd020a060c1e0e040b0d08070803061906051908041110021f0615020105040201050a1409060304030203030f060102071503021c020406050a121a0409050c0306070203070c050906060316 80
    0x4160400b02e00c10741a0301d000310790008032030503035400444003044885003a4040040c044254100101003000610040d400310340540d01035588488081c1c08070720000901d20036080c040845811840103e0340105500c21200010704148207041401e040c00342e0181400d4540d0004080c09a00381413041d060740b01c01d07003086842400003040140803001c4c200c204071841c41d00503001d81b495010f40729007143c08403074191510380b050061901650f0107845451500c1341c0c07054100c540c81d0a141c0c103c40000c0f000c210404a50701c441009510a0b03010740d0146841c2d06001c03210100005000c0c1009045500040040c0450540c0c9204184403040300d05005903104442c81c5400c8005240c20341a103500c0344085400101036800000500a000c0541c1c0e6030401c2d01d0151003000301301d98183e0007580c00c140308202e1580c4d281c10a03030302144070140520222401c843c070783c800103450010112250720050300080360306010400240519406054100da0041c5540341060100394030380001001000d8010443c00c150080501800 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 937823534 1250 937822284 937822307
    0x1090209010c02091e0a2c0102040803030a0c08090a02060a0c4403070816022a1806090c1e030a021209160504050a060513090201020601080d020a060c 66
    0x3c0400501c2c4c507005d00040881e15805131004a2500e905001600800b0f90303200d4600c28140300c0a060016400103030740d118001204c1c0307580e080550340c200008140200c040002d103101c2d420a40022030f10b1948082c0c014075009005e0130000c03032a84104103d4005035501003e8900740c07000741ca000361004110f81850081d0b9580c804448441010081c07070890618111f5440451401d9011a20551103040581039450f510040340c400001820910216040c00461821500001301e184116000c0701145690780e400f001052a0008a50030300384c440300c2045c1444954242c1c021550030291110380707000804142010402070404903128000030720000700d000b402da04140b442d201d00e841c05841e4545000c240009502511034031000c07107501000501c1110000444000b04440c401407149600e15107018400688006004c124417542c031500049132648401004d000c00040f5244003103010301c2d244c000a0306200d01078001925a81010940701d0300300c0d40020354200d0440d805100010611111501202d8203076008 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 937824784 1250 937823534 937823539
    0x2060d0f06090e0c0d0519020d06141f03020102030301122301050601020721151d21120f070302160b1f12061d01060806040b0703020403080301090209010c02 69
    0x32000c02d0807001540800d210411400c203c901c0640d10204001402d0007821001301143c0c04420082e4030002e004860b0f02e070451001d41052a0541c0310755440059400501948400c21890000c1004400c0c0d058544540c0403c094021440c59095800003900c134803050041881208410510108103c14440c044982690007640b1591810346a00c0943c003800f81551454010303c0781c014003080d1145640c022840105a110010b00480407603aa052451064106101d00c01a591600600103c4500100468424015000c1c00c40c003501268801071000083c003801c0f03803024052050312400500d500545420400b1070328031031400d5449c80b0045029124140c900e500000c802c90a07181040643d591850251901207c22080007030189120320700c43c0d1b850720440102038403400350700011a000d940700061800a07181140300006519a0943c25074140d07500004072030b07010300308000a00c00d5441400d508082180340552905180d6140c1d90901c0c00180501695203600003a0540d160380212287c1105030b902 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 937826034 1250 937824784 937824791
    0xa080408041502060a142502012d050c0406140d060b132111060901020c090112140c0d0605062101020a0f030e0d031104170601060f021902060d0f 64
    0xb030328009440b540e06494104075030342041c04e031440c0c031318410b6403452144401c0d182c0079100c000305c4d16150000c401c0d80d4484e074065560700c440601d0610600f101881780180d00024880e0f1002000d81844211f4070f00030b103041054941804144580c41d40b000907003d1000181c4000da03203d2281c82070b480018031180d840721031070983c001030700d200c045148940c0c0811a4a88a10552542c83d4005094070b0300340e40050061481084007000c1307480d0328180002c0d00d02e403041841254584280030000c250002e500382c0080b881280b8146802081000440c5880d071100100d40c003520b031584408001ca244d101d04018001c002d19150000280c484c0c031200c035802603055414031100c46802c4144212030007540214410400a00c1c445070000082d40240100d500c04a031f610001e196402015101328010506840c003030500032401c100c00140c04445080001c1051090000752803a94905000a0850350f04448002d056400c0102c1c61141140550362601410303805640d4103603101e00d02c1c821040104003100e00c0074aa24039 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 937827284 1250 937826034 937826069
    0xb0408092215061b060e0c0a0b34030f030209030619060501170136020c150c031501020c1201090210030b100507170d050708100b0a08040804 62
    0x907241c11801c48500381c0080a50b2542d00e5280441d14220000141081d0380c039005461400202161702000d14450150140e89650810900090400085501040040202003001c00d80c000190601c02c161003c250546003040002e405c4c4200d21104101d4040e00303001900051000b150b0094040780c0403100000c0c1038480da86022a9030942401c607010510807a00e107424404507c41d401a0303105100528100001143e60380b03021012031300210300040d02c0d00f411154007c00b103880c10315503030303042c520400d40c0d000507885d0104154064a810702e80c0301000c4401100d802408803040c440011660010b00c4a88014a0400c41c030300141c1c83c00341c140704003507040f44c902c4941d0043c82ea01940283c855500c02c50b004141d541100c2c00880c00c1c0d41d100607510b079004001203d8102c49900400082890364844c0824054421408001b40010b40212200001c090786a00c104188168041c0940c2d600c001c4154848101702d0030022600000d002c1c5280e9401800f21110100b4140464001a50f00170320400d14051000031 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 937828534 1250 937827284 937827349
    0x903092303120d020729090708071205030403050601030b1b09090406020903070b04092c0c0603100315050f18190201110a080a020f0c01080606030a090b0403050a0e0103090b040809 79
    0x100d082580764a11010000c10b092047c042a0070003240c10803402001c4035410115004890500042d00b04c07800d2000b0800000014030a0184500841c024000c1034491f180000b00c02c0290070a6030076811941100308040741c040d90302d44104070380207604200300580721b000d40e00100740741000d5034010f620300d0a404140002c1d0020945c00030031001e51101c11038502d81040c6171404515140c1c0040e2400c10740c1081c1c40032555800c200000d50b500c2656200504001641c81d10350340391a94801440e0124542c8034001c00403003400c400c6145400c404512080c114a140517103080742c441e0611f1030b40a94058140420b030056a1160280c1d80e03c64040344113460b2078503207d10302070071507912450010740940035110003142004000f052a041424068460b0903160381c404003000031542c001099030206540c0c0f604c458021640903500d00f44114170079212641d4a0118203c060404140d12207164101400c00740e0010000356020810394205a1000c20303141c844a4000000c1d81240743c0b928000080d0380691504007040b03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 937829784 1250 937828534 937828583
    0x102090a0627170d08160c0312020c0114070c030c060c050705030d06081c090b09151204060b0a031e03050c151e15130f0903092303120d0207 62
    0x410300e42c42100d800c02c029071402d4482c07a17800c03140581e20a003401480b050b070a0003100c019000c5442464081421402c4110140c00c9801162141c1c0f2169903079107600c4107214800d40450f070400c0c3d9500f407000d21105580e40c01085046241e4004041d02d841e0321424036100c0c003e009a582655004081d00d03101c6550070701d080d0060425100d10995440b500b620b04c072170301d03210340c1100025942564540c815030b41001c0300018554040350302203070040e440d4600a000d030080b65006e80666030141664004608107420442d0a4446140200d071054202040400c0010406844400000c02503c43c0011302052030800780c41c10300902001ca1a035004007108680718440201969214040c2c0a012502c1e051340c400305112044000c4488100c9205050320500e03917403034010b119102105110101141c0c007044002100b01b6911a03040c2200468401c100500200048000c503040917103010903c145140141000a60340c0e9107904503c02c2030101c00201c042c1d0101c10741c1c0440d00482e8220301035004041080b040c00c07042 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 937831034 1250 937829784 937829819
    0x5031e0d050f06090708070c020d050102030403140f16230d0210020733021b0123070c0f1220010c09061413060801170102090a0627 58
    0x3441c541000100c011602c0c42d1858000c000140002d52a680e41c000c0c280c407000740240560041c082441260401640e50701c1c0c9030b4091510131000941c60741820300d0301170024139001c040b4941c0500c051086414041c002c0b000c1c0e605907155140740c03604180082c01c111001448011449118418084004400550002d914007000d44913508448145031402c03e10002c074090300c1030051000b101c4880d02521005401803c10405204440c0c01a070501e0951004c022680080c5c0400c8a500a200508055140030b200b00c0b01d4008032819040030b00000d5007000003807524003d117000144440d090100040c002d0080c3c6034050f05038000d0407240581c4203980082d206146014201c03807584048036828461020601943c003542c1125154002400d0030200c040d038091001d071075150f1119005202420700403000e420701e80c0c020300c81d984030b25181f0750400c0c05000d80c12000d10039002e060380c010071800c0c0079030720b0b01402c12044500d82c1c5040c2480e402d440400c42087c2100e450f180d2140040410301003a42a50706913940d45 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 937832284 1250 937831034 937831057
    0x71d040606090e0c0f0304151e0518060c12130c030303051605070507260124080703030504060c030309020907030c03051501080114011b030207052d0d05031e 69
    0x1000d41d81e410560041c0d05c10262421040f034000d10100d00020f108036000d88a8480d001004501d1a40b2140d08282c0810030708881c0103040e40304c0051121544201302200f003030750302d1301020b032206103041601c1048511440050000c07040f00c000000301c210500c0e01903117030959404001c1340b103003648e1380c1001400f8140585038a00c40b900103000c562255402041210804d80d4480094109070b4a01040c8030500e0741d00d16042d0401d200f00850310b03808800f080c4180e4405000f82650004189400000c0410410194000c40340c603070f10040041c00441d0700702065408845484c5042c1d00c1503221840d0440c0030b40b00394500250000307040c0080c45162a0540c04c0300109030b4603940d0030000c6580c3d90449080c0b106144800ca80072078442001444101400b000044102c035041c10f1041c0c1c5030701340c40840c403440c4030308207000c0e00160003940003801342707141c1094000e09141e00d80342c0115500080160600e038880140d002548154400402c040c00c201090050b60480c43c095a000041c42d0012411165568000a840310 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 937833534 1250 937832284 937832309
    0x180913030e0904020d060b0303131e08061e100512010e010b0f150304171b0105060a03031e1404080c010915080f0c0c060a020a1101060509071d04060609 67
    0x101c1420020501c0e0b2203560014001d0001c0005034542c64002c1c100c4c0c04007143c0600041044411080002d6180310013040e4071106e4180d401c0792204c51000b80341c0682c00c281e0460300400d040c44084160b440c0140c4c64034441100013034050315170000108405080d40c0c4039a8115003040c8100c04915410f60100d480c030271403100240001e180e144c00300150034000c0c001c1035603c52680c04000341c81640c180051580140300314042180d03c222206007001e030381c00607100082e42c041d00c420414000c11081c005c41d80c01c0744003501d001c9049030455a018004090078031021080c95003400108a6480c441c1d82c83c649600740d452006a07a07039032034048042d280c2200e944a940451b80103800003c07116900400c1104102550b0755450703198440811407842080050b151f9000e649040c042c05803808410b001c440c0c000c01002c1001617440d141400f02501e40c0081c20700c03001440e49008000c204948070b14112035071020103407400c1070070900913522500c4c1034600c2d40c1a007504580342c01ca01050940e04540d6a80c20344481c0f9101c0c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 937834784 1250 937833534 937833557
    0xa0f030e0306091002220f0602151506030402041514010f1e0507020a090203010816120308071404080111030f0c161e02030109060f05072318091303 65
    0x259940006842d203c1c0c041d80f101c02404580e0303660f035024180b01107011a2000091359180d00303491004105402034a140d400340034003005902d80410640140c680707405440702891030007141c140d25085090001e103000e520000002001c558485d44034444014029400441850300e4040c2e2a07060310090706d8582c0850f01e41c26040d42034500440c4001a40c080942030744d091407480313880840d4580c1080804070303080000085e011504070707446e0000d140a8014040280b0000708a20910080d215150b8802ea40d40a012085100825444800c1c079521100c03e05120101014032080840544600c0e80001c142e0751a22030601844902c080066010f654240000d10040e101c44031310105030b10a031380d00c0c9014045603000e14000150503045210541a9140c0358289100c401c0d00440d01351483c24034200c2e0041e07034038117061400e01181e2040c25080241c61604a0160003001d09801e5240320100000400c1d804c041200110315400b8807140c00c0c20780000c0c02c10091070800c4080e400705c0141100c1d040b00030a900c08001d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 937836034 1250 937834784 937834789
    0xa0f0b03010e060406180b04030512010f060e041e09051b01090f060e0a0905011e0e0705040506030c041214102304060609061707050906300a0f030e 65
    0x3400e085482d0344010305081e0b1100c0da1807200034001d008685402c0b0600c448400d010030220540d480c0711b50700039102c041e61a400810310000b1058160030540b041c2d0b04807041170000325444548104140c40c242d80c005100f40340ca0528040e1030341c85000d0800c5841c1807503c50400c10a000ca1100060121004031030074050a240064490140c00c0c0a407880856144904000f00c611580c80026800405030440600340e031074002c2002610400d80004440031450301070b0000d242c14034004240100071400c10a52641401c40c80203005128174413800e4403451003c80480c2e44171080904036002001c000944070607860251404890b4000005030030b00c49400380344510145421a0b000d100161110850f04c0031700301c2c241361443c0304804405402582e441e55580c1c004284508144a200060440c015500024040079580e2070b150501681106019015440a029007a01c806034001c40c210400c8100220000c0c0d1488013109030403c03141c44050034482d00e8240300c1404902110602800d02950300c41110244a070103 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 937837284 1250 937836034 937836041
    0x705070902340b0a0603030806040e07151101061d0112030215040302012009041104050a0302010e0d08031302040605060a120b0a03021809060105030a080414180a0f0b0301 75
    0x460501602101d1003180c840904000300c15903214820810b40300710b185480303090000504441c1940f820b0340e41e802c10700c18540c20200c2541d00c80011a024442c0760303510750707849448038881d00c40d420081c410800c0c10740e611800307000741100d10520706000700301d11540c890602c6900d44ca82820140c0d020450740011800d115900d2091400304d030036400a12408079104490100c642c0018416401c42d56a4580103008000c10385810b0322021400400c01c0e01c4080c15010001126a905200140090704100820186e02c50410b202c0841e070702401c040c0300304990040898689c00120380000c258540000401c500b400c03d289000e00c4290080c0d40c10400c4030703258014030110303100d4000d07a1800725205181071020b9141540000c05050000381c200d49250ba52940400c04c002392614203a010403808404000c452842003140c5070041000320018003000050fa140c018084c8514081e039402c400342100c840e51561550101c03c1c080d4240b210b021038503403038000e4098008011001c0c03104d02040c00c040018210303160501 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 937838534 1250 937837284 937837297
    0xf1503050624040203070207180c023a02030316050301080a151e0f050603060105010f180e0106110607030203010f091508011e05011a03040809030c150705070902 71
    0x800030074030707038851181a1042240d41003060050b21264041400a80c5a90010b18003030701c025002002407500b8400c0000b881c16100b40342c06040c43c6400c240d407c40710790000b0310704104020718006194000c244071004141321003125015480c140020b0a0819950b80000110302c07030b600c040040d103500d58101004890364403080c45803040ca40d0011883c1c1c00801c280420b200100c1c41c00070000640c101500440c688603990940c0307e0856595030b1441c3c0c00028849026440d071181c0c0442c050003240d0704003c0043d10b003000d52000340c030400c4a14182c49041e41d60180b04017001d88100926a8210340c1d403100700825201140c5250355181c01a41e02284005009000340c9042c0c84184c6000a4000c0c284502c0e08001c0c1072211110019403415200010030034000e1141e0420418903c007500c1080c1c1540e00c4542c2510810707801010014000c04c20084443d11a00589402c1a40948290b959140324800645040c07a0702540b07581c850071144281e88130600c3c80004002491044080c0c94401343e5426009040f4010113 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 937839784 1250 937838534 937838543
    0x20c1c09060906050a0c06180201080c0403030207062712052407030c0212132102010c02010507020f0907210b03330a0b13051501080702120d0f1503 65
    0x80028084180600d02034605c00c6030b54074217a56540e42689880d0159114444201150400e1031003a206550340280304a6211600c00c41c094585495694020364a282501c0b46404015807246421203040001c450401c4c4455945407258441e40c40b1186480a11710b04a801c650034414060100e10a0100c241d1080701800ea6a051851a9440718401c0e00a80040168901140540302403c54441c60940c06420425560005071b0700050500c0d19140d07003000c1c0d0081101c400442d02c510717040181c0c0e200c107030700003025420728000d40c861026101099003841050300c00c4e40c4c4a100402004000e56001005104803010031444100c6c04914100740e8040368685203501d60550004400994100225103034954048a00c110007040800c3d0000c44c4401240103443c0240440d840d005c0059440c40e100102040c1d02910480030020313400d0901540c802c40a90610040c1031010710800129102d0080c801d80e88941601039a050b501c042d0343d40507000a0417240010030302107103080b01c42c8441c4405000c0307080c1034a622 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 937841034 1250 937839784 937839797
    0x11060103021c05070b0406020d02070f090209040908070b0601030b040b010e0d05030f0f0403150b0d0b0c0d0c030902120607080c0c2a010e1903030e13020c1c0906 71
    0x8540a101424601510610380c01640707050b8280056800c01031840201140075010752160b05200c40203040c00515604401194000d400500c80401246004000c8a40820006a4032400a00424007524203124050160b9402140e550103101c8440a81403142c40c0903601007003c0325042007000121503000511a0008020088500441c10021103451140d0700600072241041800240380b03803581d00820303140c080ca00e40481c0410800401909003420342c88130f100c0c1405001c05030404110302c2c07140e00c000501130f100900007050801c003030203040300c0c50368800d0300d024800300100750300160151030041412402480003080c4603103940340216190740030702400c3e0b69003009a01c0345a01901d00e0b0b0442e03402010140100c1d00d034031252905a00c0e00300b03148a030700035a450003210307007100240010302c200b01c03110300507290745d844809010800304288043d6a41820a14080c1e0030b6140402da05a01c0300c011a4106032000031300c13200e50700340062580d9135410190498018158055003c41c0c2c807a2152099401003400d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 937842284 1250 937841034 937841039
    0x90601140904060906060602030a030c0203040b0f1308300702210c1f0f090311130b090f2a030402010c03170c1c0212010905040201170a061401110601 66
    0xa00c0d615030754010b8003e0303001260000681d00c031070085400650114000d42c1c00001c24041050305401400280d824070300285040900e443c0300c0c1a440e11030010300104462002031410381c5e2102c8044040d01401000048800c103950002841ca01c80203110100000074090b401e001e280c042c000d401700d0b50b109a014080240107588403808500000c00308c641302480780255200c40209848c0c002400c10b10088100c655031051030300303540c05011fa07418150030404010782c51800b840400c201122824208005890b11405e15103405810300040c0004005107902410300c0e014417212488013554030380100d80350307103c0d00c10448991400000c1d030014200c10a409000520001d000340d802800190106030103400d003031741c04d88562513613082d4400303084540c1408100040350640007404402a0010314103c1614110300e01103040d0200850158140b0072002e1040c0c5500005086901c201e108850421081d441030f0071608110ba103081c0540110b0003941140c1c2c0e0407030046106584204580c06082c2032000c0070309445d90 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 937843534 1250 937842284 937842289
    0x10b070510110c190c17030d0f1b031505060f0408010501090207140712060207020a030209070c03090b160605060d1209140d23030c1009120503040503040618170c010809060114 77
    0x6e80f0782c24101d240001d10041c0c089050501601c0e200102a10000824441d00240742101c581a01c00f12010186007000c59900d020404d00c41005a84044071400d03181e1018000101591040c1d4100002039400c010002504401640142030003d20854a8008aa25810b105a41e5140342c1c80b036501e02685900a003001308001d80d00502050703001070a00c05800e0340340c3d004510740700e0f415100c580004400010001c1899800381d82000079100d0360700713410301e0140c9130201003402c1e0108501c007520056417900400c141d03603505000840803507030220044104410000e40a40509403522070b028042602e60244c5800d860b1445080d034040e94090a03030b000d40d800d0303000f1903840340c030440d04581a284010449002c00e4102003100e40d212501c1000c010800c00c445140c51000c551a185202c014400709100b4000064030100a6500b0b880d460b1900c80e454040240300310a0007046035000c00c0042c520603101c0c10b402c550210360070100e40020380713514040d901e920440c9a42c40b402403081184002c1c1c4480b105e01da92 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 937844784 1250 937843534 937843559
    0x203120a0c121a09221b0e0705130e0105100f180f05030106090e0309010c1a010b19110d0e04060801020d0204030b0f0f010b070510110c190c 62
    0x94140c40c00ca8040b902618829040750318071520b1121540881801450740d28218a02a6000103c0c0e4210010f01c40c0c2048588031400d8494402031164418004e500c481c0c521500d04030300140f180070340980140c2410f400160855010f070343c08441c0ca0681080102c1c0441041d010a0f0480c0d030042c00300b80c006003000e903040381d81031f80d000ba000342045460401d9158203a40c900010010b07101e002c0e0329030107180c13600c0101030860f00305620040d1500d007070100180f401c0384003105031103481e1802c0c02d01c03a801060600c3c00411400c004075544a012090b9000801c500300d20300050500503a85082d4101c0100480740281c403074444510740c20a041d809243c0d0188031602c510602c900c2d181029001107500c1e6102c15500303080e81c115071384100c0c015a0105080052003260410140c0040e094101d441440c20b05a03142c0754440814020f0482c40030b8005150303010481c0801507a045d44036201030411816104100c20500750b800003038400580c0c0301d1000b04048190194021100865000d801800d540d489c10303020f00103070b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 937846034 1250 937844784 937844801
    0x60f020718020d0905070504062903090f0307050604060b0d021318060906151a0f210708070207050a06050d0b180901020d0f02040b07020f03010f06080313060203120a 73
    0x1040d001d0050071180c20f21401101840c074030440141001c05e00301003d1204071138103580a942c00103202d803a500f40000c1c484000f0a048a10f0441280e5680c2c4d461104c145050800442c030b9015100000e220000d0010105036240143d116a2040c80f0443d8514104240b840b09000081c2d8002001120452500503e911024414a02210781c442e00d041741c0c0c80c2d030b03002c6544040d011b84465442c2c002c401c800040c202c4919002d0440400060300415800c8090300d9076001e80c120400c1c001100142e8508040d00c911f405180880c60010040381034030f0b00c510002c0c0450400e5035aa805445a04004626860030610050a6071040d80d252030811000b048450b0140c07081c44c2c80590001c0100c418507040400c4503800910600048001594805810102e00708586841d404002e00030300c103001c203104400704042207030225501128a401007804480019006004c42144010054601040052601400300140c8103040c100540d0400c510356801c8140d03180d110700304181200303810f0f540000e9506200c65020420 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 937847284 1250 937846034 937846079
    0x180f0601090612050601021c030603050c060421050120120609161d030d0801141c150b1903020108100302100809031e27090c09061c0b0307060f0207 65
    0x400001c2083c2208c9400e144a00b140026111170060050010030421500c90290a031503c078907081c500745041c980d03001410080cc4042402885000c14018250401540c004404403000440b500c200e80d400f51603406240d001401d130036042c0018407a441c1c40075045124800886009040e003000d424100c504015030301041b90600000d520402003030310104041c03e594002600c0b024459410030b0007044d080d10170302c054244250082d00742140b52080302d4140110f079580c0621a0f41c010306000303001d107000c0c0c492629110b4008083c4090122401d0300340000c182280d0007a29440207585030300034003000300c1c0d1807408065000800c1c100046200c038030402c4215442900d481c1642c1c203080c03445900c5c107059880318007440e6031000003007210450807c581c01c0c010f0020886841d040c2c10401c0f81c0d408101c0034000104001c90080002c0740fa14410f03155070003103843c41c1c40c14610040f079442c01181e42000800008075950301a229186000c01d0150081002881030740607500200b00080c500311726848210a100395801 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 937848534 1250 937847284 937847293
    0xb0102010609050a061a04060903030e0d02040f0f0b0603010b07020607080d020c0714031f050709420c1112060f0103051605150c0309180f060109061205060102 70
    0x184940442c883d10340108040e040200e8003030b240020003040c1525800c0d40048010080004000c00d9820002410840f90705043c400f03503a42d44400040c03a904044603002e074115003007980c0c0050303101441e803040091078055003041051455117418442c8500090113080031509082000901514100002e010424441d04803985000d00e6440610b099030058552003000d54440003050000800c14a1105601d0400340d000b40b0b0303070320a05449030480d0000c80424000e00d640d100e020600c003d220340c4002000d028aa2418031581800b03400c0050010043d4801122050307110046100e4101ca00d001140560050ba5440d0440d6030320f6152103030f04030b8114420552081c3c0c2c25030001d0110f0700500c2807912031180c0540f80030f2550301d181845401d208404580c110710b01d440c8074081c441640d44011124030710744140c192035140d0300c11038075140c51031040e500e10603800602c48045d01035003c07900f84060311440400001803925191000196502201d81c01000f000c1142a0105601410b0550009500400510454 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 937849784 1250 937848534 937848539
    0xd02012a020c060d110c0109021507030c0314160317011e030b060a0f180c030c090329090d17060a061809020a0e041a1f030e100606110d120b01020106 66
    0x2500e846d84080380070b611594482e0200c100798174040341c005a05500c42a419840c01d1031990b001030050440b0b010003000d10004002008181c1c00da48207483e11700c504664401d64040c01030130080c10740f8003070b00121164080094008140d001409a010f02844030352200b0056103401c1d682d5078003401c440204020341054039400000741d000507c910030002021071301060030451007185002800e650300000341c903051605007010b08006591100301c480480e07811074050034600c0d0409504000304a03064080485c3c041c41c0781c2c18400e001c4000f280503222a55552217400c150203180740080b44100c01240d02691000364550100500c0e406404101c19000781050381c101c6542d01e82c85420100d810001520000a12140c00500141080e100701d580c1c0f80d100011200c2c813045080001000030154202d140880d28803000102c9495009412611010384c0b20003e44280120030f00305040141014402c1d0400a1144001c05074402004101003548200caa5240380700125000044000b50a4616003241150750b00e6100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 937851034 1250 937849784 937849811
    0xf38030a053007060903020c1813111e180712050423012004120f0804080f0a12030b032802060301030f02030c120c10110d02012a020c060d 61
    0x10403c0718404c070000074800d00b943c20300034030780900151b0b41405144620000e0601c140c6490695502031140c0241450b1200107142c001111654425026001052010b03901c01c00110047c00101008013911204032940d08103000c0102e1440c01e95040c0003041b14003440c2400000a900074985c098050030039041c5c0c180403a44100140c1090709031a91641e59103070030400c0c0d20760b1212402c800c04900b0322103071428070781026001080641060801016140c03c0b0401c80100a5038600303071401031413840103544030716030f28401d40d94650705030342c1d0101c40c000035400584605078000e120340780c00e0340c0c4090004c0031701103400c210380c101d0800000507201e0b0300c8902068850050f507801000790f0195201c0c2000c013010b0b003014410303d4074048000c0813862054246000381d500c08040007500550a801c21282d82140a0200d034081c0c8a1b41030114000c00e09000352100d4109454054020f080c80035603000d11030036592080b210340356000c44074494110060b00640b620071a145010f001800305d07001c10403400920603101102 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 937852284 1250 937851034 937851037
    0x11030f0a0914030d0b0f0d0b2a040f090b04050f040209040c0803160c0e0105060a050708040b21010f060f050c01060f030f03090e0f0a0f38030a0530 65
    0x131950308060302c4162072020b030b00300b25000e03400b00d21065880d100400300701d66030b40c205e48100030a51b81c00149400300425541c1c0c1200a04080c00403460b4000d56242c1d01c460380c4110320320311800340c203000c1418a40020340500302032107101d201c0d6001d03201038120f0744c07119402c00800100180065418039590940411055018030003019405144041900f07001d401380b9000d82810102e51180c41c0541581d0010402c0c0e464000482e5143d24240c5080d907568882072420f07951078000e07504111102080031485c07904034681c04c3c1c150504040300c0e5040d884030381c0e80c07032010001c409000d001d071300c00084a40d09001c10003806000034107035080402001240c95a10343e04403401d01c0c241544203440e1104c40010300c2e410b0641105000c4d0161465200003039131132415480d040b40265014055409259455002e628848100e0f800780300034100b0900303a21421141644114080003108144400403102c80400050614000800300140703540600503040418001c04d0700c810351061100080f131041090550107880713649000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 937853534 1250 937852284 937852297
    0xa0e01111606090e01081509100501031514060a060c050f0105070e090f01050a18090605070819200702120d031e0e2e02130911030f0a091403 62
    0xe01d508012482d0075002081c070300340303603000d54101000803006101112001c10079100704086802c11817640c3c0c07507500040e0b141810307200c2071080c00c610780700002c420050310000c04c007081d903402042442070403a9405e19003922202a50011381c0719649540c1040428050701e00032141070700460607602d003134030a031428030700b507410450741d4100040c40490800300b00d1519200c250f0300002d0410210301c2640c10040484d200c0b4880d4010411040c149107003c840a1305540c012500070703030f40f000003030101b4200020060880c0c070701958031501100c1020800503c3c408184a49441ca2a030241c00544c1d001d22104600032583c0402c406907003042c01d0101001101d2020403a400c0040c00316a03001501502d0480f640d54194201c01c01c400b081410203103041d2443c1e800107410310b14524011021031403074034050f074006020003039040100d0020b400490504420190032444034101d8444040c10700c00080319410301c2089100803160b40d0040c0801c84042061a03440381d02400846c2e200300122100c1c0400d10018514541140c0c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 937854784 1250 937853534 937853563
    0xe100f1202160f0303140112080304082115030312040213020708120709050405060d0210021f060515030f04120912050303090c010504080a0803060a1508090d140a0e0111 74
    0x700c220040641c98030401002d454075006d00820795050000100c054111030340301400000c070100108003401401800c440300407a50403001b1060b550303090364902c4001000c80d001d40018031203078885041030030003104644107004400107500c21947c980d420400c070214100e0b003203c03440c0da003440305000003822080201500d0015003501c1500d4a030046004101e600c460300001e0189013000305100c05502c2d40071803c1c3d40c00e6411224626403564620f0101d02d041004130314014082079241200064521035840344050301c0b8151030824000320008081c01c03591100755050341c000320341e280005012803080000030401030f03040d04d85891101c0d42c40c500d00b940340142c68030545a0b03400c00424042100e40403c1104001c08080c00c00c2820035252413130054440702d00c1d00d00581a00800070006401d41e40700141a405010401900440c05000c48802020030008070764004080c85201c0c0740c412400e0080d90700c59000000d603445646444d4102c03030b00b1a4900c01152119050000000e44000020400c0c4100d40174000b00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 937856034 1250 937854784 937854803
    0x8090307080a060b100c030804110306011404110408071203020a0b101401030911010e01020a050d03021207020648090f0405100e09070b040305010b010e100f120216 72
    0x350a1000072195074100c114807517940340b060019015000141000d555400d4240031015584908080a00081c0a01c200754940252400424540c40700080d10b28400010f0b20200004011401c0580581c403550160010700e50103010100600358400c601c0500851103441911030341003580e0390740c40c1d400380d0590b00300c4513000d41c00c101448585019100028801d00900e004d01c0325040c10744600201480903c011030400c02d000c0b0b1649900d034020005010000c6d0b10400312400c80140e140018001d4200031080f001c02000301b8082061140b0001d40e40d4001c003c03180920101540e440d18210b2080300081c504c481070340012203070b020f868601102a4040701082541c0d0307036451550500300305210311b545200340d1049283c942440142d80c071440c100001d0b81c0840c000348016407100b0405504e070003101d5010132043d0100050203c104803041d04098044042a203c640800c1c903900304103c0c0c1c00221032110310005020038542c88a90740324820744501c19011190042c6007210141214048030f00034a0192259140c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 937857284 1250 937856034 937856053
    0x804090f020405010f02010c0c020108130b161704080f03071403280c0806060f0903030d2703020607080612070e0910060e0c03190f090203070806091002070809030708 73
    0x1c009000c440c1d6a017817440200030a480814000d46a0401070038013a041142d440000340514040c042001c0d01c49421070200180c42c6040c031280c011454044980d040056a42806804040c44500305207014a41c84035a0900705514007002c2040d13030300000c04041c2000161240f4a0071040031400840c010910f001c00b0340c5801108031041640c20011a4040c1c4000340b610300d054100ca50320004140c2c102004a84590b41c0341000703451900a8007413440202c0d4103001c0000c4250104900340d0124207074a260340e00c0500c0e891342600418441034141040030700541c0000c0700080e490f40c030400e04242c0c882d01c0241809030310352404c0c0a25150441c10b400161552401c50140044040100206c582c0304041c03880600250341003c14003403002002509d011203109000c00441c1c1e04404100104854041c000340400030340300394040714006003241c42da0690080c01313140c6005c5200000407031001d20a003030010040008052900c180030080d446141c00340c3d0350803400e00c4140e6203540c040c0f00d0305000f80108801001001d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 937858534 1250 937857284 937857287
    0xc1b0507090b0901121e0c0e16210213030602030c0c101b0c320106080a050d1d0405101d0c0414010e0301020d06061e02070b09061621050403110d0804090f02040501 72
    0x109c504044c00511240302029548002e10441c5500d800702101005030b11240d020039514101042034200526143c000300400030030700c0c1410085d000034842401291140394210a00100301e804d1641c031400001c1f03491070b940501c03d008184881009118922442164003202d072485410003000301e115801d4000c500100000780400d0261402500041018009544680d9140d607a200e204418071001e01084040c00c44085d09040803001181c00040d00900c458549000441d0240c015400752040302c0d99003240b10103448440c41d0500d4440c00740d01042d10724080c00c1c000040c1d040240890302d070f810014070b000c1c04541624203001030b203040340c21040045041401c1400c044c3c00800610780002d01021038101400125038006a50412603030f103088015601d144c0e503000309900744180b20b4404100190740c090402003010340143c02c24135901c0421300b80d821114859045075144980e1201800011141200d0309403843d01401f00035460780705942017403070203959110110075100d00d41a150002c5074041010407055 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 937859784 1250 937858534 937858561
    0x13020f0d0c120c1d040c0909110a12020a08061201020418200f040b09060d020c061f1d0c16030c050d0309080a030c1b0507090b0901121e0c0e 62
    0xc10721820455488131003021402080505089400d00c1a91500e11040c071103400741e1250f0b8090400d441c0c0504c1010320000300101d040d400618141c000440117000742000880d6031080c0e40100c0004d55810300c5580300c413010001004d00610810142c2c1d5401c03c0005002089003031110300740da940d100c1c08181000030842c800d44900703121500b00c0c05a00104140c00d000e10784030f41114151001849480c2d19074000c1c1c00441c07014066441b803000d00c0c0c1e200040010b11081c00051891003405607000c141c0b82c0110410b0743e5030b100d0000780324010079281e800d001c03201085554542c582e80900102031450034014403a034046084804004142c01241000207044140917080c04100155481410280010350301070f569000c1600c0b40441ca801010b80e90424026520700c61a0401412000c0405020344104c070360030031039294032561090460840c0b07071903800b803858103000300c1d43d034103c80b051071914140b03404ca41c58011500384021000343c05041c1e0010001d00261000200a02412404820107280e14121410702d01e071 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 937861034 1250 937859784 937859801
    0x403030b0112230f1b070f1e0c06090f0512030f2a0a0218060f10090915050a03030f0e06070b0108060a050108061602010e01050a09120e13020f0d0c12 66
    0x84d411301c50200000003041c007900d00d101c030340c05000c0f1940c1c0da40542403828008084030001045588007100d1414035504800b25214518024007010094544e0b40030f043c0e40c490f042c0e100b0540207500070002080f031454948200342c400108081500d1605207034400340c0340750b03620001c210004540d8100f81102d2403201005090101404003000f4000456160001498518442070244404143c8000101e00741c03195034100444240203800815060000d05c8e028250001601032068114984288035901004260301c0c48101d9a0140510f01e81c1030441e10211040e600401d0720000f03010704010492900c0c0c0303d0900500c185802205007491550400500c142000d5010304210886410400140a0031002048160304109500c040e002e800880003016400360003180b1518245500c0e0104218016095802c2904120300c82c00309040203103000e00f01910b03011240d03800144c00650800382000981410780c010030b04101240605800c10081a015100ba200e20304007070b50000d50079202108100c0b403e0f0141408 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 937862284 1250 937861034 937861051
    0xe0a0f0608010e0c071103010221090c19030311031c150b090f0402030601140c07031403121302120105040309030605100608060402090109080708030301061808060403030b011223 78
    0x101030070001184012030142c45c101074951107015505101d035903000d5044401c0c50710704407050110500302c0c04516130740410890b01140c2c40d010b001600303c41c40c0340c600800101058080840d155072411901c04480c60b09505150f944503110400502d43d02511820701090010010341001c00e02d90004400e014416682d6030261504040c24000c111944d9602c06080c01c02c0b81069400680381d82c3c5490040f102d07040382c0b81099031055000102d04140b150040703001e1041e2400b400c0c4200c510180c0b40d81e0141e4a10480314a00068032400001c1100900f080e03010b0750341c2e40d0000f0302c0304030300b500b40f03107442402c54505540880c0400d091000800400510740129680800309405000312030745030010180650317170000c3c1160705c260b80c0002c5c0b5482682c0070b0204003003d40541d0007110a4661548112581c99000b8081c0402240d40c024080300c200a1082e00340003074441c000082c0204d43c072a5036090700030707100b8403240130f050001d0044404481030007440303250003041201e442450b00c0143c2541c3c40804c0f010280c811354 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 937863534 1250 937862284 937862309
    0x130213051005010c1a04031b050f0111031006030908130b1902010b0d03081306150e0f13030c060f0c0201060314030f071e0203031602270112030e0a0f060801 69
    0x80200b020743d4070b4514010b0303040c1c03005261031b90707a49005c54600f0022504951944241c4030b40e10107100d400510501c10b46d01c1d55000b0000b42075059992000c901040720f54844a6540e00001d01030315211780c100042d880c0c8604601424101214404880c644564004c007600c180c0104074801e0341c6002d41c02e914103a803040c0c0000c010300c00030f86000c107265084081000c0c05004400d00440e5080030440e0748130307000740e8009100b00040c40640d5464048910301d8801c0107103c410020100c1d441103002001c0c80d008807181e00000b066800a541d007901c052610410030740d6081d0355a04450001c54860040880e0b200c20382d80001400c0341986800c507621482c00d40b402d4403e51044c0810301582c801001221070261f0403606411080c1d801400d1451094400c250003901400702040c2c1401e8140d0030742400e00818403c031007810a8214040b046081c03540003600301800600c80c0c00c0104840e0542130415204e503030291600f00c1490600c070300491031032901c40d80000c01100b20b001040110030b500110490151860003403aa = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 937864784 1250 937863534 937863557
    0xa08192007090b030c0a0b0901080a1406131506030b010f0c0507092a020102070b090f0606011812080c0120040b0a0e03011508100204030b040b13021305100501 70
    0x207039950740c40d0103045601c82e07498120328a030b560100070902190800a0004060039222403044900d60021000c090118030044007103414981c036030059880085400450380150f5680c0b00030003440111500003c4c001c03a03a140e0403d4500203c00b06114054401514046144542000014001c41c1001500000c001c09010302000042c804101d140481d40301d44000b04103c8008940d04040f221140d45101841305100d2101d0b001d180c064001d040000d00030300241920303039140e03501d11740c591600b1195488076410180c0007484540c01800d040f10302e200303e8904040ac5989642031214000000e010a5803040d10119842c8003000c0c00f40a001e25210741c02740d50089111030075110018501550058060318500401c01d00c00261091101ca03d0788040200244444109010030160700341c1540940703603c0d800750f1800311544011600071a002c5a1703008800d44215030342d03501c8441a920307014004229041c20f600d9641b016a640c12101e0019416404c0d00183c1d50500c2403c459201045038046030500440d0030b0714 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 937866034 1250 937864784 937864847
    0x110112110315120609010e100c0c0b1b04240c02150a0203070803010e0702010b0a1a03090705060309060703150510050d11130810060b0306060c0a0819 66
    0x140ca0300060710301c1510005500440c0056082e115543c0189043c0c8101d408010340440b054000700074070304401c021383c0c0381c48441c44c3c00c07107042d90319121080008c0ac006660260005100f508000c0d444a00c59450b152906080248801142e00c00e03804410036010403040a166400c241c1034102e4645040d040c540001c45450340421005101040015909078012541d980100c1c0240708070313130309681c3c0204003070340c0e03503031100c48140c58428180c030440c0045d071030208411900d090409800d07040e9800701a10000e03021072000000c10540c00101031a50030300a40c4c10000d0140c441e079010310700411800000e800309181c0f988008044a04890440c2002a81103a040140d92101c00d4640c00380d020903d805691030401680c3c41026000e480c0c034500d0f50700b400043c49000c0b8003002058400f6a603148054502032440740d00010195403207801010720740442040840e0769854240000e11500310700800340e5208192039191420940c0004191460707480fa203c241c007107080e900014101040000455803103040624115 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 937867284 1250 937866034 937866037
    0x4060b090a09140c0d0b030604061a0d110402070204020705030c0309013c030221060a08120906130f0308031806040506191401170106060c030c020d0807020d11011211 73
    0xd07201c20f43c0005410711185c440c54000c034101c228041c00f1102c25061a1a00000400e00b242411010040101c080112841e0100e200c4241355040840c0d00900310f003070400c0100a50041d80d040f079110746e003001104006041400034040c60f16200c2d02030750302d40e065600003401204070381d840102109007160302c041c61144201c111010343d00c9a070844104444660300300f50b0007445000c49468047c0c0d000c01200800035501c0ac40940711302816260450780c03603074402c0c1da151b980401400305200e0203000e00c2011a030342012000341c01540c1040b00180c400303556414180030322481941041c1e03012030000003080941c034070041d4904c11a041c810024001c0346800d4035020740310301c009404039240302c0c49031000041244081d00884041d0452641000940d43e566414808001040b44214983c0d400c01030000341890044007441c00302c0d5095201ea1b94250030303e42c01c00c24030a100390b508450500d03083c02450b0158a4804d00354528a00c10703001c50802e0000c040c00546044070b098800c69065040c850704c1c0158141000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 937868534 1250 937867284 937867291
    0x30c07090b011e170a180f050118050714010203040f060c23030d090c09021803010e01110d1e06060e09090c0109030b040c031a010e1b040605160204060b090a0914 71
    0x4032142120307122814240c5c0603081400c400c001441c529404a002e200740a94903005803071081d002007000000b02003600060915400003e0160f0b04500c07410400e1040c190a01d1004801c1481034901e416281c1c52254182010764025600090004042078108402240c2c402c08408013038544821170020192003550701d101e000d41410005868003404c00410581c4281e140280c040b00505548440c00b0002640401c20b41a510301e2196080c0601940050418810207914145480c2d8881c03510703030141c080d0342c05061134040610164040742090512031499100e6040036000598480c61200c040d602000700380817018010444940084042aa0344d0383c020400c074049039801450242941d41c0c07402d00c81c100c086903600c0540300802446032850703806c0c0c2800c00755041e00c01c0140b071400b80c2c0d1a4490b0241210100d154102c0d001c41d4108400e1040e10300840103400340003070810000941d0034141c0d0101e0260b80140e0f00c1400000004034455046160081090010301100a400c10603603441e00c280035242e88024 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 937869784 1250 937868534 937868567
    0x10f030236150109180b0111010c030902040b0f0f061c052502060603070909030c051603140c0f012015010f091a12190b01031205030709030b09030c07090b011e 70
    0x510207040d087e409030118083c1e420b078440c0200003c441150014000c0c08560720220301c91032508034422094500160350703d2a030b00d400343c601d46c030004518050005660000210805003d5003a104500685450144600c90209004081c112094072003403000152000c04105083d0b400403402c0080580300000c8900841c1c1403140040b81000945c1000d031a041c01c104030140550184a0114411407502d8829108072446500740140c0c44120300e111a880d64a0101065400102c522070481250710030101004003100810340303003010b01e5000d81b0103441c01001c0050400c80d058084c0c010454004182c041800400c003461040c00b201030720180e00843c14458406041c0300b1411107224654070a01041800d00c2c85034540001280b06030182003990380058248805c84d850030440c88521540d0b403151003681d001d101e191b11107a9565003155103a4030200402050081e007031005110395410000d0030403a202c018407442c032000401c100940c0004000d0b0390121180c0000617072050418a2699102161a441c600390 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 937871034 1250 937869784 937869791
    0x506030615061c0606090b0c0c22090506180a0804090f061703040f14060d0c1116050f121b21060a0b09010f03023615010918 55
    0x107400c002030080c000d05414183c8000700315041c0e03056201030b0380100c003900d00d41c0e101c03043c8842d698012011180700304105400a50041403514095081c0341e01071b29107000f10300f4482d00140120103081c104807405540e0903216a88184c0c18001003000d8142c00085c288040c401400c41c040042c1c41d080070610880c41748280302a82c030305c8400140382c0190b0200c0060300c40c1c1507400c0e180c1c203940c7c400140d5070b0b0400e004035056003404500000707200ba46044c180d0340d0960043e03d120704241c449040c210003841c400b2070840c03d00451002001306d03c40207001400c11105204448080b0324201014041d40801d9080c00c41d0051000d1507a40c12804c0c400208074800201d07141546080e448080049a481c1041c2c5d0400086052203001002c0c8111001c922507200b416002e4040004401070010005000400e01c500d10301c0354a1181300b0f03c00340c1081304190080c01c01803101013041c000161005c05030040030f2001080004007080501c06036920849407000300f0002468841d5115040c410020035031400c00300d940c0d607002da5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 937872284 1250 937871034 937871071
    0xd0b0609030706050f0d050c070605010f0f15020c100c0b011d0f100e0a020406020f0c06090d0203070b19090b1c05130f12020c0103110a0c0c0305030301030614060405060306 76
    0x82c543c100c503a5139070121b10038031041c00d1070389041071140c00800c0e0840b00541400000700d00103034085003000440c1c5103a840303410301900c1c01400c0070b4100c041449030411803303003100c070350700980b52807135000010398440d82d8014500c51030341000170081c00d041c0c00400c0c0c0d0500c0191070b400071000703044040d9003100070318041c8030700c0e5240e0b28070000007240c0c00c0d401922006d059404211401c0708581c09041203450503000d40da10000d040064545030f0705014801ca500000602a00c04c2506150141c0000d140c40030302110000c1da11160038a00d00d401007641445a42c0110020652107a1f01c0100d000003800c50400003400d1401045042c0b855074242c00d005074480307584000080015a034880080170032504925502008010b50920b020041c11402d50040075225070004040300e54402e21481ca0400301c1e200300f460810410360012107960078440c600380e0f04890204008804a101840158000c5204000004c2d504501011000c00040000c0c80c030391103185090100b103120384021490700d03030201c0c0c254401c008945 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 937873534 1250 937872284 937872307
    0x1210092f090a0e070815030a150c0201560d1128061403040b060111031c0b0d050c090c130e010e060a08070b030406020d0f020d0b060903070605 63
    0x10740360700030052035246000780304d41c1039044212103004d20007609001004840020a26071b072100807000080181802d4410b105103400c40303901143d4212482c1c030000c100400f038141c1100030408103091101c43e00c4c00c1e40c00310a1400c3c14000d41c0f5802e284038185055820946130100c004124000c1a4003800b80800440607410061002d101084110000f44140c2885401c8100168403800246424100d2018000042099030240040c44030142d901d04c2803038039560307035651108000341e00585020306201440c40e07581d400000c2070001c0d1440c00016050062011070306090801511b04c011100c9010b00c00451144003c034034040740c500084041560144030703940310101801007a12401e001030107800680d100100c0c41034502d4602d90f0482d80700f040040c20b00d0b151602082820091171013460069070214804000c0e04403044007840c0e0240c002c20f801414801d0b9a408001619484a0385c81c41c01a80000e1812400765680300792a10707064107442c0b2600f0591810040392342c44802d401248180700c6d01003810342400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 937874784 1250 937873534 937873549
    0x171e0624190315050f01050319050f060f100e01050d08030405070f0b0c010506031924050f07020f0d09180222080d02061605030a021210092f09 63
    0x803109030358100c20b40e02d051801c0542c0756644200049400c1401054011841101e1513042e10401000f90000000c5a80302c0d0644052402c000c0718540106090041005e4040c00702e14402e02d4002d13854000c0340b81402900d010001990400c15240040d4401400141c5842100601d199400044159280c555081051030410f0741c0d4000c0810082d5036801080b01040500078041e003000b03000090020b03844510405840315500d4804810030416100e003500420128044185252402113000b401503007801100c00075208221910100c1040a0040c070030750707540c1002150f0364042c585025040b500e45c880300c000d1081140748a183c25044042e09490081c00c0d03d0350407a0390002d100e08202c00d459019241c0c490380c0212071b2080e4500740c0503071000c196529001140e03c51190183c03060740da500794400300050707880f6000604108030042c0d007441449040b002a03a0400c1c000c02640716544811032411840c0d209031580143c030008092030581c06604030f11540740003c0c620002100c14240c40e0340313011002c210311 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 937876034 1250 937874784 937874809
    0x70501021201061218020d082104060209090f1608100b12040c050105040e06011b02030118120c150f0209090c13090b1008090304171e0624 61
    0x10a481800001c0154010304075003c1301c6440c01d02800031015262005c00d050004c01c002a40208005d01e60f50b000440602c0100740c4010150103a02c0c50309000a00790518070070031a4112a00b030b40c0000c1c1c42c4035506e00b0302100b0780c3c8240c0000350501030381340c007040c01c82021004020796420b01183c2c0b4082140c0810308100d990280c00300418454886001d5001c001c46014140c2d029100c00c8a8190041081d51003101103c00707541c0c5803400c001543d203811300110f03501d80441c082d0b1543c00d0925070504005a900b0300a40ba0411008201c0d482e203485c490801c065500c843c4001c02051100050900f400101240e110415101e40460002040010200104007070700c10b00044a44c811b00d000b080088036440305d000b91003a20507440000f000c06884410381030440300c4884040303912140440e800d00c0610303c0340c000c80b58007540403400e590038550b50f40c000003030307410444e642000b21b50446005d16501c10321885040c0302400300100140100e05104955201d80100c2c413500381c59408814582010540302c3c0a1083c0e01c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 937877284 1250 937876034 937876057
    0x20a05030f0a2d080c012007030f0e0a030201031d010207080310050429040b0301060605040e061c262703010506211005070c05061f05040207050102 65
    0xc2014200301c0054079129010401c84001500068510030401280030a49104042c82d0b5060030340c1003c2d4560700c5030340d081828400c01541d281d410b5140c02c00034440c010410b0382001c0c020643c48041518018180b4910f402034142000481e0302042296aa042400c000300c80e02030034001460b40003c11884035000d843c0c40f0344812076000103503c1c000c0100b40401140b0a85581400001c2a44c403038040000703880c103030b00b03400540b0003215540b800c0c0d0991480c004419101c009100042085044000c04e007034444540c03004002c42ca020904124002508100590101c41101c2280035110071582100e0403a100c19406030200030720001c40c0d50782c0f00302c1c03c041c18041c61030544041e40754001c080e80080b840088000906104000ca6100420360505000700c50203440010708543d00340520441c084085043e8490002c003920400c50b22a03088061489641d01a031001d90b40c0e4201610304e810904d10744840a01402c00c5000750351503c042081000c05c101054800c00c41d00507035200c8603070030901d0290065403010b10 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 937878534 1250 937877284 937877293
    0x190c0804151b12021b0d080919090213050f060331051606020a170306031002220b0c120d0603061802010216050303160303060b0708120f15010c020a0503 67
    0x40503c1000c4040071214912a822624020309240c00c0c5000748402c08403003500700c1500d0750780000041140016024404003d403595060014a00000f4040701c00d81c1d00040d0342aa0005460031081010000d42015003410f4036142403562128021404030b02c8014105200c1c0042c1c80c1000d2900e001c0704c01300044101d000707040011200d000703082c1a52110190885480340001c00c2000254a50002c640c03c260180c000060f025511030550803924203510090009078940605414680d2103a11031015096407070076400411540303419024046940e03003c0ba044822045070a100d45c010004000070012144900310780c080d9280c1c41c081038200041d2400d504020402c90070250b00d23910041c000070034084458000d07805c0b202001a04003120304620302501480c0d8060b001041a045060031540c01440340c07038405c1c03a00050480c0d9400781c0750601c1c0c0203080c0442d0100000992200c0c4a03005214454202038420301d180701e0303800d09811a0911004003c0d03214140074500c14010155a01e9805210040c0741c09810b48 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 937879784 1250 937878534 937878587
    0xa180b030609070c1505061210060e0c09031908070605150f09070e01051b19050c0102060705030609040507171e010e0d080405010209040c05190c080415 67
    0x21040d0411030700300e8064900d180020721070302e01c5501c0608120317801140c1d800c42010601401d0307016080c001c0c14103030455070107207000204c81010425440960300c15240060080e052200254003039902400d40c180d503803c103001c003010341d0f50040fa10503590318005246412406142c60402d21a021b8044060540c40ca840c2c100601000b5940c0d01c681401030484400080b8546c0004200500c2c2d402c0d181c840000b29401c401d03607007071b5014074000e00b22103e0a9074a520151000c004e03003031a00c503070f4080020b106601c503244001008400c01807801006401d00103407031103190441c0300400c076020013818030f03200d00810000304082c0b2000f40903400261200d0051541c1400c00b4041e9035598010b030088003010200903180b4442a4441849054080e6003d18041d2050740b2000e042107420020203002903070326542c2000100b9569649201d00301603080d41d0317280c0f00d460b07800c0d00a000c0a008900110340741401000032200300014540411a01920440403500c1da112041500407281c80c8009040300310102a00400c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 937881034 1250 937879784 937879799
    0x130f14100e0a0b060a09081e0d0e030a081612090305060c1602040606030c1808070302013f0c21020f22090e1903050d0b0603100311010c03050f0a18 65
    0x141c0b086e00e88660441d054440104205000ca21031500d5407045e94200c40360210400b882151088034030351004bc00c4503652055900e81d40a19802840185201d095480c006001c02242014802c0d408455040039041c544ca10780b41c581d12003d000340140f111740d10006909c0107008031300075640030054010308200030b01501e8002c058010302c100e1703d009000c03540304880d051844501c4811101603805030385c05403a08500c0c40d4010f40c0c101002d0054009080000300d003454001020412080c100c080040e8542a50340ba42e001c0752046540e100a0107041000c0301e45081c0034651002c4151400516400c0c0040c0c0d41e4200c0e1050085500411503030740307403101900300b4455003600115802070958545d00800c00c107525068859a568080100008560b1641c0d0040e06000c24004d401900e03c03111100004200203170f00100003000c41d0320481d40c6801816000805000b804119441820500b1082c20304000d00d003c1500d000c5d19070b010343c1174512030140d0001000c94040d84200091030058014184a04003641c58009 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 937882284 1250 937881034 937881047
    0x41e120e030105060a0b3f0f0708011409181501030c060309240b06030717180c09100f0305150f01030b06041a130f14100e0a0b060a 58
    0x840c070712960030540442c2c418038090080108072403681c2c102601d0501e60281c1d0031a180052442c0b1030505070510803111482e1040d043c0b0100e55001060303204080c0c42d1042c800402c1090107070042d401c1201241c014042c40c410780c00102028001181c0c40c900d141e13211098442c180e54490314801c41703802001002c0d1043c01c68002d01742c1c160f80c8036554a694003503e03120200e0884080040142100442c01e1568040c0100440d10b00303520540180702055018003030010484590003a100d00d00040d507904400651180710080b0303035030041c0481d0b50140745024690050b5035500103581c00c1911800c800380202d502082c0540d00140181046486041c0d001d550741046c0780c413141010302c00058030201d0000645c60b100d211403070a0580354000140ca07102c0c1c8484d01400010440382c03404500c84501084c000036155075081c140b204200407140040303440160030983d4410345102000d503c149040e4581031007074404504a89406a07000c50600106554500581da4007a0403114005604100c0010f41e100a03240d1211 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 937883534 1250 937882284 937882307
    0x1061d180a1b05030609010e0304060804030210050115030f0c0e060d14070203030601090609050307060c02121b0a0e061f1b05011505060a020a0204020f040e01090b0301050c030f041e12 81
    0x4042d141d960761165007040c2030f5a08c51000d000c007504204414806907016050840e0042d000b8412142001c15981c40c030000c445007a00000d04910304440d0414211780d0600650014404660381442440c1e016071020b010100c041c0010307481004045120385d042070080e800789809504c0d5800300d8116048c10740e4040d450364010f0302c002e0b00003000c0c2800440d14902507090300003161000360080043c2440c0010072507603041604002c982c4030030505001d5900c0041005518000014010780d5014140003100300001820303140c2c04000342442d403108102c8640c0c0d40c039400d107080c6c0300040c0700340c50802c5071842c04071042841404086041040014660184503055114030081d903c01607214600c59103408c01c00c107284c000e40c001d00300140e01201c0700304010b091503006416001105681181802e4030380d0064100110241c0010b041540e454001d010759250901030541c00038480d0440703a203181031400c04c46030503500081014009000c0c5008403061209000110125907800c0000031400305c2d90000c0040c01026280d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 937884784 1250 937883534 937883539
    0x2d0c2110090e150c0304081b071806060e0609060705100209010801060932120f070506090918100207030e01020609060c0d0f0e0304060903030201061d180a1b05 70
    0x2c001d101544400140c0ea14002440c3c00c050100c039941c0380900304090b44000c104981d00f074414401c6c201d0b040b250b024034004402d90032020301151410030b4545004800318140c01e51095040034000c1000580100c40e0900c844001d07113140b50340c0c0c180880459281d01c200d4600070940d00c505e000c5c0c20380041c456800f41c00151401da039001d110b6640c420382124590400e008241000e81002c80f500016000c1004405102100e03440c1140350884010000307045110b800c0825030940c001c2013000c1e44030b82c4107000c4403014020803911075007041d01e48808503100203c01850102911200b158092041030b00f084403c55400f0307036400070755854240707180080078840c1059901d130151240d6400f150781800040780b240d11803080b07060a030342801000d45200024008250300061070326542d05c524401c00b401400200050111501ca050001e4910f00d002800c41d0100c0c1e000f200c10200c0e00302804100c1030700b0266190800d850b042202500c0d500c82d01c200f4245418844014809070071400c07420661078401c0d0f012000c48408 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 937886034 1250 937884784 937884791
    0x20a06120f05040b0c16020907090503061f03030f050c010f09050606040501080613020d05030406020114010b03070e060315130b12061e07140c01052d0c211009 70
    0x5561000b81c030303019140100300c000114001000b040f031a1020b0300201c0090166041c0801c115004907170000000e491120001d09455001d205074202088541e4122600f0200d8419000c00019000068075050000400300041c0c540e00031443c1d071040c0152002d021121001f00626500a2889402400b008a00f1960350217500d002509038901031040314121044040500050f2b5500020070f06950050b0004907403240a401d140c8010400070000790010300580c1d0000240040503000c4441d2040f016408203c1240e400c10805c10101c1c1e0252011b8801c08003918629103d850703c0f541c000709200102e41c011b030800001c0702080342083d8240c0215150a80a40309941c01000b1801c0b0951540740403103030080d1b6009803080421068596035080741c3d22196900d000c05480e08804c4e4582000c0e4404c0d2561141691110180400307051401d02020744103481d11007207203070300400301c940c0d141007080200040d41303103c008107c0140400d80ca00000500e40000c11903a12580f5100310b915048100c24002d08602e80d20b0b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 937887284 1250 937886034 937886051
    0x21e0307150c0807030f0e0604120801050d0f0b0a020f0d0b0a0938060309010c031503021f0201020c030f0c060a02130b090d060c0804050c1e090402030a020a0612 71
    0x41a120710101105240e0f680d00460343c0e12030041e0054003000d4058020107640304590b01c0d0050003440840d0095114142001c4004204d0500a101e0b86040c1c00c0b0a02c641440d201040025840c02000c1400a51000706122903036240d014840080c050460080584d40b400506402c000006d039004001c0300e03800710b035202c8481e0f0b29030f04a403013250800b03420600000300342c01012200e00b1111400d2007240c10018100e0310514891404207009403c16039802c0481e80d118000345103401d405000300070381e00d0004402c50070410b20f1a00044c0b048400302c00c0d00300ea032000300c03001030344041d00c02e4048130604070b40c0e034049a0343c40706015055170003a840058540d560b4040c94000c11118407403030007215841901034064908aa00b071014130032040c2d01540c0015845840e2060b034000040b07140c0601d05030462a84c50b50562840c1c14104107081c45041c000041c07084904c550091004c801d4880d043c0c1031b1041c10b403400d280039038407407000c645048541c9001a500c00760a0100081c41c903401030200e02055840304041c00040b1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 937888534 1250 937887284 937887323
    0x3090228060807020a1e0609080301080c0d024e010605030601060f05180901140909060702100c050c01020426030f090d02010318060b010e0105070b01060f021e0307 72
    0x6800f0340d43d800041c0c202c0f00607100410301c09005002200b00d00360480041007400da0740d1404550303892030308403080035010004011380c440910069403c11002d840500e1943d0283e40007451a0040d03040700c8181e40d1460882002e5540990446004107180d5005d914010080380c10204600d070585d4a23600d0190700f000b4020032241804180360b4120390711034554a15000844c9011b5419070401d03a980c1110004100403c801c960716408114000d04550f8080e03081950402d0520003421402010701456a000c1014040035650009424004405001001855080d24101160700303104009400c4110f41c0042004240c80d401c1c00c50034140e000f200100f0038035504030036604544900507a00d511041c1e00c4140102403807801c0002c0c041d01c002d48140f4001806c80e60303130010b40e558130300803140c190340f05652200480b01958100d402c040c801c2109080c540e0034400d095036480300980050148001b04524601500c041c40c0c0200801d44503646034044509402c00002c01072690fa802010082d14881c003851800315022 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 937889784 1250 937888534 937888547
    0xe0f04050f07090b0f1203040e1e070e041407090e060a0504020316020601050a0305060a150b2811030904020d0b1305100f080c01210212060a0806060d0f02010309022806 74
    0x246c03802c4020718145464007441c0480c415006202800c10412465010000c01012098520550140e1681820034047c54240700803a0303401f046104110b039580e41070101036900322207080103d41300b108101c2c0e0a0340d940004660342110551005170860b0011042c401403187c0303000304500d000c1040d8211040c1e60398590401c840800540303c0a0240d4009001255254004ea00007800380c082e00f80541810990301d500c0381060742c4c40105210b041010103100c100304012481880b03440c05c6180c2c601524008800d05d00300f0346a104182ca0540700b0356000902100312401500452945e00004051000c8d48881a4100b070260104035a0200c0306580150041000854070740c170203040d00c100800400605840030019142d440200550045003485a103000185688030300040070704003460204d41309282802424032180c45c02542140980d0b030401400c01065444150b10b02001c0f0b90040c1d601d52806505000503001084510000394100b0300324681c4800315891001640c00d000380610f510700c40903580d19403c0354507 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 937891034 1250 937889784 937889809
    0x7052d01050306100c0215040803180306061c0614010e040605010506070b0a180206030c12101508040311070e06010e010f02062d0708011e0e0f04050f07090b0f 70
    0xca01658010344d0a10030703e03441a074148041d0901e004c014000958a01c0c81d0065440140103510004002c02c660000c0210500c070807000b0782c001c0506013051400204213039802d8200c804281078044c0300070306100c03403031300310320b08603030b03030704034089046e586038142080750b84000c8a040c1d5243e0b04040002800342000800c44901d607411100b56001500c03000150300103422410ba140d00060704040601000d0baa64800035800341c1e8142410f2652480360070241c3e2140e1000819a26031651902e03410050300141440c2c1000c5440c55282560301030340c50f1314080e0b480d80304580d41c0350301603c80c001300402d403048010401030160500b622001c00c0004848011a90705120589210043e0030450204d13890060b0724803000840100346416600c2410401303880c458280303049801400160800d001045803520180455200400001c90b9400300c9007040121400f40c4800b50601d04003440036000507082c80002d01011020311680010350300d05590750940d1038083d1060b8a51984036551069028140c0d1500c00d14071410b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 937892284 1250 937891034 937891039
    0xc11060606040e07020a35040308030109021c0c030504150510090f11030f0709080601031e0204060503030c01150510140702060c0d0c0507090506090402100207052d01050306 76
    0x2509050062001d21054044c25210552060848100019038a0f8842d603035044454800c02c12110010f0702098640e100025003100b070b200e4200018800704085104690654140c00409030b5550310602d0f4049060451130070307408502d49054100c0e4081645a0481401280509500c4400144032000070f0110750040d16540748103441400d041080e00301d503411880e91002c00c1d4100280a454110740041e85a00c22205140c2203074004041143c0d51703400090307a10280910f00d000300007940c1556105240104a85120302e800c0c07100f400045c0440d600c0d50004405001c001d425242c0704e442d90f0204901821400304451003a4410010104035030034801c49002da41600c40e0b450095062200a0008444c4e00c105000e0381c1101c400c10181c400414100f00140b01072070a0354a4440358030060800d1404c00c0300c10341254030600e05080034441d00d942c5102c00240c000d90102c0e918200400010700591034030310240c4c041604203803424905280008840ca10030150000343d03554113003200c0c1503401143c00c2e1000710b4110383e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 937893534 1250 937892284 937892287
    0x30e10060b09041517060a051b04171c0201020a030f0b0315130f051b0a030b061c050d0c0507050f0a0b070503040305010204030b0a0c0801030c06050f0d0f0c11060606 73
    0x8483e25194010071410000c51000e0200d1a803201e00c1c42d400fa0241d01c1460340c40d94060814003803800c2480c4140741d400140c1403402d1013201034610302071240d445107119460100c0e40440c040c0d01c91003014018001030880006207505504401c0304049e001c1d41000d24450082490590310f840c411100c2d004a01010350010080c2004189000132020001d9014104002445030000c4e8400040d00761514904910b00980007040c603180c0d82401421445280c812050141c42c15910400c0015500100396420800403a21a6801d003100d03404e52030102080000905035200b10b09501980c6504081ca40c52000d00407002c0d21001c60f00d0380144032116140c00e54503500300d455030030100949222400500000c03403041c03054030f280642c1c0ba2205800ea0f0015082603034450ba5450034004880e1041c8219110680c040c2040c1a65616645400c499040c0341c4c4221018058000360031408071501500325440c040a140c030400c904089080444018010f03501c0c0300c004501d40440140032a42c0004003d48074600003410b43e03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 937894784 1250 937893534 937893547
    0xf1b18091d10051b0c06160c050a031e0302040b040905040503040b04060f0e030c0102100b0301240303021e030a0e040b1e04050c0c1b03120a030e10060b 67
    0x110000c12180d800c54128075030041c00340607803072030034840342242100c20b03a404100c50403d01d601c810003031072640d14455401010020a03885440c0030881c55400b19050013030420111a60300b09655502d1394941c02841400b4520144081540005052820761b100d208242c0d65014441c5c4149c0803441343c3d0040b400340d000305000800181702207801242d445442401528186640c88846c1504c940003604840d01241c00d0030640d414080e804003c1005000c070443c0105601d085600001c2c1d202d6802e003000c552120f85030406000203171400d4100043e60249041c412482a1aa068400e0301031310b1400100d006002d082d4180c0c5200c801403c07110080c4007100091071a108030100140c0d1164a45036040e500581c40326842c003c0b95580d844424049200030b810b800201c0523000401c012100000c2079203840f60300038400000c00c8100020814150340044000c0781c41d4864000011b8607100711005000c00308071001540d060080d605420100c22110310b401250a17102e40503503400c0c185c5420b03000d501c0d80414244941c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 937896034 1250 937894784 937894799
    0x106090b0d2303030403020304060824010f0e12030d050f0702070e072105040210140919030b072007141e060c0c01080f370f1b18 57
    0x20000c40002c400402500e0031416440c0781560400c4400758003582001c2401c00c600c0d600031a000e50b0000114038180782038a0002181c031901c651012883d8100704003d0461144a4020401c0d21007080c80101030b88001401d290301c080e035036400486111829814980403a04031180300b04100d00942e2103030081e1a05030b040812810018100806080030040d080020250702030400642803440d202010000c25546024018407482c401443c1c460000c02080d800d01480f04129001075400200044903c050303008a11540c0100d04046a0000f8040034160ba06108030103800ca03a03101d00002c0c0414180400341c0103e58803039291125807103040c09001e40a5412951490569a0070b105003458840940d502c050900101b04141c0224541002036801403250071490b40e005154194004008400c0710301c1031400c11600c20800302e005400c500004a41d99038244840031000420b814806078020030400c18080c10700200207031074006c2c21208141c0c200c0c40c3c8850424400c10b401e20070042056141609141390144 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 937897284 1250 937896034 937896053
    0x13060311091005011b0602070c051206010b04140409080c0115120b040618060528061809020604150e040501060507050c090907180c02060f070f031a1306080106090b0d 73
    0x10b0b1703130a240340018000010720144050320300507000c0c0c0ca401081034200010312600503043e115000745940700300300400202200108403429940c08030894000c03e076000d00414050564240001c1115030003043e518a2500305501a01a03507441092902e02a40da810440c00a1000620090705644060f0006000301e11550006d0820300070944440b200080f25851b5001261002d0302c80b900c54207608801d5180020500c000c007851941d441c1000c10907580b42000d8560f5880c03008100d04036142c0c98031010710541d5140c0c0296001008640b460000800204400070492200b59502d60300c100e1400c070000c40c18501c22030a441d0500d5114009120003c01c1008100818400810403181da210350031001c22f0a00882096020003c2255401b04005014002c0a030800000500c03010b5103002c02c0c01001300c41a48141c48540345005420001840c0c01c5000ac003000c400021440c0c0d81c2c01040d101d40d4410030100c264821003c80f101c05008105046d1500340702c40546615808444c1c0c010022b201c50004142d1014 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 937898534 1250 937897284 937897307
    0x60801031704030203030c0105041101050918041a070306032003030a210e1605030d2c120a02030c030118061509050f01090b03031905030a0b1306031109100501 70
    0x50301c040c02d00b5640e500203032a60b8070040b220540c907510391050000304501b89404002d11202400c08a060000d050045444811170300c1007015000800700109061140d0109945040c1c00c8802d03a50540c0d01d400355015010349410321044034034500a000000c0c010844442220946000501843c0340080e102011503007844142c10280701000014140070303a01c0c640e881683c40c55070f500701c046e0a281c44400102404502c495001c2e5004ea001078441101d155405000b1511014140030070124400408080c668400c072101e401c1c0341c0100102c1c00f64180948000340c800302140c405c9003120f04001581e002d05007a10002642d64915506240309030300081e42c90703006074050500907500c0745c03845541d076290281614026a0015100c4102c0001400301c0c6865000d61807007000250001c5150100601b07a4000e0300002120070410010040003140710700c9000c0c0c001c0e0050500042c41c003c40400801450720040c03589120071550500061481c0c106810647e50440c45070501500310a81e051178440150344146155 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 937899784 1250 937898534 937898573
    0xf0412051911090612070603140c13030f0323040905090705100c02040e060a020c061303080f0703090c0618060c020f1207031e032604031115041104060f06080103 71
    0x481c1705c050b61034040040d00c0003040c09603004200c05180c81c0461101d0440035000251078441044032408005103004a5021254040a150011140ca00f800c43d9803e101c1c008042c640e031003d2141000305c00350348014000741c0d01120000c02c00d40c0c41d0901c6440e500c001a1150a411259460103002d40501a401c9201d0700c3d070002e080801d10215240d001d40c1401411120004841d5000c250740310400c008111a0740d100103101d800c1520091161400b030170f0b82c403009050004044104d80003036052031181e000b403e41e59a00c2000001022b071100c4001d001c10400901d04c6000f11850b2900284c1c0078442c610810b4920f0300a4040d900d60000c8070140117614050301031444581c801e2100000010343c91152a1907502200c1c0c1001e030f450f00a034070b002400103440010304204881c42501141d141909020242d801c00d6060902024850800004605045500d0883c2c4c0d0411068020002809505180740720020404c0b1030422000e925429407445290560060348005400340c00144001282e4401c05440304909 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 937901034 1250 937899784 937899799
    0xf04051501051b150106020111031308090d080304030c1104061811190e040606080717150d03050d05070c08071b0b0f0a021e030f0d020f04120519110906 67
    0x11480c018544541d4410090900104000421070340c7d03420b100b0301400c2c83c8261819071450a045503131850440140102411030240010b205066a54065000c3c880d642d200e482c9c203480b444c2900b03000c0c0c20541da000b001e4035411401d089003156440c140c460742d02901d131940b030b0007282480901440d10007400ca0001c008030441c400c005030030040034140642d0f05140c10940d80c41e410041c0041c20b10041e2902da6220400340036082051110b103d40240d141c251992100104850a030f1b1604546151000400e03d256000a0304004034001d0542c424018102e10a48200c1405540c41e00300044079005110a03010307000c0182070040e040051200540700210703429400580655586078113020f6030541c003c00c9811060403000034001452074040c80401c0ac024080e40300d0075003108a401c190f584900c1000c016013100c40000900030f05000f040e034107445123882848441c03a06c45071661a20224071001c01070951351842544451076240c40c440c101145810790000ca0000c008407605d007031101d0040090130241d4041a03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 937902284 1250 937901034 937901077
    0x14060f090310241a0904020a02070b0d020c1c0203070312140f040506070810060f05072001080901180f05150f01090e0f210d0204060e0f0405150105 65
    0x28010b4030308401d8540c02c0104150b2503070312981042206680580b04d554580744280301034921081c252410000c040d02c01603940c0400780c20403801c0103007035041144124004034482c0082c1040b07501504907294114119100c15010b202c160b402e50341c0c840c602000581c810420301d000284250601c004000400d800403449250030042412a52000c44045100780f080004000a128081042e00d1f00690b841c10001c40f241800082e080a00800740250814001110014448280705408948010340c1081c0301802034004030820803018840c00350000d000440341804219030010611030000300d226021b1368200030039419501d184030000180d000313403464003513410020002c0106441072481103000207081030596040103610812203030724064a0001760f210611661405500042202070510445424a00d108410441e0f0b6114450701c000300980f5400801c0c00550107800683d03401c18010112071201d9424040c0d000e01088640881d81910000c0c01c1d0040030140354010f40051825106401c240600380c41d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 937903534 1250 937902284 937902313
    0x21018170d0524010c0c170708060a0b091f03150204030b040b0709350f0f0a0501050f04110d14030c061009140106050d14010e0a0614060f0903 63
    0x2101160f20724a200070884540ca0084929040d0049207502403c0014072212280c80b40c040000c11401504040105500101c0810b441008906c00800e9240100d51041ca0402d9402d8041c0c960b41d82e1050103100310704040741c401d00219071584030382d95820700c0c030041e2249140c0701d410701e00e0a003000d81c01101b94208004404a0000c4d001d1610450003250012028101071a00030013a0141e80c0c0903840440c100c0c651170300507003180403400c2e0052644d8400301e0440c003990a03000341030806040d9090b040b131184881504015802203603400030b04e8096402007180341e5854001e500e04032400c5030010300740312108181d40101c4c5814022070050502801111040302c4c849042e06107075601c0a036504c01940e2042c410011380046911500025204200e8280054003e1110252001d80180110350a202011418050303c01c601d500420f45651280c0c0c1e0341c0495650f824440a2040044e20704248090810340301183c2062072207098251048042c124034604080341c101d200c01c0760007144031668503011b01c84100000c00d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 937904784 1250 937903534 937903541
    0x70e160f03150b0c0d0801060c0803100f3c060302030415050112060501080a030c030f05070f030f031d06150a180b03061510141b060601021018170d 65
    0xb4203415035400d940386402000145030517034030304840041006810040c04016845070414031056881007280c0c0d1a03458541c0a58040125070700b150803400c50381140081d00f400030184001c00c1d800401d40c6030041e00548202a42c010441f0210180828034008041001500c0307a402154006d00541e00c4502100c20030702c40360183c0c2c00a9000250400c0044201c0b810b02c515071207601d004081040051116801c40e80d80a4054000500081c0c1409000d149041415000d1021103400580c0124074000b0313821103107000303442e081c402d500000c002843e0005401403a40700c800d56503202c0022030020006561380110505507030b14200c0c6815000f44000d20b0010f000303071812034801201e489011000c0303031058504040c98540031004083c42c18448030b100d00b43c80962242e48a030001840c0514000c03020342e0030703007004a54506c5040009606002c0c0380b031b2502030072400440ca550050000b41d0079100c01c0013901d842c2d071080c3c40f8940c0a123070044040e0745036640000c142840310034900301a2071040b4180441400c811044 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 937906034 1250 937904784 937904789
    0x9061e020c0405090f010c2d11190b010519090c0201020408070e04060507050f030106080606120406050f07021209040e070f0303090501030b1c1518030c05070e160f0315 74
    0x139503005015014034480203005400e140805850036001400c007031404068101003590500c014540c800110000c617621a00d5001d0004c1482d0301140c2403002c1c525502840b6020301801558918a200e001192500d000708030b0015038260b001484c44103600307000d42a8020002504900d00b959801c0200203410b01c418002c0e81e0041103082401200352411381800401da40f0001d14100420034100302c90300107661040c0070381e41500c180349010b40c030907a208008070301c03c1d100b141b142e0f06c5040c5100c020001000940c0e000140719080f034030701851040e10750b11000d03a40c585810305095000c000600c001040b0f07003040c2c2e00610b4149003040454002640d42e00070321a000c1c0c0320350019800908600e0060289580602a0f00c07030150741a90b00b06620310f0520440e000102042c1070050031181070315144608600c0c590014186400c2c0c4900c900d0044429143c050052000a03808851b50300500c400094a07241440095100d0181c104003403004c1a2810011205030081d10454801d256840d10340d08040a00d03846001d02 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 937907284 1250 937906034 937906051
    0xc0f080f06190303050304060513231207050d0e1c1e060c09080c0d020a12020411041503050a0203070c1509230f21090f120a0201090609061e020c0405 66
    0x2c5da414a4140030044d81e10040c43c1d17402038046008004d000800c0b011916400071400c0001c455942c105000c0b0b6030500651240c04c00c400704020dc0c10710148200841c40601d03169054444400b810f2030300e418400640c44a44551451a07050702d40580440c801100701d0540c43c5080c2507060521030966944022125400f03a0074000640b40d0f2800d2115600420104080440071a812401004103500141c41c1c0c0f0203601800700f4158141c0460030840d00e60340c00c0782d122410003000c0c40d510f690b01d0b078140000343d81c0684901000030303080401144e00d80d0914400c03203000c0c0009940e0042640385c90b0b00c0c1d803114001c1c152203c5484642d2102c2c10b81c041143e21600748a1214141c610312020f030b2440418600e00070702c0c02c038000b610350021200d4041050604540e17185000740351030201d444208002c006a400b10300030b01d90f680c03c601d40c454803000000001c56245c60441c401d0321181c04040e16810100e40c1d5400310701641c0e006c9621000c200242c00b50356000c14072590121310448a100c9112008641903501c140c03201030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 937908534 1250 937907284 937907287
    0xf0105011d09060411030f010c05030610110316080f0406080f010b18012a0f0b090a0c0501032a0e010306090e07030821010e01090c0f080f0619030305 66
    0x444041041c1034024051500104a0700d030801c04007850b212203010300020940340c1102c0d1196010380f010f100b0036544c100c55100803c4014950400036045510440d06a0b100c0c12070719011410b01070040038441000c0340007c00031401c01110f03910200454006031400c2d0b404200c01e114824111302c42c0300060005d04056030715020343c0c0c1400300b41c2e5624910180c1000d000e41d0020b0205904019219041903481c2009103014209c04015141031b28080d040c0043c42c1c0d05400e03500c1c00342c40c10704c08403000020909210301d00e804c3c03066a818a1050300c5100110005001303d500100400140d032103a0024003c1410349032490444200c0000d8041051400b0421f100116290340d144400c150f0301413180a005200041084c020020003000e441d445140c1ca0100030308100011455140300c0301d204440f4410b1420341c4c814600196104c0002510045091244400c41c508040b101d1117803c0c811820007500542c1925540680e88520540707a0203110010205c54101da0b84ea1084508000d561003020300440c022703152507 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 937909784 1250 937908534 937908539
    0xf1203041d04050c01030c201b0102010207030c110109050d0b15060a09031e080f0d0c0306120201120f0f0e0105010905090d0807050d09030509040506010f050f0c0f0f010501 76
    0x2070310300d220a50030314007064903004204070204601150070303015400246000104854250f0781610742ca401c03052103805468040d1300d04000620001804461603500c1c1c0b0310b0002100903000120b0a034420070300010001900c81d801040024044d00d190200500d050401980454544010400410850f2800c0d03803000c240d182441080040c0c60200125014150307240d500d06080e80d035018003510746601c4001c0480c590020030126024441b140381d4174890b0701c945c3e01940e40700945242e0b01a90086018400311750716000810103081c0c000d101d40000c44a4207555580e81c52000d030015202568880b078000c0c015900d030300c408010713150180300d00c10380a02d000d4000240150000031050031114140c102d00e6580340740800340f04c0c7e685000140602c5810403440e25281c90390b11040201c81c0d0703000d03a51815005a00300000306c1c0426402601515070000d00751820441a13549500464040f0350507860140030a034104003c2d291007080d003005040d1098464100c505900e500101d242c540090000c1200311655182d006 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 937911034 1250 937909784 937909799
    0x306011518151d0a031e08070210030605030601120b150d0506090102130503011e02161410050708102c0a0e07080601064b0e15040b090f120304 63
    0xb00d0f540d800701036684000d11811540d4001280368020f04407510703090314503020340c100301c02d03c1c00301e408203a405070420360395629101c0090050704103805258800d00a140002c1641c504c00711144c11301315080940b030307291034444441c054000680317480e01ea6008481100030a002c40c00c100b00030390091849000040e40e900344a066960b9034a4643c20181c840e90408940c60040407050f120b040b000e022503200165507a000500d0b0501035106543e00a0401e03107111910881500301142034080070450950500c425501c0d0082182c501d28112500800b09600b80e0b8203001008001e40ca50705481f0410791410f80180b4210001205000c1c200d85240c14161517440120034210144684001411001c005049550424101600d8035100403e50140450ba001000c1d04400c1d285501c0710b4106038114400180700c51105104116000e001c40f04030114004803019801401c00000100505400d03a010f141401d0901d48503041560003420303003a50003040c1c603031411301d03e5031190f06071481070700180001c0d66620328040b003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 937912284 1250 937911034 937911077
    0x15110708130e010501050c25080706030507080c0306030a030e01091a030103021c170f04050d12030608071503020d0b030111071401061d04030903170d050105030601151815 75
    0x341009414010a680d410340000e150b00d00500c44a940d000003640c10100104034108c50f80005200d00c903194000542e240c140d44610700640341c2e50388007595a91480001d0425100c15641c0035050f074002410b081c0400d203c0c0420001079141450315940180c0d4525207001030b0400c5128040004000000400451501d01d80030f100d96500c240000e6009036542e2105800b0155041c541401074000107140759085403070350100d4001c4c20004049072840380c03013801d004001601604040000c82e1410b007003c1425580000c0740001c4800c140c00707050015049640c00c401941200c02d040111a403030359003458960f502070040c11001c684480c03090752902100d013440b500881104031000e51a0745000c80c184042c2100207107120000c035140d040241b1584035450304640d195800d9001814805028500c80314045a460050600b0b203c4440709100a98881d01007503107030602032140d134810301740703502c1c141081a02400751641c0e440c40e807002c85101c90f59204041804882c1500c141800a52000345069048200f400f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 937913534 1250 937912284 937912289
    0x210106020d1803240f0603150b090405030412030302070c08030910050a02061612050a0f06090b100f090806070c0b07180e0a090f08030a050702030715110708130e01 72
    0x1150030b1041460350300c03480b0102c86081c0e02d102c07209404003040c601001a40d0044104030b03c06403401c004007a41da04018810030058a603083c1c40c02d0030019490f1003458030354001c0f8000c40d00003002c0d40c40c107864003203809081186640700301d05050f005d1040d1008126a880010024038551024545d510008001c0104261700c0c64a610b042c01418002801850360000300c5039403041e480c0f41441855901e00070150340700c608280c00320405900308002c210b1541c40700d401401c05414450f80a10210b91111040341c261036080340800d421240000000c0009031003405184030064250800f204000d8a8460b05403c00300e00700c0b107a00101d03041503442410000a200d51079803000c032900e1301c01000a0048a01e0306611f0880c410444080c01c2000401d000c000d03140e00091030305070f02c0301c004445007000389001941500100c039414000b601c0d04001420440c000700865024030360040c2c882c0d100004640814009000c81500c2603030035401401141c0c002060745c0c009150060940c080d00da603027480c11665048a01e0144c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 937914784 1250 937913534 937913567
    0x6020d0c020a0309150c060e0705011d06030f04081e030708070e061e0f0a0e0f1507150207150207060522080c0c040603082101050f06210106020d 64
    0x82d0110003007644948008180d45048449200310041060225040009000d01802052038a0900481010002513640071144280c035150140390b004807800c01c032011400c01054100c4000c00c00104021088004c00c1d5025215403056420089424060b84a424600c000d902c842c0c1e00000074803580540117819594059400d28201c10301005400101b201405840701c4040c40c2c0c2c5070b08003120111240d482c103548500c0881e80202340c5403101e1000040801c3c03000c000c001c0c068030301003c41c0c040c07070704010102180c1e42000340016840c00e1019a25410600c0c00d420729084115803d10000300096105800c00b0030780540310001513100e00e41806c11504444000e850b0f000790001c8070280341d43c0440020100f8100a0300020581c0d240c1c40c8034000241402200c4500aa10a2800401200304a41c0354040c102410701e6018094029640e21107d5540c500b0a014a41d8400f100030640c0c08145000310085c00031400c290b80031000d207000f1451240b1808000c0e0090f401607000001c050386502d90010400002100740c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 937916034 1250 937914784 937914793
    0xf050a05130b040b121f050c041a040305030304030804061d0c01050a0e0901031410090201140304050309040515011416032601030c0509090a170319060306020d0c02 72
    0x34540000d0644003926041e0240640342c8400e00050f40c1c40e40d0000c04920400350101162614a041c0340d41c6810b00210480001c004801c62a01180090311807144580239003101c0718a003900742881d0192042022641c40d901020400c00840061018006940140d2003619244440d040030b04c5c000055503101d1600603407000c4000900070b1402800143c1a0f1031a03c00e0800d04d80e14114040704842216030644601c0c0c000001c400000b040059110f201c444250002040d40e131800d911100010548542c3c50700a800101c0e03104841d46180e00340c000464019100f0000c50f8039100c12840804c0540e87d040310140d100f00600000a0f00b196005608849100c6544c2982858061000f0658124424010000c0d00308011200815000804800c0d074010543c60314000c0d02c40b540e0740c0e05d4001c03503c14082c00380e14004c140d05004529680c2c40003502c00b44040d48601160680b417006940385034250001443e114a0f5061000301b510405e906200e82400b85001d08030160303032a0081014541903c451603580c6085500 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 937917284 1250 937916034 937916039
    0x2060d020f2109070302121002070f0515010e040b07110109060b13060b12040602040b16050106050a06020616120f020915070c031103011e1401080616030b0d06020f03010f050a 77
    0x1002c22210245c0741c1c11110700d034140f00381c047e540d0302d05000303030026a40c118070004a02c02400041c641d6064010301c1241298044144640e400039900c40c203204e0386484640003004100061480501141d0103100c903d0044103003115000100d081d54030411040d1138461391440c0891183c01c0844070340a060019030710500c40f03170380351440c1c9008511819148820148260004c50100882901103038000e040c0781203155102d03142440b200c90301c40307204501225251700e041800039190030040340e60411100250060001a5911202001c04060b00f052030001c1050b465564015151148100d140e00c02041c00d0058441003d8410301c4030f66101400c1c2c104202205000100000b0300d0400b160702900e0340b00324070802c0c21414502180c0940000b10080c0360075170320340f0b00c03201c2c00030305075444141c001c0b80d4040c11007016642c55009640307c4600755800081e14002075220f4140ca806900074080b00c09000c0e1142035440d180d51651000c0383c010315010240c1460000c0100a0f040318035a018020f000c0c125140030400b071 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 937918534 1250 937917284 937917301
    0xa0b0d060b031b0c0106080d08011d0f180a0b1008060f04080a0c0602090a090504210e1c17031906081c050919080d1d06030402060d020f21 61
    0x10000f040c580c00180402c4000000c2d00040018060a021103d100980c9140a030a00c40240145e050010130f0642a0414030b1171400000c0c0203040c0e8600340034403601c48415055a03062110001c000d24800c0710301c0040010001303102c0d40e110f12001403204070f03506d091004181c2002d0000d0005c6800710b00d0300040c000403402d40400c8400d4440d0500381540360280600e04800130340504450194000314446002683c2d041d03a0300000d1182c0d1003083ca02d101008185824102c008081d1012000241984030215050a11000c408210704a000c403848540b0047d5648990524190222800c005d07400f009100b600440360004100111144000780034545c140181d05545035a4880140c14005000c00490b00d000d020f0000c85050810150031041d090707002c400c1e1744041d25098030401216201b5585032094403072181032030082d0380041c003540c942d222042500f000b02030340020344140e038011800c016840c075403c0c6a1000381010040712006c40c0e19184004500003110709450711181030903045030304000ba0308 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 937919784 1250 937918534 937918561
    0x114280e1515030105240d0606120216081b01020c011b050a2a02030a12020d030911040207080c060103030c020f040207150504140a081201140913110a0b0d060b03 71
    0x40d01c040c0c0c0c41a214a80f5500e006c0c80180a89a507040c03001d00002c1c0566519010b07030040000e0301c0f07480d2540c9105032030452100c03049100d8110304280700050400b80200050b100f03001481c2e94591456400008403420351070508907441614030310b020781c0d03650210850303001155820715025011410030b0381c20b20780180c00c00382161050058180a410b21400c4460348500c003040340901d0aa0050100e804020f00343ca003030660381310014002d9001d481105103400c1468442c2c000c60341880d50101d40d0034546007641c0203120294004600450300c00d2030510030709460000030446180214043c0d0b5520f1401180785c018040b0700c0f5481c0c811640250b004100e2840801d018401203100c1c4d444407040090603684134149104c280e02c450715200030a02030b0005000600a4136809806804601c0d0b121603580d990310019441c080c5584d208043d00141d203100020010038003803004039440b9008101c02c2e031145e03981c000000c00b00c446d1908103a1880c000400c01445504140c412140508615810603103581400d42c1e68a259 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 937921034 1250 937919784 937919789
    0x325050609010f0c05120f0a14040819060f110a0f030b0f102304050301060f03020906060d090c060807030b030114130305040e0108010606170114280e15150301 70
    0x900c6009039052017042020052003541040d003a044c80c0e180e0040c0802841c84c4d0784982c40300310000c2e8003410000d82450400f0125421514108020000c1c015044500c164412068400342c40241c0c1d19404031858003002d0240c100c0002c0c81070142d5503948840310300a002005010742500c200352401c101d070440c60f00d5407500100c902e2021901c01000381202c6204907240e070304480c9038202c3e03800680c02e036808040c00c9101400a03600110000e0000f84d0311240801c3c1b03400080d200c040e612001d40e034003240c82401c2c82c0f002800c0d18648000e01149034080f540380c2c189201095800080042c1d101001c0000d01e551510444842d9201100284013500028001e4201c4160103010540306124410080c3e04041c0100d00b190300800815100310855030b5110f0130349000305840c0c030480c0046040c248603501030b6100c000d1243d06031448840e076a030781418142c09000b00c007071200e00340b41b60314040100541d0541d6110389411009015201791102d661410741c8800000015100c0c00354040d4003800064481c8407200002ea038103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 937922284 1250 937921034 937921037
    0x41109100f050906061c151406071b03140607090b03040f11010509030a11031e0304140604091503060e01060605030103020f18040302060907060e0306040303090c050325050609010f 79
    0x19988640000424a101b070710341180092101c00c04030380d81c980080d040032460203084018003044990f03c60714203030b0b000440003141d68011020010b40313002030443c0030945014001c003084c0122040e01c960781d1010b8000e19640d09038466111104001880d58850b044001410201c506c1a0447c101561050100100e0b05001001c0c01c459142c0e007000742c0d224209603040180300504648a04802d8200169101c5400c41028064018800a801c0b81803c00607549004402c0000452610345030001c91940c0300c04c00c000095102d003081200061803d198083c10030f040e61504010f680d00380c60b624110b81210340403d101d00355a41055010081e2030742001c1a07078112501611014201e112502c006000611424800650040c0c00340c144824141e00145903445a0703106000c80e9040d4ba00d0310300c241d0300d21741c1c0004a260726134440400140040e03c04d4100007400c0303120303c2546004645079400241800c054460201d80e01402c25044d0070040d0410030000002e00c001e6030b890b85811001c0000901902842030359a0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 937923534 1250 937922284 937922299
    0x15050310090501021c06150216060e0d022206080c0d060b0609121c03021e0c2d07090c020307030c080c012c0705010219050f06041109100f05 62
    0x707007804800c1d011204882c940c118441c0b1400740c498911001005940203500440711824005458540001783d0324545104c40d0442c6403502e80b602a08a5450312880d0302c3c550019600ea0309500141c039400301ca100405c00a40010040c41448035050341116112b51000030107510a80305004a6200c2450f003800040d0424008110a140f500104243d0b114007603145c1d1300200350004001c00040041100000c4010200110300c0600480c282101a4061290001e20b40c601000d1045903240b200c500030301c1071000040550700410400340000c6d20700d0ba11103a90004a41c00e078414290401002d02c54071010305001c1303100700b00c032080340600203686e805243c3c8000c05100010104400f401001030596071408a08002801440403004030b150703030303102c0098200801040440201d09003940100d4004292801070f402030030602c2c2410050a800710400101743c4850081040d0b14005400910105109038000d802000308800756500303010580c0c0c401402c010109030146014001078000000c1c034011140c003192041c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 937924784 1250 937923534 937923551
    0x1032103060f0605040305070f0503070b0c0c1315090204081203090a051213051027030c0b071428151e0e0a0201080f04060b09010905010915050310 65
    0x140d00400c0305400c816112032001c60001a2164403100802c01c1c0c9108001307071190290799044440480100380a100c0c1d040e000701c5030502c070303456a83c4040c0c40d00e403655200711480814004041000c0301e103003084103d00c141d1140c4803505110401c0d00c4900050180a1085144c28604101c290304c1c0c0c200c010f08940c8405002000c164416800c100b108620380c0c000c0156500328501d200c001905a10400301a000061442c0f000291864211701c680c2c444d030815280d2501e003181c46640320100012000d0400c080304400100407000c00d60a8942502900070200451341d81e000754140b414280c0c900b99032010495010002e0b60380300c401c0100b90311410300015610340400c0031092130140f000100300c40c050300d152460043d0103a9130790b203060542e8008a095010400c84428101e25031070325512a00c001a010484030350114051030340e100c0700f081e849801148001040d6000314005100301c1001c0e840b402005490f00018000302140380301c0c0a008208800784400b00c503181c000417940320784466001944c0c280d07440014 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 937926034 1250 937924784 937924787
    0xc03111b0c032b091a09010f0f020a030f110a0c09050627060a0b12060f01051e03130b01030807031d010806040207060b1504090e071a0309240717010321 67
    0x80c4c0117090340d400b04ca00680117030b003c400c600b07400400e40d990014124007100010580150110001d200c0c65601074800030005403130030b40e5003048011410003002007026801004001c24008c0c542000d02c00c162840d100c0e03140190020a85402034045449240d98404040340d0340004804080d4440c10904400056500c04001a00c00006a4400c290314003000aa030440e83d00804c103100e10400007102c4100300c250b541c0004403464006c0c901e4508203000c5450f00c1c000341c001d50304043c5910003c5608200008426543c8285c2074080a03030086030000c8000c142d20080580006541c0803071780071000c1c1c40f0040f648a4000800d52075000d0300050140354000ba42070300340013894204003043e000103020b448015445900c001036950040c41011070301440c2c043c14000c00c00000c280c4508965800c0551301000644500e03411065001030640115886042d40e03224041103080800303188001000c0900b0510b1606810140c0903250300d90002e144170315402c00500000d01c0381d0f0781044044110100c142d032002807a210 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 937927284 1250 937926034 937926047
    0xa0b090a090b100c290601080a110a050c01020903030d02070c0b1204020d02040f0905032a1b01021006061d030c1302160c18140c07060c03111b0c032b 66
    0x2e900c1c10381600300ea07000b408003010055078082d003001c2c0e0343d503230107070341c0390841c2400b00d401d8002c0c1450004070800148090a1003280900031122400300018508074080c2c0009144d607000d4181440a00e4001c1340c080184800344200d40018041501103030300d04603204030300750018032000700000d03c5410880e243c2400d54413264880011418024400c2140110702e0500c1981c94000f0b414070440c43e26442c0011a030350701a42c1441c01c50100c01c0c0c000708808003130440c1c84803201400214082c11031050000e4414a043c850242e00020012512401449108040040100a10705121a0003540504501c52145d1140d0306031481d510341e02140142c6900861700c00c90109542518082c0c0821072105000c601060a2041c0c3d05100c0100b1400b04000305016116039904a4105d40b1148000428001a40800d800d0341100e034402d0800d05c4c000078500740800f95284503801a00098030000401426654090410031015a145108038020b00e080c2c5140c500c00045150011040910100c200000311502c1e030188a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 937928534 1250 937927284 937927313
    0x50708070b0c0705160509060f0a1401030219030f18020319020a05060a080a0608010b0a030f150c110c03010506060409020d0603020301020c0d022b0f0e0a0b090a090b100c 75
    0x1001d9408100c200014948441303240e0040c540b003111500302280319403409c050302000ca2070000e0309a104072443e29901140f0750a0b950142170500d6000c110a9135150394984000c0d40050a41c4c07400100d10250400000844650354210624078200068800151342d00041c0e000180c500074100841c030071000d05c040b0342e0404080d8001a003081010480180c003d8221528034400c0404502c20828296251f5406081c2c0780855443d541001c0010400e10208840710046183d990052400000502c040c1c0c4c680300440da00000550f0002e03e138900c01125404041c442c1d034201d40c108034024401c03424440001850341c412403007401e020590018480101410070b030030440082d50020000c541f611000e071141600c3e075011042810060082e01e04040720b415008141c10451707401d0001000c002e0000680c01d030745041c200c403071100600c40740442a199503030391084502c024202c21414144c44203105400c1c080f56105c40d80100307000e2400d20082009071b48504084e02d4941000d8070f054802c04002d800c20480100489 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 937929784 1250 937928534 937928543
    0x90103110412060e070501090639121d0f041503030c17031308090d0f0615080712061e0e010506010806100c02010809030f0309070503010507050708070b0c07 69
    0x46400128000b034a021000103e004883c180280642016455118011801464041500f17010180030507817140c04419400b4550018101032240003000800d291a000c1c1840c24030740c3c00c40015a010000c050140101200300c500f0080258072203500340202e00001070341d02502450803d0300e2a80071b551070b504540000c0304200140415283c5138100200186814101070b9481c000c8102880e81402c3c0d4042101d00c1146100340c0030304810081e69805078a9445084401e40c407190031105100428810005000f169106501c000303401d1105a0001e118130b01d061348940f0558100d01402c00098007503a05200e001540a000040c45018001d00c00125070412a000c00ca40c030b1519402440003081503000c24062442622041c015584800c1004964402d0702010400944003484000040d401843c0c3c08d42c000c00d402c0f05076803c0c0400c8240e000d039075070021a40210700e5801517034100420709080c030595801000d50b150161400040d511182590721a144000f40002d2a910009100241d040d0a544155500 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 937931034 1250 937929784 937929787
    0x1101110a022803060e030702030c0d260c010e010f0c0314042a0603090b10061707050f180414040803070e010c021e031b1c061103090a0308010602060c04050609010311 73
    0x21092643c6c0f42c11405089000c0c0c42201000800f514001c40c203200c00540c004100c100e60b078038018141c855001001c818008a40301886081c005407000e004c0c0560601f90200000b03248855100400251984501c9003c18140740c5030f030002c040031001c208294069080b8a503808150b12058420141e51411003c4d840c006400301408900c0c40d42c56005800b0840c0604460851911009290034101529120300e1010500b8280903810144055185a500821a061041c200584500014040d034410385d000c01d486445400e402030149082c1c4500078800c444550845003600c3d0942e1081440e1002402d003d05002d4010000c5805078072900d580007125070b0250042403080441c100d0003d980c10b160346160710a0044d14011440400f6001e030111081e00010007401c2c00003016007500c00d0b01940d504003503803ea03807111a540310203014940210700030080000100020360343c03030038000c02c07924041e041142150401c90500294103400030686c0c0980d130701114095502d0b1030305001a00104a081e0b42105140030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 937932284 1250 937931034 937931051
    0x30c04020f210718050a06111f021b010b2215030803040b0601030b010203090402070609060905060118020c071511011406041802030303010b13080106031101110a02280306 75
    0x45620026000f040107454a05014440c540d40007034401c15401007075000343c03000b6010050584280030b8078840500100556141280030060650403c26284920341d5568001a050b54414041e05000a079062003074003c21880c100314001a50090031805aa6141c044c0f044009020a00f5984a05480000c000c0d100c0040340d40c0e4a4854042d41049400761400d09074034000610f03950003130084440612050380914541421801000020b422042003503c426680b00380b1480001d0442c0700f0000303081e0084006028540c90101108100714003d0000c00d0210b00610103820840310001c0c400040c0d400c07040c208040b1501c0e9410032605001509540280b0b98244600600821800400540120300c1650180540200d10030a05045010507038029007607402000104100a4880c01a0000c094505040700741d41d580c950010f4255040c5800c25166800708100910080da00301403d400070322506406407440f645150001010348400300400c44074000c403c40d0502c1c10b514054505009107610440402c1501e5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 937933534 1250 937932284 937932337
    0x20030c01180627140117090a0206030709090609060e07091809020103020c03121503030405010c110f0d030f0e0d020612190c2003040f0b0a050412050312060906030c04020f 75
    0x94190041e02094038940306c403941c06402c0024500c264994001072400d80c60303660078000240e000030300d03490800446842c01f041040050107200c00600d0010ac002c42c1c4607003414621103001c0f00103896013080c003448210410001c604400d20145201b450140000e0b144c01d1400103030003921404001c00c3c3c0354000014140540760602d101940901c6032445900303460b1071604141540c0f4800c500a81d4041054041178100058601da04041c000c2c4016044114a0880d8004a1006011400210042107145540211050784100380510805040750b044900c0601741d004181c1d144501400309038880c80b2480000c1c03c1c0c04d0105c0142070025401e5804001e0b035468050f00506220201c1818222904900d0080003280e0000064405a17400d408071039a40070f2a05a500700150700a904140034082c1c1440001514103001c003401080c00c3c0280c0185685040b4000d4006100600030000e601ca44824014000c02c0d40380060460b044c00800c1e0383c01a61a44031503100012030040d040e0036692401c2c00440c00c103015 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 937934784 1250 937933534 937933559
    0x2030c0d0c11150919051b0901060c0305130f08100b03010203060306220b1602010507140d0c092102010f032a050720030c01180627 58
    0x1500d0400c2240e903080d00c0e801c5801c0d04030106401101c0c0d0142200609070011031815540140707001046441007510241c1000d10240344c0c040a03a8190004180c00c1c4002036140382c4044c025034119541c2172250304110002d080103101c1e8102808010b400710b9241c507c00310981d510005445450301c142e6106030b91746202c80d56188001d01d000030302c50030110300c8015400c0500a43c0c3c01981d0041c00345c0003540c0ca02d65800b502034008415201c00303038194206107001c210b600d08500d0199580d2014100c942181203406400c0d00c0340684510100305100b010814800122380c103843c0940d40b40c0f0804180803410340c0c0b00f201c00c00382c0ba422480d441c02c5290b21400e0481c0080069400b401d2007038941307200800038610141c040380e032541c02801840c1300f8000840c2d4006480b141c6600031090b5030600a00b171204a84030802003080740e072181c441b120703204a0a80741a18080001c6000030780700740303090340b0001d49a0244020315030062069100780210151101103862000310740c1c510504002018502840e601c550010a0303 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 937936034 1250 937934784 937934797
    0x7091503061a0d12021002040311040b03070b030702160501170103170403140a0b070c15050601030f02120103110a2601020403050d050d06090c0f08040615081501060215010911070602030c 82
    0x580300e0710510b048119858000c0c1c1e400c603500070ac00084100c0c00c000c2404080d00e0301c0d4082551500441c130001c81e0700004900614003480c00ea90051070b5660740c0301c0807184038402c107801c240c1c103102c000c3c4845010401911101c80c1075030340c424094a050b84040700b0b03848860250b504010300b504240140c1c0b800d032184c0021401c0d0654001d60450f000c6032191803080d80c1d079a1900c84c0240c10000a005403490744201908850381241041c9400920515440e11180c1243c00a00c041b041e082481d10041085c0700c01c4100640215004503803602034145095034940703108168904c001d03051844418103081c620b03000e505440c000c2d5040029281014100e05004205030300c606204013541d81b9005012038504905d2007210440081600c1c0c222841d8400e0100382e402c01802042152090b03101d0b5901d9543d0b5101c140e0160061a00c40000c03c4e555240000c0c803103002d0016009641191b04c4400ca0000e030340c681b04095411580c0d48900003890744642c1d080008640300d039002c040c2c410340c000002d203c0c8210419004120707 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 937937284 1250 937936034 937936037
    0x42a06020a1704230303091c021513050f131e06060f050d0506131104140915090702030705030f04170d0807110a0512090307091503061a0d12 62
    0x740c00c1c42e910102c4125000c1d82c00307400001c8a0401020103003001c0404181080b0307078010120703410580e143d030010b158208503214111402c1a000c0b0f00c40c0c11418180c05c400310b0150f04c100d00da410a40c2020382c803800c221080c822140300302e401d9035960201c0e407a00141900462409813092098180100c10342e0100c2100c0c01820081c00d28040000038000d20076441d03a08028180e60740d192a02c8030313401280000d82805441c05078020b07003501d00c29141c400644101e8145096440501d901e40d4071785000710703d400d984490014011b0b440c03001008480c60154110408819048419912a845590080b4598040d03032800070428400040c5050450141c3c40150046a036081083d44e090b4a550044039200e580642c8080b000c0350300c03000451011400340301032120722400c1108540407690b076602d90038640b0098441161001c0c00024002415082c10700c01d200250802c00010f105a1090240c524280841e510010304540d03519504a18086d040042c401c0001400500250707540303a950422401c4034004100160 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 937938534 1250 937937284 937937303
    0x708090a06020c06040e1f06030501230609060313050d1718280206070602030402041b0804021c0515010f08010b0a090c0e031509060a1103042a06020a 66
    0x181c682c80051555030070f0502a02c1076003828170b004180702e10007601409180d40301c80b20f401d041c03001c410001301660050501d40d0300440c417545001d20010010141402c44861090300403160501c54843c0c6d0201c0b1600e21099401035541d5450313010710000c00a0380070f0014080d001d0070b00f0705905180e021521100840c1101301e160310715240d003c042c00001c8031550940c40e4540061505041d00d0180c04801402c0b00c4064000d501488001c0e40007404d10703400304100b125076070385c00304c140001d6040074803e46030b410806200c05112070812007000ba03d040b0340240028400d008080c801801c84090b0224510401d278810203c800c0301c1c4c40200f52144916003406911085800c100000920a07014003800c2d10489014041d00c1125040c000c1c10030103098010041014448014072214141e103041180c0306442e16005000066400d20b400c2c41818074802501e514107072818005000d820610300c0c0c04403030300702c2d40c01416560003d604860b45100000885010b80400c4250788000030b94075008220065240d20505800 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 937939784 1250 937938534 937938539
    0x50901050108160c0206041e2102060f0d11041401030e160e06030a1403030711070506040b030901090803011706010e010602070506130b030115080a0c082a0708090a 72
    0x11201800c04460105a0742c03812040742c3c140c1070040095466040c0040c140901d41030300d92142001b0b201e21100b400d000e2608401e81084041c01d1500380900c01d002c000d600003007201e05c5070005510303400350040c07850f41d80e003001503010300640e5198001c1d100001c01b8111691282e59a0395298a02c001d0928814082070800a6002c1008000304284a10303211400ba020f00850030040d098107407010007001300da050b05c9203180781d0b800300c0c122103542540000b00030000c5690f0701d004000100840c410b03544002c8039a000b22000c0c441a600c03038065078256280f1840045d00c0b0b80c1c40303c4c0000c2c050b200c0c411028024600001c0042080c4c030001041c0000d08180d03204980310369a0310b40d11101c100c9024401c10b0016042031005110301c0c900300004080302c805c0708801f278024689030b60030b03181316a0081e42320903003040326030030b0303c010081d080480300d54010841e500030480c004000c000980f120300c0042030414010b132000384106001da0500c00c0c860621b0910820240c45a6642c5060403040c0e201c892154801c10070b801d0700 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 937941034 1250 937939784 937939787
    0x8040311010f32010e07030b2101090510020c060c030703021201140117190902010507061a0411032401030e12030f0c04060f200f060106031b1b0314040306060509010501 74
    0x403904075600c1c0c24400540340d03070b001d074118000d02c00d00c505649d10041c0b035200c00f6202d509611f80c1803806041c1d10000601917056291640c50921601083c43c1c030703140180701d54400d650012441c150311401d0010010b541c0d0713480e94401c0b4000e2182040c41120b074086100003040c4041e41c580c081d01700b001d00382c8444051144c10401406050011100d501031354801042018143d04942c1142410314030604100e0304060641d9508425100c8002110421824200c140070b100d00d0907025004c04102442041883c50904046424801c1c12024000c40d2606d41e00d01d10714140e0b40300342d11804501c01094183e45a40022106d100e043e6401502c0780700fa0503c40601058140e10000125811610980c48242d102d42034000c0c1903800b00c8109000307469006043c032032510b04180078014020084100710281c002581010750103001c86100305440a0402c2500e0000d86a8a80103008461040207034900c1c1945401503140c11a81c0c00f441203c95a50698041400000c00003150801000e07641d081701d1040060ba01c2c3c500 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 937942284 1250 937941034 937941131
    0x3060903040f15030b03030f19030b01020615210f07050a0b1e0d1404060c09050d0201120e0316060b090402060301051207090203130b1608040311010f 66
    0x5001000080b03407010001c41ca0000c40e5101c0c00c0e04a4140401ea01d403540380000d0454000b10300407038500000050b00745420701c6034a00c40c20625960308040100d1502000001e6448070b00400304803505100d521103a541c2d5845407025411490a1a030740c0a91101810f41d15071204240000c16a86204d00b540100d1107141c0b43c00c11034169280b0b060160704000b52100500c140804101855540c540c00308213040b5a2581c1d4020f4248038405201c8021140c00c140c6041d20813200d1180c5801e00300f040d40c15081c842c0e43c0d81e4410010405809107070405a0120b900c0c0b205004040132801d40d9000c0c440041c40310341c42c07110900302294503030041a041206103c02e801380303d5101c4085500a40c0204208018000c40c90200690f0300d0101c1580103ca41c0242c441e107103e400c0f40d10503520611640e5008025170104192000403680c8414001f03040a003618410601400c20a00a0001018040e00c51610185180c0942c00304281c0c9081d41b405114043c2d481220342c40151180b2040049403c446c03102d044030604a80 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 937943534 1250 937942284 937942289
    0x9140a0b010909121b020d0b04020f0406031e020a09090b0613110702130f05040308012c18151e01090c02150c070f0c051807020a0303090f120801050306090304 70
    0x1501142c3c000600c1108583c0582c0e80c6120005d0b11510361410005a05d4800c10606003a02c81c0b5141000303400c041c0100900e6403644040035210b01e003801d0003840021041503608250b03802642616108139080e1000540303d041e5500161000e80c078211205040c440c104030100c2c000d140035100c03030f90658003503d1010700b42c0e0034402d41d41190003401c00001005041000c26440340804144000454155080100041e64000e1710140c0014400b140140980b250030141c401010900b610011501005254244402000180700803920700d00c040580000c9041409842041c074000e4050313010620745540f400703810a40211042000340e400742d0010402c0c0a05100e009501105a00100040000d00904c29060f030740c000d00341540301c8000c1c0080b10008898500c1800c00c43d10400d05500414100f8092042c40364841c40100001e18800050051003500440ea0440064041ca00030030b991074075090601c10184004c7c00181008984084201010340c0a00200c1c1a070b0001c90a0b185280c640d81e000e10381e030780242e0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 937944784 1250 937943534 937943543
    0x91d1e01060801050f040e032703010e070b0309010b030a140114062d0a0303120c021212071b06020304031d0a1e0b04080a17031b0a0309140a0b010909 66
    0x42c006000501d001e005c150000400144046030040c0740f50300c180c2c00c5030031046a40c5800003008480801a1380203070b030410044201a0000c2001041c282d4002d6139070341441c4600d10210344000045204083c0c20740100c1c480000290807603001c0502443c2c0f142c422603021264040c01c3d442c2c81c08050032503040600d181d0007814000d0180500404a0100201d4007180d04a4203a038801900001c103c1900c4030404d01e00118041d440c1c2e10611120b00903001d0a81c0c110007692030440d0040010300516442c26400d492000501e40c2a1012076500d4000640304e4101d2200c40d004544e440100c82c10403c8044d0b00258404d61096a03003082540c00c20003031000921030f10b5920f50b40f003002c422061041c0d04030101e11600c0d01e4151031008a5541d0341c0c000701604d4ce4010b070000c4005410000200040c4900341040c1007105500c1e41c603040c40c41c0380144064445c40203204a07041d86000010b03203034040303078400e4006140143e0003121107044010102001a503070070844208488945c641e1000148001261080c400305d240c01 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 937946034 1250 937944784 937944797
    0xf0f1611150d051f0f08010e0312190605060301170c09012d0512070602150915041b0b0c070605090d060c0903060915060b0910030c091d1e0106 63
    0x1000b008402505005104000380c076010b10041242d4030f81d48016100410414280c500401e00303045069007501d9005408102c1c507481000044980048035050543c400f51246d90700242e20708662409002c1c0400c2d81c40150710680120002c9140b210705054009450f05180460b1614101d038000e10094010900c50102405141202000d940c86101451400d96040600700d5403030680783c400140044250320001c807502e5004440900155804001c84805016031005c009a5850007031403e41e5a42800d111413001200c01602040800100d05007030541329075a000b17000301d201d03101d102080f40760300404601c140c0d0303107e100000101180034034111a51803001805d030b500c100c0700b9034680c035002d0304104003c4c604000c400c600c0007021074468071461111a1107040e1401035206000e40c0c2c8020b507401d41d00081d80024041111411603540d0720b1220070704588604010940c880c3c20f5006994445480e40041008070032043d513030b0078800d00c005880e0f2050002000c1141e000054421074030540c6c209001d03c1012514 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 937947284 1250 937946034 937946047
    0x1706180a0b0a0b04140903090123090d21030c0207090c090902090319050705101407060b041104060504030c0b0403050604080f131401121506050f0f161115 68
    0x700c0380c21100b00044080c0c0040340001c0c41c4400b44102030700c02c5455021b990008a008200b560b449241c15540400407880c80841142c00a4402c1e018403c5140711407040c80d640204008000010008114500e444010000701d00100d80b80a4003901c0b280190300014020918045030f038040c18401d06046a005030365008a4605001e81d1100030741c032104c5100c3d814401c03980d00f0071130052180c070f907242e0311441750000d0100307245403409111210b041d80c0d00441c2404a03c0204001c54040b00703058030074444d080350000c2100010040800c00a000d0f81038045080c280015001c180d03590040c0c005d00c12244202e00f003107140c0743e4552143d815406580002040b5400c030801003004111904003914510600754a89403138180d552a030210403050703507484480c1440003124070010b99a0460b02101d0300b142d003081c042c04a58003051900c540400c05008410078840042140c803403440e400c40945011a461030a06a903c040399030503002021741d08441110030004e40c0e10142414100810207034900c20561002c6403e004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 937948534 1250 937947284 937947301
    0x1a040506040c06090b1e090a0b18010c0b060418020312040608010b07170a0e1c051c05030a0903090b0a02070806010b0c0705012001052706130b04020a1706180a0b 71
    0x1c00c6e400030642200034032154a5a0741c841c00702d84024000342c10321507507a007032846058440d01980c1125a052210780e034010004102c9403c0b9942c1d1041007190700241030f106840180f0140190f0420103905485600c80c142003144602000304160740d00da441d0405280e981e02c500040d5842040c4c0000c0030340011004107107011503980c0c09072900d400344e410004841c051000104030048940350f031001e1100d45460b601414001c0c14490050003500051000e02c405a000c203000d4154800a0544022241c2c2d0317840d11028503205a0004000c3c004009119560391013502000707650761414010b44503180101000010a6041a8200d07100680b00c00040c0903000d15281c01516692507480d42d008482508189250b1410001e1103458400e02d8640200100c4080100140c11008205461041e03aa4040d0003804850151244611101e40e4864841040c50b610b9102144500c02c03254003912035180641480d6441c1d02c000305100344910544030210b031980040d0400c41c0e07654290780501429003041d5201050029 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 937949640 1106 937948534 937948567
    0xb0108060f0f030a1401062d061206080a0528080702040f090209040f2117181b0a0b030f0705071a040506040c06090b 52
    0x3454a8008a0388003008825007a101d50304030361211807a56020004080d00a070b04c0350a00424500501d4900c0c0604164010310704100c02e480341b40f174082d01e42207901102d0541e00a104044032072a00d007080d07a102c1c0320b403001141420b80754000031a0810003048911007441c802e100a00d4001544004a0280203078840c030700056140052084020640b030b102900c1c0c846804490004a030344e4240d11003030081017008030080d04403601400b000300f401000c50f40100b00c54010040c0800703160b1030203451448103010500050200321000d400c2c20030b01d90000e040035840501c03542000740383d103950301c030140c03070b090904900000c0c3c03421801101758541012850741e00102500e014040c110f080002841265010040c1501e080040100e0b0f04014450705000c4800c0c1c16009183c0c808081c2040d003030950b09c40747c0448060b100e030101b0701400245039204004004c2280c01c00e0100d1424801c2d0700f0031141c0030 = true := by decide +kernel

theorem cover : BRFrame.Cov 937769784 937949640 := by
  have h0 := BRFrame.cov_init 937769784
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937769784 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 937769784 ≤ n) (h2 : n < 937949640) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
