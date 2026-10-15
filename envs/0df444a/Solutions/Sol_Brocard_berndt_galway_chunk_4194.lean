-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4194
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:50:45.801048+00:00
-- url     : https://prove2.me/submissions/d73465f4-7cea-433a-b976-0f5e4549b797

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 754136690 ≤ n < 754316546 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 754137940 1250 754136690 754136699
    0x60103050d030f0f0c0f140c0c090a09051603021806010e0d02010207120b01140612040813030c06170903092d1f020607080709050f0123090f0d03090b0a0c08070804 72
    0x2034190580d9801247c0105104550340840d02080c06440048215181e5403035540c3d5141da00f00405034540003a095108510035515462305841c200015240212030810030400c0d08a40c014460504990035030000b0b40c4150001c1d91400c140300c002080d284140191804d1540303030360601c141020000e409887c0303894002d004011589035031440121a0b0740580c3d846141c02c0f203120341070140c1c22014000070014100000c0700402d00c603000480c00080e640c018443c0d600c0b2551003200402414007141b0b40c156240841c0045040381304004125003c601c3c0c080c088500460fa8a481d1020f4140306008568203c0f01c58440407805030b480d240080182c0c10940c031410202020958002c0c41c06c03400400301d005116004047c81401c50304411544c0489200300ca4910078119030000480720a50340c0c201c000a403128481090001c0141240944a10301c0d06035204550070704a042003100715190700b600039020410b0244e0900030350010200a2101d55010b00b003c402282407559070405a912649083d40c90b8600810b0910 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 754139190 1250 754137940 754137947
    0xc04180b13080a1805091302060c0c060703030506041503150911040c0504030b13030813050309040c0509010e270c210a0b010810050622120212060103050d030f0f0c0f 73
    0xc0c117015105410b00e031030a20405c4d0405403002c9000707813003150302080000400004001c00e0f2031070000909011388038299450044e0107084290b0f00c6038070481c1448510215840941142c0c4220b070740101c5500c401c212800d00740002030144100c01d41c1d440b440d009904c1c12589486c066010703506c05079694255035a00d0f505000444690141507040362007500e6100c500400d5000c80c5041d0801402c1030b02d440c02030403d00c4d10900e14460440801c0d0003600b040911501150010003421050300300fa00e030000081c0c83c01003040302404200d01c1075100d6125646001c0700b100603818540d076000c212008110728248500040084184083c813641c00350f0003802d8100184414240a4507103241c0081c01c1c4800141800e03040c4041d101828050a401850085800e000903d244150036240790050031400510a403515074100800402c550305a002d003800421100281c6000100c190480390801c0140c0720741003407040120003600030000305443c813544400031540362526610800c100078034280c4031608001d82030140078 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 754140440 1250 754139190 754139237
    0x807180608060903030c28090302040f02091f0903020901081c2a020f283011150c0c040e03071704030c0b0403050c04180b13080a 57
    0x140703015000041441180c0c8800025650414900c1601644400348aa403501505541e504d030035908031928a000c412460b0408841c4058070300030381e801d210544d00d0400c4a016485040c002c40d03000103559299545084900c0c0c1003501c0d03a4240e01d04228a15600e070000342203003c0a0700070001701e800c000c400340715980150b001c2e411070b5826802e005a45000031003d074040d03113060155a080200b11000380340110360340ea54100020410081c5480890003006502c2562008541142c3d2400d070100d10011034409802d039480807000411071058410164031090080441c1040f40040307400c50b0f00650286030782d55410442000070410804070139100e50b11041c01504e0040340c50262401a440d100d62070b0003070321004c0125840c164000d00ca462824220b80c3d0b18258920413644080e002000310503000c103070032101c03000520072039009d04201c0c0e5501c03142d181000100d80342005c1100000c803c4211000c00580701040340e41d408441000d4a2540d015283c841d0490303540a01c0007a8001303501147c05400100340c0d41c1c01c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 754141690 1250 754140440 754140449
    0xc01113d180807170d02040e0606040e180106030b0412081f170703020d080306210a030c0305131512020c03040b09120a0b0a0506061309020f0408071806 67
    0xa01680d60a680c854440e61110003015105240009200701400762658010004c0d44aa0010300d64134400801035400030340190081d244042d20702e502054503454000b0036507094a000510102d03850b00c07003035640d4284074000ca5045140d552906070010206031141102d074070a0740154203140002c0003002c0300900148004141e0103d0b40030800d861b8666540d03e2020300169403c8040014174110b00000951a19980d80d0009603c5004c0c00c40310020042c502c03001d0f501071002913407503060b544400c0c10700c140803c044212600311903028803c0c0b540840d0ac102c1410500c02d0182c2850b80c40e000c49815034240b0444107401844400b606000c0030901260f2101e1150b00a0708903480071800d203058100700540b03d200754031843e2666480800c641c0c213140c0d60b000101d01d10341120812507445000b14030782000040303803c03523018014070b2601000030480d0924400325802e004517580f08c94595030070302c2248002034108680d6100418014007011580c00f000301310341c401a100b1704403029162144403802030142c42c4283c01 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 754142940 1250 754141690 754141813
    0x1902030c1203070212041d070c030203091516060507110d05180a1805060a0f080d0f03020c0307050a0203190201140a021c030207110907020c0111 64
    0x2000803201000c80d0460020903152009503503034442040c102d1a04084410b40203076110002000240c4004200012524450a2403802519a29110b0540b2803060b5118041d000d0380041200803914a40340d40101102d400c0d410a0505040544080001c0f910300c100c0c0403070f1b050783e0b1042441001600301d101d54084200c1070b0000d04201004880003000790081102210280002c858594000d41c2e0364402a070180c5414400d1310710303255503c82c0740c0d000340005a403418000e030843c0a004c901c80e072444401c00d003903820050080c144036400017801c441d0034041d91000700415034280080f4104000900041c08414099801801c900080d401050304000c958a208032456030305e0b090b1240140d8100303c2c01155451f00b9420103483d601d542109a00f0403131001107040050aa0541844000343c060780034010180c02403018509400c0c41c401403203407184055901074050b078040741c1c1504566200c2c80962a1f0740d840740301a0380600040100d4111000d00400414510301d801c9003550b203a10038000d80034000484480c9 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 754144190 1250 754142940 754142947
    0xf061508010f0b04030f020402210a0c05041a0a030b2d0d0f02150c060f0f0f01060212091f03061806030809090c070506041b060918021e0a0302190203 66
    0x14141d003e184540c0c84000d15820020400e0000d41d070391903054980c1180100b03064a00000722400c82003c021088450301c2c0520714058658008522a80a41d82514001d0600103402c4040d00c0401c40c080c3c110065900c20580c541b09201c2032521000210154204010460244541e500d6801d0600300c07074940d90380e401200482500408141c1c0360445682854060b10707646990310403a000d00c0020b02c1004146112803040105101101c0d803096181c0317100d00d42020b41d0a00703942303d0403003003a5070758028421103006a10215071241a400068000e0184000040071410150b041d09502c1902843c85074458010a9461200f0002402412400200d05000110030400c0c142503075031764165405042c104500585808000512030500b0b80d04660707c036a04002152407600e494039041c07508010754851071205501c420400030b103440c00b0703070098000e50724034520300854840880c2c1c1482c000d4201046120490b012103d040c01c00031500c500034490a09960740250b5614100349000c009454800e410000710b45c01003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 754145440 1250 754144190 754144199
    0x30305100b03090703020423040f06050603060402010c020f0a1a1305030312010b0d14160e010f02061302030a1e06060b070302030d09081308011b140304080d0f061508010f 75
    0x1326440081c3c0758100e40029088941d8002d0003200c01940181f040d080c084d060a00040c0005409a900480e100c4c01040c0b08607a5481d082c5520382d681034070003d000c00d0360060010010300d0310398051144d03014080c1c0140e550170f69130018031a01d40c0c0459080c499400000900c503032600124205030028150a070000c41c50103c02d401ca54049100521170030513078800204000c00303040d845030480407102e01e02c4142244142040a40c480d01c422426241c1c1c80440c090540c00d0400d035006820440312503003141c014155583c2d40c0200e05885800c55031080b6411301400029200060402010740f43d0490110680f02040c0301e41e1800b10200c58541d0031100c0e400b031041c010a0300183e400021100c441c904200049400c000382d181c99080c501030104280e003410714507107020804c0c400542c408280541602002140c0d661141320070f495a440101c0850140c520400004010588010040c002200c0701c02c400522004213550100c110b03401c903040042e07580c0f076001d4a400c4050f80107000a000d06480100085810b152 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 754146690 1250 754145440 754145443
    0x301140108010606021c110307200102070906320a060207031511091306050a140f0901050d03140d06030b0a1a0a050f0402090d290105090406020c0109050a030305100b0309 75
    0xc400d86802084010f04085210300428012703034250b40c2d407000e030354001500c580c170306410401015030255006128150300060303500075034050001242c0007101080707040d1000c80d42144121100c0c0444840d4081c50030011402c6480301d103000c1004248540c040d0100f5800d524059075907400814481141c40d0501005a0301f98000c58129242c0100c1241e14041c20300c001c0c0b0740400a8106540000e5102026000c00184032903403d0621b4495a01100c0c00d20344141d15004002030040c0c00e01901e80c020540101c006e0000c1d00031180400c43e040c0076a1a6030402c00c24000380425120281c004892401c110414001d0524050184401d0800c05600b440115070040000c00c2081d01036105152042c80b40b01c2180300ca540f52076049501c0c4c140c020b40000c02c1c103082d45c1400c414040d1244070880d06c00e034488610034071080c21085135a050714070003402d0010b6a1200e0b103801003e90498003050780d403550b83d003242d100050401c200c0821801d1190700c0100e4603280174003c05015030102d601c82d030300a200030420081b19060 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 754147940 1250 754146690 754146733
    0xa0b030303150f120102030a0f09080706090f080304030c12050316082a18151c0209060d151d0a09030509030f16060c020d0b09010209030114010801060602 68
    0x840003080c2e01250441c4000400c0158034525564001c080080007016007030064004600c910051403083c402d806800222404540c41c03802c02511111061041c007000500c0c981003101490301440000001c1840c0d91944221030340180e60807004910482011800c100094607070128000b940e00301a8218030300481e41481c070400c11800c84040144010002e564540e155218488480150500b490f0341c154100a45406a00101d10118103070980140d5403101d240103402d148020300365102d03650501d4a070013480881004801800884143c0a22a041d865150100604100f00180703002042c281458484104200c0c0305030001001c46041141941548074860205a00620807020000750524171f030800b00c54030b0040b2640f090b8103000700003080054900018070b1a075104003441c400f80000b640c2e400150354010918000940281d0b038801c4640104500802081e0320441d07810001d8500000680000d007100d00c2c0100d80062149850b0051020442c01d2048202410b4180000e04102d910b01d0300003140c888 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 754149190 1250 754147940 754147951
    0xa0b09040509120c0c030c03010e070b03090c0d11010e19031b0e0f0703050a06060e060c1606031a1c0b10080a060204090f0b01091e1701140a0b030303 66
    0x25150000701e00d50b038404000a142c440c2c0c1800d07916460b0500c0c9800c150b12000c8a5110500c20310502c40c00100520707040c071454001d064044002c0c07103858503028824100341c0006140c03400d640038a104000c2c01d6100c030b074841d009045c842c072003a6059031050b00000d011f0142d02d100c040d001e01d0550020190030054940c0850a1302d0304001c582040f15688407520600aa1540008800d10b10403014014400070107003003580502c0aa450602941e65100ca98400312102840781c43c0020340c445032140700608159004180d410003440c1a9010071100413a0a00d9841c140e03032144d40000d54034034814070703c0c6545205c042505801200c000c100420580d9001c013035000b1403040035140c1641c210100d07851220b121020002011850309031242103110f8103011000f5013117849a501c080f0b0a0904061323040c0424807914161079016100c1c2c103210ba06000c1462070300f085080d00168208018540464441411803000b04841c48281c004180300858594001103c0340c090020340b03034103040c0402000c083d0303800301c10740b07a104 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 754150440 1250 754149190 754149199
    0x90e090a051b0d1b03150e0a030e01050c0607200334210e010206040302120c0c0303031501030e0d050913060e15090133020a080a0207050108060a0b09 66
    0x1280003600e074802100f002454040b06445007415020714001070421a07029034017a550380942c0395001d005503420b04200034415001031041d40d0000f4011001c80c50510010700d00b1032b0a140406001624050084d00c111001c07804645180b5410070503403000d81c0c40301142d2400f65050103810400480904155100a608205040c1590007610352190003032035070b03640251803c0c5001c92038410009484d81074561510000d00700054140c0e803540000780c0d80c0d0085605500415140744070050340c51080e00005460300c00741c020080f140300a82d5003080034502a040301520702021002800003d4201c0b0074403024000d403904001c88258115402c030041d83d0082105403034451121f40c900c8d0040e401424130b504106581400e11081c8104c0c0d100d148500c1d8150402518140100d03600d440240c040341c810520041e460810509402c031500f80e120b014a030180c18203004881010440b0356030513415030810154240160f010310000c1220750303444080590414000e881030310005050095450083c81042800382c040e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 754151690 1250 754150440 754150483
    0x207110f06160303060513140402010c060f09110a0e070203040312030f0507181a0d021809090a060522061a1e01030509010e061b040e0106090e090a05 66
    0x1a1589402c845681d40c891011504110b210b15001d002000a4050301c0e0284d41e2450b1007440b982031900c60445244008600c0c1c1c41a90b4541c0c1c01124100c0b03580c141101c1c0c02d5103d1f1514100c0c000d01e8040ea80e405803280000e810b0300b00800c02808116901c03940040000c0d81c150040c446c0c0c09402004407003c1c0d13608800000500b40f601a03003600607025410b0140446407030901085030242d480b16101818641c030000c0c071004944d95107404450811990002c0b00c0010003000003154013551a8000c211910f0b005104240b004110030000352824011075044200c2d0700014001e100300542c40c8940760744000300001c1484592050300308201e10f10280e8100500321907541600d229100100340c40040760503c0142031841044410302e8207080b55515010341e03400b01e400c0801088403014107018100040102000901e140c0e87d401015460700701803070443e0151402c0401c008280c2c3e10244405a008e8945070701c590500c0c501d0005031400c801d030000c02500840d040812150002400411082d00060642d10300344203 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 754152940 1250 754151690 754151719
    0x906050d020c070f03060b031c050c0708030403030215100602060c0a050c06010311040b0603060f1504031401150b12010608061c0606030b070903050d050a0509030a0f0b0109020711 79
    0x80c494411a0300c1d40740301d241c0000039444c864101e9142075900c030341c10038043d44100c542459078800b540d41c036907004410107166049100e88210043c00300407002d8000c8030300d060b80d29000c9905641c8103810070342c0140c11480d40d1503400260070000035004a42c690140259616080c070094550001518036064504005880644188034800f0354407110b000c41d00351200c5596a243ca0aa482800c462060059080030151551483e12b01c0950b40b0503500a8072400d02030102d807003009801d80707050354035241d601c4042c0720200114140001c80c0c07090001010002848100c042080740e0744075030b240e0010a608400b0400000c80a503030250940c1100c3d181e0800c60031b1520f541e0002402c001804c81c20030581039203200c890043c41032079000784007100d02400c0e0020303141e1079003003048640403640d01021708140d104080c0b4000281c800c0000f04452016031034840e040c28550000607041c075203401002d0b076070035a2106081050181200c000d0b4010189408214942601c0f42c4d00c0380c84a01c2000c1c800d42c85020103249202 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 754154190 1250 754152940 754152967
    0x103020403060c0f080714070f020102010615030203041a0105100c170c03070c0902040501020d0807210b15090d06090503040b31030c090c1206080f0114010501090605 73
    0x10003555100006020420f1014401441c0680301000c2100066007500821055409003440302644000b1266a40c90a070040d120500b0280d003200c0200d046640c1c501380002c404030003444449440d4601c0c0c5d4096601d00342810030400001c0142c803901c5400300c01f0401003003e40d81d04050030325140c0c07542c188540e0062650078010101c0303048450780d07011140e000924400722800480140701507032007100c1c2c0180b25511010244101d0007a4000c640c0075a01c821a40e8a00a000c0e255256000500c0c1c50704101c10b140c400f0100140d440016094034855480755072411503440c056480c0071300461000040f6040000e0140065880e003011940604003565a4504905005040c4102c80141c03580140d05580c8559800210304031785030a1090560315810041c084802840300c00445003141e401078031a0740380034148605980200050306581040c801d0b1440c10b003100c02d00764000ca00c020b1074014041c03e0610003032203001d0b00f955008403040e8050f0500d0f030018080d5a1704819242e096034103500c1c00d140ca680b45200000c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 754155440 1250 754154190 754154197
    0x1c02030102030a240602030412050c031002120a0b1513030519050d080912090d05100e010c03090803160507080309071a03091c020703060203090a110a180b010302 71
    0x194055000004000d120b8003550016803013070810070103000310a071607402d4920054565000c1c8000503042084100710b0301860345102c04541d030084040c4d41400c022a4000380c50300c1003804039440f002c0d4002c83c0740001d03035081425843d8400c410340400d20000b0315040001d107000345c0c0344a01d9a1001c81c045108840e894640030301d08090755000c000c80ba481c6a000f1030001d128111100c0441c3c0d01d10030820340482192003682d040f4020102000100001c5241c07841410168106030002d030f0300300802d1034520000c1801000811100c0605500004e05140c03804403560a4030701da015410103050920040000284262007100d50140481c0005000708e031030034404a0b024852090042c00c1840301100340300c3c0c40c0d8408500e11003264420115060b0a104040c004451808120f800103541c0c0c000000851111080c4003085801001610550303940355100d0303032078004980056684881c59488034180400f04510210b101c1c4042100700c400c00e0303032a0310340101000300310000d141c451030168541c58034500d1a40a0b8058 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 754156690 1250 754155440 754155443
    0x13060c02101a0306010510020a020d0311150106110a0213050705070c031a0703140a05040c050d050601090c1701230901030303050f070e010f081b0f03090d080f061c 72
    0x521000d0b58400c1c41c1c0d074050508000c90707803003070103004000921442c065146045050031070300079080c0300306140c0070402c0c254a40d0300190240403481c0c0c5541f5040030180300c8400c100a203140417640c3c95043c154014030340c0410621000e07040d0700080c54040541d6a03c40e03041c1c080442d983e000b0445540300e01d02140c0303901030781c01c00520892810401008022843e4281c048000100c0d100c61450380d80e1541c11025a01c03109000c0310400ca104c004101d40800c6030b0000c80c0c0c800e00864900060316640d0380400c00ba5641c0810a8070990402e2005000030400ba0103400704c070007114a04000410710f060481c100303d901c10700c01c1c2030f50762403808040b058001081c2c144609a120040a0007060f6a4074140500601821500344082d02d04100004400c14020348091100e8041a51407c403604d0008406496503180500100040000c84c1051a640f4600c10300501c4025034000c50b807501ca050007207441d85130a241001030400d000318a010465519030001d1580d40c0040b0466241a040c00c03a20007540408440d102c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 754157940 1250 754156690 754156723
    0xe012706060e0412030b010806060f070609150c020c10080f0907030213060311010c050606060a1803240507080a18140c0f0405040f12050d2c030313060c02 68
    0x41005108050001104130340e042d850510240c50707210b004403803100341100c001d540140e0a001c1204505100c0b4080c25900381718420010701c032600c544441d005a965002800c0c003441d214801c1c407004540c14031135904100400d980c0406a030810701d8021300403000040904d416500d00c6e100045003c0400c1110700f00031078024010800e00c60b40304002070090f010364042aa4110b0310510021800c0d40f14440079180150401c015028944400d07007001a42d9021014500c01c11070704001d40d204441611000380000d600c40e40e0000340220401c40305044078020031103803080c400d2030401005496500141440c0e0700404004001959400ca42c90000307501c0404075015003021049a05a0781550002401c030b05045c03c00c0300c45074040f46100c8100010b507001107a005010300060085040001e251a003024244d0007142812804c000d601482034040301c1910000c24a204000920400801960326200210440307104c0694558580012120904074100b50004c200c1c1d41e45c0d102d1592128402d01c80c1c1d1058180950 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 754159190 1250 754157940 754157969
    0x60909160b031501080912030a0204030803011d010512060f060d150b0111071d04060603020d0308071202040e04020f121501050307080106060f05030c040e090a05010e01270606 77
    0xe8030301074036070030480d1818102000d6268440c0c842d80a404018440c40c2020020b1010120680340c640d8944c001900745003443d0b40034803012001480e0a805540604801d00081f84901003a4403004070215041e845940071302001c1d50028580b9801003a507a500500001d2a0400d90700c1b91004038010704a441c201a00c0300011300300b60212000940c0008003144002d03039400b108090485115501ca840904c21034040140c013080040301c101e689400341d5030090207180009000c585d40c3d00803a03120f29015000f2400500300204103d0400c0d00062445c4540a00c00000c600309810041540d01d01003000c4c20207882141512065031160b662030b44508001a100310130f9581c02400c035141207420580a00030380c2d110b03000701c40000c191805c0510030360044403125640d40c50741000c840300c04c3d501c40e8005040c14414040410000c140511842d4140380100d205200074900c21031241005421142410302c400420303410301580c240250b00c4603810102c0d100300311030701450307200d89413414400804065012440c040c1514 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 754160440 1250 754159190 754159199
    0xc061a090c070c0e07032f040e0a0209060a05070c061d0f0d02030f0106030b0604091a1909030c1401060303080a150503060709030210030b0915040f051008010605031506090916 77
    0x5807c80784c44070000600844100c50210b80c0340e1400c018202ea40711071f0341d60a01080216034400003425401c003400d120014584540074021503e036038402e102c940003040c800211a400c124100c60760000902039407920a40b6000f6861246123012103117282c1901c16402c410200f07180360350780003000030100e40c0101102d0514052140440c06000c0c00c0c030054401c204550009001410306004215081e03030300c0702581c0544000b44449a581d04405045552400000508c40b2a110075030f100b4008035038080c2d20740c031401640603e8000c52159442c401e19049904107a81040001e4100b4a040d4101c05134210100d400942031407244500490350344001e40c51f00c501c9041c403001c1504154020140e9009580703100901501e08419800d40d24040489a0804005800a212400c070b060038500903140080c004280d080c103203a04a002d95005407a056001c44001070100200c4000f40710700302c01450103502070b00440c988519500d51f80c0400402d014050120100001d05c002d9080c000301c200c40101001c04076074541ca8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 754161690 1250 754160440 754160447
    0x41208090415063c020f060c09040605060a0e040f020d0513050c01022a061b06090c0a0e0c0f0f04150f1119050304150c061a090c070c0e07 61
    0x81d4450900400c64903640101e00c4c000300700300c1180c0501100d14211031203c420242101d2022002c00580c11401040f5100408580c10b000250182002c2c0c8640e03a11070141c0030400040301c19a40c4940d1095000f00154003025070404a44d07850000e08480c00540340420f464404060b03c1072001408100c0c0c5040200812840141c0f400b1a0041c041c00444e500c825440c401640d68880512091041c020341c0c0f1205100c541e0200d1001d801d00101500a03070415100c0640c03058a01e20f0b01c40f0086058010380100054490100803e90201c44112030301c90a1500e013a580c10703401c60014108404909000031040c0c0d0b80c1e1448001c07110301c0650342c1e50440d51a80c0c2d80d9482410b8007101c00c1040c0c0003030340503001d01d800503108106210158106034043c2c01d175200f0b4441c01d00e446080510341280c00e8001403200142405092a0500c480d16141e00e4209400401d40b6041c4100e5000e0307500010207840311244452191a4a12103030743c0019110b003602d0342d8101d281418500c60031a035000c00c1d80303901d0309020844020390 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 754162940 1250 754161690 754161731
    0x90302010c0b22140d14030a05130c080c100918020f0708030c07060513080a0f020a2003010f0c020703080c07120f15060b0f090109050303072d0302030412080904 71
    0x6542d0700b039036030409007585e0071107045030350000350103030200b007400458245405a80880d8211804030041c104502250fa00c11500190680c803100040d009181140d001e41000c1e5008450070b0001d00c0c00d02c0b074240c00e046002d1038440807101c000c2c0750701d64045408060030544d44119040981c011544640320300e03109003441b0180d80198011035560781042c0124513151205404050440d5009814908100361030408580000d000070a24007107215050b10640415a490400100d40c607007044030300071700c0640e1800d142c2552030440303041420b5840c041d0245249503004c12001300b41c2e03500541282d0b4035400009402d140030400d4015a80741b44540249808112000c05812201807062401082e21071309c078000071044039060303c01c01d500c40a040100410000c4904000c240f0140d0504200180640f00c801091558110410450346003590000020403540103095003aa44c032a200021000100641d400035180e000b0b9104003504520074001c881d041001c0c0c507080d2400381a02420802c0150041045801300a4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 754164190 1250 754162940 754162973
    0x41716140d0201140d061403010b011d010f091d0a060b071203020c0f010204030b041e081606181b0501030903050301031101020307050d020307060507090302010c0b22 73
    0x214405000508400c554003100303492000204031220140e855001500e0300e0202501c1c008100a0030407840d99031214611520f0042c080310182c104203601c070714042c1401c40d2050080103041c041282c0782035400c290318040c078041034030003032a00440300c00c4081c00039a17031440d103604014900214044226103000d910507401e4424504541c00380300a030303641e04100885106a007805031600003040414142c05019070000c02d604160001142c0303030740160942107400c9130040e400c11600c1003108020b100510240031003440c4103199421807590a43c40c141d980c00a21310034051404048001c40c080c410070b000c49030340b001c090ba9061251440c80d081252614054220718400e44420fa40c000c1500498030b54070034030410f05c14076411f8540b40d140d80d095480b400d06040c0719241c558112f100c200003440000748180000c24000c503584d0015901e450384d074540070050320710061480d01001148082003000d81c1c1d04c0b800706100f0a800054018040c1c8440d4040e100700b4841117221346480005038080c100b045509a20418040c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 754165440 1250 754164190 754164223
    0x606050f04051c050f241509101e031a090316021332152101020a09030b0912071103071505040914040c170c04060f030b151c03050417 59
    0x130f14084030104800c1c5041d64056070003802d040d05091f05080c02915590002400032001445070707507818594150b03046802c82d20b0302d110000349042080148540786800148000b8500c03a00e00c0c034285207030a0360390003040c00024a0301d4401c0350940c20354039800700703004584495040030310102d01d01c10205055040401035020254000c8071190f00b42030203038024140900020302e40d400c144030580d801c000c440d40c1c0805110f40e081a03070660754410035100748020056003106484034040c0b50301e941000c0c0c0003854001c01c1c4401e41c1d00f00322140910043e0840484660561154414494000140220b4a0410190080d038480160040708010894108001c1c20440c0d1007104144070070360034821101084002039a00422804002c0c0c8280800e400280c0811030942c525401c03264628019000941901d030103a00140e4181400300091040c066141881d13988010403803403141c03800c042030001c070300300c0318100310811000943c0c41c1c0108101803007101102d000300714442c040b00560581a4095454006520001e03024 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 754166690 1250 754165440 754165483
    0x60a05060906041418070b0a091e03082a010f1508160e0c1201030f060f05060a0b0d0b0306090f0115081506010903050307050607030606050f04051c050f 67
    0x80c3d240078054940319091030300d841ca4064940c442001411500c3c9440d00c400307801391040108800c0d8000707001c2e0282e105a56500f1003681d1500340b2000072901482e9007818500003145050010a80c0101101e034200301110040e00300b00301c60005000704c140d4150000005500300702011000201075003107014201100d440380040c0b00d0352012129a142000148070f0602c80c2c03150402c010410010000c0d0340d000ea405803209240c500c1044600019940036007044400501c284014420301030580300340b1480c119005020046402c00800050180c03d00d48205244c107440052000e4000d1060341001d03107844000303411100306007031042126850b00c04801c040c400311340c602003440c86050a145d0035181122900c1000d008000088860150400401041c56060011802d000000110100001e014550040001d0003140c1040c0b00024103079142a84904208038061140300003043e07481c0c044604035030040b20070031007070040e00503030182038802d0b04809040c9004e456080e600c00d20001c9850f450650600d0701d01c43d607 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 754167940 1250 754166690 754166701
    0x703170307030b060d0906053102010201091e150209090415060510170a0603080f0706060b030108030703030606110706110c0a0e0121030905011d150904110705030f030c0c060a050609 80
    0x6804001201840320410766100c50400c080381c0481d1a100c89d40188004640d401d03180d119003404516250591a092254018110901400008110019034034140c294500403034178001036038240001d84007030030320800125860400031056020000900c005001180607078840c44000d400d00d00d0305403170102e56002d48400104070b1500342c440d03101a40e6000307a400c2e081240400a50049400904c0b0454480c1e58414001c6000400b4070041e40c000c10320340004640d01c0c4840e2500a050f68030b158480414072003554036510790168046400020340e2082e1404031030382140d889070b40e494412418001c1c1e400c0030388001c3c080750703194210107418181d07910b001d1141022420090950500880381d000940044e4510314103000945c8181016001081c0081041003480810000100c224000b024000890340c400200e80201e81054061102c2800068048074100465921035645a01c03e00380150300300440000095109074910003078600b800c44420864000e4034185880c40010321003520051711030045800080d4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 754169190 1250 754167940 754167961
    0xc07060f0903050412060f1b030b0901030c090f0b1e1207030b0411120f01060515031b090102101b120905100c0c020904050105060a080703170307030b060d090605 71
    0x30501d55041d0380d240d240c580342c0346010a04a18403402242c0a64803100350341d1140f035a60103148000c4002102d10840f242000c100030782200e01c0121154050035089004102054400781c9040803207800350004110400b00300240e000a1000300d00b11640003040861000501281e0000c1242c051020744403181c08801c021101613641c506440001c01d0500850300145c00600c03c0c0fa40030204c910060456088a42990141828554550031002060395170340070401c0f041c80e02c200001c0c0010064901203296081020318403100f110344106591403080005480b4413117920801c940400c02e005440c01b0000110018900d80080c2d01c109945c0c0005201482c120b4000881d5125000d901135014000300b0390303a00c01d48000b00c00b17409002d48480900200440c10340c0945c580c0903402c0c3c8a9403052000240c90b2a0007810446e0350403a54111640c40e0380314840600008040341d00305080c00408103840364480d41c456108602074403107800e0041d00568042032400e0588441d81000e100c403841030000340407a0b1303100704804 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 754170440 1250 754169190 754169201
    0x1092a081209011d03100b041a1e19090501080c011409040b04060b040b070b070813030305090705040c0809071a07150b040c05030118090f290c07060f 66
    0x806000a040288032050341c0500020824104545410030b032041c40103001a080041a81c1085100c9860303000c00045460548289d18030111845425841c03e020080401c9180501100d083d0941503a48001c140d15a00c0d8042155540c1c404066044c04903110030415029200030f100ba882c0303511030342101e14515030140c405840302c4403848150714184141c5800708405888245403d98002d5039581c2c0c0070403c404500003c03c080d1404186a43d56040c140c6480450f50300000c05000410070204e042c0540c0c2d041d90f1414840d129003626001c16162240300406082c905c00d81d002552080c039081724034125941040380b06100c0d020b41401d0ba41042c3d521084aa02c04550a0684840301420080000090515901940c0e00c4600030700010381007043c1c90118044070b09542558001c143c01000400407100c000036030f0000b04100300001d01175443c182d51a080c442ca680b9100030402d11401c0da0040d90081040b0035816480301e01d00e008003030350402c00303416840d0350301000c1c040e00e00d00e00b00b03160480240d8290240c0c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 754171690 1250 754170440 754170463
    0x50d08091902011809021b0f0c210f03130608070e03030d0f150603021e07050a020411091003060f06230c0f070b03010e0a050f0a0b010201092a08 64
    0x4121110282d0044840414280360b420380d003062500d02040822032072018090f0b25001402050444006003102841c0100c0030700b010740706900c0724003112504c1d25141580031070b1030304080c1d100c1c0f215001c20034a1401d202840c210b0003854400403413410710500401c2160811034038140c88210840c1c4401004446d4074007c3c06d01c160301540700300038050b8520078652261414071000c0c4400646002606884c050714070b115032140300040d4001c41c80c5800c00d06880a0280c518014a881e40d140504076540d40340c072100c0c1d10b000039100b1030b902d02100340914110021074405880c0100510038001e2959030160007082d05000d41c1c00b012920001c003051060184181c292010948045014480a144ca20001741d03845404980300500848245004d00ba008002d144007a200683c0501d8896040c400b15160214000b040032515506002c00c0c0000012728030003044c5c005044080c042508040400141c0c05801c0300c0d01c00510881507091b10010034040808071231301c1184ad100e0090680c0d80c2c1d40035010703940d03c00c0540 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 754172940 1250 754171690 754171723
    0x21011214070308120a06090c1e09030c09050f090313030f170309010921230909091b0d0b060910051203030109150f2d15030b03011b18050904050d0809 66
    0x400c280c01c0c5d291034035404a556110300e4007032b51558490381c07080c4862005502440300d0700c1d118010b21440d0440d400101b0b41c0040c24600850900e030802c00c500c40369201601c0068481440040000d09010082e404060040c403011000781d41e900708001c82d5030003010030000940d200880071071883d102c0744076103407805046107407980c0d502c8840c885002c1036131892000e5002202380c00001c000d0a003081d12001680352007043c903c1c0103410035817004086c2e401c0c1c0620004080d441404400213000010781110114ae03084102610309000359070300c0109100c020070080d0080d43d0310901200300000340c4007000004505a894598051029140075404a40941028041d0b141001034106051110650ba014900280d040c00c0c940b61500c6107100500d50941400d0350894180c5002402c2c4032034020380c044c02a805c240d4820350081040c0d49000d030032245410405410102000941200c80c45401702450f80b940c0680802001c0702c880c1d00b020720380700e541ca041050045001c2070744000007403840e034404070304002c01e2420780c107 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 754174190 1250 754172940 754172957
    0x903020c120106140f060c0a031d01080f010e15360606090909030f130501020c03070e0c09010207080d020327060403080f0c010501080321011214070308120a06090c 72
    0x40100c021700c030041040c0c100c082402181c2d500101007040b01645170094440390a01c481c0c0d84007003118000614400381c10300c0319181c1407000e071900951006044500302c000411050301c1e25598208130b9220124569440f4840031801c809440800380d1641481303000380c0c0d01100105407072482d20f081220445401c1d40c440b500340003c800e1800e0104006610a804209881c90001141000708107a0080082c55451141c0c64900784a207580410000c070712a501280203105861601c0074401c0381080007050b8031601c0801042c070740040d900030002c4802a16142d4283c0b100c1822200000f541d80e005000f0380140195140d1100038150800507881d0107090001e00360740e11301030964461500c190f001c0850400b00007401c10085040000c00e219841c0a084400090350707a51048980d03001118902c0b01039a8115040307540100800300c070740540800b105510440075280003020140450030a0410750000d0091540018040040382d81c0c010b01e24070032040024200180c60f203901ca1002201e0741510303c680820002c4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 754175440 1250 754174190 754174229
    0x1701050c040302120307081306030608030313020f130908090114040b0d050705190207090c02010b0d021c0b0f0421120e0115030303020306100f090608090c040903020c120106 76
    0x18100348156494131402c5a26040503960ba00f02c0607489010b0b4404802c0b000d50051002e2503040c00340310300601c0090021403c505040303850100d94621010001c0c4188000d041c44c90390f0392111b0030354003400360941c803080000311100d0034010241c0d0312508400380050030b201c4150100900340b8007135a096035001c12841d41054604c80e0f40000078000a019081480800c0c00207101c2d2204010240030350300850350240000030303c1c03d2401c005903030142d1000010f59040a0390400c0380c2d180e1505804116404460444000011000d86100c2005a280140540100104000070380705e02002c1a80114480d04000d641c18410081100b4030702c50501201c80080c50100040c0c070b43d0012070700510400030242000041a144200341d50700d10100641c021408a0340200411600f498400310f01c9180396400e00741a05908007241004100c800b050140205100300c0300d011841452040020004190020704200718003051404e0207940e409030601c1248c420f04060f100c021056806001d200c0440d58484d5180b184601e00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 754176690 1250 754175440 754175449
    0xb04060f030510030f081c021e0d140f04170711040b0a080708071701060f05011b05070b0d0509210a0e0a0b03060a060203120610110f03041701050c040302 68
    0x103894284445070804011012a40c081c042c0c5d103039140300b560740300d0340c418004803006d400501110106405a10501c10184080c2014560003071640c1c21072016641c030845001d6490051142c101801c0c034107400c100402c145020301414803030040b400f40c503034020a840c8000f40030089104545d002800701e000000c91310a6414241c01041d005900100009940c51b10f805800c1d00d40754056022020b41e500c6210100b160800c4152081c0d8030180000c002d00c81c1904241d01a00d00e03094511980b410495205020f682c04c05803041d000d40c4056005090361030495842000c2c8205400c610100c604052925010410050000070484020000e2404141b00500c1e01c1c020a01c00b5007000f50709406001000c0c20911a81c1d850480b031001408140c0001038503170602c0010b12440d2662900400d05543c82041665090070a405510b54131280071030f540c1d0015000e61400722200310705a10f41009620403074800480040010000d0b00650703541c03044a5580c18484c040c03403130a0b03440c141c40103103e01c0d83c10401400541031 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 754177940 1250 754176690 754176701
    0x60507081f061b0210080a0614060f070219080a030f03020c060705090307320d1a040f0b1627030b0a0e0304080c0102070905040b0f04020f030d03020c0105010b04060f03 74
    0x4041e10104a40703c0f403a00401c211491605102000503140ba04001800034a0300c01c100203400c1c200210389605c0d2529010036146d00c1603030a20b840100d0007240d00b408660f200c0120b94441c0056488003a03609035100a0316655506580e0101c020510040a0a4a1900c24802d80302c0d1b00d4081401000551580181075800350b1160041d242c05010310701011840404a031035914007080441884c1c0c2d0310f024841c6481400120301c240151058101d4462100402d89030344000668a400d481d07004031036104c0d403070320760001e4612410051445005000304407a000004200101584058a81c985071640c115000c03a1304400300028101850b80c40315043c000b00701b2000c9000d9000071580b9000032000c03200002149150070560245151754031a05003000750b543e040c000107005040e030010501c80c505086d940c40c04842001446030490440e6200000c040d9904c850003201200d03000b03400d0364045405480d0007000b030750081c0080c1d10309608041c00040c607101c0e1030003120200c940c1d940d600203880800080403400b404 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 754179190 1250 754177940 754177967
    0xb03040807020120010c0c0b0907060819140c0702011101050613110c010608030406030e07060507031d0604060309060e120901050307030b060d06150206010302030d03150e0103060507081f06 83
    0xf408507050014911003485506d451201c56100ea681d10030151401d14050140202911069000a00c00b000391980026090b50042101c51040c0c0302207070401d4840b4000e020680700803102d00140c10a101145020400a2080728000c1ea240c2c03444084601074a400e9580a031082a002000b0294420342c5c01901e9202892290302806810b1800041d000803909442250300302c00d000d600001800c000c0141c00d4440c04900400700d03405005c3da94038180c009021802001d0300036013402880014080426100d10444031a9a401000d40752959101c00c1c1c0100101207204040701e020380740c04402076452800042100d0110880c803030f03075031034000d0f102c00448003034001030140000e2540390030030b190302d80d40d07050050f01c03103803803880c000140540c40d01c440008042440001030095410180061016842c003040f0000c2c520900d00f404102d40f46100f580440c0e111341ca41c0510341446101001000300b2040d500070030b000305859610403001e80c481d00941180110350341081110400c2019040003160700400c444041003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 754180440 1250 754179190 754179227
    0x606040b1c0204060803030408031914010b21070305060102010e0a020303221815140a0b0318060103080a110303153d08011a0d0518030f04030201090b030408070201 72
    0x29a51140b0311752a541080d58200c0d0b07408000300030002c001201c0a002d002501c4403190600c0031034148164100441418041c0d000510b80008070070203881d4115034501701404031800030165501d4050700040c010001580c038a80154205401c0c1d220407000000e1104490390010050b5140204081c00a45038540c078240745d0351720050346000007845082508050004200e00d010100b201d1102c0c142440103c1c13080d421080c0443c5c400091342d0001c0d1180b8a408040c1d0382c12003080350703482c0c985811134826040401e642c0485403041c4070000c0100204003000d04000c50298239000b1425101c08501d51b00ca00085401c1e410a04481103440034928005520041541041c142c0d0005024a84103000084100f907090701401d044c0c3e010001c6196620002c05d0b401031506a016050145911011a8840c03040240d444ca403581c50744045210802480d0110100c5034407081141c0d03a50b41c1c412520403154004e84000d0f80469a060000540103400e038007102e104651207044c103858500036500545402d820982058002d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 754181690 1250 754180440 754180451
    0x426011509050417040617061f0527090712021e0c06160c0206090a05030a05150a060302100813060f02040302090109090305030103030819020a050307020606040b1c0204 74
    0x140c0102400da5409070011075000310b4107190034205030f40f1351910030303d107105020010003041001a40c009081d81c070100008000940301c0d02c8620010700c50942500383c074181500c070000d4501c941c54101c1d00070582c880031099040c40303000c81069445039038070407030a0150700b200d00d190004240510a00c611403203e0258079006082c820101440c403a6201144031500b50a100003c18180180d02000040d5000c0c181c190920000f03494000000c2014445d040c001703000e40d8012420f481641d4410041b40d01415014085a08400e002d0030100c0da18441c2d119020ba00301d02450114041045500407902581c0c0c001d80030700703152000000111090b0400521141d070702800c046400000517030034010200c50301d490640141e00c0d1801c2d40100640700790181e0207034030f14914205180e80000d801105680c116a0181003170003141c0c2d200c0502d1020501050f1444222600c00503940c10305540001c0514003d05e0b45500b210003659501c0d083c00200d8800c21003241c1c0c480414a44988280e400b188648000b61025101041 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 754182940 1250 754181690 754181711
    0x1c11030c04180902011b061415120606060a0c05010f1814010603030c030c0501240816140906150c0a0b16091712120114010c080430030309050d05042601 67
    0xc5540040c2c402d10304009c0500b440b100c8604c1d01502490007081d18038041c00c0c44d4188000040c0c0701d8441c603640e000a01c0203a1448a091210a500c0014030080141d8144803803103906c03203202c41c0c06021903400c88461500e45400d030811a8140b00703010039603625840e1041b038416580c5040e11440d200c1c0d401203403699220400e0441005034245d5180004181c0b10440b0b18103400d1589c03003804c081035992420201c0303865201c200004502d48042c02e034404019a0341c2d031025140d030350100e500c2c81d40683c140940c400c00005c038007840520000d000380b001c0c3e0150080403010f80b220a044030340c110b041e042e08000590380080900c040c40e1080e15440704d5244410444190100c1814051000c0c0c00a50180c81c000c0250001040140e5000c101401060024688464030300c08903074840c4124011400344180361641c1040320200c421707683da0300c4162900d00d01851b00490004d0314008005d8201004215440d00071110100f807200d015100f5a800c0e6a83c14417003101501d81c0001001034000c41c0342e00900d41d0b40d240c034900c0d131 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 754184190 1250 754182940 754182971
    0xa080a030207030221060606071a0103080c0c060a021e0c0a0303180608060a0e06032b090e06010203120c070b0115020c0609061c11030c04180902011b06 67
    0x400051181e00505a1989103004004454401c5844850710210012686407503034004110658001002c03a800c2e0380b500e5240c1800b040f0341c0200d42c03404d0301804c8901300200030f000700d0401419075401300b20120781031610b01e5018031036540122950071025074460300111841d0300034555041480c61001080350940496440090681002c5070700550100b8181700c61880b0000c860000d59000c0d11250400508505000000c200c0c0c000300f41c850b110300d0244c0f48000c500281d500b8044802d403112941440301100c0d444114241c011414130050b4000300e4500c103000100c044440e040030b8440c00b4141c020b035062226009002e490254000c4c00250300e9001007001800003020040524081e040d07042ea0f81c144010301102c080e10f0650804021441042c090144100c0c503665001181c4004400c525042c0c8808403140801026040904115604040c08400c000c030410044014004880440001034150081085100100e03190f50348068002017540f450100c440e0340449d0010446840b440c40001c40f138140c4415203 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 754185440 1250 754184190 754184203
    0x2903010b041107021813080a05040801061d100e0a0e030c0d0203040f080606090103150f09111503040c14120106090b01171512071706011a1204110a08 66
    0x1015500c00202c0d42405604200145d40c0790880722018410003418004030b0040d038102c4000c00180841000a440c4846504c180c01340c600808002c4020302c000d540750301c2c111541d80c0012140000c4414180001500140890344000484803084080e034400e440d24401e40016281c500c901c4480d43c4030410200134440420400198508215400345840700e0409004092514166000c0020340c2e00c00340034884141e80d00c0071158112039000a03d0102c0c48840075450303001d840b840c10101401840c00d00300100340180708a00c11419502110100d2465402282004503800156000b40500168032024001c0900080e03c0054601000340311407100403800c4201425110190050401c498440140442e2560890b500da4035028a0088400407890301b186071089012944211030320810b03425030415141602404503001410420444d500c0d542c1141200e00c3e6640020301c507485240c01e000041d2044110bc0c0010b0704c2d81c07480b403040c030006182c03a284c482d2040c60880d1641c0310342c4200b907050001250201004403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 754186690 1250 754185440 754185461
    0x1725090302090c0309070806040503030a05040303091401060603150f150c0213090614060d110f04151509080d030203071206030f03080c090d081e04061d042903010b04 73
    0x383c9540f072508901a03414080c440c3d10501c0698080024000001c4000c13080d03d9001c04c82041c00103180c3d80300c0c141240500b180fa5009015201200419010200c06400c04000c0c1c030310f21b031010b0003510310315000c006a60807144143c0e12001c05020050240803400002036942081c64500390032100304071703000140c000001c8070f11034102d0b680da20a03007c20400305000704400c001c2e1181c00e41c0b4a03440d26030040340c4015174251004000d186401c1c40051a0303a20303c4852420360101a00403c030a079203803454141d00f80c2040c01085000030050b00540101380c810b0054000b0340f5206005003404200c007000950194001a000c4000d000c54a610a0f400d583d0034405c00300254040c1580c0c26015510741009442408050116000424100710306045034407640b07080702d05603038481b19041da07400100d546041000d046901040b411840001c00040990b030100340f00c02d00000c4040022410b107120002c10003118040d84012081003d203016141c844203d802c014101e0010180000c11000c42d0200003c0440362130011 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 754187940 1250 754186690 754186711
    0x5010f020f0c010b1005090907030603390b070b071e090e0708040b0105060d151d010807060806010c03030e100515061c2c070303172509030209 63
    0xc8180c007100090140f01c08000060720045c5031051a00d200511922440103250302402004010400e0719202e5400b960055420500c41403108080c2c16088000038000202c0d40c0403400b03416000060051305030003081c03c031010044003900e0300d03010356038078a002c0f9802403010044c40198194188418903100b82204a80740d2660b07030389001e5007087ca20f10841100500103504002c01903082000044c00040700905655089035050348807200000c0400103851041c58640860920303440001c0d0640440b250701806041c100c080f050540c1e00d40c0c01040e82c0c0d0003a44640070004000340f01140030365000f402c595240c0c0c0c1c064900400c00041f544002880e06035011401e404076980d0320304009903668050390000c1440b0084940785c0c581940c04101c4408090700e1024005003581d6140c0300e0000143c002c0c0b25000c1c054001c203000400075200c400c82901d98540b132005a0109440000c3c00c80d00c10035402d0854483c1941c5910044103944074500300c4142c4000150f401d0030f110b5401c0700400565284503170107100b40c2030b0341e0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 754189190 1250 754187940 754187947
    0x302090d0b060319260903100b0f060d060603050106110c041509021317070509040b0c09091504050f010302010c030f020709060e01080f03030f011a3007090b04030f05010f020f 77
    0x3d81d041450312400c4179550080d8240400c140c1603801007101892200c0da000041001d07003c40d00050b0365041c0e41c484140d0b00c80d2001038082c500f2441b5400c500d00f119000d480c200880daa03581801e071180c102118100c2044c1e006440c2c10000380c0b6203644510440030226182c882c01c1c0f5100c0c20100201c3e80704411000141e500c4000802880f0280c10700407600310214409400070614100118003180c0380900014400700940d40010307541c4610350705448042800030840d16850800c070001e5803090340e079a0031030383c09142403400103a9038031320500b9080c0c1200ea040e0349131040203055440440340351061041c460114018520006012003043c06041d01605844d030809920b54074046030b4a01d0484040724801d0b043e0014810031940b0021940c01a04441c500100d1803081d80c141c0303611243d180b203042d02100826814030b240d4024404ea05121401108001807490a5374507403407000c1d142046140309100d00394000700010b02c00554507540c00040f0921031030000c01c036451203043c04026a00006140000301c2000f1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 754190440 1250 754189190 754189223
    0x314070f0b0c19050406020706050d0906060617060603060f040509010f020d0c110d230403020a0e0708090714120703060c0206160305010e070309151e0c0302090d0b060319 75
    0x5080143c140c4a4604184d4a4140303001d0001e91910103030b20901d400d1046c007041c40110100719401462640742d000d80e04002e15038079210003500f00f140490601104801c0140002c58905000080324001d100042281090540c00402c0102500d402409903941f9500e83c8807440c15004640042c10040941c08c0f00440c00121070301005002284100000f0b41da41d1058040d0700386113400644800304010440342c451120800c0c441810054072983e8002900050b0405c00010346200c070428984c0543c002d80e0391702e21700b9116030180950300c056600031200b5610902003284120b02d055100c0c02c100c1e24a01c001e90380d403280c0d0f0742c0b00c5c0401c5444040e21140543c12107010410b03204410503001c00da02106040800031541011429001680b0043c101c03814540d0f50714410007800b0200c55100340b1090550800c4c0304e06101e400295000e100155038813080396003000c0320309000c50b0090003034034841000a0700c44461000d968480904240010780500d80602400044285039420b0411945515000701c03d90482c06080 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 754191690 1250 754190440 754190467
    0x9010203161211031c0b0a0b0a05030f0127150b031003050607020d0206011412010524120a021c0b0f160914130b130e070905040314070f0b0c 62
    0x4450f020107030410002c0c0b1384042d05100b03560120a20160340011410785c200c01003465520315400561110102040c601100c503884401140705106054030080e00381da880004000c49942d8040d83c0719450301d020141066000d055018050040a00c0038081d900d035550019404070782e1042e0340106c00301e69899810301c14803070300704586600246180300400154502c20720082d00c507a0107010713400401c0c10a09420405582c3c01c0804024140303198000c01c44d41c100071242000542010b0200c07900000405140b0000d8900303455200b907180649006002081859400c1081c1c04030442004e006540301c00010030080b500e441d4040344203070348099200c1914142030702400c54408002c402c41c400c2041c82c10003400070ae400180b00e81413642c1e003a95a80715515048580c130025108861881e034000445004851641419411118a240c0428190303500c5640310f00c202020f80d00d085038060702048801088811602030a0001c08180c1e01031800342c980b400380b42e500d40b2101a404c2d0b6500d1a2030b4404500542d89030701 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 754192940 1250 754191690 754191707
    0x2003040906050a0e16020a020a140112021e0304020612070518060f0f0703411305011b020411040e0a060302090c0705071802040315020f0906090102031612 68
    0x21503c201e5210301d06a200f00d1180001410f50001c0203120440c5036496000b00402c800c80c03940248811131003502c509507200224082030308076000483c1d2441e0b90a00705a00e1017200e00390002080000c00740002c03100941819440640b01f00d80001c010400b100c2204800007190f4040c0e00382d036841c650340701520103084d800c0041c42c00704188500ca04120f00000006c20b0380031a00700e22154035400781c0303481d003d080540e04507680910015000b0403040d0710202c44801d41c80e1441c5065070084400b030000f0b0541c2c405010724084c0b0785032101c4040303105505200560066000c0c2280150b00c065809101d0000e07400b01d410341e0b4401c08000d4a2940209044c4034a080e1000d946070310940692041102502e160001484010701800b00c2c3d8654200007541000e000e81440600d01401500c000b500c0e46941d020900802980584000d966140d48554000600450b5000303c40d41d14541c204520700f843d4904003003241a50100408a066100070441c814058401c0c280e008441070145040b08140190038201914910 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 754194190 1250 754192940 754192949
    0x140109050c10261302030601030302010c0f0c02090c1b0102040806160215150604090e0c01032316031409070e0a11040905060301020412080301081603020618012003040906 75
    0x85070303014001a80e100700b29280f021422044402d0100d4403081d413188100c0b041600081d425006250010040c19015002110380a1095885806d4510b002c030003203450601880f0021b51100111020070203c81642004d0044070090050803a6448450380391942281c0c0503900582d02c581281d02003100340c0103280068269203126001901451074a040488046000103000e01c00801c2e8a101026407511024241c5010b021002000c0114005e074000711a51558050b418500290920b0440407070b0001c41c0400d205070f0741d0340100010700d40c4c803900c408070f402e445802c10510801d80c1c1c45000d5642d84508030045405084084090a00340f82064400d54050a00034034200c106030600c4a002290305034002107604603104410006060348808000a000e40f045038000f03800a8a524019020300601d01c00550407984108221200003402d100007103000591440b01960244091281074103441c4011451813106005143c00858501c0e09548035201d621003145000c6280d0010a007032020310803034401d000160 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 754195440 1250 754194190 754194197
    0x906081305061b0c07030503090405131e060207021c060c0f020a02130e250501091401110c1926030a0c11040603080c2401050d140109050c10 62
    0x100346840d015558040038041c007003003100c040d818041c0550400255020041c04500b43c608090750313820046e541c1c1e08041c4045200d9403a00011035070b5504a51001400c455000307800c00e10124002100900b0000201016070300d6a408000110050340c4044911540b0038280304040c005ca882800d0200440f00e000070307402c082c4601c5ca103990007119000034241c0700461b412241d4902581380a00c060016147c0a001010140300d001c4080c0800c0851507062059041c051201100e11a50341004640420301d52007a040000442c0e904001954418503210344146503043c00c5400c0000c06001103081c400401c1e412342c0190034031210a1043d07198504203809100c0c049186075015841c141d8241c1d0310791140c0c034188400c3c0800801000d0401c0381e80c85030f000103180010070800640707a881c148400741d82e0080071072000a01600d4498000c081c07406112454420119000103520b82c2044148143c03016007240540340319a2180402e1400e003000d0080000131032281002d4000707002880c05110310900c502e8a0310050 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 754196690 1250 754195440 754195471
    0x20405040b011517130206041703090111060c07030c08160b1603050c0301060f14040603020d06060513090b0f060f120108070305060f060f1008040506060a050d02150f0406090608 78
    0x4200300404400e030000c8104030032860f041c17900e00c0000c0c80e9110f26448607400c0744d0302141c031101c02d04022000e44450030082c4c80f030300e422400b450101d640713540c000c4070804040e600a000503000b1921500302034402030702c1480c0b0503103040b018000703a80c4804000c0c00111130200c003543c10000f600e11501200386220301941401e02150900b02004002c038001405803204008129880303110061040100c0083c40c1034819840c0d40d1240c44000080c080e61041215104580c00c2c07083c0050102d00c104104c0d500d8600081e0402d49450416200402510703500000135440308458451081c50b03590f800c000d00e40490701800e80e0f039484410070100d03411100705900c243c10f1500403003000c00100307902148465000b03400320410b00c055035803540040c041ca00c10000d8a504040200c8201c090160041500742c0a58042d90072203030207035a900d080107800c030f500713000f041e030421101e00041e0010700301021161008000d40c00068117185200c0000c2800390450f5008800103040c1120808c0080d42108000ea041406654007081 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 754197940 1250 754196690 754196717
    0x40b1f06091203020717030705060c0414040b1518040b01020607121503080f0a030b04050106020a020405100911120106031a1207261b0a061803020405040b0115 70
    0x203406450301c038940381100049000c904062007440000064140c3c07406801603032400a4400b1f03902e80001070308a4441c4281c00204240b2070002c8140c1d4112200b207405140c1051120081c0006081442d20064002081c00341c040007880a44c1c000e0300c000c140d1010074220941c090010481076401184101d4195003001c004d100e42c95038404034005124140302004615112800c2c00e03080990030a07072015004c8540801c2c8600381b0019134000340141c08580e43c0c02c0c404034851204000c21268207118840160303105030040001800c0542059038000314000104180c903507205c001c641503a000d4058114552000140b881c0318081c50b44804e070240243c0c1c41c0c20000d041607a00d00c0303000704107100c8a042c480da692609820030702d0000c01c031083c00303070210061030001c058207032106030300f400d140d09608841802140e9100c0100f94a400161029401c000c180c0c0c0c040d986022001e07a5000c40d0700745040c00505600380c000c0003507281c1c0d00685010324071a003003440c0e42c1d40c03501d145110100744272400602003140030031001a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 754199190 1250 754197940 754197947
    0xe071208030105091f0e0f160801090e0705090103030201021c0902060403060e031b1006170d03020c1204141003090b06120c040504061407050f0f0a0c0b040b1f06 71
    0x1c2c15100c06660b800e0094481c400142e281d000301044944006281d0320001c02c02051001206020b01340c94422054940c40b901950880c41c43c41116460020760390a0040050000c0c82c0c0010000204c4801514921380e12880414501e01e0240c105030003507900083c3c071445040342c034109000c00c080301c08400c0005158550004c1d50030f1180d41720261a540c0c075071000b454051402d2017101d161008150381d6080c01c0c2ca90f0211a40ca0380074105403001184c1c9070110002d86003940e000412042c0381c0c0100903201c1d190200314190025084039400001620508120719032250101c8004c0c0040d040e00842035060340d111008001200f155107a1020800d810945480001130000310300c960828400c40306c02d00300300320301d15155252040300c088440d8400e050200317000600c51310754400054140740340000d0150740c1d2200402c0d5054807038601c0a4000b51010007184000c0500140a0000c0b102c0d0351034030811042441d210303070405500c1600c0a5460f003846809008000c0b45400c0b4080a022440740f02c5010146443c4015 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 754200440 1250 754199190 754199197
    0x915181f0f061d0a08032a0f06130321090c0b0f2d131827021801090c1806140d02090409030507032703080c01140108010e071208 57
    0x7030403103c40c2242ca100c10303035614401140030b044007a00b1262100b5a40c9010250743c00b02c10018442003a2881440c40805030114502450000d0354009100a4840c014213048111144a0035800c00c8294035292500e041c00e641c51080c030703441000c404185c0d120b040c1040800984554808500035408000c4d0030320b54600d0600b83c41000800481400c40030344202151210314080040f0302080100c00508654182e1412052034280c40d038000e19080312032241c0c14004200c0701409480e05420340c0b0843d074100150340b0315216201007440500741200307250740300700c14140e00c104c203801400000d5142c5001504243c0d118441c012212559001006011f2074190702501c654942440300000b004002207002503070b25250100c0c1c09049010f001000321541e181001081e0360803c5104800092540082004031304a10030503451815000e00d020b2021803450b5103101d050b500015020781c280d500e41001d44080424805980c2c001d050002c004203d100c440440c16041c0310b01c0303420403203644240766081004500080700340d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 754201690 1250 754200440 754200467
    0x170a02130b0c1014010b071b0b070f030215010302090a0b0105070503040e01051c02060d1a04090c061704150207030908010906090c0803090915181f0f06 67
    0x103035640380050028003503004903081125506070000ba40c0d60318140000348911040d144903400c02042c0c000281c4019010000c0c45140c501000c20b00422000c9418048102407081c80d050321881d00a9403164910015081680d007038401c0c2a421220b4814550103100202d520740342d04200401c990304640c0003032202031002c0c182d801220766502200501d0390054084400654000c3c04417074035a07079100714001c00c4080c2409118040d241880e0002070000180040042d01a4028081400c002c00305c14014024010850f008441e50707600310410300c4988591003210001809108519013603428804013500c0700b410851900f128421600c20000419034038046481108a10880943d81c0c07102410201e418510a420201d040d5281618410030860a80d200d070120910642e10490116507540792191030b4003540504c150014510030010b08200350500482010410007450b1040001031140c10045010f4121540c0004080b9902c440759402c5040e8103030700042460110319000701c0c1c00d20400a00324142d0848 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 754202940 1250 754201690 754201711
    0x81b0319031d030705010e160f03031b1e260702040504020604170304050112022b0f0c0804020f0301020c1f3902010e1b0a030503040305150717 63
    0xe80b0a00002c0c1e0b184468000200d800c1101d48454a504009000706811030700300ea045d00c40d0080701640c0c3c501000880045400070034003a035483d8070f90740b03088e5420303810402c909400d608030942c60030005580780708040149c1d0b510340e492407480c001c80c40c4c041040c60f030034a04072441c401d4944c10016802120310031119070f00e905036004981601d5610100790140141e82183d2895003d1103001c50740c03654004003500c101d4109030b0700c2c460101451101c1104900c2504d0381c1d2001014560840c0d90b255401e11001c00031000340c400c00196044c3d002910703030119a0304408240c00079500d101444190310b05050405160401140214949040c01480c0c80c0e503201b1010031180c1c490000544000030101540c4000c40c0119100740c0c03020f211212a2410651184904000a442c00144400c3c200d00c0d10510402010001d1100104074411500c0002d04c00c0755160b460303041e4403000b400d0300800011740034000b51008611540c000d110600b00304901c1d0911541c001c1400b4100041c2d54180d400300200035813801e820419446 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 754204190 1250 754202940 754202951
    0x10b13020906392b1e02100f020a03060b090f0907170a0905161505091c03090302150c0604020607060f060f06090e090c0f01110a081b031903 62
    0xd6980044403400f00c8141c2880d41514a09002a801040c4030380104480740d044200740440c0007000001009140c106400902c400500b040d00c490080c0307400140220038011190103507650400d440541e411219505882078020032001115505070240c000a840401d405509103006100840d0003020045101481014002c021558190040c0d0b40f411444401580407511460512a5180600501181152184036a540405860710301c2c06066040d185900310300040c803001c03034100f21080d8001200c0c1a0b0f016525900c000149400c064403a05400c1c8251a484006851801000b080001030702d5414801e070800c103c205c0a0103c0854078950280c0d048442540320526405d00c00024540d000380388859034503104011881142110011080b40d40341d64030062016110148079546680540f803104460340564209900c2e494000340f1001902c4d0103150147c40b101d14844100c0c5130865a41c81980c3c51180041c0525641100074070a02071494550021854041e543c00c900c00a12080382a400c100765941c4c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 754205440 1250 754204190 754204237
    0x30807110d05120c0c040e0d0c0c1d061309030c02040c0908060f0604061e030b04170a03050603010b0402070201020c0f1503070f030c03060506030a0e0c06120a06050f06071410060305010b13020906 86
    0xac804000341550300004500c00e04a45e0001c9c2e008001954458802c020900d50354140d0406401135501141d40741d034400d240c4200701d5003400041c0c48480d28007000c0c0040d00314082452002084007030f10903d001c110784409414401c0c103010454415030808a284141304a411419144540c90503040ba90710000c0e803907072681c0b5810b000c139200c43c180b40d401905400000d141c00045a040c3c028030300403c3d04500800c008071102c0d003080101c1c824080002e01582280c400c104940c5400d007000300f150900a007020070500381c90803003880143d10803190900803c5500340840004c036410311440400c0c280d24201004810709003000100640001441d166160b501c501484040c00740520923404903603405050592190b25082103150200c0701140c1c1c02294503e42170f40060a403402024210f00b007507014011a00d8403c42c1d80302e44200040b40c1714640d80502c0744038161b040c6d1134014410940118020400002c650390b5810821440c002c0319103c091480f80180803a0501e81e4901086800c1c1980d0103d0122104125 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 754206690 1250 754205440 754205453
    0x603010609020f1932211905011a0a090504020409020d110310061d030a0309081c0509192606010609030807110d05120c0c040e0d0c 58
    0xa8101d160894004a8000300820082c8041c04400d81a40b20034040c19a400c03c2c111002d04003110003440070040e07591003001d00b05a0801c407010072180741031030390f00e0700c0520030728040b410303e440e02c02100c080300010420441d0000341e410300c0501010a6000c2c44079526104024100203d10354400c15082c0d40040d00740e0400d40500c6000b001030a005d8001c0d500e0310340d03400a9000940002c0b4140d0b50b0f0b28141a00b100350084244200c0c0d21070802840c0c03034140c19040c0070044400c80006562004010010000428a903500708038007a2200d200342d85407400c440c14004c200703050610070f104001981030b900d203510452a0300181559043c50054410000350a2445e42c540c200092551022864a00f188581040c000c00581c14210120802040386c7c816641c80c481156a4242c9202c0034100140c18041000010b00e074295581b41a80010059081c800b11a1100d6043c0500c4508010b00201d000403c0201004244801d601c24041190100441412280619103c40d000000d0004002062030142d082020 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 754207940 1250 754206690 754206701
    0x20d170c0c0a051c030204030b07031508070905150d0b01051003110d06050a0b070f0f08090918060603070806041502120a06050108160c0f140307060203010e01080a02030312060301 79
    0x160080750500801c0f810075646841c031609284a050a41240080c80c1600900840e000c03254050f0744044103646251003207008100ca80c140d00511203004d50005078420b010031114006d001c8a4100040030308181c0f592049200d20700707203028000c0c144001071002140c1161800f904403001980d4141420a58100880c000c000300c11183c07070314040c0880d9584400d5216440070081d9541074503040301440e100c14404406005116000707088180e1064000300013500c1e5028451030b140301e00d80490a110901d40082c1c28140704444100c2486e004182264104000f00059508000b056001d4007007142800700c49522194001c00c050b054904038a081e111030030280d811545901904001c3d00342604000700118040d01c0d85100b81400038a4500200b03518016101008000c2030142e103884c0741581c07841c0da491100d0098240103803155400000c0040e8011814001016554840c040041e6607605001110010202c1030300030030380c070750b1107c004500181c8002080b01c0b1410300014115007103035a60000a800f518 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 754209190 1250 754207940 754207957
    0x304170d0903021b01082a070f0305340308060d0b0103030503010f1e170f010609090501053d180f0c0206090304120804050402030108060412020d170c 66
    0x500c1c01d00d140301450f501184400e2048900400c04501d00c1c0c55100444403e0000da90716500c00350750400c0684281000380d1a18200780c0750880303c5062a641d501c1e059023010172241c0a5002c5a00043c10000481c4422014010140701e10811540f580305000c400c0714000b10f1321001000e010003032010505a540e0414000d0340c20b40c0c4640407d907190703100c1c42c005010760001e1241c280c00b5140c0f0040440c00070b44034540b46038101034440906209a150803100140c4100c442c00c4000103020b054000040b0728003c0c003c0b080070308000900454011803e14049084403002054131101340071b410300c22511101100d0a8030141e046001d0b000d5a864a034448107015410103500c03441a041c0e000502c0143c82070315400146c031070760241c88104448240644283d07115201202c1c030803031039002000203000a80e224402e044a00b40905480740c00c1c143c444001c10200c0c1c0c020b8111424660140040004214035002509a81492032010f0100422203081c058a5282002c4501c2c038801a80f0001441026110f000d030f440c41c5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 754210440 1250 754209190 754209217
    0xa0e0c0105250f030f1b2a060509182710090b061c110907030222030b090a0f020603040f02030607031b14040b1e070501020309010f0e03030417 63
    0x2c09146820042100c40c410104c0100700b200388503200190040c010707000d8000c4159410401c07516150303940d071441c00000103407405e540c4200b400c01c90320340c40e400308070350240c80561a03240e40e40340b031001003004d20b01004820358060ba2221080110742202c25030740702d1403400106c600b005403000300814070342404000001502c00314548a07402040c001e06109050007400b0545a0b05491001c042085842c03c034404c1c4060200448446600c1031801c20a42440d030080181c0340060801d01001c4a0808410820044031008100180188207000c401500c0a8000203c94006d0605101e1036480030f05d804000880031307106000200006081c030501c01e2a00694a40c0201515091314016802400600d02800400c1d076118a1400c0001443e00826104c00001c0e103801909040600e00112820a94007200e907203c0c440322001c14800c40005400082c0468030f214100140c1c4038a450f6158600b195070581030100128100a1496401c81e40401200d400030380020898800b1252a05d999039144110010400354 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 754211690 1250 754210440 754210507
    0xf070f050f160e0103030f0f020304051504150302121b09040519110a120f0b060c0304140406050f040903030b120d121b0f1106070e090a0e0c0105 64
    0x55103000c9001c080040112802c84400d40e124003044120207002d000040c0410820701a0150090084c5802c412080701841140c0c0b0f02511000400c11000fa02014101e855401040034422254000341c0c000d41e4403100c1c5001c504115101114501d801340140c600415808444c4503070079100c0c1c901c402c41c1c9410301d01520521443c244100100c03a196140c44c08821a245052140c4005196003c111b0307c1e0406180d441070300c1d1640d1420130f03034010310300750b4007403130140e640c89103a1304854440750013401c44c0500700000386480b940f50803032640c3d110703030002105071195113440030500403642c0381040031040c540b00796000102009245000e50041010800c483c5e88400042c0464511007000240c24170310303002503031302d65007403076500d0032400284c07020052020a01c40811010340c45180c460001a941031a03140b406101d9111010702c01420308030183d60413030006410320703448030302410042d00098100e600c84104010002c80e20f07071703140e481322942800c00341080300000f03440402c079440380b9030f60010050311440801c4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 754212940 1250 754211690 754211713
    0x1a09101103090d02070305070603230411010f080907120503090d0c05041503020d060c090e0408030f01060e0d1101030b03030c0a06110301030816080c030d05010f050a06050f070f05 79
    0x1100c1d002210061160b02c03409401a4035288045491400c480d40000201070881c240300003640a4a07180600040d01a000007558420710141e040d92806180641d0342141c1b1601c4070400181a10448490030051114010900166400000f0428126050722441d4a440d418030b2074140e0a621801909942c0211003d5895050040e0304800500b181e00407030701005110404101903143e0320451001070361102c00e1160703510200350907400102115400e881e1460100d61504001010a841500c054940c0c00c004810000400400c0c0c0f08117024200b03a05005890484180002d00c084041400040080b01800d004d403042d40d01175004101c5a05000307064989522484000c02d40d202c804e044150ba00b0390405081a01074041501201d05883e00442080e00c0d0412541e80c0c04d05519844904440d46601040f065617805018400741c42c0041d03c008011032a54940001800c10350f015402085c0300f0402d08504002c4540c0060844950b610803204240d00e45402d8104200c02c0c00b425040904103009054040c2c2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 754214190 1250 754212940 754212971
    0x9121806040510090e090c010e060901020304150806030c060301350f16060504080a080a0e090a0f0b040c0c061d010c05040608010906030b070e0a030606151b1a0910 72
    0x2081e107045d100c01a92070790301c0c019519512440c1000e540c1c0400c00e44140b02c4110300b05100200f40322130040c01100d117050703a20b220000d000e50111010a00040f420b00502103603260500000e0505601110501d0035541020f40207581e414920b81030240d0800c4003c0110403880e180840e2002c456016003d6a1b80794004540d0542ca41d01d01d80015545003891500115038a03024405503001d4462038401020750010b80ea42300491548030306044c0c0148104a088040103a46000440b0b00c2021150004103a030441c1003210f40589000101d4a4440e41c1090107803007503a68011304240c81a038000308045103c04014682c040a07030300c3c1c089152015420419407100c40c0d500500200219840c83c0d40300750780c03a0781e159030401c111005400000c002c3d0080c140840c109911442d00030700100c0c001030070f09081d90340d02e1b503e1038200d442c144e00c600310701941c201e1488211174021002c1c01070f862a00d105c280d4a8000c80e034414000d0015802c003030a401085002040c001c00042160007801c140c80c413130402c0303151034502442e03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 754215440 1250 754214190 754214207
    0x519260c03060c031b040f1202130902010e13090204090f020916020307060c030209030d0929160f050118230d110c0a0312030509121806040510 63
    0x54464060000000e0a00041d01441003c4080c40c035810350b100c2245039001d903034917041d1058646001384008102031021004070300040c0305043d504503480c18944180560300e8800b01d0840d482c42e14260f404405030740c0040c0d10320203984044604100c41c0b060540e602c4020085004081e400c2860711011000300200844d01c480003a0089404c000c1594404c1d85841140d03807004100801a0018800700340041c9031600002042d40042c100541000200d074040381c07505000054800004250704010030900a040b5032404088031440081c60100710f460743d030010940308800c002c12035010030351b00701814480c5410140700c019034850020b1080d00e82c0100102c0d5188100300e000d40e0404a003010b400021008161900c2e03220701d200b0060a4819035101c41a02c4414001d80300301424010700010464a94441e0f02040144d4400c00840405800d00c44005045a0004203a00c44a6000c8501c549a404030711003501d1a03841e607011004041c40111000c40c2440c05030754016a04071700480c861148840c2c01100c1c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 754216690 1250 754215440 754215509
    0x2220906050f0609071b0c05090f10090b030a2d050604110103050f0412050c0106170105011d0a0902011b1a10060e0105090d0c0e1501030b0a0519 64
    0x116003180d1070f80020880c040c501030b141c0d5070115603c9150501301d0070002d03545040642c002d100c440d00311559200807401100084800480d10440e58007007280041002410001030205214108203c054a00100307607a03100d110000780509203024082400200c1c41d12050000b5030300811243d20708403062404a81d10003054a0842c0c6540a02440c50ba85501c01d10503580302d80204c24a144241c1c90345d0b1607100040d01c08040f40030402004010707904000600340188001030aa410050441c24006d01c003180c210f0f030040e082003a0a0074001d1400c1c80300061410703940e40000d03d034140003c442c50340d440181c5543c1c100c440d600d030034004040007440c284122191681c80c00307517055106a0145da00c2011060058500c4e000d0100860003590b1001085c2d40304d03101611402c980a40080007040d12501c8001d59500c80394800d01e04800c5400801220010000381518040700c01c1c2020f1140ca14900e0000b041040c0500450b0300618114009052107141d07031603480c1c003c1686006492061310003161051819041009 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 754217940 1250 754216690 754216711
    0x6130f080d1205060d080702030a1b060306080d080c0c03130e070210050105151c050a090302160303080a0b030a141011040308160c08120d1b0801030222090605 70
    0x2c00d9211804240109480340500070a04140c002e19a5134604190f001420180c2e01446900c1c0b2940001d800c00741c002e403900148010800310141380140080035220640c104000c3c0e50084005124201e403c14076258005807028401500c4160100b070452442c043c1060b800c0340344010380c400040f05c030b541c2c0264a002d0012035003590350048000c3c11540c20303550203200c9c603078010004c0d8600d184111050b2000e010300390300c1144180c070303401110300144095079400d0320011003040d40c40b29101f08164040142c111008001c61003410817074070750b84001d0103140b00100000c85142d01c1d4100510141d4052116842d0180d0040c00c42d1001241d803041240c0d25001b0b4160f520b625860810f410b01c00e001c24400380c034101c07644035001034607000307201a4401c5030b100160340448210108807c040344894080c4484601401c2000c800b03612010600809000da810034011034802201082c2c0518003141d01c14200760560741c040d0b4413801e02c0c0c1001a40c0030020f4800e400c0d2000030b0340c903003000501005a250040c0d070007640f4000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 754219190 1250 754217940 754217957
    0x43005190804031d0d06060305061806040305040e070e030a1202010b0604080a0f020a0f0b031f0302030616020717100b030312071b080c0102130608100506130f080d 72
    0x280291601503080da4050049144136007043c031030903094114030a926002510b440040041640c132442a00c02c02d400440b4960000f00070403010f85c1440840d080c803e4207000c010510b508094601030554819401003400e00c0c0420000030305014000c019000f4601c9000e41254507444003400c108000d010450341c55001542002101429803130144160b5060b10722001c040c005040b42981d81525402078420100e800c001a5400060003080c0a01c1c154001c040180005aa03458404091001000d0121401d07410341a080024000740c0c030005403690303001d480782210309042c1c40c10140503440d08410368803510050611243c180c1c113004000c101840c40e00007000091000d509043c4c00c041e200d006032160074284020710000a68014405c0d50a0343d0540c94000e040c2c80005085d44400505610021403610303d0313074000409110818580d020240144014039003000740f41401c103011b400003000381c8580c905c2450089001e14104001d224210300800802410a4580e50380c1c814554807061002e146002088020 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 754220440 1250 754219190 754219237
    0x2030705060c2b02070915051207140405150103020d1d0a02014808120117010b06040b360a350f2d0a0803043005 50
    0x9002c03c040d03121550040e02a050901d1034010040c0f01540300c102140d0440c4000083d161220a100604245400d000d000d20f40d04002c00712010b00020b42c075480c0228501010804046102c0b400511498401d01e00542d441d0250007045c0050403807680a642942c400640103c407070040080d411500e00e1003078885486901e0300c1c00c114203a0480c0c0d40c00120a440060001030400e0f126010000407000c00c8074198600c0d102c09480d0f0100c0c83e0040403104410580840050001100098440b6000300000000740405a5510049401401248900d84403468081410342c03200003410203500e2119101d00ea503060704510040c07005804083d204030280500b04210740850159030038a1000c8240040b5488a03881c032204413030039031180142c0910f01055026010340e1400c465800d018030100156201e50b840b01c4200815004550406001744002c2240d2185c1c40300000215060149c81d48260448203600c503d5081500383d64181d0810052441040303d6810003142c03c03a00200075100c180000308031502d400c03004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 754221690 1250 754220440 754220503
    0x10605060903031608070803070207090b0f0d0308070309021807080c03091c05041e03020111010606020703200a060201051012031205090c060d061d0403120902030705060c 75
    0x649029603015001041391400b44102d11074040c540c64030500d113a03480e100351515090103d80090304e0420068100c03004c00c001c2d0b0412406064243d00084594004030851403002079103008000d80010203101c5603200040000d8080d9000b44140c81d0060711800810340507444040324950100c4004001c9032080700403480700154002924850425240140040e0021090341002e9580311505c5400b001020400402c6034103545001e0900440a2005922200d04520024100c0340086403a45842e80c074250301006400e5000a4900403282c0100c1c40e405103540c00c3d0503070a022601480c54540202040030001049541503001c6481140d090025003c925120030b00740380c2c4604030780000340009001c0807202d00108215071000c0d4004900b44201c4525a00ca100812510340002c191201155503c10003000f9100d030405002c25103800b0041800c0c114502a9005481a1840140070804c155a51000411920f0400c00d00c80541030003007001c1d07291915508402e540d84969201c8400e0f4141485220b00203884 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 754222940 1250 754221690 754221697
    0x6101202060f07061b031a04021e1602100504090e06041703100f2606090316060f0f09020f0a08030d18020901120317040c03020d0201050702130e01060506 68
    0x1030041105203491600c140018403500481d100780c035130944d102c000680440503042180a484038070385000c03406034150701d8503200750b001c44030455025500400c040400c0e800418080010070740301c04040e03500d41c00c60800c8624050314411009410080c03050754007800307035000b0020b081190111042482803101c40781d0b0a80e1121400c0e80c0090100caa8031a14a0194604d9006141d12000388613800301041d980c0c99440540d419664406203c00b040c0b07584850111004c42c00760050444d038240203040a0500c05440f03560380c46110001e20203961245003032000c004003a08440c04154148006000342101002040000c1600d40c4040341f080c2c405c810601400c1c1042d008c54000c03190900c010390b043c4014008008060172610141207002c1140c0d5543c84016518a21028042d04042400301c40b8406d507882c0150a02800704a82940e0740d40103020400004d07403840700b10b1b0559505441c4e882c1c202c0d08520050f6068041c0450081d0700c951458103000c100c0d07030a03074403e00200041c03c000740040741d80d900503c81c2a12 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 754224190 1250 754222940 754222943
    0xd020d14013303090210050d11030f060108060d0b010f0611010b010e01050c0a141005060a1203051e0d09030816090909020303120916060801290f0a02061012 69
    0x980c035036000c010020310020b00d01121851410b0200f100d403915070008a803102c4035055400813540c080b41c021052401482034042103070381143c601e461400d04845901107400005d01c0d1078100000580000c14644405400340300250b40b00300c80c1015540c607404c2c00010314949004e000001807140c1049642d0030014011250740e401d040e1101400c5401c41001115160300007032101080d0310585604030000f480034048800303c0b0612a0107092083ca4044440080e01c5014100502c42c201d079000038005442c04540144409030b1606007a9601c1c58190070007400c20402412440c16020301091851803280c16801c066400742c4a0b03074401c500f580c3e8980c04400300210544c900d10003d03162190078000c100c00c9134004401c460004089a091800312000403866150449064860390442107100348010901d02081c00945901d042c80345903036043c0601000300140d0a00e44110750401d18560400b40e9201a0450340100381c0d4907441c5039540102c2201955410301660b22841d9801c07400e10024000101241030380146 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 754225440 1250 754224190 754224239
    0x1030302121c0c140c0a0b130c0902030603010f1d010609051b13050303280302071104020901090b0409020a0e04050402150717030a1a0306070e040c050d020d1401 71
    0x100d80079914400030560900410f00f8080445803a5016640312406851180404802070a030144c0c00d1030044810381c009400c0350000c00c4001d0305174000441180030082039824201e070040e181e40d940c10000b405802601d0f0b04040d43d40c50514286408201d5440500300c1d190402e00a003c1c150341e586041048034411210841c0045c84401007100d0141c0e484010010507005007000e403d069140c81c0060300316841005141000c80d90380401240305504031100c40060304103400d086003000585d0715040800750a500e41c407407040e68002010105a030081c41c075040500451078140f80c0b1a41c035101054000d600059898010612824101e50300e0300d894041c0c00c2c80f030b5a014003042c2c000044032415410580007942c040f180c030304401004c02107031500702001d9032140c2e141420104140c41900d0103031300081c00d12212140a500f00b1310401030b505800001041503d14150f0340011040c015001c01c46040c007a04000340d03402400000c035400400c03620f030020210b007040724100c2c07155a44d0360000080011140603101410 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 754226690 1250 754225440 754225477
    0x18050c1201020712021e0604050a0f1b03120e27100e04031e0e0a05060c0304030501051303020c01021f02030a0902040906050708061e120102070212060103030212 71
    0x1605242580511a46040c00050700700201c50740c071414448111002000141c1c030110b60508040b811024803c50160017030040c007841d052a071240c0791107548503080a0405410020300e50200117400c2c41c40171908224403803000c000d81d101d00d42020014150250040010300d100c5000025161440441c51946051284a204d100b4600202c1503400c0c0001c0c0180b80601c1c00d0035000a140000c000b059200318803958917801c01d4290051254905240211007804010240070596482c0d10381840000030784204a80d05516030404d803205c6459403003240c01c028059401c040c14442205200712481f02310f10b10070703001e07140da41e1020303001240d403140c2d130321720042000300790900d4015242d41503401542c016016540118108030103030003240544100060480d6580c4d0342e801000109540081066007114007110220400c0001d1849882c0c541c1282e03041500c00e150300b019964523079109504a44031030382d010700740c0340c0c403584851012500e03880b00344821b8016014003801d0b1050b02840300f0880c3d0309415121107021a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 754227940 1250 754226690 754226713
    0xe0706080402101b0f051002271219110315070302130e0106021b04020a09140a030c031202100903201f0204060909090c05330301091805 60
    0x1580c0e0b00000c150f0f0a0040140c000b0951803040195a00300600a1003002000c0100d4501146425020700f82c244a1510503c403c1c0b11018a011602601c070400d1207401c48020100300001700065441e01c02e2402d039100d8589094040004002d00543e105e001300509400282e52005054480030204296522400550b0004031514040ea024200c030340500c0103609002c9488114500201601381c01031400f5a0169903410141019036031100c070040700640d002e505190364164090002c070018040c1214001161074201d1040e221460310780300075504224510881556420440308002c1803c4040006004900d8810400c502a0041d440c183e54955152500305600c421682e40280511803844002c1c080c03085003003409040030485110111003501c0059660f450325402404ca00c2d6558805607080e03040c1061440403400c0380c41c21000302c1342c062fa8854a403811080c011025000c501c03000c620304540f5010b001c0840c1d080a0b010314141d841d518000c1101170a20070f10844410032180005069500000c020703030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 754229190 1250 754227940 754227949
    0x303030103240513050c010f020c130b041506120207020f060d02071506141f050310030507140405130506010504110904050f0f0c0a2c1201050106030e0706080402 71
    0x2d84a0100c110203a03881220000c00c0320603614280c4070035488a13801d96483d400c0c01400d120a0100c01c609081071103841c0d10340034010b515103d0a881040c814401c6145c1103a0300b06081d04514a00c8500410406c0010010005403911411a0040c40000b90b050002c1c0c0440c8050b910840d05aaa00249000060b200310030802070300360301564446041030b0f000c1c000c0310300041ca01c0141c00d001c06400340c408180a0b04016500d503810b885543d0040c8288409038000c140410f05103c0c2d4203d105c075030310708140c1c1d90b41c0c1c03424400c000c9030b0700d035100803c113204042e0001000d046840303a50390528070031682032106482c2c07411080034007004000b026015420080041040d0b00d841d80c020285207602d0100203041c51122400607003190781c1224924950503841c0108508035031440e04991380a12180e2140c3d00340300c4c015100a0200c2e01081080c2200140141040710008204000f00d1400314002d1001e0386848190310118040c040c00e10076500407034149a065800f040c0041850b0081d2002659003d146940350b40030017 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 754230440 1250 754229190 754229213
    0x807110f0d1818090303060506030a05150105040e150406050a060302130b0702062706180f030a080412080d110c0c06181509060a0c11042304060617101a0303030103 72
    0x49050698a00300040c0d25268840910f0bc551005400004d040c903096030801001231544d4041410003404200a01110584c10070032908842c006640f1040400c06802040040456800550707000c0040c10000891a40c960000c1c21419030b03600907241c00c00d541d41c0740105107000f200802940070070140620201e43c500e0700a07280402041c41214000040d25030040707017082d8007003580700c0d0f9124440c41200a013400d01095980c0d1035030080e8001c019a41c55601c504d02c407801107004009401185c0d059180910018009980c41c400e0044000c002d24000d10501b00c6031035020741e41411003070060785100d050302d141140583d01108a0204022652403222003006940040c850440304010702c20302c1541280e403600c0025102114203a11b85000c0240541890380d8001000b0400740d1203030341070640715042418100c104411405c044541000c0a442c5c6203401c2c00500115007000300344400c40300d40080c500900280828680c9081102001080b40c1d030346400100740941a501c5402d6802080104002400c04614 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 754231690 1250 754230440 754230443
    0xc02010e011d1315140d0b07050d020a0507110a05060a20010e03070308100b07020909030d05091c1409120321040b060f100807110f0d181809 62
    0x310700b0204092000110300840041140e940c040d030b120350031100d8180100c90031010301500d41d41080c92810150000d468000c3d0403000170115403401c000310b11050b009100369041c885800d08255240e440d260300082c15a00b003488143c1c2c6400d810f2075000d681c0c0c10000401e40a868001d00290b1030140c420b02e0944044102e01d1111041500d000418400144203203c0d0016803003403c1e02940c0e0300c9010341401401c4180c0648078801c41c1c0e103041010407400a54500301c410b410350507a044025039581e08940790642c094071080c5010a07003062308102040078007103820a0090358031030200b400159030240840d03000c0d101c10072170400100c01b0040325a01e0b140110b140c0010380071002c06c5900c0d00d65881d8804484418a92403401c2440341c01c4107120401c000f621352243d00ca4002c2d80d9480120140e4800030340400405404030080c40859004101c00511135000b6442e4a11240c0c2115503208022800c156075010354149000096890700398005000c03442024141100c40c80401208450480307403000c0010701c0107620 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 754232940 1250 754231690 754231727
    0x9060a02090d080f040f23011b081303050d050c03040909050c12010e010f090f03120213061205070f0f260a0507030e1c0806030a0204090b040c060c02010e01 69
    0x300400040d0403400240140a5600190750711146000c2c1b9100c444003d5422402ca569206074440000140d8100104003c480c00d00c7c01c0c1d90310340300a0305800c82c0100c44030f202410002000a40c00d6070000030031000740071284582d0031a112920540411030f2940950b0420300003d0b00204002c102c1c00032160091500790f405041581d00c40c0403014001480302c19004411282c5175190601241a6030b030030f2140c4103e03407850500c244011805603541d4500707540d0401004080c40300040f9038501c59007550307069070f070009502c0c85d81180710742c0c803402c015140e401107540410380c4030304220004107030500c96030700d0038410100c5850f20a0040c118020654121140408140f00c0c040302c8200c8904d030281380d80c103286c00b52242400000309410058001019a440444012800da0218504034a00144920304584200d01490704180940310b420009040a00814019602a003440d03c00414030040c0c002581c0158850041c0107a070350754030003041d01c40307162408000e404911500035130651b82d4080c03441064200030044 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 754234190 1250 754232940 754232959
    0xe0901060902070c03110108061f090807060e041d031e071505011e080d200102032d0603030d020a0c0b1f1703030105270403180603020309060a0209 65
    0x2036010883c0c20401d001e4034600c1001ca01001070006582c0d500d540c445e800e00e45a402850840301042c90124501040d013151143d60643d80610b40c802d21001c00541610003c7d80d54056450b4001085015541d81c024403540c0303045510700020081051300b800000c4402d01841c1000c000540c003031044080e1498045485030108807004c00541c40d403149142506000500162550411040c50742650f113050348004c60815a000600c0071090001d0005400e401d1441d260b901c01072019480c090911407548010006d41c00403061003440e4103000d034160162082d510f801c030000005241402c425810988420303825801c00c00c1415140f01c00b80c0c00400309500756050040c055181540c5400d00a1002c4072044840d4281d01e14101c0710a0400e0440b000900d000020b400088200508c2c040d100d00c0103102d00e910420700b400400990391460500b5203102c541c011900d0f03c0610b06410050131044134041120040441040046480750281c8290307405540d901006004d03d41e2014a81c10023035115101196024a044 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 754235440 1250 754234190 754234199
    0xb09030a06060b040f120320120c1b030a03080a0504110603090606041824110d0606090b0705030d05042d02040b010c0213111303081b03130e090106 65
    0x42c01900010a034000e843e507a65031074182910450101c680000621018800060380440d43c0b0128800c0305001010700900503403405e0490510380300042500b15003d4901007203c800750503010030310340741d48106400c17242c144155082c10552038603009907008000c2031703a04021a4911a55a00c0680c0c440e03c6a590b80c030050350720030000b0b44190000c80700c1142640c07112003000000c0c1805c0c041c2c18909980035070040d070b4021042d50340c5562961410481d451318a00306007610b0311000b1a4010035080c2d0002c01103240e80307000da04000070143c4802e01904000c1960807400081c82110a42116009034211000e181051003602d4480c1c00b41030060015505114050310814540404101c3d414007400308030401d200b07107255072040c80152441c0c030040605200b1145a03d502585075400401100c4441346070009c4e02c110150091f024070300640300c682064400070704011007041481c0c03004100550214109500075040d448640769030f0700c52842c4031029840d15080410140344034020b000d420550b114000b01e0529102c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 754236690 1250 754235440 754235453
    0x807030f06170c060c0a03030e0a1e0c150906030902040f110406030f020a09050d08190e0112050c040b0a03140411150405060a0509041409010e100203040c0b09030a 72
    0x240d00929007204080b46018421007081100341d10700c2105032200d604003041d0340401912030001c1e03c809020f15484001100c3d0381407080c40b96220701d541c010011110300e401c01003100780000c015142100e65100824000c54550404000075442c0015681e806541034204402100901082031040383c100b92510303212601c2c00202d02440404500b019003458075030b403412900070241c91030514a00905d40c0304000d10301200350300142c008103682c025500303c0c01d00d4107180303040641d600c1840300c5145810300346c0320f85240c0700e9840850007901080907070703440394031143d03c548900c11194141d03004003102c6010481000002c40050140c041078a0303500700020320900700340100480384c000300c3e0119a003c900d483e6403030b500d00d0404120403802000160b0380742440d003400007154a5100d03421588040c00404100c11000707581c0ca03040b100c080002214150501d00b005817186001e040410b04503407140c001c1c0300030445921a548240ca118940010003080c5561900f00c21480c00c0c0d000c485010341501400280501140340d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 754237940 1250 754236690 754236701
    0x30f07020307050a031d0a24052812020408011a270603030f130f06050a0c020409020d0203100b0306011a040e0a1508030702090a02030601080609070318051b010503010608070807030f 80
    0x140807880100e4174032008051280c0f080c0c400c0d584810b01200f408824000122512050500c601c00e9000703072640a02b682003600e1169012240441d80c9000003404030b109581900f1064030305000b150703c010b85000d01010003004140c40c0220741c1e88a1a00b100c00c9140110208007a030700208040c05903490b05000f19030b140300320351000e040503030740143c1c0203010084150b0803103010004200c44d141c050b00f0010030703a400500c0e0241c0078102a02c501c1e1900050f000799a90041410700c6260700404440401118490b2807010b4000060014840d005000000484003940d01015100e00b80c00145c032494a41001c03502081070402500000d4565070740c0c00d10b00d6059106c83c0c421009042100c000355200c1c5018410440e1100c001810340c40c8003401030050004998012000a0704140f003216030502d40d0766030321001c5005104610b402100c850100240406110b40811805400c2404c81d075a41418248d0900540d4035100a108000009520b140003542d0684034000b200d42001c500d01c5e02107030b24011113003810295070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 754239190 1250 754237940 754237949
    0x4060b060c0c21070911090603070807030b1e04090c1a072f060c0f060a020702041401031112012c06071d01050a050d050c030f07020307050a031d0a 65
    0x920042c020503052901400c40c52800040c000014003243c254242e45031140203502c03030030030960b0b2100300c800c4c61140c50f241900c10290015049545038508840d006106910136107168001c20701d00540b03140340f428a00c02000c080058041d070318407200d01103000d000003040019020740e0f000200303400200d9442c851061007540c400c5000705554035407a55041c4a010090385200420318940c0303801014841c0d00180b071824207400f03030843e80707075803560f04100c061828481000c0c40d03464a03009060030407841014541c0500038030f500940c0d00b040032880b41000854860b10070700001e49410600075143ca2146400004240b02001c440008600c40312401c00103c2d440c1808408811508254091024005010000d86034040d10034034000d00c0d8112020300100d011916802c24074108600043d805200307071b004004455002d07010420030046450201c0c0b1400032900103075800c1005d042c4010100c1c94071807000050f41c0905802c2809420305003101e1f6010f441034100385041031420718074500059103ea0703581000d0750040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 754240440 1250 754239190 754239193
    0x6030403030b12010c0807051b2b020a0213090f060f020306042f0d0e120403060b15180103061503050402010305060d2312040b0c0c0109080a03030504060b060c 70
    0x1c0c01c0300d0040041e8050f030040d2034500b42e8942040c40f0708042e480741119402070785a0510320b6440e25060050030300f4658403521980c00d445205405401d028040039200303c0018104912009410040412601d035101810040e500458040c00085802e000e83d010a21540c800d22011710321000c15543d650a41d2084006200f0703c940c0401000560b081034040d282994243c4410030a444141411692000c2e50803c00400d104101180c6002d90300c04540c810005401c440040302e4665040400c80c01e8598028081261540d040840310411820540c030400700460082d00034038109a4140f01408000050b05440c504050b00d84800045200c41c400070401442116500070825103014000582a030750702400c1a4010340607030f12003101050b00c01461020f50700340030307034520280c500300031042d460b200003107440001c2030380c002400140044011008041c080448001d0702c03810142c4000540381c40b582440b400c81603400c0002d03104002407103a40b203d5406480f4280c000303010500d40f0040f43e11900702540d4146903 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 754241690 1250 754240440 754240451
    0x10303080f22030c080412050f10060503030a0e04060b0a031514060d020705011104080a061104060905090a060f08010209030114041e031b030e100e01021c0c020603040303 75
    0x30003500c429540012602c0181d000950400b60811004408103806010061003407100800c010458003110003c00340c007802ea650705007040c105113456031185442044a84a180080c201029071400790350103d400050203036007001070b03a03903056414031040310400b07a000b035603080d020454000000c0035080d1602c442d607000400a00100c0c01c4407407440700e600300036214011801805410b80c5c4002c100e40001603420000358480d50a45022405403103185200640e4002c0400c0c08946503800045100c206402810f0600c511800c4000348a4248a01d003c1d03a00003c4402c0010302c0709080c020803070307030300080220000a40c05070343d0302c05d0b84201d007000c0c0c0241c0d549035000944103030207180034000c000000403003500d000366600303156540413407880c034203050b610000031000101e4042c580100700640541c1414400720240306098500149410702c0502e03128843e1000d40307100200d05200c1c5000d030804e014103030001c02044c2e500c42001072090f0203c0c000001080a826034075001a100c8002450050380304c0c0d10b01095 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 754242940 1250 754241690 754241701
    0xe032109280807062d050105031e070506040801050624040605071511220b12040201090b0307032a08040308090c04020705070905010509040c050f062203030e010302040b03010b091801030308 83
    0x2043c03070179a50781810b1142400b00610140c4c0d00855070610681c07803840b003250380c0b0041190071420010310350710130b950000d00490000fa201c00190801031180800302d507040ba040401d01c2e2441d06891118040400d074283c28401400402e000308000c0c81c9590050a503810300040e00044101903c0e0b04100704aa80f50010414821210034107000300041101c422000c06054142a00900f4500801d02203910200c40080428250b902030316803a4060f2010352900c40d42c0b03142c000c2001c0d0240407000320042400c1260b41d288041106840e01c1034200040c10364441c0003d4032251011120040c0c0940031680c03e024801e48035056070340d0351008007403451003000500441c070318020011080300e005038082c2d802440741100b00400610006101c0007942d41c200c420002c00141100400c60314020890320704000d03d180301c07203c5d86d5107076084014812079200e540c9091092110800440a900540c492207651200902c018440324611402800b45600094100c00001c01040c04e58003c0c00402ea000b80c001c00c810009005 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 754244190 1250 754242940 754243001
    0x80105090a060e12180a050d060203040507090606020c01081b040e010e010504110d050c13080615040c050a0c260406020d0f050a0c02040e03210928080706 68
    0x3c140150700f2001d8080140c40e280f000f0041e01c01c2041c15992614503d1700301340d0940c0d4000710780c0d000e024081c102c2030880150745003900007540150340a592911a210000810758910b0040c14142e0b44241e029003080380c038030030040d1113142c000307050065050050308000c14030036a020064801002c0c0b0120001555240441e0f030b220103903040e007201d4080c9050148500403c60200c0440d01d90590300c600c00249075855075100c070054011810840000c980c130582c00600c01000060f01c40c0540c0380071400010031100382d0204400c40f84122141d202050042c05003800030340c01458004a0180a20030034410211000b914500c4540d5414002c01083c1c401b007800d00201e581003004103100304140c2804c0000c0d01410202610900074a00d000c1d0402400600020854556811415500c51400100cac1e803228803980c035040e2031219002d55130825115100010300022000201441c0d15210b04a4201c1860881c00305199041c40c1c9604c10f0715903130002c01a040020340c00d4411059601030606001c881c0111003001071 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 754245440 1250 754244190 754244201
    0x3070309090e0a03080405072403150509061207090912091409010e090102070507030b061003051003030c0302120a0c020f01050c100e0a0204050118060f0e01030219080105090a06 78
    0x140e0740701e191420700842c0310000101c10280503054140401d03d030365249805032400030321390410802c0d0842c11540c1d401c2c1d02150124281c080080e510240103103c5c038801986112151485401c0c1d01c00100408581142000c894458407021002d06861540e03464011100644032820300480c2c55162640d1003000b2241c0c0801c1400c041c0144c09002c02d0f6640550700011a5540e06008941c07850a40c0d201240d00c48da000d504031002d06a1040c1600c802607542c2c01c0c01c1c80915812075005002d00c0300c0030010b545162080c45814401c400810150600d03070304680782100d5255070103004500703500c00c101d44a00c0399003941000c0c100d209007955485280b089240b041c0050300d01c040e20100c4c1031081c203000c580000c0c01d01042e41914150318040001d0702c2c80c0c015841900d03003004d1100184d08a0b03e050004254030246401001e0740d409000800d2044668030201c102e05001c0720f200c1c00c1e213041c1014005000500c2c03c1000c100503921181000000c00d81c0750b043c41421124280c5107050300d6071000c84c4a00822000e4081e0307 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 754246690 1250 754245440 754245449
    0x120601050c0604060213181508070602032d0d0905011d1b0307050a17010507020703020d080307121404110307151b08030c040311060708090906040605060c03070309 72
    0x209081c0019a41401e9031540c002c0d20041500340c01045e800b1041c06c004002c00e00916403130990005004408100d1b81c003c1148a520113260008181c01080d1502c00141450858540364011481d0041c1c2176010007403443c410300120001148401c0ca4a20300d4800300246c081315070303080070004040441e40303000783c01c4419030750154480742d4020055580308140483c00b030000c01c0010b03c140a0200c0d0540010782400b0040c0c01c5140c0c001e0313a0307150100b500d1160101c891140c84c3e1800c02003095444100c81665180071078030000754451114600500021a22170107150801110b09102202c1030000d501002641c00c078914200040d074007442048180b005110100380105415400303010021b05040c0c1300d50030b503d94444e2640500c0f61000800c401e007042e80304042035003030304004000e40702e04000ca1040401e038000e200c141c40005d5500152a03191414004440c54240c0c495a407500d4407100305c0c20b1008a000080089610541d07424001a07952035040003012801d441402440c0c0c3c0d07601a21b0060300c4501d0b142c01 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 754247940 1250 754246690 754246697
    0xc0a0f020115031e05010e0102090306180327040c030f1802091605070209180f07060509090402060c011a011103040b04051507210807020f0601031205040317120601 72
    0x1d802c05024088111105903600711030501100794540168a0500c440c54000030400d40c60080140709003003040d40600011101101602c92545841940d03296082e48031807940c0c107a030400c000f040c0c03414041c12440c4841c144012044042c0c1a21500003c00720750642203c407020036110a4246051b4030988540202d40603000c000041c5020103401083c51610000c01c20140e59035006c40b000041c0740241c0035075400580c010300301d4146103800e8140481a42c6076800c500494401c030003414117004404110b22082e03545079139503941019440d60801c60b040790b0141003a608220100060540000c00b8020b005079030f80041c20360608440c43c10001040c8140c41048194141c005200c240101c1400d44111000c0f00d000300c40004020301181688401071240f01c10049c040025101d0454101c419014940190b003003540341d0089660b680182640c440c4030b280f4808200d80c10060052000414800504dc02180782e440d1080c241901c80d5600c82e40d1190640e580310701c0341000b01c2c2c00d0458050204400303502c81c2d428603 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 754249190 1250 754247940 754247951
    0x17071701151403061c1104180f1e0f0c081603020310050a0213090b09180a1407080706050315041e0b0316030f0b01090b0a0911040e0c0a0f0201 63
    0x1030000c2860300c00001c030718012000000441c00c0d039a100035681c0300703a42001c00701004c0308580789081b400d098451240180100d080500b010703070302c1101114981c0c4468210190b010f0850315642ca000b10340d101c01c0900b05080d1501c5094801040e4640c04861280d441450300c60b001d00e0402d890b441c40c1c490001e51500e00c40803100424030050f20085076007181c0b17101c201804551074903101e01e504042d00038500c0b40084081c01110004506565800401701d285080d24140010348901e1040c126550302e6100079449648860031810004103101840e06c0c0080689065420980d16070104c0c5080004641c0110001140030040c058a242401c4d80200c51110403a41041050040103500805681d4400c080c0300b040c3c1c1d5005440d8031a1001d10014820720341d00c0c04603144150301ca240451450f070000740180e5070100000d001040c072100c1885600042c080050079440d40920f4500c100e005003200607800c0c2c200d110b080c00002401d80985810a0195030a0002e050f11000340040c0103040e4440c43da0040116814913 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 754250440 1250 754249190 754249229
    0x30b1305341403032b0c0c0b0f0f070806030a020a060207080f03041511190b011d190b040f05180f06070c230a060506030708150703090317071701 64
    0x1040711420110a80454804843c0005c03040b00f9640e0080103002e410300f03044405980700d6100e140140d000e40724540022042c0c03640307045101d84c43c00880e1106408120030000c21034007030091140c07a901c90710050851792002d60320703030105d5000c01003540f0140145c0d01c02d44060100220030711181c050920b42c1c000541c1050710f0b21038906c4503100213806202c140305014001d0540500203000035084180c0c0c004032400c0301e1195282c07045910301c003403181d80c1e40c5613a211400524400307800882401264840c6075188202554090070300107141d10030025600a07965a8003001020260248621411070b00488911541074401414101380d21104183e619410510400c64802e801015200c05160007044d0f400c104c4002c00701241c4800028400c0a440b885144001ca080100726040244214415010b90b0000c40c2c1d290b60031940e8154018204000004640000c0c1c1494803a038055550700d0300901e0034410305503425050320141201a9500c07800141920010a5001341074605107004084c2d8035058844507801 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 754251690 1250 754250440 754250443
    0xa09020421110108090f010c0512160905010e041d011406030d02151003080c0a06180305031306020906040803070b220f03091a12070306030b1305341403 67
    0x410a002e81403180c25400b00d000074108001c0c50f80002c0148000b0030001c128002e0240c240e41010031401860021200000e8070194103c0074949160102d0b192086031900703040054629102d10305072141c2065903801c141e00c00c000010100049960075100020721200080803007440300100500081c0281d00000c001c6400c1039001070f1407441920415141036a80d12100801c8408801750740c00a0000c0c00003050b1901240800f280d42110b6520410003041030b2016900b60702c0c001c1c1d204100140200300305000141420a40100c4680b1079840f0b490011324100401e000911150825002104280d00105404040024581f40960003d404200580602c0040e080160f0a044001c200410290300c100039881010700032040080074011448610500a000c3c81c074280f8141c0010f40700b00000e4910001254001d8007034400c14041c1e94104d00401117a640f503000e002000d1000640448542c42240c02c000c180c1002541c4480c882001840521500c0c5a2030711031451207801500040d6081ca030407151000c05990 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 754252940 1250 754251690 754251713
    0x61012060903030b040f0507020601082d241807030b071b120c031d0102070b13230909010e033a020307080f10030209060607020a09020421 61
    0x3488803010401c4201d038501100688604081250018240040d0702100001c54004501c140740da982100e010384e0340e4907034495813010380702c0a207522581c10803443c54000040d50482003240f4607400480c3c140b121204500c0346041401d0a6910225002006000346d0520205464114002c0307034000b0966141151152003420b00d01621503018080f81c8cd07540300d85102002046042e10341c004003580107011a40502a2448039004000c0700000e009001c8140305217015443c1d80c40780305060740104001030800b90300800c503074480641c500c0c1c4080c0040001039107150341c80d4140003c205130114042c0101591040c440e42090180600703a16904014009024182c0002680d00da5001c0414440708488046001c41e4036134000d40000b00004841d441c170b4448030b0110b0700154011002030f0b440214076034136181c41e6003800c4000c0d00d4a05510098074010005481c0104400f0340164004213010324203146a800a15424001c2d40520142134010404101c404081c10a4000000d001841c20050000c55620b00c1c61010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 754254190 1250 754252940 754252943
    0xd050405010528080a0b0303042409180c1101021606020306040b03120a1707050712110607090f052b030e030a0309080d2c01030f0606050309061012 65
    0x408110b10b14101c9030510385504240550f03a00151100400100802c000c204484044106040500443c40da040005c2103e0803a1280040b0340c50355003480ca4402e40041c155154402002480070010940c81814203508a010096000014038440441400352070401d4204141384a40d2040c0038940c1d1303164080c803850003c1940a403005a4a5583c400000c00501c00e24030344582502c5202420f000743c040010080c0304d0304a181e00d0301400204030b103801c69910702c01281e03040000745051080c2400542034626203034051706076042020548041d01c0c0741c07600c0d0190480d00d501c00628290760420110800284060250200341c4055015013040324810300040032140e10307249480555254030040c584100028945080d00800341c40200703030381c0d05000344506464010300720b06001e10158690002d010b030009100070300c85c150890070f0807034904c0341d040e0802104140c150b05054803041112600d00003441084040d00e00d5461b01512400c21b010325902c3e000000700903161441101c00d00740b0681d55110400010a03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 754255440 1250 754254190 754254197
    0xe010807120f02090901050a06020703080f09040c0e09090c01020a030e030f250806010e0c03041a1008070504051e0403030b180906160516020f060d021b0d05040501 72
    0x151180322003107400040c6198100015880c08000e60a42c04580c2c00400080000b02e807100040c0e601c130300c100130091100780720341405a401100100b0004041c0b101904031002c102407554186001000800d041d0303011040c3d40c41c000350b401c60300c0300f580d4034081011680103440c0d400104113404000b030010355a0680c4140c0074041c040c0410481170699010003a51a091007241c1c140d80c0702483e1196201c900300130341002c00040e1030040c0700c040b4401c00700151050480703911694104154031844d10b117620079400500103403040c1f0401002c2044070303058810302d41d00505800c2c811120141c50302300c0450810415810041c40fa600340014410701ca81e08440d6084046488603003803000c0e40300d40c5010740050083c0d501c15038110b11141c0710403004900d0b03c41503030b03ca11041d800381e0316565641103011404a000706070030305c04a00140202e602c00030f08440c0103a545440944030f6500843c415000400380e0b0400c0500004c11600010100d05001e25040100d00040b0400000c1048414451014010740118010203040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 754256690 1250 754255440 754255457
    0xf010c0204020c070f050a0b03102c2701050c0301090e0f010c1e2d17091011120106030506130212040b060a0e0a020f121303090608070e01 61
    0xd40d03407154111982820004101c6056941c2e032510480300c21810301c0b0341d62045942c150009031500500c000c891182e060b403190781c204a420024400c55071001401541e0600d003951a00c00c1040c0703d120806805080c2d4014040019405501070075103004012046c2509a41045c0a020000505400b40c1e0b040da182440082088003045022a02e4916588007206084d03080c00f100104c0b080d003140c8111310404550307005000d8805145030988401071900d8034a00c1440c0004109050710706104000c0840c07103c1071509000d020502555402042e10030346a41c5220b40040031084800085e901c40c0d518a05988445c6509105030b01c00c1c071010f0180c0501ca614145501c1da40081d905940d106440f600c4610340d01411900c2c0e20f6956004d44032520112021651908000c011903002d16103082e5150490f20005940200c0e0390700d08101d00044d400080404002d40428481484d030360160703416075803090540040075007144400e410000c0600e9090307485102445a410180180c20350702000c1043c0c800428240a00d9 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 754257940 1250 754256690 754256693
    0x60a05040b01200c180703050a0501270f140a05100605070308070905060c0105150f0f2416200a15020a0c060908011b02190606090906020405100e0f010c 67
    0x4045511504580c4917064078005a010322400c040540038224503542000305036103031840001118030a000e50b019a9113040c103200802400400c450103c484203a4010884d80f81030440e980a43d07105c4010724211081200c01c112a5207540d20903958080184017001c04028903200014003503114040b030240802909800040c1030303034040c0c050070000f8640503045607901c4603c43c007898000c1c142611078800d1107031030103110081c5150400c10a103980500610003482a80300c1020400c6100e41d0361150000442070010700c0038803003513000161002c41001e1100706882c02c1107143c22140b8501006400d43e072041c0700244031045448024008054494480401c410090082402e9107020700f00c002c01040fa1011000204441e5407164502c01150403500080c404070740e214001c03e8100280807140310040e441500000c2540f41c020800c0e03003410307009280006509450764a401c090f80c04141040d50a19000a4104224101a40c0c00110000303689424100b25034088002008040840200381c1089051a00d540 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 754259190 1250 754257940 754257943
    0x605030c04030b0106111005160f021c05070c0603180f060209030a050d030c0207030503031f030501180b071b0b0712060e01080d0c0308010b0307030e0a0308060a05040b0120 76
    0x80141d5001a002280d035a91668002c00c0045800e0b4001051f0054001c2c00c0f07203040d00d034050a40112813001d074001840044006c11116030800800c1c00c41140301d00240e4400b4490b00c4110100b641c061a44d8140c0e0f501c01c503040c02e80041c112580701a040500d081000d54046d401010008542030f803001200010910030709110000c0d00070402c06d158140688020700e400c011001404003a02d2541d51000d01c0f17044450710b0240d0b1181d07014400680b1640003080025031a4074034660281108900200315842241c80c2c5d2130f298212118444500d249a106140010078802d031030010036400303a287e00d00404a4030782e00c6200c00c8002c5503807000901c90000034021841c0d50f400b80c04019141000c58a04010309940e4803014408100207200e0351600d400b55550344850303644103110101c500c941540364000c9691070850785c11050342c4014070a00805903103081c000d040e400140324100300345000ea903601c0024100201004000e8840c0d50280f48528a00700000320b03140d8021a052a865190140803000c603007000745802e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 754260440 1250 754259190 754259197
    0x304090b0d0209130b10143109110d0201020a1722170c010512060f060705010b03100204060e3d020f03040f0b071506092708040605030c 60
    0x1d42c49a00301c1c0c200924256960803072001203008051071012030300c480c1404180a81ca500440101f900c140300c800e0700d00e040c441802c0003044c2216803000750080384261888000b81d40034100c9a403c0c2e490360907407807e01001d03041d1a1500c103401c440c103401d030311aa03900103541e8100d80b54000b820240b0102602c4000e00f40b10b030a885210340100002c2d07240b020400c0d5200a400c0a5001d00c0c0004507440c0601c0180c49400030b1141c1e40c000041e1109403420961608031043e1510040140e0762100c4000340c8d05030300e510399078050404244200004552110b111041505041c041c5900c800c0e058410301c0100f1015a00c41c45108600b070081c0c6480d40c41d02e003000d4500c80c2c10103000c01c04440700c0b103050000b026600d40700003154903145030550a076180c200c00d58140c1500c0b03114912800802280d02c1c0400d000b14080d10f0014082c02c0d210b00c5a0000c041100f40c00c0c401920590350002d400180c0c0c4000902c50034144486804403034031010308040d81c5120341c0e6180e900d1801035000e61010040041700107101840001c0c200c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 754261690 1250 754260440 754260443
    0xc060e060907030501061a09060322210807051c0905030a08041a04020307050f122b210e030c010608071412100b031510050103060e090304090b0d 64
    0x1a80d03000e2800d40e41d800e9035120b5034442114250310b050350000e40804140d1807188410b48282000345002841c0003045080d070000b400315100c071018101c448000d1005d14114071805842036078a1350041405649041e140c0209a0382c220520450b4420460303450381c8401160a020340501900704500c1440d03009000508444038010524030000451007803035030f04a80d01034440d6114442c000c0040b0b840546116020205a400941540c4101003e20491500780d0094080d040003800034100c0300c01402109280031010350b04d26421001c9444083c003809520131012004109900f00784270340d085881540f086500c0c504405086066480c2a02c082c04001401180d03800a03910000b40074143d11006915100c4040f4130880e6015802c0005c00e400c6424104501450900c1520184c2102540b65092101078a14500c0ca282d040c0607081d20055200c14808141f4041d02254032090012420040054200c90040e08915040034249041003a00c4800001300c0c0c0603a4008480400ca40c410307400400d50314a05e2200 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 754262940 1250 754261690 754261693
    0xb071b080f030f0c0703020c040f11120403081305062d1e01060c08032406040303030e01112704090b0702101a010207030b0c070b04051b011e0c060e 65
    0x18914201d018440146014006010745107034541c582c400d12040134403820b503000b00988c1144540e040540341950050300069801c0d100030500758001481803e0703079842148000c2c414926601484103169001810560106600703015002e6100d0b9601e4031f640d04c2c40000c2c030a0f101c11000f6410300c04045c0400c8528100c503146030b00c41e8012428109003204070480b02c0b01900b104c10200b1400003840c00d1041d1090134059410001340f51542d1505e00c000401516500011b0181900f44d00455110f13482d0440200015402543d0006040e41c900d4400ca094407031011149140740d0b0f00344a400c41c50003840c038030950b80075088444049154880404500980310011000d03183e510010700700030120f070f0049425030303d10001e60000c2080201d407900c1c007240400c18140d4036005901c041018000111000700c50358204d400c012100b801c2c00901d5641c41c020400841e002c556680018482d00c0414400702c00300101c4481c2424000c0880c8500302c0c800c4080d01a000500d010400c0b00d20f003079410b018640c0d001d110300004000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 754264190 1250 754262940 754262947
    0x7051c0204080f060a050702060601050a080a060b0f124203030304110102060610020c0609030f0d030b010909020901050706020906070c0f05031002130b0f130906031401090b071b08 79
    0x40125484900417034480004500b03150000300c200b4030110b5000d105a905031a424141610314000301c8038444000c1550032010307600c8601003840b50030500504a040c41c4118086d54030000d44049000e0518007400f481c105800318100d0300300ca44611001c803808a03404264a0f95015605480750101e80d010070b101c980c041c040003040c00f080c04134281c0703030305c3c02e040007a000c40f01140c9418040c4070702c030102c5244103401a044003501c0886d44c03910758010712542c4401411605020030842c801030804002e402d00320040b03036440440020658000d030b41d541c010003620030b003107041152240c0040c3c0703c0d1107079150040080340e0000e0010300c00d9a540c1c050320704054100d00c00c102d80360744403c511881c1c0906030040c0c5101c0d00c0307a00d03c4c840d8100400d00071600d5004412800070307862458040485642c0d0005041e1540320f080c18050201e04e142c412000e60b008041d08070001c40d809180d424400761800c90700c214034907141d0410b22208007103080c540c402504500f2902d070801503241808007480b2243c058040040280382c002 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 754265440 1250 754264190 754264213
    0x120e060c3c0d0e030c0f12150c03091905100c120504050607030e01020c121605030f0a090f0509180106121110090806070c080409091202070e07051c020408 68
    0x34a00c0c0458000f61104050318030010205541e510840e002154010603070000d100e951308008007589a0044280200c0715410030000c001d1082400499041700d40c040084108120b2032400c000306d80340b000e5060519000c08038952220342c0ca488400c1c0c2080895901d855800d02418442c4c0d07100c4220325004c145c2085982450324090362208429940303900040e0a120040801c040103101726092208000c004103a881411203001da16034000d140982e921000301c0d008140812014802804220040103940c0c0d039071100e45502401c0d58074030342c004031202c401605083c402500c90080c03032900124040445010340400006c0a0b0140c0040e4001d0544801a84110740c2040911800840c200100b10780d00c0c42c46d040c0d0301a00715070451580c86404ca036544000c000c0b401e060f001c1c00050301c0c8a4081c181c103601e410340350382840094441c118001c450740300031059922406039051010030f028006044e0420070508001c0c0c0d00405078083e41d0740b0380c24064a420b00e81101811540e0444000745001011b40e528141030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 754266690 1250 754265440 754265443
    0x70c140109060515062b0501150f0c0308071107150c020f0904080301151e08010518010b0a030e010f0f1d010204150c02010e0d120e060c3c 61
    0x1c140c0c049641a0902020500d944c4c01051161010782025000e182000d80c1c40e40100c2180c4002401d40000340189a100c8141d14101c0c0076060107000c80e198002200141004024142c1011a52a004000d10200f44100083d804003009400034102e107496490004050001801d00c0700790f0344802c05035440c1010f00c969407608036041b44041402101d00020360604881801000d074408c940003010b2502c2040144131000300700154200c00383d03c0b45090b000c14000012608074000d04c120b00c0d00003048102c801008586000c6000350f1a100d03a1240348142549842040240340c003c0a5040040c5030319981290400e110035800000d40f056260000d000d40141101030500810707904d541050f04c2c1c1c0070f2210010158105000b181c0c01c5a4120100300348603a01400304445901004a00f2030400c0894141a40190754040704404072a0141003800d0b042c01d070446c03024051028004805004600078030a0103400c0c00c0200ba0562030620819a1401c0c130000200311400b080e49080d580a100c2c0446c40444c01041c80 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 754267940 1250 754266690 754266701
    0x130603060c02070605090d03050f0f0301032d050706050f0c01060b030601020c010207061b060b041a030c0d0f060905010b030607030204030b0c030f1503011b0302070605010b0403050312070c1401 85
    0x41d03001d5a943c903446000803151446000030450700140b07810040800684103400070805035030164011400c10708103805456256000703a2058510000e9000c81504c00c00c80c0428000392604040b03403196903442140c1d28a504c13041103108207401e10201084c0d41040e60205000c90300040c030240000c224181e1283c04d00c0600750000c0c0c4025005125620107500554000101d94050b00c10b075444064503100130910803114112003910407900c20303489101d070425580722800381217000e60710800807030040c590388028140341599032450144505004100348000c94422202151072642000b0041510a080e0401d2030140040001c02501803080b9000c1095071680b42c3d01070002c0c0c80c41004441650340701c4e41d0400b00c0078001540d00b91040e40e00c020104440842c4100c8220005101800205001c0350440c495951945901d2441c1c000c2500058100100449886201c4c0500310004010b4200707415501d580d9540c1c002c42d484a40c42225100c0810305090081201d03900a991001c501e901c2080702c008242d02811 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 754269190 1250 754267940 754267961
    0x1e0f03030a0c0519030503010b0906041a0a0e031b210a030512100e060f030f2a04021216020a02060301090603030305060306090c040902010e040906020909240f13060306 74
    0x984000800e81518208006900c4c0d030305540c40b5400c2d0f908288400e51141d1001c01450340c410340030000054a03026104101102c0402c00c00c0710f6480340303c1c075140600118510850103119402603080c8500b03040c200140c0e094000015a034005040440414202056000e409a80880d1252969100c20075501600038449615010081c9042e03031911201c802c803140e0540111000c0c446104001011420044c6040b50903031001412039040304281c0115a00300142c20304100c40c600342504040300c6002d024800d0031060303403041d06d0840c9006004801d200104001800b4683d45044501000d0b050394420061305060030380080002c3d989582d5084030000400003844110040390910001440c41c1c500401c0051044d0402c40c040c1020a490004200c01845000c0080341844205040321420b43c41d68401d0300742c60b501ca410f0043e6582c107084204518000700608580090221040300d80c000342301000310003c5403900340c9010200d4184500090b6401846100c0d014042c1c0c80d08000005100c06500080c0d5a00f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 754270440 1250 754269190 754269193
    0x62104021002010504110d0f0606060e030f0708062a0a0c0210021c0807030e0102130e1b0d090204110a0314010506040302090103080904021b07080d0504051e0f03030a0c05 75
    0x5481c090810b0342610021100903041c1c105060386020039040c40380040302542d203d0204c0d900702044c1c0d580c0d08011101642c00800c0010035034107004803903007010003603062041e418000034910302d450041020354960b0300525015005034040314107420324030f001c00f0310a103803090114100c1e190800108010300a03821020283e1244c40701c110101c20391030011400d06c00d1201201384844c41c000b90101c2c1603488242c0a0241d004040d175582e02188001020310180c0210142c141c1c0a1251a10300211400f070444040d011129801550b15102c0011602408407000e018040c0e401007100d910307900001307000b0a150600710080c502c0000d0303403000d4140d2580c000c040d02c0078035002050160340c17070340c0c03d122150144c0d00009402203c2d0600600100d43c81101601c03100b803000b000541b81241c0324903000d030201c506189001160780245d10900001c18248001400e1040c98a040c6061034a0100091006d80600c6441a807034408400c540c075203600e500707101070302c41e29029085960b07036031451304011305a5010341d00580c0d09 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 754271690 1250 754270440 754270459
    0x324040b030d030c02030c0f0f0d020705100f0e09010e040c0b03060f06031510110706030209060403020103050604141501090b070c061407020a0b0405030f070f06030b06210402 77
    0xa240030300c19420030020103401003949800c0010142d00410300c1c950904107501c4244a124200c140400070800210b41c00e1025110440f40c2c02000c40c030701200d4102c21010f40d00440014041901d038000061448412880d000c00042600340081c0c400c0d0b2000141e8907041100d0400100703d06006418803406070340f00e88011080c0c40d503280c819841074081075468945c86003100446003a5841d104018580104200c000d520072071102c80009009522002856008683c0440100600034010700002e40100a0b604040d441c2854200015207240f0035808024141070b607800104155403115803240c040d20b0307078405841c0d03514100b1798400b1402c100800b2400380018040e0b0b80100d03054505006640140e076020300c10001413420f100f01035a48a07000301c5070b640010313000c0c0895000342e500c002c2d0702801040c84414456482e414041403600344002e40403414425032202e203040105d0a03000c0d518001f11105440c000803060360303440000d40d13a489440d804ac0d04240e9414210302c0c4641c07100e03101c0c0b400342c2c4c400c4915500c0b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 754272940 1250 754271690 754271761
    0x417030709150906080105130b033a020a06110909010609080f03250525030303180b07050f1b0601050a0509040b010b070f2a0603020f04140a080303 65
    0x2c11140d14003814001840d60401080b407401c3c10034081c42d080b94241d0300800c44500d2741c40800d261084101c8141c1d05465007016030702c0b1101f1150702595441c1c21091041c1c4140b00010000ba65503400620010f00c000e641e4803002014089032001d42e1288180103000d000d0650395018000d149004078040c2102e0b03400b86040c10100d1003400800c5034400c1614446940c600035080b10029924141540c0503206401183c080c807549a55903440a0640540c0d03100c449451030940c2001402c03204081103401015400c0840d54002c10500c802c00c41c4e01005914180b0750b20315141d01d003010140100c4404d80300c81c03102c4640c004009180860441e059540540300040c4042d684e0041101d00503058802500704a0001c0041c4221074001004110482c00755145d140040980c2e0303100303101c1244000d48011110300400c1c0d0ba0160303260240006008022501c0c0950400464401081c2030b80b160344a490001110034174158800c0c1c85011180c0014030910090380d44901d00300d040102c1d81006e0715001c00341d449110740141e6 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 754274190 1250 754272940 754272947
    0x14060d14100e01300f0507030309140a1202040e2509050a18060203091203040f0b0c09010203120603070f0803030108101103010e0a0617151005011403041703070915 72
    0xc1c84c070200d0300680728589421000b500c207880ca000e4000e955484c1440c00d00c4000c10780c1084a1070096102e680d604102c42d02d010345800d551041500c0d45c902c1011446800c000f5202401000342d101a0111000500c038a00c47c80d105243c620740303490001036030021303a00140d442c2d5000e070300420489070284800d00040d0b03107071450f1404543c031385182c01198032009000d41d808154940d000d180e0001100c01103500300c603c104402512600201c0d0100c0c1c204a14001d01d900700100e038240c0a41107042e0024640c03c0680130300001c1c1d06c1c2d00a03400300c0c2988261207000a10183d4081018000038004d507503031403011548501009440c3d47c400d000b100b660740314180c2d100160123a24800c034010b02c403c0d46a400e043d030342001025040102e0140c0b800c80c489494440110f0a100b0400c40d030350070700001c000140802c0c01219000409000018041130511400120070002030340c0001e0440e0a0748050b1440c02d90300e0b550351038864164880f150001c6c1c002d030404810000d00359081881c14003a2043d42c890b00000030890ba0302203 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 754275440 1250 754274190 754274219
    0x301060f180209030a120e19090e010f02030c120c0903071701020912070504060618030303050c1c0c121e0b0102070803031e09060114060d14100e01 65
    0x20348480308039810003854485100c0035511849080c40540707040c2001c00040d26000080105030303080010030f1038516809400c070142a210140039228400802a40c8600310090700303182c46440042c03a1100c1581b41c5050382940710110020001200f1902c0741058140c605c3c2d036803c58040c00304a80d040c0c4010501004194040d076092940080080c070800d070800501c0c295108820341e9a50480d03409001c06241ca507500455941004040001800070518120410041e40d00742e5002d03005000080c100c1e400185101860300050300d800d41000304403501ca04124400502c540074810240c481130151b80c100c901817642010b03070140034a030303103240c415aa03100306403086400078861003114070304000781d1842e504416000740e40c50781c0c414015a1a0f90f50344000382c6003941d100300c85105114407201c0e4038104034a1411010783e048040324004103d0f66040001c0f00c4020b002401c8140e05c607100101b03d000004103550030880740300d81010501180c80c10040301b00d60078810705008110381c564407680089112204007404 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 754276690 1250 754275440 754275449
    0xb090411060a0e0607210905030a261b010501051c021509030f061801021914040906030807120e031b0a080328090e061c060c02010911030106 62
    0x1808900044904101d00380d40852000014859074a000010f41d9076400007030420940140070080d418107280c01083c448a480e07048040920008580610080c0c90000e912101c06030710101505400000c1c40101d900d2003200c010350200d148001901540c0d8024071482d03000a424980000d111590b00d840c100300c030046142c80d60a004014181858025242a949083c05d80d00a4061240b80005460100303041c10420068190507501c40001c0c0140e194003462100311f00f6000b01c0c021810803101c21a502e000600700f034504002c03c24082400e946410a51085500074003420b642080302a990340b80815894104050585614545a11407228980500160074400000401a083d402c0703001803607400350004454000e4100300020030220780c2d02001c20051111522103c440f0311011180300070700c440c032880040380300c041080c0160100180303490088032582012046622603500140ca510b10007012114610240403d801c0c2030a10fa421a010f61045202a0003460700c042401440b90516080c0ca145118 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 754277940 1250 754276690 754276703
    0x3110f06011d06040b100c02033f040906120501290d0f0b280e0303180c041b09050f09040303021c11030f09150a0b010207050a030804090b0904 63
    0x111210b00c02c2c012030440d4031600040c0001100d201880c04111036000c80d50404d00032422036030141003546400c000010000c071101c00706502c0c49404074060500d80e4001c0c00741c1c914022812608400141d5800c06a07000780c41500c00c100714113569205e40d1a5650308451003a0b800e54640051042400c41e0326094030b03081c8100340785410095000d8001d0202000c030059040d10301114691640c40000c20701549140102070006101305003008540200801c14914810001d1140c0390110031140c0c0741002c001d036030b80241c4400c4c448494003501c0c2c1980781011402a03001d0b520034542100200d400300360759008502003420ba540e55101039195030034001d1240d01c41e966a94048194400180064030035001080744802c2d40c3d40800c484110b80d0207070f0003543d00705080c24500c00001300800003103860070069580c0c0301562900a2954100108e205a24000094070300b85180c3e46030460310101780d008105240082601404110055569080202d01500980a4011428100305400201d0f10748220140c1c0a540c1140 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 754279190 1250 754277940 754277969
    0xb0f0402010c142e060608040c05011b06150e0a0e0a06020a0302090901090c02010c0806100c02041b021c0f050a0c11040609020706050a0e03040b0d06080102040303110f0601 76
    0x2200d2440d0307142e00c00f089480d54441d07526003484040c6010b4400184000301c0040d9002a5a81001482502d40940008080021107030422000c56110304041040790300c2824404101d184045e0911a1000901c82c0500001c0c1098420140307282100c0c503440896801140d84a019120111030030242e581c80c40210300960700030b12004000c03600d20707801800c0584980c10014a40090300d008218060402d0b070228408903502c8080c030440907028040c0445c0c58100b4501650103103800c40000d1145051300001d94100034105180c035046455980c01624039805a22007034070340c0404100000e60f582d100c2041c40902400384000700e809980544510407408002d40c80b01810800300180448079502500400c0d41c2ca80801c2c0481200c81e280e901c90000900481c071400345e03540303101d400c1010a6a401914001c40e091900d1900e940000300403044c0c900b138030200c2402541c1d503142c5210103000741c407032500301508951001030000100354201e049140f02014030002e07503030161450900541c641b8001d1144034048a10315 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 754280440 1250 754279190 754279193
    0x7080c07110303130806190209100c0201021e0d1103120f100306050408030604180b1603140f0601120b01081803070f112e1b050f06040b0f0402010c 65
    0x40c031228081c41c03010342103e040c078040c00241840c0800550003080c140d0003140a00100000044c40c2400840d4042c00561400e0b80883c0803420a60300090700d034041101080540045a01c02e10400d20704d580c41080d042694458110003907110b5101a0b0000081030b103011009a24610100c15104000c2034401e540c9282d89da6101c01c1c0305040d50091041040c80c414801c0800028210701c20309000f50b0040f0181b6071a131501c0401e000071074a04864100440042480c010000744007004210703031095003103208e0351209403140b000381c001c5c0941c45c4007820301000302800c0242248543d80014483d06d426690303603010800c02488882103425800d900e6000034182d000280c0700070001280c010f207415401c42200d20701a0303d40c60f00d86180100303103003c5031050013029040c07840f1314214103031100d4034031028080c031802d4400304c1c000e400d81454010444140611020517603d1800d02030410103203a038012041c2c0760045074075428203440c0e14084a00312000130b4050041500f446030741c49154811541a1035840d000c0d0000e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 754281690 1250 754280440 754280453
    0x305090307030806120106030c0e0117070b0a0309020901080f12030708060607020d1e03020c061204020d020d0507030b06090f27010609022205040b010909020a0323060907080c07 78
    0x1000c1c2e542003c5e8030900210004001d110fa0b400840c017400201c0308aa040c214104900c06040e4081c420000400c5d1031417942075030105441c001c03201100307082a5108124a0294050041c1240c0a9032240019000107041ca4001c02c8104020070004241d0729640c4d46c469240d4903500064030440000390440300021031500b4188010025207000820000480b40f40f99140002c00c0d1040340c421191229000c42c9004068040059500d50007046031740c24205007060010700d05082e0300810281c4201d4440b0720480075911083c07100c0d810395412506981d111500d9007004902218142ca00c1802000e000000402074500061400c0c020711102900c210614081030301070703d071043c5202a201943d540c1c1d0100081c070303442030b2004000218440c2005060740c0d0203910652904c2c0b42c10ba1040c1c1c0164100070a14400380c3c1e0080408041e51042d01d401603d580040500328010b080040e1817441034109000190380908554055601c9210200c1d070751411030344c940c003040720b0500c01558003071080ca81c240070541c0002c00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 754282940 1250 754281690 754281707
    0x4020705150c0f03041b050105030114061e04060c0c081506040c031b0c020a0905060d020d150c2d02120c0109081b07080a080409270b060f01030509030703 68
    0x100c00e100d400c01c0303650b000f103003040d6100350f400311a1a01054001006030015014107002407109081003411b56140820306108101d054000611030480011540340c816114001550818800340c10f0f291156100d00001d80300c1101c00c40c080c1c0380244d104000244c0004005115031540781c000f880070309076464080034400501001041202410303290040215000c8081c0c556100d1000580da4401150003d07006006000d1443e411440c000d078146010031525813a40c0c0303c2c080c2c180d0f40c184c544c4584030507141804015244a1138980b0341d403c0c01c140801034496401046c0c4002d050051604102182c070515140058011810040000d600003c07845c6880c4440c16000d807540454034000030485668035074800b0351990141034200d6034000d0301800c0502d0400b003040048040c0070b12070020641c40b0388580303421906024510403844100c0c2c8520300f58104a0a041201c1c20810802c6500c4140c040c10340740c04450000111102c030b010304070040700c2c0c200d150311070b000710f5000e00d401360051450304140d924229010700 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 754284190 1250 754282940 754282951
    0x80c0d06111903061706040506010303050f0c030d090c0e0402030c0603060a0302120d030c14031303030f09060b01020606010c020a0317090d030206011509052101180f110402070515 79
    0x2091144201007110184142c40c0d0411581d000034244e07060080b001c4071108140c00901032a80040c0400000800006074281900d406092041c0c640148018043c2c951003503103040d0300980400b080c0810703102e10b00c2d04003980c40c1d0b2291107803869076a21010038040c031420032100a545a0710483d80382c81d29042100c003c43c2c1000001c5e0030504810f8070390b00424a00002e9095144090f8005207280a00c6903161040501035071440c40e040010130100c95040009000203001e40b040303030301002c05a0041602076840710400511418091048520904054005292809429005d0302601000072425807049010301e045544c02005844060300710f40b01c0da250b03100840c0303c07200b620404010010955507007681c0341004038442d134001c01680d818044d10703007104061840002c051240c0d400c0180500c0e55102c25810b0b42c4104880288682624801d505000d03243c2d01c0700080d1005021941d9400380050030824040741806408100b00f29040d03081440101e02c168070002d040741c0c0101d5803150490303100b18542038009 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 754285440 1250 754284190 754284221
    0x70503120703060f0b041d06060f0c1504050a1a100303030e0f011401030606051c0b090c060408031e040311090903090a0b1b0616031104030b01031b080c0d06 69
    0x6441355201e0000c10b00c55082061070034070109040001044024026410102c01c00c83c1310304d241010341c04583c050049054040003500003040e030b00342003203080060400703902d078041c80d00d43d5901b000e0514640711896088161010800d0008203003e0300b4601e080c42d4000c50600b5581c1da001442d42c0c400320000c050181c0640c6076802510701e4107460b41d00c2402815588074052111041715407561030800c0031640c96501c42409410b000100044050080b41940705441c3c01070303240040303030343c40718061070502182c080c641d5441100484c000c1109640000982000086d00c921440b040824980c3d1003840d009906c00201002d030401c43d12945030510071540e607007120006040f070381410700b504001102c2000b1604030031584000400c0e145030702d080030311202002039046000390546080000310900d0510b00c2c0100c001c107140c1c4030f4045600c0d02c01c207601100c00075a04005040204c1d616850041c2c4c1c0f501003020040f0381c80c803c060300070500600c08103141841110080c1500460304495440c40054001081c2e1401c0340c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 754286690 1250 754285440 754285451
    0x23210412023c03030708090708061513020909011e090b062b0203161b0c0302090c04030203010509010603020301590a0318050303030c1b0d02150c070503120703 70
    0xd40e041004d540608103d444410451410040e070034640200e6030700201c05503102c0070a0205414030000c5081c030b0000c082d9458000e040071113404c00064441e1000c1c49030080c02400000070704100c0801c2888045505041c12130246985034100d00c00d5440c09101030b80c0c46081000b03904040140002e05001c2c2401c4001001101603c204083e01283c008540c1c082d214440c10610b92515a80060300d4030140d0740407029240c80d940d09403540b1039141c0107800004d01442810012030f00c00c24807002a10300841e4010004e2040f894142c00b1180a0304035407004901039800e103081c3c80d404404103102503480c0c1e480b07140016410013404482d01c80c880500c0303140c01145110000c5150810550039140210503210708000c0111440b10720b00101141c80d007140444140620681c1803200e0b9401004507500700c550b590240ba100d0706089000c483c1400117900504a5108000b0a61159600850b601c003460312440300f200e031980c1d105c14a0300007034850180002c1080d0020050042103240212143d81c002c800c5190004a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 754287940 1250 754286690 754286803
    0x9060d02190510050a020a021201060f0314300d090b0a0e060c190507061107051501120c2304021813020702012321041202 54
    0x11500703540da403290311007159014203000700e0400044040c0502c9041ca0000d01d014103100703000f0b40301d90702c03620003e00c5103e8018070134400d902c3c02d400070707405080c0321011150180d40d01d207000d070202140440d0030315490141903507021502007400b450100d07103120450324440c040342d5034683c0380d083d6100484111f0400d0769a80c5100108040994041c03203460481800515035503c0002d071460000020b0020201c3c000c1001070a4031071130010000480180c0034100241c40744414644080175046000c840c480a03100403504505002d00001c034004440b044141801c000d03601c0d82d424202080c42d000c0060b2003140b584030f003081019110380d00b00c4110502004003102a026800c009801c1c0da000114105207007800004083c400e01e80002c81000030584110114a010f5135036001070700c1c1441c081135400c2c140340190941002e011801041300e880001003802a95140d1562950256400080c2c07019905110160901c01d661800000c0c05005810040a114010381e01001e8020541d0001031046042c01000380114a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 754289190 1250 754287940 754287949
    0x2e0b0109171513030e0d03120903030f0c09051302040f0b09030f0a060c1106010f093912140f0c090406030605011a0a09050114040503060907091a060909060d02 70
    0x9001d107111070f03000354194005013001405900b1208820b0711480b500ca021000080d04510601c8624603003a801040c101c00d85d090503030003810f030086c0b689405401d000c0e84184c400da101080b00700f510030071030302583d40030f0700f6004481c200d0081e030090392034241520006000b503d122102800303840b00001d084407a500e0414540790305000c2a80c0d0103d56007900e540354241070540200b6440702d10b0290343d006114640c582079072100f0100d81841042006981c0751101c03000484c4488819440d100040030003000540240c0504a1080c43d240c60880007608070a052490440035004904c600150045520181c3e16a0b02812000e24000707007020004440822600e843c50b102c130b01450000b50300840e40043e0315803400030503400c001100490408085410003080d120150040c4c01c1505a5100f8601031102d08110044a520341c8500e0300080d81c94131522080140c0104d0000300c00341510181107090025054074911108040d480200c40d0307501ca0390500c20310445060505040d42c1c8003c0c02440c20503000119000314 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 754290440 1250 754289190 754289233
    0x50607060b030312060f030c090f0406060b0a1205010605210702191118060d1709040516020f300d0e060103050c01230d06082e0b010917 60
    0x3d0104e6001003004228a0314084c90100400154090081002d0b8140048c1c4c503002c0c0100a111644c803d440454203104580d403154015100221b00c040c1da8160b10080500f0186490800119190606001144003845042941c4800d41115040c9a125502c003540340402030300140240c0c00c41c852503c0064103112860f81140c44517001c0c08110940ca10350105105500356002c3d64281100e10800030f100c12030301c0b240074902d80300350841c82c00308505088101c10b19840c402c0062007a40242000c2c1401070302990111540000000f0f9000c5922084151214035180c409000050380c8407030072204140d12051000440d01004c0c2c0c6120f01d580c2c50002c40c00304200c1203a0305c11002100b00d038000f500502c1000020445251401800d003001c1141e0a25100091151465500c0160080138041030700d800e14104c82d001000a00340103820b4515280e0754a07100328900c01c080703880c0034841c5c1e00d070b0403411300000341c52040b98411401030f52420341103801c04603125090281d2140380d56251103206401c5282c0b100540b104c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 754291690 1250 754290440 754290457
    0x293403020a23040e0a0b01140d0912050a08060d030503011a1b0304030b0106081b0c0a02040f240b03060f12030d02120c0a09031506030506011403010e070f050607060b0303 75
    0x7601c41303003007005042601800074a4202e1043c942410070a2580e0407003021842d40d043c0d00b0116030b4401d41b80950350007511004000400300c5e885092288c42031900f050242078441800d03500c03d60160f80d035504000c40c850003003a026003c01d40400050148012402803281055101314802c0d1a0a9842290a048011440007840c564001180500c100110001b00600420951030501c1e01070400404800078104100e01c2032000b0f0000051462401c03d060007165052a0010010030000e43d40f03550384005454940c0c1210b01d0325503407204000b44401c00703503038010981c0c48030800c950540c0d440300300303002d000c0445d24440c41e80525280160707900c42e282003000304030005c03c4210150f12041135100300d228426015000442542082c01000d4849a11290800490340c00407030a10206c02602442401400b85401c060300034082e1600100d2061540ca0003200352040c280c0c000c001c11111088219103441c1e4600480303951460590080155103044130150040034002d100001d101101540000d1031640082c04 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 754292940 1250 754291690 754291757
    0x1c060c1b0c060206070206100e060d14060609131e0309080304060f02060709031509110301060e010e060f09281d010f050c04030b04293403020a 63
    0x1e0502042e80d06010707191704010180001c102c83e041503003400480d110f00d80601540101960f000a040781c0d20005414045908607480b1200d80e85040c10003501c0b01d501702e440e1402406020302240799210030141c907140c1c0981002004d0840300301282c0403541d01c0002c8109030700300002d112020440050a200a02c0145100d4840b441d42ca07000c1107010382000401801c1c0b00a01000000c1003001c1425040d107000d19140c00c1d0310005144640c1d1500e24415100010010f070150301e00b050100780e91074820b080c0c1c1d05880081c00a03c586580d0281000001c0702c12070000740d001107004000c00e5a042c400d03205658904c00483d001d0702c00d8500215104200c0d0384601c0c52046c40d0f0280d003040030059500b84907150700c42d00740360301c1444a0b14140c00f02032130600c91448004c250000900c00174080c02090135101c0410140c40c40d01c1c10342c00f4149105041d00100aa80c01c1d4009034a00c035110340174100350f8202c420b00111059040340d06c2d4181c00019402508200285002e0084040414001c0400344010f049403990416 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 754294190 1250 754292940 754292963
    0x18090c0c06091621080d0b0a050d02060406212c0d0203031b040305070312170402030601061b0b011e080c1c050a080f030a0b1c060c1b 59
    0x1120340d8030340140038058000580000c042945041445000c00054410546990310fa0100c6102403020080b03020001900e4143d020650300311010b0150030468901804952580031b10780c480003000407800455400a5001c0320030802023003058043c2c0c1d1400305600385a01d4900d0b0341c90014514106460381000c841e403420311118212948021802e200c400c002c034002004003025101681d010755a88000342c140100c0c407603410b000d42001460a001c1318040c607440019128059681c0c50007100100361455a64042403141c15070740d0741c456013103050521442e001401840c40b80d19181d400c0e030710744007034081c0c0383c0110419811003004540342440313060080c8114404140039002180040e89074140c00e800981e00c541103860845000d5642513180030341d040884501250400a51901d10f15007001c41100401211010400c0c100c03541e0088003861003520026400c0c4542502c0c10100407000700740c0385030352551506820884002c43c4040c0e02900301403819040440b04070b6641e11150b080070360070b45803c451415090 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 754295440 1250 754294190 754294207
    0x18060f14120a0f1b12110405060f13050f0c0c0606040f02090603090a0201031514100216140a05101718031602030c01090b070b15060a020312070206070e0618090c 71
    0x500138001005050605490700ca240c0d5622101c1910b03a00b520307032199403120046803c640d51b09407640740d454030040c40003214080303500790400981401c484190fa00c0e048a0001039850580404441d050030408000c0c0030f0b40d94964080000500112a4010050384d003403244101c03e8030b42600540c011103090740100103461552000509035640b50031140480f1381c6640b800c119001d007441c0c040d6401c0a046030302d0320600c01007000407403a010011404c020301c00407113100014242c075042d103074078150319082c0c0744201c28a8541051001100c0d03070740901d4002501c3c012074100d244030884d0f00319410410480001c2103411200812501d0b50b04101080c0c418186282c0c44407046240410141c3c405a40c01c0c01c220031190b01c1d221101805020700380c4081c00c443d0f8640c000480410400c0803000c65200700410341910740b40d10f8a0020351f03907006280003143c502c0780400414401400082c80d60711800b5a0ba07141144001c0080034030080780c0010b05d90b401e480c0d040140541c4240da80040b0b151084408450b1640c444e07100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 754296690 1250 754295440 754295483
    0x3120c170d0b220b04020c01021b0708010c080106050306010c050d020c0109120503030105011115040f060c0311090d030e0307060c022e05210118060f14120a0f 70
    0x4180d00d141c03041c030800e144980522500c0680f103540304440500000c95220802c04a0007034811124a03810039440081d0030490325041f081819503032030919040715812030f1143c090703a080f074080c2c0e10b41c00701062040c0c2c0104401c81c49130703000303560041041c03500a401035026a1110300e407560001d030110142e0403088d8110b000d540d00c400010b00400300800034016000c5c058580c07603103d10040c0562410800d408401a4412404114400d800842241082c6183c5498104800340b07144d048406c903909420850540c81c814030034040c1d08100c0009061540c5015610380410181002e0303900100d003440510552070a03203035001d0000d01e00800e1242c8804d0712041461040115864442001d03042003210060b202d11118101480100000100c3c00d00341d944010b80580303803076070340842050783e6a2682004004164081450070015030b40c40c203100240701603a203d4030b00c1d05440d8164060511120840340a48000d480c0c40320034018201c207004240e404545060f00c4459a003941420b0580f0044220588007103800741 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 754297940 1250 754296690 754296701
    0x9050d020f090103060b10093f1a0c030403021c030f060b030103030212040e0112060908072015070b1008060a060510080103030503180f0d1805060408030403120c170d 73
    0x1403a123003c543c1c1c181040d0841d80f248c21120403501802d80c101200e01c501c1c02c404949014001141c61000000d02680d1501d60411544000e500300c0e4015840c02003020503040805581c080c5526030058034504448c1c101c41d03400d45107061a030b40304064640701c20b40b403801e140c1d1140740081c0c42c642c11056900d604504010b450692a00e1307020403580b504000801240b10850000b50542d01c601c4010ba00129080c240100039089c130034809003601200060742802c012450784c0d000c001512404072052041500002c02600090914806144035010049240020364141105078020040d110307242985031942e02007454140104e80c0c41c01d956030303110803e20082c80e081045800503030b95880c04103007030b41c115076000306640405055100340b0904403101ca000506c0034007641800b50ba01004079600c2c07100940b401812085402e07008a94003821400100e07440c10480200c13000e4a9034480154a171030f113503030b82d10300c80a00e10b01082c800b0460346842100c0080c0210700710000704095004196141c10103001003004480 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 754299190 1250 754297940 754297969
    0x604110c0c150a050301210c09140f010609060e12121237140a0605091e0402011107030b0a0e06090a230c0a0e0f0c0a09050d020f090103060b 62
    0x15060043d9485070750f02c2011a41522410b207601480a243d030505062055503030800200750325070040000c12041e02d29844807036541003000134030100340c039182e14151340d0038020b0003564006800114140710041c01114903004c4040c010b4441520003404421450038158000c00d4500050800a4030320f03d80311400481e07a8100d110b2400d5013440181c02014a405c170045c00d941031050b000c000c10029a40c0002c1e030b0046d909211a129a07124514101000714018501c1d030051a00c02c1c3d5245020661075030b4002000c5601c0c80c01e5130070401003a201c0d9001940d5411002e4861782091181c00070100005610944240c080c4e410a80046030000c40e445007030307003040c00040202c440c030b81c008103400e0f0110781c10803030101c07521703c41459010258030380440a60404145108280d004191044c0025103120040d40343c0c1e00c00c40d11403610b10315903152000c20651510400c880c07000000c60074102400746203498003107034840902c002c1007030040521040210310b85d032400741d009403003490703071003c4100c0a82094041c0e076502c0b2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 754300440 1250 754299190 754299229
    0xf0105070c06110d0921051c0809070806090a020f0a2c010617010e1b03041103061308040e0a0207061401080606010e2116030501090204061202090a050604110c0c 71
    0x81c1d00b00100c41e00724480404281c1601c628800c641b0043c400300348011f85502c0c070150340490341000c0181c4003070300d01c01041d54500840e20504000140800f4003050040c0981c0000014242c441841d408010f00daa49810305607a001c0000080007818605042a0f0502540c3c4a0780c4030003030840c00c1e0710000c0f003620142d1013401030051142c0072904150751108900c0c151404000003901e2521022186054072400260312000003000000344800e01503000039088201e5000c4007201e1080e41c60441120540e0030320100241000402d20040c483d82007400b8903240d109034894030060500f4126107410060311408242084c1081c0d615005000946080c170240f40c0c040d00030b081003401800c2d110007003019120403101d1a034522140c070850102c0c125050104501c000724200d508851680c407401c01d03034000d2002d070400b00d201c1ca01d000780018041954414261304180c0042210b85680e5840514401608008000c2c81d402951102d507821201c04007030290405102d410018000850300d8418400c0740490050b1070b8591 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 754301690 1250 754300440 754300457
    0x1103190b040501080307022e020304090501140603040f02040b040903054914090d12050423100204260102030c0316022a09061e0f0105070c06110d 64
    0x81c0715000049403461b541c1542c030a11002040c070003c04403003800300d0301c4c050101c00c501410396185500001500a0b5041600100700d0f0303980c0c0c2c08104032810598040c4a0304842305100003404503d40243c588071942c00900301042c0444840c0c0090203c400b1410100e011880114040768407165403c840311800341044c54040d036400402800c4a900b02420a036480301c0c800c24038030340488403247e80004814000c00925801241451a00a51030309008e06e80b001c00104140c1e002c0c40d8203909400b070103000e1504054901c02d514800364000100064031002140680704101442d0a225002d10040006081160101c104140d44010442441c03410000615150380103100f407060188840c0e04a030742290340d49000300054010f1030b00c02c1c0d003452683d40d02c3d101d50a040003203030a48561750b440c4144298008481d0841c196880b1030030007594a2a200c80d103050210b481244101d68244100c06401105050500c20b0621813542d484900d05800d40e0041c0b400626181860715401e417040140300c20700308050030404e26 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 754302940 1250 754301690 754301699
    0x609150509060d050a05010515120a0f0206030c19030e01060b031b0a0903120302030a0e06130323071103011515050a030906090609050f2e1103190b040501 68
    0x80c81ca80280510f0721502604800d403041100400c102c070b0000e540403000344907a2412801c14610000c10707401d00d40c010a0244440411024041907045140703038400130401c41c0b0b01c003079024000ca903040182407047c850410419494400104105182e0403075255a0104d000d4240214003402d641d0a58001400d00c0414400c0c401c00d82c0000d441e40039144070108d044e507100c405610007218000001d50024107964000000c6403865980343c2c004520500d00b4020a03c407074500708560941c1e4034002c440780c035841c000202c004000244140e818007032920000dc80b4000c03c0350600301054556000d400211040c8400401c0307440a41020b0003003200514908070740306c45c110715002c040140100741c418908204800040c0d0549124041d50080c03895941240c420000c5442070320301107008012114013998144102c86030250030550002d40c5411449056110306140c94070030f64042d00070b5241240912501c0d0f20750108040d1f1884080141d0311640108500d0361601510441410031911a84040c60085040800511 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 754304190 1250 754302940 754302949
    0xe01020a05031302030102040519031106090906130e0d11011d07060c03020a0c33090e0405030912060a0b0d120e0109081204140603061c061b0306091505 67
    0x79440280f44030314010ba048107200003402841143c000d10360090014100034840c1790b042e00b003071096a03c90320502002010074010062039010395a600d40d44030705144006001424100414100e2510354a80070810b10110244241018003440320440060014a001941c0c14002d0141d520214924401d0304103140b130140a103901c41640340981301c20f00c414440000704142c0300f0801c90071110741006104032216110414080b03440c440c0340202c440d5014040e20400e01c010b841c40d09640a603030a89411103158a4200d19030407990004000f500e050006022044103900c4004d6000c40b402c0d11380c8082e0285203401070f0084c085440b0142c240c0d000340380001d580d03400103032105000080c2c20a036040845074181004012100d07180c080e00b200201e4006e2917281300540318144068000e031003602006443c4507801c6400d200c8207000454206500111000c2d03250101600e00400c64801400b60202041421b60b4100b4001101032101221000941e43d141c2080040003920610405031040000b84611614010015 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 754305440 1250 754304190 754304197
    0x50c0d020f010f121a030c01030b0919090f1202150412050c010f110a02010b0414060402030619060206010f0603050403020706030c020a02041a010e030d0f050a09170703060e01020a05 80
    0xc90500c0120510f10300c60fa809004840e40c00c249144052024580d21001004108400030364980a4810460740100c150300a002d80c155606003d8505280ba42c0c5004000450f0740c107018524646a81d9a8408004100041c3d0b45200c800d004103207410003950b10020080c81c0020600355000c003216000103100002d024003024944207401484c0c01500c440c020900f540c010b003141810340110520700041c41d0708040541c0c012b4051000030ba0000c12280d1020010710060314140b42064500e80b1100000807580c0c80c0075405941c0100001e02002d2130f215401444c40c83c558a50342000c1e015902241c010001d40301c0400915025241c545801d116038101a50007039501e4800d0f00440701810f840708021040c10b4801c208005480c0c0d0024070901c10102e81d01c43d440140340e12030841c00c0c0007528801c400340c003a00f4009004104c184841d544d1003030501c07048108540c03d030003040004003080190320000a02d80b10000208038121711240c080d08002d46980381c51070454210b2041c2c1d00250b40103000c0c640c0595040300c01d4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 754306690 1250 754305440 754305469
    0x51510111015050306090706110703050a0b0c070b010e01050307090c0c0b060118030303060f06180308130504060b0c30030c0f0301180b01031a01051b06070c050c0d02 73
    0x2045042e07051155080714100c60300200c1e0188031300d40030848030900014580003101c0c0c040c1c0351031820100284044e41c980126000290440e030140e14102e0025405116440c2d2103210045503600304a5242d030f43d001c25000c2070303211001042d800b41c0180320b44d10701803164000501c0d0500040000051621000d4072521004401a0000c0b65100c00107940364003c1d0141c0610401d44200e000c406030701c1e854041d0041c0064029480d50300080c610100ba054054a403041100c450b4400c0e181c16545541e071340d400c0d00d50003913000440592030640c0c001036541311409044050407101c11405d0305e0344030413608107143c460104810800c540d894041c80c840c00803074900380d4056a0003084c00698907a64004040610311030220305004800c400000000c0c1c5c1d0808018140311088050000d110340c2c011b007401103050f1080c4514418000701d982111009960203400200068108540d07588582d0720601e40303050a2010031101d0720003041c5600d00792400c202c000d0111144440b000c6811a800000c150085407410f160440c4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 754307940 1250 754306690 754306723
    0x71106030a0f020f0703110f0a1515090e0d140405010c052803020706092103110105040c051201020c060c13030f0309030201081623070605151011 64
    0x840d9940744079801a2008003004a0103643e6080702c0b090262035580040c1c0c003a000034070381c1c014400d040b0001056000ca00d1178004028902c3c4086a10760074900c000c468200c2c0e44050781d0384040c040408408a00e40c0c01840202000280705200705025420010101076803c00c120310144500d002c00210320a86060700c0c801c0c60200c014000700c1c40c0c02d62a01184810303005890031707042c06009110140148050946220782d003640c02e156030310f28098400e010203002d090200105490300254a050101c03c1454490007072816010300c04e450600d039821100183c40640d42e00f5500002800f41e4200100c1003030307003095100c008501d4850450b9607161507150144c4200012040020502001880d034032540c0c001c2c640104200c1c041c00d0f003604e0f000e000d940c41391104074040351000d400650440c00c08110381c481071140b5150304c4c0b5025502c8200a070303e0b140c680c4080f110364100788190340203c1c50501c20503100308a800060800c40d1481810071008041d11324000d000c111504802501c50040410030907440c5a00b900c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 754309190 1250 754307940 754307947
    0x3030b010c080705030903070e070e09070903060e0c03160b0403020f0a050a0b0c12090306070e01090f06031d06060105071b030f0807020a0504050c090d05010f0e100c05071106 77
    0x40125100c40c001d44020701505004100c01040c00000300040811200440840342c4599480c685010181d01c05c64044021449142120800307081000b296075001c0d410707180040e5115140d96030a4119804691070015560041c03280d0f00e030a04040249804007004000020035840c5001e0480440b403181e0300000b0b000701014850114992540007514028050003011a15001d0300e0b009040541e8002c0f600e508100d01c14040088214240b00d02194800c0c000074010380880c0d07581440a842d002c90440b000c07810052115000540d900700140c0b440040e0019550100b080b43c0c50700c03100b102180210f002c04095400000c01d2011907a0048211010a0b074852484401d020084c0d10461452003a40d0016003e600d0480c41281000840c80042c0209803007110101e03546a294010f01c030460300215140318425804020102d80d0345402c2d001a01c0540c80380001181c003c110007e46000c1e82c50700070603d00c1a6000f131104c4010411203000d001c0c400601480c10174240940b9480b00161a001804d03050700035038002 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 754310440 1250 754309190 754309211
    0x1b03050906070203120a03150b0901030c0e190302090105030303010f180e0109060f0f06050f011d03010e0c09090303070f0f020c040c09150c0f020405060a0e0a0911120a0303 76
    0x541580c0e8050f400900780c07408044000c42e4030300c042e40305050460010707282911000e00724a0400744501500c01c1d1444c01410510300000542c02040c0c80c4074420140038000302203407403a9440c4101d031060003804000d5000210310790b00c1840540c0320103030405071094106000501120480045540480f06c8050282d0040051286c100006004200300c52a8550802444809208040d04a143c1e415001c0904001841c134100d12101100c0c06405810361001c4020000927156104a0102d000b4429414414005031180700029084a00d0a0326400140d001542110440d1030242600c99201e16420050742c03071032507d000028555800c010209003441510890035000c14401c10003402d040c80040c0003001100c0031070901810310784052043d034040ca0303050112500c415125491030725616a001c54000b1024001d5030070407020b0304004140c140c010750469800110800c400d4903036406501e008000140347c8a1905014110480d21081d032402005095060390a07003c000071224400703501840c0014405180 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 754311690 1250 754310440 754310449
    0x10090807080705060711010c080a020307050c07080d0e010804170a03060e2401020706020615030c031009060c03140622061e0906061b0807080a021b011b030509 70
    0xc0a90103840710a020400304100500000ca00340100300ca0346540100301c2190005900340c0f402e640c800c500046040c004580b0310b1502c0e4003c1c5030080990f06002c0d05001c8148601403800c5003e0348030802c2580080c0702450019000000280b803e9401e00e4202158505a03d0302d081c2c600011000380c40700d09001442080c0988290b04c1032014000c80744803005a400e1907220103021100b29a91521880180c602c002580e40c00040e4034811108990040c01165a0701100410000b000c1141039405000c0c0b25807000a50340d041c07004100a00c8140ba001400d1586d038207041040320103412144080c14a8182502c4c40603640c1c20040703901c00d0381101c210000b92996051440035840c0107580d440309909090000c100c0741c0b02040070045122210042c113500965400440059410f10b00c10513000c06c2501850b824620803002c41e0143c1140600d2013070780b41800d81c0d611401281c3c03012154100581140c0c1003091060f09040e00031541402c02d2030080388081034401c0070122000005401000d00c030002a0300c0f0615100c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 754312940 1250 754311690 754311697
    0x510080402032e1409060106031a121002120f0a051b0309150705091e0a15020a0f0305030f09070819050c030703120206010b070c0504091b090606030c02010509100908 73
    0x1c16400501c00080ba100d0480ca14040544e0700c5c603007070b01a807400440c0c02c600c030344105041c0d00d00e101452031107064a40180100c01060004180f103500031400c4170580c0e502e00307000500c56070481e458085050f2130718041249a06202610710003081e400c08003446440d181004000f040d549000300c5d071070b550751103820341a4a440032104030201818084000c022840c2d42003c0175018a5030b041d81c540c8a0003800c1b400c04003c013508148019882500380400b44030045500d150044400c1e40350049803540206030b00c0d40301e401140508202d00013023001007081461800e0030000d54200c0080c0d802001c1c0310781441425a00c90082c0c0004034081004200d540303041c0802000f02000e20040a810780f1b8107140c41c1d09000c0c91844940106802621681c07000052080c1a40225a00f160f04503d101d08028240000c010203400c8100e42a120350b01c0c0744101203c0451078a00400003040d20010009409180400240a580074441c2040669241034204082810301044070042ca00e05840c00090f024120700e004900d500 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 754314190 1250 754312940 754313023
    0x2030a090b0403080108011107230a0602040b0706060b03041211070b16030809160504110927010503070608041e080c01091b0602030d1d01090c051008040203 69
    0x612400502c001d05410404c500e0613070706040024406240c1c03043d00d699061040c3c850042846080072928a00d1059158040b0003050145007540c90a540c0b913142c007016a04107802500b00c921000500c801002101c1c46820001d01c0c10409903801c500c1d05e030326480d40651203001c5090501c41900807100c0014007c0c410b8001510010090644820b03050030b140e58030f40001c00d41100401c02c48008502c00203800268140000805421200c8a600300402d00002c0c0107480740b000000102804070002a035142840103400003240c45110a00d00e0040030700c0001c14034180d0049019130000001481301070b034852201175025410114608032801c0e006d541c10318003480e4010103030488202049a030407805d0b064004070841e600803420041c01449101e80c0c68a09c40141c4550307405a07100300301354154001c0302e4000c00c3d0840040c034001e00807a003000d03000c5420340d00d4614044070142c0009200b0300c52460191070178601e0b140385107001241441d0550111fa500d01c1c07900d2864003130380070b03500311814040151030300f109070403 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 754315440 1250 754314190 754314203
    0x6040510122004090c020c04050103050d09090516030b03150c1801090510030b1908011508011107201503010513050405060a1a0301020c0d020f011e02030a09 69
    0x119003403000400240060440384416824224494080001449480201e51400c040c0300c0ca040d01d04a4148002c0160341c45100c103600401c103090b425542d6512509000314080c1d800381482c0300c41107034006c0c51405160060512145088140f1009071410f0f20005a00400c0d414005500101c031070000349000e0610101117900100e040410070b4021201c00507080810101c0488030100003080c0056504c039909020702500001e0900038035088910139000340c65803079400f4007214500c0d8050002c440c4100825003106a05a454010001030742019a504900800110b4006c00c600b45c00360080361f14900c203041d00a492071079038020702920405540011000840003c0c8411050305403102e000c0f4254109104003131041590000401c0d401c002030151920441d800790280c00301f50348450540f03008208035a640400e1806403002220551404d100904100b01418002d05104007051002881c1940c02c00301d0840b142d061500700c2d0f981f282104042e4210b0b801c0c070303440540c41e0b64070b48140b81d000308202c84015105 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 754316546 1106 754315440 754315459
    0x2010c0b0402040f1113060c02060f0c15013b160e12030403050607050a2f0a0c0f2108031b030a3c050402060405 50
    0x700c2e20040001424030b84814090048929408000d80c1c10840090244011010111194014080762a140071007102c164046009130040561680003064041101c0d5080c040034862614584410b0700740091560b51000000403030300711f52000c100b450b640d05015840003036030f0000003080d0004030050b0608548840000c0e41e00d14142c01108810400911013400942e0348410007550f240c012080110744580c03d50421505004000d0010000d0050800c01540600d0b0800100d03154500440c4140e07055007080084480803c0003681d035030426004180600d02003000d40d0740031206032015103452130f07042502c4601da210020001c545410301441c0189601d4002007444c00150340c0001c80d0b40c120030313210351025940c1100780c106988403c0f40a4590710b1000e66030680500030034040c074010050030229880e88402039990100340d4160b12605450f400041c1c15510340300c0031100202006095500d1 = true := by decide +kernel

theorem cover : BRFrame.Cov 754136690 754316546 := by
  have h0 := BRFrame.cov_init 754136690
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754136690 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 754136690 ≤ n) (h2 : n < 754316546) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
