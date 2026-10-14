-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0698
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:12:39.598507+00:00
-- url     : https://prove2.me/submissions/91043608-43cb-45b1-867a-cd9c77574ec2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 125359712 ≤ n < 125539568 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 125360962 1250 125359712 125359723
    0x616050a0f1209090e210d020d0c0801080a0302060f100509091615141e0d02030f24010e150a02100c03060b030c0f0403061b02010b0f030c210105011205 67
    0x136400c1c0740c24007507a409100400710f5101c1c2449440f000307203a83c1c00601100454644240c070403c1450a101080d01030103128103500555004c1d1917a15103d1140c0d0b25520030580d5840c03220001001640900b001981c13584040c0540d507008203402c10366405d0b61740c4410019860b83d4080f5514071180e8410032802c402c0d010f000b802100108083c0c03103001201d50b0103580091070840141d0750845442800100021450a038140340e19480c003a1504d025141c08003200940041d6206990f0343c44052030190205030301c000c4034402d0f00030002d440039269200210030001502c03510444440c440c1d01041e84140f24194280e0740008010b0000c281d4041c0100f52502034051086580c1841002c0406190103400d100c1000c1e40c10440360821161540c0e16180c411281800c407a6205503000203020901b80103c203411b110b0503541900c00d80145070024041d400522041c00040640c01608550652211001000740d050104400030030b6030740a4205a000d400421015003510001e81c8501554aa2505a502032201c14020b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 125362212 1250 125360962 125360969
    0x1b0c0924120714030a050d09030302100510090b01021203070201061a1305090a02090301020f03251d01020109050d0206070818060103061e380616050a0f1209 69
    0x40e11501e241460521075600c0075103004030200350a000b4403030703c240c0d90100210b0303644035030100458185e400c88603401800350815200440241c80354852440d0b03409290301a4610030a240700d01110b490b0b20b4402c14101074450b0340c000c40d065008100d003415030b0030b0610005605c0707000e031500080313a640d141c1013504941c0030400c1941580004240101c100443c80c5601160454100700e507141a26111100d42c075000344209006958150310000d2540303040c00e4400042c611904140003550408840500c0203405000644d803498001400c2220f05000845845184c004462062000150502c81582c0e213614122140c2d40020250b4401402c01a02c5c65201400300c8d4400c00d01c00300902c0d800041a8030b50741e82d8106010052075152941c000745045d00c10a0f00740782410164030750600041a25006d2400303c044d0101c104e410080c0b9019903840b080c0d0301d65820440c00c04018007554500401d8186404492180b0305040b20741c1c3c001c0400400100c0c1414058503c00390003014011540715480381e01a042c11fa0951 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 125363462 1250 125362212 125362219
    0x7060305043801060207050103060602010c0f2601030602040302041112010b160813030c0b0705030409090c030b091020090d15020a02031b030f1b0c0924 67
    0x5041000103281c107800c600b0381000800ca01440a440c881007196101d01d00703040c0c00e010202a000010384103a0001d690000c03200c0030f0320304200407522442d0032403ea840702c11101001c1545d6843c41ca2816105506800078400b60071340159468000c6078040c00d0603242039000f901c110f030300401e05000390b181c28410a01c0f5514820a42e900c0d000059000350340d03842052140c06400c407000f05a694000c600f00030703a480c5060b48291010f95468011005003803905c4207000c1540c1c481000700c0c0103d101d04884089031030b03007a040402141030614102a00c40946501c500442d51440ea0080000000700c1004445000f81c1c15200038060709a1001511002c0361621380e000d40a614644a40c0e001e442202c004469001e41c05550307020300002c1d1030900324103484003502404d04d19480050315680b2180e010020f4040e0301c0c0d152407007110407110081d01030303034a000704641d4a903c1502000070342c240c41d08841000351140c10741030030741e40b41d4059600002c1e83c1c131308201d41d81841188807111900316a0001d01e00a0303032507003046 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 125364712 1250 125363462 125363471
    0x30c0905060901080601030326070309050c03011e020d110307020a11030109020f0d2102030403061103060a0b0706060b030a0605030f0f030318010b090a021c11120c070b150102070603 80
    0x6613103d5a200e006200150621003441d4045250b01d0440e510300c5615806428440700b01d051814008004066010341521203005003540d048161806014845240340da14903ca01079001c2c4184d4070009602074012804056600c0702c0010400014502035881820640c000c4c11030704020b0f0800c500c0c59262611018480d03454698410010b0b56208170602c3c607074005035100303a401000c43c03400d22060b8040c0b25007071940009a17107196800380da0000c010410b603403007601c4c1404155215403914000d408240d070003a610608000c402e10070b51018201901c109030003000d000c201e2a40d030f0180c80200354810b64402000c40d80f110001e10aa040030451b4a01400030f00c0010901c103051036123041e4581c0005440d00701b030744241c088174403254031094024001c1d00c1401040d00000d810102c00440007035110515096051000180e5201906100d04c9103240741c4641c1c07450107107442c07100d040d583c141c0b1700010185528500d0a108210220304040031080c030402d840311000300c0030300b640d20000e8904250382c3d01c4a002c05050 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 125365962 1250 125364712 125364719
    0x51b0c090702070f03030e04150e07020f0c1008060105130b090a1e0b0c07050618030115030c0608041721160c061503021005091009030b0411030313030c0905060901 72
    0x2001513000c200d94251814840c3e618580b00090040c1000024810b1514140c10020500751280014140a5205902292a80c00303491329a41e80707515000000c2135011010110b2007100c2c9000d04016030380b003041454550700c1d2280301c640110703504243ea0030004031244d001c00c0d52101c41c14003548100c081c0c4840700c40340d5107100605441078108000350080405e01d08010415040014082280c00050200148081e880f440c0303043c0300c410300589485c85140b1035800d203641c059420300558400b40170b40b03400510400c5200d0a0160503103174000b01400880e0414006004a03001410f0b0101070680342d4000d0300e8001c0c0705103c000415499040140036a071988000c00400411660010b040f1520940d10400100d41c9804100f032200c0c100b10150301c082c3d0443e4200c195140010391110050044e02c10850740c1001c0e10348003407011618410b9500005200e108180702103408601c041c0000c10446000904480c5800b1002d00c0d02e0f503520407a94011161309130152420b1201c019030f4081d06501202c2610140c6843d8075 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 125367212 1250 125365962 125365979
    0x61b1902191809210c060f0e0706050f040302090403020604030f03060810090c0801140f010906060e01110c0a18060801050c0406080a0207020402030f0f07110319051b0c09070207 78
    0x18003448000c0403c2d0360704248010444c01810142540480c60700034641071103180e002400306480b0340012100540340092400701421385104440d46828008000c04406041400a45695210382c11440094005010003c01139980000c0702d842039100c0e0780540240d0405103030281100700140c094405250a1090500040c2c00000c3c950941c1c0342d401101281c403401500b8602c0211140e90409201c1d07500b01584c070401d040e004140d06015001460f10080260783c0c640d000d81c1190350034040c00c2c001640e074054081803076100d41c15800c032809464081d660724650501c0018140081035200381401c210310607841d00b0304016446014010b00560000f440b9518040611043ca071107203003d01340505c04428049910080941e05403903081d580034004555906100340d03140c5400004940c21800341c06507100141505115900e1403500405030401942003072001c1c401d008810425900c2601000028410b00b240c03080c040f1104110610050702a103480c0700d21406000e82c1c240001c0240c2d00791b40c00401d04001000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 125368462 1250 125367212 125367239
    0x604050f16050d060605190503060a03020906180403080a1d0303010302040e0304080a2102010b010905040209031f0504050606010f050708030705090d0507060801091a061b190219 78
    0x54805451400d1210350140c84501aa8108443c0c00e0324101000c0f5256801c60018107034962000c20004650040c0c1c00122464401242c1040d046903402c0c400f000103080009200307401038001800d40381d1000c3d040000c2d01d42203d08460980c001000c5506016810040e44902c0402c10b24003424030fa00590403080c00b580d20321040c8802401030340c1d2030700d40e0401c4c030205000b600c02034444282910315a00c2c0c0790600e40710007004281640b81040e00800345943d40c5d030052058100300e01c0183c50b4034081500d0300c42040002e41001300c09613018094500010140c140e80041809020240c2e03200040500b440d0921900c0c03c1001480c01d03041c4049004036000407a086070544941d20360082030740e6623a50343c2d6001254030340104041250002c0301030100070100f200111301c40c003c0c0c0d452661000500da0f038409581090390200c03180c083e100603003083c002540d0b0900100400030303401d106151225a00c007a110302c624044c0d0040341348041340e00d944502c1085240100c000500c41c24454003001d0b000c0e041902260005 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 125369712 1250 125368462 125368471
    0x60806060f0714070e07020706020d03021c0f061508010305060c0903060414072106050901051005040207060b06120108010e0d0e01110a060501090c02060a06060c120e04020a0c02090604050f 83
    0x1000f60b100c0c84402c00c0820181019003031000000440d0304090101030f6840b4850301804025000e109a14000603119100341c540015820074200304015503141c9513001000080103c80e403c0fa01c43c0404209400f64104e8064507840b01d503200000d035071450924508025003d0660b00740d50f17401700440c00c01c9550000d4280d400c82d41159280c00d919042c18421450402141d0003010356480b150740d201c11103003105440c021020302507071048c40156507200c040e0742220411200b82041113034444003400036081075805042014400c190026605901000040f4690440207503003804020600041c409400c083c003441d9654692000100160749401d4030280c03508e416401e9407810800581e191000f641c00401a00e44100e40109003042696100c0c840080604121030000e805071107540082440c54113548180ca0464031103680d40c0340c510303404d80d5a51420b007230942100810804000c200c00c400380d580d4801061141000d0700d400405280740e10600200400040915100f546400100410101c041030500e600 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 125370962 1250 125369712 125369723
    0xc04050109081c12090f0303090b070306030503030115030e01021303050f0c0603130503270103150b1209030c0f28050a02040b180a0507080c0301080d08040c0503060907060806060f07 80
    0x81a4403010b068000b017502407406407800740501284810702da0950f01c079080440c000c40820081d55a41c00c015000d4070300e90306c4018059803082004000d020a000d00c0003181c10010b240119000d9405100182a43c0051200c4e5510035620801081000010000088014a10406000c19180181c00111a400300600f600300c1011540504c104111007441107800e510144054482c0c2c0d44440103504d0ba4250211a52901107440c0800044109054030785000032140c40925140c031b01040243c148200c81c82c00344c0403a4213884148038407800700d0402d01141d010f0640703060081c00355000c00c484e45c1084000002400309a144000c2000300800c10124101d00ca9a805650114010103180c02154600c02038003050401c2031448003e010700d9400d5904054040c071240e035101043c68a1f811855402c610007845510b1007036020800040b409400b5010303003075205000e211001c81c40f654a101081c200300c0101c0743c40304103070400d0006104107500300340100d402001c03d4880c6400d2a03044440b8110303d00c2039207000f401 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 125372212 1250 125370962 125370977
    0x603070815060103092d0c320a0509010305010504051209100305280203060306070e091803040f0306050702070602010e0d1805060708040e070f08040f0201110102030c04050109081c 79
    0x14040545a54804030036009406c0c18440060901800c0c80200d128045410311200f010016010b1542e00441000b0715443d02d00315440740c0c3c00400180104081e041e4141c1000c07070040c0c0001c0c44ea40b040743d100c0c000c43c001c42c0041038500d414540b581c2485542c0341c0c039841303182081c0212030075912407400342481820f4a08000446458802c0c101c0021613609200c00c644503280042c0500c079280c190083c60042d017041e4211001502d44000c151180c00c4a964026003050300240060380107848a224070024220030010750307107441c2c1c4541101090988540043c1c81d036580312800e0004156040240c940109100d10080008006504440341c0354680010202d0422540084807080a002c496080001300401042d083e0303070304800d10700b9842c40d412038031039544d84040c1c04d00000e9100b07004600021700e0701344651701d0300440e981c0c2da50b5907504584012402d074100041448030702c6556000348021405510307415150390300c50b0710307040004041d024190451055900110080580980e00b072140c1c46400d006824483d2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 125373462 1250 125372212 125372231
    0x1060c060504051f020a0909110f03040f05120702030606010e0303030c0c01060518010e130b06040c02010207060624050f19050c15040b010806090606040b010e0411030603070815060103 81
    0x514240022100c4c0d1144882c44c2e4440160f103005a00400d15240c917520b4184005984045110454038030b0884450500d00c10440380104024070f5005581c041d11a20a5a0540310350741c49440c40c000090b003600f240207000041400a40c0f60402806030b201009184c0040910302e40408079890340006840000070800104804402c22801c0d000b000103400050440700300c1154400f10189c00300070030710840c1e900741101070114810f03200100f40d02e40a5900825100d80e0ba071180420322009024201241d001c655080c401d500005160f40940d80003070000742c1c406000461000ca0300e217046c07002c1c4c0b00721200f48241000025204542c000581d84510500012100f81080300a001d13200e40c8204185111a4042c484841012190203002140164011035132840340e41c2c5c846044a81c0c0d00010b8a00043d9617011100040321032030160400d1040c0c3e101854030040c2d6044000109050381c50013004111444004410401941020801d00005014010041034080e21600003000903000180c0481d0426031030300c1c03040 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 125374712 1250 125373462 125373473
    0x90216080a03110c0106060906091d13020402030f0603010606050a0e0d080f070803090c040606020c150f042306071e030201020f03090a1a0910020d060f060c03120501060c060504 78
    0x1a2012400841c3c00d5950700005680314000c01039401041c001c1a4402d9020070a1445518001c0644400e141c00240114841258088040e0020304580110b04204511001070710303140042c5010f10b01020416509040030741c00c15003135074050741241d41004014440c501015900c0400301008103002c1d659240300450078105040a07214003020312a002c800080c1200802c4190320013184550720080c2070300c0040007101c041006031540c40c418280103a002c802145224034094000540d0302905a0301c443c81c0042480c151205600710398400c0c0b200f2405c00140a01410074648094003081080781c02526010080d6503d844082e09181c002420041040c08a410907000758126489100c081001030b441e8075085051564a4040440488040c160484180046548188128012a440b201134000b90138581c400d035009400c5031484940260311168001100c01c858001032014102c950346425120034036040240019850480c0b2080480c07030030f0010450258031494400600c0d51040000c90b003900c1d5030420 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 125375962 1250 125374712 125374721
    0xd2d020309010f0203041a01080307020a0e060a1a0c16032f03150103030f090f0519050402030403020d090b040302061219060605031006031104030813031203021201090216080a03 78
    0x10f041036a100000b800701340308030501500465062100c80c00b00c1c580c0c079091080e8485c001c00c5030003500481c020a0034442c0303204e8900c0c02a4041d4019010f1035043e0360b51318003900980381200e035144e800900000d1034000c140342445554600b010039101c0c0201c0c14610b43d1425100841d44054a030301002d404c0b0a01c0c2440744c500c034410f1079480d000702111003848003007081d8941c0f201c0078441240032407948070388481e07200d0155a5580407109040d14640c8030030f150009015125000b440d40d04010602000301042d00e80c0c951002e140110b02a50050000c020f2a420203031010545801c408030070342c0309200070401a078801b4100da041400c012031400721a21100c614454a414900c40400ca013814694080340c07840d803101c00303544a4140107241d00306aa69804082c0d00311890b4000031640f071002080700b8804520f16070014109404d07580c0302071100942e00e444640c0c0080790003101c070001030b03000101c20181041035071002c0d000d81500071045141c26143d44501c2000907280303200501480b40460002c1980c0d0103a4023 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 125377212 1250 125375962 125375981
    0x403082b060b180306040b0610090504020c100507020f0705010f0306050907030b040507030c02060c07050f03040807060314090c0f030f1002030a0f09120c0c0902040303050d2d02030901 81
    0x10038041140c50306001c0d01c880e0440703903c41c6034000554080c03116038030300040c0150003260440d140c11015250001403201c050740d03d10f250001d102908000043c140c4403440101340c82d9264202034500d00040030503c10035150007400d0352045610a1603100c5230444c0100f8901c0490324242030060440100030300c00d8001c1c00890f407000e540855003108100718941c054010000f01c0400300d40c104801e030b0350349078141d084465114000e4016886400007404100304000200340360386c042c00480c4c400e103680320034140c80c5500c2038100041d99000403000700000381d0036028030280640e140440c2911881c1c80003010b83d4442c0c4551040b84a038520202409a0341c40c00d00c1420140d10013403060300c440094040e00c0101075417095800080d5a440c000141100360003510840500303582c00990304045640b0300e0307001c450700310140d00141c2d010310040c1310009061901303200070300045101c2d449894440040142c41c500301c614149500004031940c1c0c0d00c04a00074030300100302d00c0065010703000603140c2c2c0f1640111801001c4400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 125378462 1250 125377212 125377297
    0xf03151206020903070905150105090d0503040f080601060201051e0709030204060801091703040b06060d0b0d0b070314010e070302070c050a0303050306120d0807050901020c2d06040308 81
    0x100d840c1842429001030003818002d030100c5121558840600f000c403807040380c0b4440d6420500b81c0f00880c0c0e620600003000b1007a4010a060805006621001d040d83d1041e404002100790185080102c0745040c04020b0040000f0f0008002c02e203440d000070362003d00c100942e9400810300c1e0340001c84440c0545206009190003400810882d500c403d140c40c02080403c200b600c803204072000a40d40d030b07140034048074800c039400808507503262180710501045030403181c0031401c615140c840980c5280c4840311203081c12070041b620300c9200c2c200610f01038101c40482c0446c200440e000750060004880c004111500274249140060b0b56003680e082400342c400c865046a80d004001407000400d1540c004040d50143d901207500941100d000140786580d40d0b0015000f4002c104604001010b290003200503241e034040c1070061b2054a01d802d4005503017018035017507285240e25802088080520042401088003c0c15a0424900760868032000c1090045045010b40798000104810b00901d610009000007101c80 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 125379712 1250 125378462 125378489
    0x9020a0521120a09050d120804080d0e01091403070c0b03090a0c1418070804032f060a0b10021009050c12030705010c051602090901110c010603140703030f0315 70
    0xc000e0206940306205460001341800c0e0b01140070b10b0402c05d203441d800d61081045020980040b4150f9003408000c02c02d954000081c080c600b40049140190f1501c00c0a8500000d1085150b01d0800070140d001f91003039135580d20502041c03002400d84404581543c51010b4019180d40e1014090be00e00145510000e00344032300701100144408c0840b048400d84602116410340c1c00000c285480c001c018100d81e42000100f688010a010901070b201b010034110740d50b0320110300403882105401c04003425040c01c401d654410010404800d45603c90b2102c0380380c048600d03015141700114000e582d21213210000100654a90030041000010442920064406840c2038100801105201e440e81c1210000b0746003942410001201c2c0d03072041044580120308150603800b840810340900c1343d01280182160055036071456101e118905c40c0c00648180071240780081525405e40c68040101c00c40307440201c60503485010700b800001e4000780e0000121400303280000b04100c0c00400004240c00c0c0354080c0c100d146c0903 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 125380962 1250 125379712 125379733
    0x40203013209030c06010b0d09120f080c130e060f0d0c091a0a0306021c1503061407020a080a030618060611060613020706140112020a080109020a0521 66
    0xc501c54462000ca07801807a162955400242900e92180c03200305141c0c5c4c0c10107030041c8000408400640b617044504c40d00055880626910251a00d140080060120f02c1d034940c1000140c0e404a000d961041c0928101405d06a540403200c0091030740740101c442d90000000010610b8844098810f4859002042808140f12a0a1000840c100c901458003200c1c188100b900141c1000fa191100c291000b40607500600d14580742c144c02908580030a00c51006540c010520b024030b2409052082c026003d009031010740340d0708c0c000007203454108520320008461801c0094580e000308107262041c2d00070040f10b41d14406440c0c00c90082c84681c0200f1040030a24204000404969106209455554079040c0510204058040c0e81e0003048542d258003c2c0740544081c0800c4150700600b8800b0310a1001040d0044a0382003a42084000d0300404240501440d044055140014102c0c008001c0302008003c81070545c1c0114141510600420b40601e0038005044400b42c0c00100423150380c9004820b40c1c10076200c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 125382212 1250 125380962 125381021
    0x60c0d080402090f0103031d010309120206090c0f09060405060d0b0a0f0c020f0c060c0c0a12020f01090f05060901170f04051e031b07080d210b0d020904020301 70
    0xc081d07800307030f0042c1040c1d07000942a1420711840d5043c1c1750151582c404484c00c1408a00d45503002081e1141010340340c41400e0002804e0401004c50a1410340260032145403a8940c03a03c0c01c0342107484140b2900c01c1d028800429218402a00d402c0340301500c020549903542d401040c54a40802001001c401018041100c0150594003d10802001c5001480110400ca004a80d50030704d04891031540e402007a09030403540303407502c02007040c041d280040d90303048080e030301c0040c02d00030741544000800b0352030041000031458001b81400380d0140c00d0800450007410b291010040f144240a0346003d003400151070507135a800b5691103041e4007c80d0000c5099440c0c22281081101025581110a449904080a089540a080c1c10351103070100c0e0055041115000c04824001c07003070546031402d800392403004202c410081c0614604a1040e4070b6042c803130450326a5445914072400c0080001c0c40c42c0007402d080594642030f01d5801c079501100c0c441200d445500000303005003400340c283d0001401c0550301d4070003c207 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 125383462 1250 125382212 125382227
    0x2010207030f1b0e07020d1d0409050a120f0807030e0a0c09020d0501050603010b09060d0902100801141e01030506030c190302010809010504030203031b070609030e030d0f050414060c0d 81
    0x42e4650410500f036a0386250328000302000707464030b00140e000f154221004a104482c01c2c547c00c9480c840e0741d92041d04c001c02003400c03035001140a40e000d800c00c1c805003041c4507100c44104081106486c1c800b12030402008000c0c201103000e80000c0801da22001505040394003000200c21907504004501001581da040c158025406035070080354072420580006154a0400192070484c0c6000340807524100d100801c01074681d01107600120344954842035580542ca07000c04000c02c2a19584405880b9410400d030340c904800803100b1503200d5500000000040034215842c090400d00c2030a000c542605d5400010b0308107039400d5041900140d01c0456030302941915034a0008482c000c0e210003e036500c94410450989100b144c02402503401040404e00c0d58125814000c52150015400c80c00c0c5221551201d00380c0324012000d03000504404020007061400b8040011420900d00304110595000c030b0740a007460003a0b1044001401040d20803100c0c548406040305c0e090010131099402c1002a49006001e69 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 125384712 1250 125383462 125383493
    0xb010b0304030315030201050307030e15010e18010c020d1409031002210f041b0308070c0f0b12041101050706020408030406020d14120a140403031e090305040b0702010207030f 77
    0x2800e001080d16085051135009050783e4069560310710b1a500c030b80c02079014201c065502d6220f849038100004805042c1510315010b40710604803c081420a400c150301c0040d0800c5c04065264035050382031014980001307648240443c1c82c00c0c00060320050305041041d0340284000140c15000300e924007003130900c2d20350040148c82c2902d45440442c0007500024207103403d0469171002c80307202d200007007000300d58020b0403118062030b80328a0740c01c50717501ca5540c0c00481c0c2040348100c60001c890001030103a00c0e1800c2d421005030480c03031425070030107000615400a20801500207040450700300030351a4145d02c40d201f203030b100c207070041004c0d541c4542d070750340c031981d03d07030140c4110303c014000c0340019000944240784c100080c1070040305d41401d00d0110741c09185280c40185c0040c284603514105100a03030020003000c1c0c8114048e1300c00144240750200d5982d46e40c5c6100c4002043c01c0e1a00080000107a0084281c506440500e4003483e22980c4c0c600c01030385441c05079000075001005c0f000000c0100910a03403143e000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 125385962 1250 125384712 125384717
    0x30b04180b071d060405040f021303060920100e1f0503010807050405010b0409051018200306030712051204080303160302070f0605040c03080a020d020c0a050f090705070b010b030403 80
    0x54003c4640040c030301294410000d41c4944204410020782c6007680028002c1411040300500e843c1e012010b48600034078070351046840356120013031f400500c0719003102d00c1c134540d41c00550310380d000c100880080c5200445070b0b81202031110301d50910f0502d4843c40c580c04522908868070ac0b03c0c500704c0c0403014110b50000d20401140e48107100001c18641081d003c1da0303040318511018541490b00700724408001d810000c2c046240b032000c0003c0000c9c605410134640114005c1680004fd42102552a07001c035803d02d040c1c00901c00b1420000c0c041507850028860003202c2d55545e4054201c081e6281841c109400b01004d00e40305140400c000c64641c8001c80114042d5014240218a02001e450b0603400d034006c03101c01900c2d00c16590740748008218645c01035980030f8800c10200c0f6000d5101c0e5140344050300030442c1c4d440180e0103440808445501002801d440b204222a510391842c9801c000803640302c45044901e0050407041d01064029000d0b400b0b5400d02580061404040d40c0c480b945100d541d001103406400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 125387212 1250 125385962 125385977
    0x1606020f06150109050d150501060518010327030320091903170901050c070905090709140c091f02060601080105040c081f03020316052806030b04180b07 67
    0x1203034400b07161103030720001d41030312030000b030f1841c0030204500308500c1c0e00261417140148540041c204698404c2c0c0d40030f01005d8584586a4021412441141501c8580030341810f00e059042a03c03800c441c4107102680c182d0401312100c04419185c110081c0c82080c08a021400b460010150766a83d5240034081701710b42650100300c0484445203040d0352400501c00030f002411980724200e40007000100503c0c40e1441130600c82d2900c04441074881c50300b4101d0303011401403035540d8140b0071a00c0040c04124000c0261810902c047c1c0d6045050071a4254081c100c6039940e100020340da07140f0b0f2111400c010030040546244079900504003800794954200312442c0d80041c2d0b801300045124507180c41030200391042030b900c0c0103280da40c482d8200e13449482d041c80c4d03034111005e8000000c0141e03810002007110f4125800500344082c0780c0341c1480100300400c4100c82003110850034510104004802503401c5548614000c113507540351130701180050483c041c40307800e0076114904402c14400d41002c0c0c24015182e0340d95101 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 125388462 1250 125387212 125387221
    0x302040b030312060d17070c0602010612020310020315091e0c030405030711061c0e0706030b06031603091406040201080919260a0f090603020313141606020f06 70
    0x182c881c411841d00303001102031400407440700d06002041040280c444c41030552074a80303c003180c90700c0e0340003940d04445040000760f040c04510360a0240c1c2004040b0300c40c80300d210b9a0703154002030716880c66070030024210380c2c040700140b4144580f0981c1c5042c2c030406845a0030318141740c9003c2c2c6400c0050081c1e2800f41c208440410030390650b49040300c0c421a0443c4c055800c011041d51a070003505102c0056603406003090010503a031702c03500c460040401030011070019081050007011410f210003544007409040c80c2034208081611910300f00c03540100f003200c500b02c455030220025801060b140802411030400040c005074102400a511070184c0d0003626880c002d0342e9040130706980c0724401405454100031031038024000428020900d51032440341d40c0d400080f03002c01000380c5d505801c00002200000e024009110140c0d400401002c064580c2d850150b20310720f05640e20b8450704641e010024281e01c411007050302407003414080d2014000b00c46070084c90752952010002d40c0c859a881c2003429900035080410b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 125389712 1250 125388462 125388469
    0x3120e0102060c030f060409080a030b0118050105030106050307090305011a1c051002070614091c0f0801050909010b040e010b01120501030209060d050f0106032102030a0804080f12010b040302040b 86
    0x20744990040ba100b41d00c4d55842e036050394884a40a03081e1074110b0b8039071000310005101c01010f004111529940042d4500d031520005140d0101450211803400c3c102c3c005100d01d980c010222415610f00c2d051480e0303252507011003119841c04d2a800039000c2d51824515180714481500307030a05065089505402000b91040b02c0807a084e11000700800b180d01c41100c50104018540103404014010ad01c009001001c2c0e00c0140315450007110b0404540d00002d0100300d10100928081c41d0304100b0f0315110701d41583d803590140c0092018081d4500c00e030740314000907200810035084003664400241003840306d0ba014100380d90190601500d86800f054011740c0c400517042062040701c0c12a50010300780f80241d10340f942404181c0b0309420007581c3d24020110b076210f4440003401100300640c401c0c0c00c5030141c00200d0b45100e02c2c0c0c00c0c2e030070314000441d041040501c10207030744410180c1c1c0013a08201a00c2ea66201c0d041c0c0541e42e8802c14055005915200000190010b8601d025104880c02501c0c14081700f082e00080 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 125390962 1250 125389712 125389723
    0xd141c03020c101a0d0b040512030c040317070203030a0305060307050d050a1104111204120c0b150102010e0f01050411220b04111b0f070f0302010c11090103120e0102 73
    0x10425107a1200f8a04019581180c005002c90b45811001240c84119040860944d04400c001512252000400d00041103001c001c4041c4031001c2025190031401d180381c001800780b090b44409001c400744000340c0c3c0070a410318011156010340c0103007100e0350f4130300d48140540509002c981c000c0c441e000b1900f0001c0c20381040343c08402010741c01001742c01b4080c002d6948214401200a0032900305664903c0c400d800c490100041103542d029a84846035032400b1b1030b0441980000703403030300801c104d144130001d000903170904803da8100c0e40c5030100710f820000c1c900040340140850200f0300c41d07030b2280101c540c03080441948510f0090b4010340c01c201465080342e040c8100030040062440751440d011000b80041d100c0b50b80035011810004101180030f0308042d0000c541074000080c164000c00c51040720390b5101c1410015424002841d801034000c11f481c00404e4514451184000f034184600000300e40704000700b4803084040a00000d001800ca961681011840f00c0101c2e01c1d20b4002ca9a00f8500e03001e117600004c5c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 125392212 1250 125390962 125390977
    0x71101081531060305061009090b010605030405011415090a0606020c0d0503040503010f020a0e240a050c010e0d0206090c0607020f13050c0c07090b1e0d141c0302 71
    0xa400950401400200310020203189002c01c1c6040900501031580c0c0905802540280d0042480e400c1526951110306003d6010441a9181022000010f10605109411940c083c1496030b101e0740e8905000380944443c600300154140c0040c10020203000750035440c8000c00d03040e01d6407800c41c1e4030b11150404a0b10036018035000350b802020a4046898009998214079201d041a01d040940d034001007420740780c103010500078807500840c00c0c5500a80c00600200565801c039042a5000c841c2d03644081d100d0110001150031031380000d0029190307800f840840b1000c800380b10003000f24481480d40a9154a80c59891a006002c0c450118185103000100d4441388440144542d03d8001c960b420820740410007162150812001d5a41c1c041a03d03040c07040e244200100b414865444e002c002d4040e040c140c050b0010440355151030b00340c480c140c850b0400c50041c100d500d442c0e6050300e103107100022405c2200302d000030800d509034008e9103c2d420340801e00c1580a15562200268441030171400c1e0f081c1c0c018141e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 125393462 1250 125392212 125392219
    0x20f0705090403090e10060806010f080411060403080708031602031e030a091202070513091104090f08041202030c040e03031b19030e0601291804020711010815 70
    0x9105000a00c0c11015040e04103200f0f05000b80c4c419034859070340c0051801100c03451400d84000d07000304112600010f44903803000c02460640140c06881502800324000500054003404a0b44400c030400e03102c4004540103180c10a22030754454101d4607200402d5801112080741469804120700201400002510251079120785a502256641500d10000340c1004181d200c800e80c5490f5004045409030020703940d11801c581c003410f80d00b0305041c244149442d091002a0b100c03450306284002151000000308d8200100b20360114980500d41040c500c5103407002c0c03018103106030010340018200150359070084818426800d4131a848024400c102c215001822055091341042000a5480d07411440081e1710300f030074050040c20302544015a00901d661014600040ba0342d8401429140b40d0400c4858010074501103040e1300c039100039038503040c21150b0000303650b4103120101d01d031041100050035518540402420454840710581003182206104d0385c40103011803108400b040d405c080305180240c1580c4041e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 125394712 1250 125393462 125393473
    0x2b180804060302070203010b0a08011d3f0309070306050a090317070903200909030903030406050a0201060801020d0524030c0f12030c0a1a0411120c04060305010203070906020f 77
    0x4000c2c1c01039405820101c0c2d040d540c3c0c20214030140d45030400440035002001c000900c1c1e4202c03030441d04d02d04190b00744e00d400c03e902829280380136580b00311180101d9409a440c5007403e000000c02c8400b101140100e0b611044000301c1004440390001940c60308030303800340c0001e000a40b40c03100c4c1202200e203050005400510b401102c0d403d032155800a443d0811124607010311031030355a231240141078502c04400f591100600400707210f180b0700300710400d8202c1d50000c0a9031400c07401a00080d83c0344034a00c910070510801040c902407050003907220304000c200440c0255a101ca0b240d01510003094100e51405071082c2c010803d0500b079094298070181514003900400c1d003540c1070300070002441d5801c05072540c40b055010406036254014800703455201c80140c014a0040080d1a00080c0c8440c410741c5281503c1000d0100404200740c504c481d000d039003054500c20f641952102005042441d0302d90ad0035003003814140008204507055000f140b10b0940c5035500a0105c0d20f0310300490b01c0d081021010000c4d075000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 125395962 1250 125394712 125394719
    0xc10030207050601060c02010e03010e100f02120105090414010c03020901030608010b0a0932090c01110c010513120510110423040902030609060708070504030203061b2b180804 77
    0x180d0840c0c6c48581c014100b8040300c00708540020709582d0084803030a810703004a102400aa08a8007840c0e400c180d40c1203080d41804ea40503119505003030144902ca20901d00701010405212900c113149418400c541c00130b0200048452000e0040d6200b2080c0ca070011389030440c001541241881440d01c8010f00400341e40025241041000180451700c0a0b607000351800d03a000000000041c0305820450a00d0010511619000c0d140c582019280e443c00790512031003c983c0c108240b400700e039000b02001e003402c3c02501d4183c48020f0020b0b1f40c181390046030246007100501003d1040c0011100f0888038a00428400c00c52001c100d007020740598819902c2c1c400030b2510310ba40d204500d6004050103800a00009545040750300040e00d401c2c410345034022a504600240f1004c45c1d8080c20b025400040c50922a19040c84c45e404680e640030011f02480c4c40e0013064a00e03000030041a402c03105130040000c04d004061404032a1200b5020244005003407440ca0072400844800c0d9400f2001e04964002d46203a041624 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 125397212 1250 125395962 125395967
    0x30801091b0305091002180411070305032e03050319050a0c03051810050c0105010506070f14070803030a1d07080a030c05010609050408030402030c1807031e09050c1003020705060106 80
    0x140900401c80c1405992880500c1701710368405001c80300d58100002c2001641a014482161041a02940b0009080000700302080d0004100c030f0b000044440d940e180181401031400440e00d103a1034002001344044400424000d001001d01501d403041c1081068048442c0c10998907440f55008840100720f65138440c002181c042d1014245012801c50342c030600c000808000b42410701c0d0324040801080c2c0c08120101c03604424410340c0e014040607200545010300c552548a8004e618100003040003881075240d006181c1c081c410305004002d07060403a5220b0074040b6420001c0e00d002d18849003c2041c051896900540014201c02140d03008006440440d07410340b03085480840e03000081d28559282c03100041e048691384200c52040b405819200d4890400b84100750034a0685000c0c80d05c22050700c510480400010b210040d00040241000681000c600351040003500d10a01f081e0003041c909207144050080c086000c42030000b00300c0380c0b2006200f043c0025401c900075050301820590280c0018042c250 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 125398462 1250 125397212 125397221
    0x90d0e090601140d020f030711010203010b090d05100f0e010e01050c0409020309030c0601030501060e0703020703081807080118050705030a03050f09011b0f06061409040f020d02030a030c030801091b03 88
    0xc0200f04903242031041c3e500c01060f80c0c80740e540c000c0031000000c20000400ea11007503011448100740001e6140d5450204d4080c07550180e86602845042002c08150401804000b006500341520380c042c03040f03841d4105044010540c2006481c020750030b101e00090712a03810300c1194440d040607014107080600740071504000b908010500d0000b44400c1182240180382000110700075031062001180304c41c01c000311b03508031a5000d0b0082d42418014004540007a4000409036804001d86840c0c030101d1640310543c3e4a0102540e000c1500d035482c01c0c40c8159004030310380c41400074030302039070494200307943c0ea40034580d071999401009030009000740310443d1284048001460702100524002c00c26090308001181045010790080711615040c20503e404c0180c5405000700424584201180008014022400d6020020001860250820407910840d41e401c032510b120703079030003600710f0300703c10785d50303c2d01030115180b0381030682c0421011400011000c0060090b425280c0c0354250307800545110f010198080d2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 125399712 1250 125398462 125398487
    0x60f07030c0b0f100605040e0415110a0507050c010c020d08030604110c01020d0e010c0e0d05030f0313141b09150306100e01080307021507030c06060e090d0e090601 72
    0x210718501080c000c9a10114803601800d0391a41c03200850501e418401c0f80380e54150f104d042800002c1c00304000e1400c0d41c0740c4680e88113406c0f41c508070008400601c40c0c0b00610009a001030500004269480b960b81d0040c05400d40c54030138401c0300d415003409801940c07072405582000750f010882040c00c1000070020303805035800203c080c0022400d600924910f140e030750044c5014020f56940400c0c020f025007001d005558031000f071240204141440f4490050195408400700ba0040d19520503090070400d0030400c40308040a20700303c40d84c032410600c0140941c0d00c0005026580c5c2e5003c0c96100c0007404010541500d4120303904414003252050b041030060f000001420341e41c640c515103050f005140c03814456540315211000d42c192286007048005100c41c60183c002c510194001e000b0300005841e100080b858503140e2280003a1908034510b0201ca184500c00c800603c3c0b14142213001801d9494003411501801c984c04c150350410001e03450803500c252588014940c0031441c400494125406a800d981a0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 125400962 1250 125399712 125399717
    0xf02120102090607030e03060a0b011b080d0614010f05162004090311010e060603073c06030c031506050334091a0306130605040906060e0a020702060f0703 68
    0xa2404a00000f019900400300580125201c22a000518901882615030202c1c031403a080100c8000311780000d08810391500d5120f2040c4101c0c40d00300c1030203114000c0c3c900c04003076040240320b004c1e1104001d81d8a080c0703410345140882d030318082090f900e5000c2d9040e2448022005e6061401e1040e03900c8a00c5980c40e85001c18140c100d807900d91a03400d403150302801440c503029841c0d04c801c6090a80d081130868803042c0314003405801041c20701c2070503507000c80c0c64400c888000d03000301100315011580482009110202d510700c029440160342c02c0b004400100000c8410944040080c081c00c032000768250780000410500c030840c4500300740001c60158025680011140000109015545d8081680e80102480d0000c1c02440d1543d081d500550013505035005d0580c14014003c00d10846030608000d00021b0b007610312a102c02c2150a1000c24190b0100d801080020001d21410a160808100401c00c60042d121400941400101103030654002ca842c0194090107ca20b4600f80d038004004070781241c90101c04 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 125402212 1250 125400962 125400967
    0x1303180b131a070302030d0b04060506071212020c0a0308070201061802070506150904120c080417010b010f050a0c0c12080309010f0513080706110415020c03030301030f02120102 78
    0x11054244000350894003650a0a00c0c0500c0c01c044800d0907480c000e45800b41540003c010140002e5400300581d000d55403070030340104e5000201800034001e46440e802c020740101c4041855400e01445819201e061452030312a4918a04003041c03a40a81c17180401c1d003230a6901000401002038492200d13030343d1254151000007160380c0c4035030100b186c60700001000301c00e00b40c020540c0014044117100c0c0c0c81c0c10416004031018507400b038002203041544001d001810598030000d10407c0c90340034801307410549500c14101c076075a40e201c40400508001d8143e10040940c60140064020f5000d40d000011406551301d0396130402c1c00741241141c0c0300100d49022038000307110301400a42d40d0b0700b0200c40e41406d8403d03001030f503c9161101d02d440c21104145010740003a1b040105001c1c003034080182c00e13003c05800c0020701c0d40d1006507040060203400c104504d40c034002000180003446290203420001c000342c41e81c2c01d030f8950315540300416585e03000c00e01000c1c1c01c9a50b1000a00c00614104100c100b201a20000150 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 125403462 1250 125402212 125402219
    0x603060607050705091e24060d140c12100f1502100e01052a0d2301140a0602030f030a150305030a02070905010905070c14010b1507030801060206130318 67
    0x220311450a446c07540c0b03038150250600f181c2441c001c0045a001d50340447d6a1b005e00c0100d8084a0010b6074400200d0040f580050010040d03107150b007103c09001000c02036844a41450340c0c030621158045810750303200c4180e4002158a540480c10540308803561020740329049410301003002c0801901468403001d520640d440b440b00c010490003008107440166000048915247c0e55400c82180720300380c0c0c01041c20440d00490644006c1e0010740c0d4451201c0c800003d55400181c4c00403007948011044451881410000083c008032040201c1800301d00c20340d0041e100c0d60740c0728002d0b641da029a4940317204925003400061314140b020b9210b082c900f19620245180d00341c1e00d44a40d8110350000c2c1003100103030408070050084040c6405074a00502c1c0b40c1d0301c10130540ca80840014921100440003c0218004044902c410103094003c0324141030b000b003602c505200c0b402184402c13540811021400325400c0000020b42c90700205200344105000802042000035950b0101d90300c1c001058017500c291905a40132 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 125404712 1250 125403462 125403469
    0x8042a08070b030a0b06031006050703051204060902030f0109030c0f0201021c1206060c03050711012109150b1806130204170f010605061803010204171501080a020603060607050705 79
    0x4800500480440c07581d0f07814116581c4042d118602e0b60240a00002c2040c0309498005140300e5003214034514140e5103659140c5021070307241c440d84104440100c1d0000070710040c0030465101400191084007290b105010507515203090b40ea4540300580801c00140149021402005440603da403051040d43c0822000c070b0100544941441708a40c00504003084880c050003291044c0f4024181c0350a080510068940c0c0c002d14501ca01c60004203140c6a00140046a0340580300c03000e0781074000c401c19840066444a0200102a5000103070355008443d0500d80c500000da205040c088400a484440408001c00d409803224202600c41900885103114180390100c461000d00098548502100d5007008441d40551801032403050702c980c1a490620100100c0d6600c10880340e10707000448141c101d490a1100080c0203004590000c4055540c0c21052038225a0128800c4510602e410420300182d032103420311680c525140200941002041005c10524078140700175090444c1704200b00c8981c207445c1c1011 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 125405962 1250 125404712 125404723
    0x806010c14030903151b04030b0115031b1101140903090d031101020a09032609040902040b0904030c03180501020706030f1506020c01170903040b090114121608042a08 73
    0x13210001e0342c00b01c003441040b030f07005040c0034401c0c41b95540300e0b803d103030854440900002c010311a2000c041840030016404074000c1d0072003058078402d9002040030140030b0728094a000404404000c89510340800308010010b001d020f240140c81c024011804e0a14031002c0c4210800c0c010300c00d500b840fa42180901881e4000d000401c4140050307a1290310381c44c5140303880d909050081d900003d0030020b801030401030382c0002d0140c4443c11001c45000c902c05020b40003081c014581304210a41040d800401c0001b890f401100c0386149910035075509400d019140c05a00880740107011301030040c1c05c61001041030b54480e07001035010f10079480380007642298001148072040e0403a440700c4e025802401c101c8140790781110880c02101d2160a41c02090324102d101c99481344943d020746844010007040d8598075034400d246041660001c1e9008139500e514218103883d000c0b0b000c4401c1c2400c0c14088030618011407080c16668043c503400303100c0c500c0100c0081900c00d034001140d007620304100b01c0c5403000150400200318 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 125407212 1250 125405962 125405983
    0x2040203060a031b060e121005070507080403050c0a060f020304060305270d18030c051306080706030b0a05040b010c200402041403010b100f0c0614090c030106060806010c14030903 79
    0x4901d525a071505c1006045030740b8002c1041c1c810705503214081007060000c503030040f0348415158002030705d6441500c155603500651401a0a407500820040b04100e0000343d614410030044441d1211742e5603800d42260105102214200160406d000070480d03640207802c1075401c1aa403100c2e03c210389228905c603404030039921000c1d98542c0c0c03060764000c00c241e4100c628114000c841882d034903515802c5881c2d05109152074459140141411110704038904440e0b4020300140c102c482c180d0744450b40c0e07940024064030800300c065202d040c01000000c1c840c50035105820083d4410b841d1100800384544658400850803207500c090200e403d035240c00c0c1b07540e039880240040d00d42e003080301c84101450818076003141c4541c00d4182c0104000c54440c1c44450304421282c101715602c0c07400040b414110301c3c0c03d50141840c901001208902c01d000c0c08826000400c8192407030006174000c100c0b5980d04c0204450414040d54a240454010060200491055040044540246000c5914180781000840d150012110 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 125408462 1250 125407212 125407253
    0x60303190c02100806180c070311010213030c0317120c0d0e060709061206030201090e0405030d060e011e060e01030e0c10030504050d0c1502032203020313060c0f02040203060a03 78
    0x2003100f00e24240c1c3c000000060600307107841b0903103046102600d040c400c1420280900461240c2c2030b081e41e0302501180c20182505055a054540d68501050700c04120f000864504070100c8511040040c48000d032004185480c10340b01c25034035080170300c84995100c0740041500e2900d401c9000510358003080564000c0c01c81c2d50b955110310340f41900040903000900030786100541410010400b40c0ea0000c8a80300340c8080c440301c0070f06601c071442c0551540c843c004005c8852030815a0014440218503001412150030300740340b081c2c02242503100810041d26000381008140e00d003d0f040e40d0fa52081d40a0000621a9011100d42214603000104142c50040d0b0001c0003a8881c3d042100700b18040c05580300704441d03802c0c8444044401c0da564560354004198801c01c0380d6010001800e003041c504d610440b01e00c2d113046c3d4004d0406042c24000e403a54000643d8500c2d01d140780200080039441240b808000d1500000c0146010800340e003040060f500142141c0e6001c0200100072012954401301011040d1450 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 125409712 1250 125408462 125408477
    0x30903021903080106030b0303070206031617040507030210080601020607200102160c0506040806070311070602030f04051e060c0a03150609090501060e1e0a0803071a010806060303190c0210 83
    0x900c02807c0c3c0d1031843c2524000d410603c48400103848440c2503a41041781e2429402d00805141000c82c0c0a9440442c11100700000d01c2c00e000c02c0c8400441c1c42000e981c02900c40c00485a45114195803030941030390601c2c010307030081300060001445a0036401074412a081c9040440c80001655800d80c0c2000302d2541c4002030411310041040205424034000f003906441803801d0528104016480300401040c80042c10340f5035006265180a100c101d440d41c2e644000115107a003071420010362101c9044508607018400c00001290380720101d00120312241e000c10051045a40d10a011b40700c0360407100d2400145500c940740101d1107000181c441c00941500d588e80892035141050000940e841030707220200303201c40d845000d01c040e114640e56440d040c1c1c1c9003078104034a607150300201c0e000b85619448440140000b141000c208040ca00c01c00400c09464105408180d80303800382e8a894810580741e55a140d07004000c0444190031040500411808034103000c08180d10035000b10340d01c080700707810b03050006c3c80c90b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 125410962 1250 125409712 125409719
    0x10e01050d0305040b1303140102072604030f06020714030c10060b2b110d05010819120e031009060e0d021f0f090609150203090d0309030219030801 65
    0x4104450040c002210344010460103600c2c041c285114a00038480d0980000803602d182201c01d0040b4001150710040b40c00c4030000c40d0410500035004508121900340349141d1001e00500e0081e0500251034030030303000c00e103001c4c82d41c0d996032014018150115800da0302846028003182c83c0c110340c3c0e540fa55803040656a22018403c1c4542417210203c03070302c03d05c0c614003e01809490310070001c0c0e810808200b020200701c5120400180f405840c04110b17140000d00340f210000b0074082400140c400240b0f034103001d00c85c50362191116070316280620401c5404160400440b00800c500851402804485080070314080c081ca0001c0703410110680c841c502c030035485102000070404035200f50241c148054010700700c0500c0c0d0a0f8001d4440c1902103216013055019840c8402c030381c000b0751021100c607000c20002c20100b503040c41c003a0003030490940151030110010500020301000c6000b164424141000a0480c903c61000203400503d12030005408501c01d403514120311612000406c40c80364003903290844a50b15 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 125412212 1250 125410962 125410979
    0xb03100c020d0206070e010e04090c06110706050c0c190f0308270901050105030a0e06131103160504050705070618140d02030d180203070f03150209090a0e030904021201 74
    0x14565040421540130804020a4561100d0350100e4103e00340703040745c0350090000c0028060f103000540500340003503407580001d07465082001d000c10f00d003a51781030f918006d82d5100c043d50680585031141126030010402d00c80c0328a4410301c0c5c02c00c48500c07583d18541c40d940340c1c144048003801c2034101300c030f240750000b03100c1003281000c580c201a5140402e01400700200c541012034000a018428141403000c040040b902040d41a000341201c00082003c48400b4904002407610741940d201c4240c0c0d8048200b00c50448608010903605c0d81e22042c0f065010709503241c0810b03c0000c0500900d520300b04070040c00710034005140c0307016406021104140c44a003c0321076051041d6030030361804100210b540324429259505401000f5208050316114000070090580849503105141007240258035004124000c100d43c580050f0725070950780180080211084c0e0b4211000c1240304505031198000691000601440300e55040510024400415030b424500428041001e91f08020b42c00000e49040c54010b220344030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 125413462 1250 125412212 125412223
    0x81005040501060e01080702011d0309090705031b1c09200103020306010e04320a050106020307020f0d060b09130605060603040b010608100f15180501090b07060b03100c02 75
    0x82140c0810a40d40340c0300002d0003510891034803e040c0185080004d00b058002c1d840040200110705004c581c01a41c06100d5031039500c00c400d030700c0c440c8003201e01142a40340300d6001e0324483c4020710058141480300e2011240103812590480f00340c04c0c0c07c100080c00450a6000d184007592281131007401d0500c54210700307020040e884205a04040c4184100710b031980c0d000c0081c00c8803030f40c00d41300003446a52059540c010243c0400948800151845142d00c181c3c0300b02455a00c18203066008114998aa032000c980703a12030714001951202e1207185800f40c52070400c0e4610f1405108120004625107004003145a0040444280e0746021041c1040000c0c03054500a55500c1601104d042d86103181965a4609480d4180103000c1004100d100080702050250001d2014120104e40003c2d403c0c0d40b4100d0f1007200c10b41d80300070800030f0607500580942d00070001da520103840c4140c44040344181040b42d080301c40e4105402c107591040e103440007464552018400ca9850040c0482c001c10f641d01c4543d0007a2611 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 125414712 1250 125413462 125413469
    0x6090c0c020a1806030605070e011805060706270606060906080c040b0306120f0105012103120f09060609050a0c0503041a0601121b110718050606040305030a0810 71
    0x85448100300340140d0b20510060709884412410058450400502d080104000e40008014a00d024284244240c01c00f0564032001e034240c1e6000e10007401c4081d8100110207500c201ca800910505c0f44000059294005407102e0526102d5004590200540700c50066203900040e61010b50382c1d1014440c1550201c000e0000e07061a0800e480203051200c820202d0741300b140714003034100f8004008608181e450000c010044c04c0d401e01201d0203061950b940c54001c0400b8866a2116030b0300c00c500c00c1c540310210f5030028160385c144d00c9401e040c0c22568a80d07000b6066644080c01761554030803544000404502c100c00261030303000780020307039440d1038484182141c03149185002800418810000029240f142c40504401c104412100c00d4031004c0050301d4001920326000282c1e42442c90410940e00205134040d010042075a900d07490340651101203490798400d004060758901102c4000000b24000c0c0c2086e50004000380013546456500d444141c1180c21440b800400100030340d052289035100b078074030321014 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 125415962 1250 125414712 125414717
    0x806090f0303180f03120906011706070c1b090e0c0402090d080901030b041a09010b090307050409080f0c2a130b040b060a0e01110102120408030405071806090c 70
    0x2034000460455660b00008142c03035412401a00701d00306400050080007020701c4a0400c40c0d489810030981e001e0041c1080fa00c50a491160341e0000499400c2c1c0740c40790040d045014050f14654131410b008440c44e21800d4402e403044c4408588840f401441080d600000b0600c04c40e000420075440303a50281814400c80c3e01e81e1099005100058195442815000c1520307884580c00d6660900703580140c001c1c001d0f61001c1903103e0318203803440300c2880b0440e228043d2508201c42183d49a0b88502020101d03005101d80740d82c040e0301c1580c041c4103074102584000c2103d4042c5080b01c1c00c1140261300300900d1352015200c07020f82e41000003107049114400c000000c0c0c003003209900700410843c2c03102080c0300381481c03140092005d40b100b29455442c1c80ba07a02c40344142074040e201d10b0781c414000390081c050402084456000807034210b484480d8080c10301c00c0e9410050030350a21821500c458480d400c40341c0001e0003d40d514010302030006961090810444042c83c00f01c00c01040d0240f0f440799002c1250803110b420010b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 125417212 1250 125415962 125415973
    0x180102070f03050c0d0c081207060b09190207050a080708041a0301050310020306040b0310020a140405060d021c0501060314060d0c090e010b19141e010c02060c16080609 74
    0x440c04207860040ea241035035005c21010075424401c007248020703807003802d15028900145d604010004014480640920018041030200d00e050100c1310000b201c603602002d150707002207142c4440d15001030900303600640844040d25a5911040090ba011003812240280006000c02c01c150b039001c4584000300c000106681190b14140c0031036280c19030b080819403003550000004003250ba8a40c800340100300d000c0c04a454003142405217070000d5000183c0c01000c10b128046079007584044000712015550090310481c21301401d0301119021b9000244081e0b406030401c11410f00f80030442c46610b00910184e580403c888d8030011410060f8100030b00114041c41d011000e0303c0c0070031040003201c01212400c40001803402c169046290040c40303106001c650080b4541d00c030040c00b5407c854010280c1301120203441c02c8001c500204a03078440c1d10080d00d20158800d5804003c02d6000b070203c4002140041c0415240a101e00070440c00e01c0700c9192190f0804c13503160402d0110389010007210341d10a0101d8005c04 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 125418462 1250 125417212 125417219
    0x2040f0f03050a08090a1508041b030c030b04020a0e09010603060501050103181b0b04030303050609100f03030804030905040c0309061a031203060a0e09060910020a05090105090307030206180102070f 87
    0x54441901c0344010381013510008a140030340c1c681500d400f0050a60440d0348440d1502080010a00070f016074046d510044001c16001101511440110440380d204030045071240c5560b448a241c240003e0091741e1000300b103500081c10085030001c052054003102d0002a0080c154544841100d5060b0040ca040618244800d4481898090302c1d59850b0b8100819000880100380b81d980700c810147c01c0303000b145030007140000c105030b055000140a141d007143e8a10300b40d641c0792041c5c50201014859081c0e0700355000400c00c042170281804c560010f000b450a041699110b130080360544040c030052400090b0744826030024048640310308030803d00446c105024444014002030355601042d410420340b030301d0001c0800c102d90380d60380910b0003e00a04403c8030075850000d4609440b800c0c00c50b41e401e520b01030180040d00b101102d1080b98440a80b98840c1c0381445200001141c40b0b400048055030148105940400541e95243c0540f800303001080c0d02070310348180310b800241004403e6020010101a404062 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 125419712 1250 125418462 125418473
    0x1515040e1e0c0d09021528080103030f050f2701080c0906090607050a0c0e0c070321020d0e01050a060519060c0f0b0405030406110303270a1502040f0f03 67
    0x3600071894401183c3c0f80d49020107100001c0c01c4902c030095029042030464000707013004501400852014940380c150580152101070480040b0060a0001810314001400002e0145542184000d42d0b803a04038105806112650f0443c0d014172208080302a42d040d6030340d4040300904685922840a03c0d04011700c2c00c010002d05450b024884405104206c08125002c50ba16120191998140c0001c11158404040e04000c420706c0824014400703282d100c500001e109080c1c01046407072650340755490354203d800c40c100101602400d4860302c0402c0381c0800904240160a000c3c40103d0443c0d40300009090902e0400d0400302c800940c05240500410280c00c002c24404590840499403d4144402d40d01aa49811001161000d2004140a8422041c8014000000064800e484154a41c0901310300c1010134580c1d24001207910460030203001c280041d0075415005018619040f4008449042c3e001c1e83d2400304918075a02c503101c0c01a40880c08204413a409140d10700105114648800340e00d00311340701d1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 125420962 1250 125419712 125419771
    0x90207030c152a08090303070c02150705060406150602010c171305061003060513020d1203020f0409020d0c030e1b0604030614040c0603110405091515040e 68
    0x74044a0710380002c16260000c030f0b00007019461020f0348043ca25110741080d40b5600c00c3d050140320004001c10005801e9071000030460380150416264a88060300c01c0d0b08108003185100204080301c0b40030310054000500400c91140124402c1030081482d204201458bc90384610380d1054046a041c014480d140e0b80e00300613034207070003e0000303040840343c5e0f00c408075030407005000c0030014484d1050a0030040c1083d20ba03003144003660700c104024010b0751243c00f4122505110100f01a500003000215100000d10510500640e1030307541c00c0c0903040c203d00d60950140303a00258004a02e07113070005017140d1040031074400e0046100c13460500f0458100018002903842ca6092400006e60882417246034480c1e40e4802554000c2d81d00140500618034840a0341400c443d0a59040719000d0210304040b54160090041050804130b0321010350605103010100044c098000e811621216001184240c1984480204203c080c0c1e2001c0d42c181e6680c0342030700c0c07592000e90003403030707420300f00ca9645804503502c0341481d5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 125422212 1250 125420962 125420987
    0x702031204060b0916050403080c07030f0302031305040504080a0e0f0a1511030a231210030308090d0e1c0506150102070e07021905100915140108030306010807270e0109020703 77
    0x9d952611004d1000514101160700080d01407200e002154041507400802070003291840e00e44076440320b60390380600c82613540a0750700400e554008d014655100e44544010030442c40c2c000c081d044000c00000101388a601c1c02c0c2c2010714681e05114000022030b4000c7c4042c1c150609500056241c852602001450038032400c0d042c070190800040c030841108111400d4441810030409850198140600c2c880c94840881c0301c2103002c2000070b40050004240480d181d8840c0e009a2581602c120a101c1001080388043e9040d00107915526000c20110328200a418031614100e05880404600c180001e440d108151b800407a80307074004810030204960103d2048680701c0c40202c90114070003185030890404400f503d51050710780c500340c4880c040c44001f914880e141010418100700440480e5180c6040e1803090040349141c0e4400c001242595101c0c60709a0fa1121081c50b01140503c445203054100540580c0c540f2004101040203010442c002c02501d4014007528208610700811541d010744804800d00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 125423462 1250 125422212 125422223
    0x509090402011407060e070e060105090a03062304110117070c0f0204090b0f100504110715060302030307030804050c010905030a02100302091c1a041502030702031204060b0916050403 80
    0x14004000307505440a13900290307070107030041c00781c2084c0169160b44c480b500d118080703d64103080302042c0d295000d00110381400c00043d19001000e41140c540320080d00980b14850b03500c40940008082081d40d50500381e0040f40301c0d458460340d01c10400001002001810345c0e44510741c08180c1800b50860b0480301010342a54041040102e504580c000240202000600541b038a03010a00f00122144000e030305274072540ca444800460183c642003480b040740c407141200b11503420100b080402245440707002030b04100742c85101043d4a5140c0e80403d0440e00b10410443c04142840180000c010041c81103259179902031901c00c0086280c030703001a0f602c624604001e0300034000840302e160f01510a0b01203a454000207404080c0d90050360b0014405030b48203480a0707400302400900850592400407055004942050350b9000c00c41120040d03500039840507106400b5444104801d101e115141c200280c451809030400181c881c40780707014804a043d0040010004200300012141510740005c2500e09690300071 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 125424712 1250 125423462 125423477
    0xb15012601050301060b210c07060903030e0f0706090e04020d0f1b080615130b03010501120203070b0a08220204051008010507021f020a02070503031614070602070b07020315010b19050909040201 85
    0x5023071190240b0400c2000f0749903e0030301c5840e03400e150b0541c11200c040002c010480302807420a60003251100e049000d00c000060110008200181308012040d8209000910740740009845035107110720b00d191410100c4a404030b050340c2c11030148602804200800c2014080e003071600e000340d0103a08003030703011a96a108820803080700080c180658002004000c02400030043c0b035031200d444c83d40d0580d501000320310921170f1110100c3c41d585c00b00241d6841030780c66104c0c2061900d40003008240b05101c44c442400303544c1c80c3c0400202680e128092180600322020150408506040030075003036900c014101c80c15940014450210140c4000341c14224507005200140c0b28104240100d080c0000c40d030080e40d00d84004600300c086160340d0100e036082244100074490300c0301e04d144455900e90486225200140c0c005090400031100030400601e4500e01c0101660700f8640500b600b00315004082e00084140400420044410b601860752460032840b42c0c1800790616420710001030074800300800090411460 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 125425962 1250 125424712 125424721
    0x907060203093a0606171b010f050705030406030204090b01050c1005090f010516030b010212040e15090a0902010201050c040b09040c05120f04030e0a030b15012601050301060b21 78
    0x3904402089411a03440d450f90881c0074107110001c1c00640c040c0e094840480f031464020b14a0004442d503440c8040200c1a000076482801500d01102c00f51f904024010100605000034000f0f000800140c25940c4005131030300d0030404214200c9940c0320545050000030802002c0c022030015085192010b6070a003c6a2690340c1c40001b41010040c03900c99402d503003840280030009031000d04500f450040355504102e1171608100480c0e0b55012412110003203041088188144007500010580c81a41d030f00303c15404041e5180816a019012a03021540a07501c8080f0000c6680c280610340d08007400e0000c01c2c1c01c290038803c05e0030321440307020340840c800d41d40c6400c12028280580107464030354016001c0708143c0d14241c52901c41c00c0004560441c001100a0358a80d05171801d059408180e980003840502140e95840c14407501c00042c0d05000c1c18004080240c0c04406951254400c8881d00480b4040700c652500c070a15094801c5a001020b000d4028411404040300ca440b2000c6242854031503201c03c3e448 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 125427212 1250 125425962 125426029
    0x1803010f0618050f04021f03020717070c0902092211040b12010501032c0106050a09090b0a0c020a020910050607060c0e0d0c050d030212070605090706020309 69
    0x120440600c030581d081100000c2c03412581020348100410040d0180220741d903081e415030500070200d4000b540945aa40f810080c142c802010203080741366800c0040c071b4010355841d003900c4101840c001456071100060514100080b080c9614000c01e0005425420690403100240c00d989034215082030008602d9208508e80a003500841c0302809644d0126a0344e545a060006e020b0b4000c10340c54086c1c82448000003215480b80c1301e08081c5101100166038041180c143d010181191ba0090916540d00e031076000c2026600c140c2c01600805038103100090740714183c5024203040710f00614240c501032034140607042c0b041d00490764a01c941e0741220540d100b5500c88a20800280441d00015003001c1c000c83c0342800c02039640e105090724145910782d0344900e100b1004015040002400003890052208010813940c10048499075040c2d201b4016901e0300d4001c50210300040d004908240e965135110b5050014a8000b03104000207000c45201851070022104089101028504004541030751200155000e400 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 125428462 1250 125427212 125427221
    0x31707020d050a140a0302071a06030606060903030909010801020c010f142a040306020a090b0310050f060c0609010f0c0c24020912060405060709030b06150702030a0b0708010605030705180301 84
    0x1a4080e100940329054100e00500a4000e0041116a40209e183d03848000f4100c0f9100c0e40310741001001401555a0002800415000b44e46100e406210034441c00725540d5501c078000340a0b0059500041c3c45040303111100d400d441400814400303861800300c0005400200d02c1e00564864000c60200e80900c03c040101d40603da6080940310300903102180220800186400404410070940e41c5c0100b484e4481d18280c05c139110558a415003107950502c00c00043c1442207107001c17984070090205090414a2542e241081b00c12240000a0b0355038840f501142206403058001012403403034904095952640c809041240000141070782c500f43c64030102d41101242c0444006a102416192403181c50707850190707403a1800e96084400340100c2c000580b840d4030801e101c1c421a80c0000800c041c9480741802d0007080c4140e501d4000030280100040c0001d603c1c10450814807a10405040c004d910700408014040301060300000200513007007007480398840d0300c241588c403041107808031a403030550080006801070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 125429712 1250 125428462 125428487
    0x30409110903120c01060b09010f0c081306050405030f010204050d0305090d15051b0f0d09050a0b040c0305010f05130219050a060f0305180d210203010e04031707020d050a 75
    0x62041080e91400c0c840003101a10308225031000902c00c6c180c41d900441102c0c0649940e1900182200c801341400e144140b41d850130b601c1c01841018940a07500f040080702c0080e40e00888042400011f00300306500b405c002c0f020b90b20004900031404d2505020024003800e800c9071000c0c00700600070564001c00e40c2d905a076010813235441048150346140010104002c0c1a0445005040482d5522010060070b056002c807082001c103280f9203031038941c886001400920a03044103848500c07507410088005051203140c140202c0c05030f910044030a14500d881802e4a142e10303800031441e4106010f100c54049050500c2217003550445583c2403100c60b001a0707216681181d03100b1640480b0006000405a4100b0070040500e41d465500744903e6850b00303122102d0070140c0750014203d5101032212569144180c680080c007401d9000c01c1420100c0911000c0c0580c0c1082e0088443c03641d036581800101a0014240c0581d1580b102400d040c510701408080e480304400d0078103070203000c00024038094984c803808115404c0c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 125430962 1250 125429712 125429719
    0xc0d0207060b010e030705030303010b1308030a0519030216150b03061006020705030703170c03070804030c05010f081003030f02030919030507050306090309131812030f0e0304091109 80
    0x440030903003404000350803844116404201c41c0700101401e401d01050603c2607800107001549507910340012014a980102003403a5006000200440d0036881030004104020460341c4058031485a0703496420000010f01c00c58003803502c100010040c2281c036000e140340186d0480d42c070421840f0340c101004c01034408400b03e0380e414090901000343c2040e85401e0380c010742d00d00d5400c4681d015203d000f4965101840e020160000c0e00b03a22405c810a4200c0300108601c201c1c0109490601170550740b00380715608680c10450751440140d6042c051541e1040c0600c880d41218907040c09541000081421141040c3c000681040580c00c0c556000e24000c10440d243c2e05406844445204e20b03400c246500c140150000b21101d000d105000606071900080b0799000741401400395183c08210010000c0381110801408038054854800445408461800002d0702d4003d5034154030841400d0070043c1150020f26403d0842407070105100d4821030000700b69826100b50501c000788502001c21801c521740141090b0560 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 125432212 1250 125430962 125430967
    0x50607020f0312072a061a0d0506060409020f06040306050f10050105090f0a1a0306100203070c060e010207051503070305090318040b0d02030d0521010303210e010c02070618050906090c0d02 83
    0x40007943c0d4001300d2041c00c0b41d488150030b00d40c0390080242340c65510310054896404440422024540740d0300c500d0300a48000d00c01a082ca81070800300f02c07550003540c429038140b603980d01049800eaa002082d00d900400d4044031640250904001038842d000d0160018050800d1250f22000e540710040701001505103441d20708054010b1300703c403000a0340202c90040c01041c0e60541034410a0002003903d0080358041841280681800ca080b01e07844c0721508254110311481c20001000c2c0c840712201c21601040c840101e40e05e150809000e015100e01400d10702c420740c01001105112070104080c048000c130100d0780032071044481c030300181e070f1070140a402039414025070b81080400b82d0418024060420000848490380c6005481140050424130000d8082400320341000f1041988100500131010091000138404a4504000d8211025145841c000d44e1148000380222600003121030303189003065581c58510750810300403505003580605903901401b00c203030100300f400c881e039003d840840c5802e110854 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 125433462 1250 125432212 125432297
    0x6030f151502010608030a090b0a031b030b042307050c1c080f010b0315130207060e2104030c0603150e040803071103031605180409050607020f031207 66
    0x40c2948000c1c0380d04005076184c80400180d80c0c0c00070058808a88280d225000344520701001e003141395002905d030004160ba158036a043e000211a180d1b22034501e15900080c0e6015600207201c101c440510303907542d03a2700014040f00810f0f10004c2c43d25a000100345031040d00c5103642d20340c003460240c17040e03500d0040b004001003401032180d005400302e106a0002540d000c20b42d0340caa86598643c4070640d803084010201034443d59130303401c160300b4004203800b4100d4014a846503944a410880e00d605065515075013140101255441e4010300501caa42c24407881c003450645196a80a107890543c4103400515840c0d505600700c03504032144807001400c060055007140c2c81c040c54002070960080b240100441c148500010940c0d1001003030b41d204401d8200d01c001141b912090036582a0481ca403500c6926a40e8000040f4a4403070740a4461064402c8005240fa403c1440c0003906180c0c044e0114076a540c02441581c040e03c0040b8101900100c00d07007040d945080416100000b40302800400e44528a070811080c17 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 125434712 1250 125433462 125433479
    0x3020c010603020d05030d1413110105041d0106030605030d02100b0303120703050f0c04080309090402120a08030402040f0207020a060e0d060c0c02011404050109062006070815090c0406030f15 84
    0x47ca410409035001300820354901c10301204940090340c1d46c42d1135030000c2d42050001900c0c40301c0d4048040b01410700c5420076664540ba0902c0d0078414501c0003000c0c4031040108225501400350038081c1c1411406442e170a02c502c07200954480d5034a01200141c6c1c6c6510705209d10f92000d20480d14219011655110a032600220107800350509032034245881820700c002807650340b0948182c81c261903e002c080e52a0500103000c21241c44405032090340c1c0030504568409444200304071690081d031007041500e03220716040c01000201c80d07003071081e403500b107004220343c400503075603d0501403d507042ca08050101071040004250f500400750320003807034a89407003a14a141034000c1188809981f00b40e070740c021548a0980707040028000c134442e8502007411804103010b058050074000c804044149001310b44182031a200c9072515030161452004a0007840c180400290780d0070906a80c104240d40e2102942043c84022999205510944040654400e0050058101070b00600c101c0303140000044140c0380c80740e8a1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 125435962 1250 125434712 125434717
    0x310090e06090d02030a0f05132103090f0e01120503070f0b0f1608180f06040b06181b090415060e040f05060901030210051606020d0b010c110103020c010603020d0503 73
    0x64261038800d0b01d90050f0a50310000480d1038018659642800201801d541aa42a0007016a10f401d520580c900030603c440d224140700001e00c22040700c080b0130002c41c02c01412030b0106401c410034001c07020340c05005032040240c496045640340820b04101c132005040071411f50044400c000c04a801100d002020300c40d030824070324018042460703405429100c2d40c05c00400c01c0b628000d1103020480b02070009945030000f0141e101803824640507104060b15040c02c55051800460742158454814400d1101a050407204814412020184200d050070544611440307444480c249004406000811400b0380d2285c1c0c01c8050707484800d0301e43d103041c1070f01c41e5405002070a4a0782d029010781d16141c0290807010040c00307000d000345005880c103046a42980c0a00081113500b08000d07040c0302c4200008600d1881c00005016200d024620050b11000880511410744000c00a40b504000214404401059644900e102104070900300181c0e6103182d1752989000d000c840d840030307500c078000c2c03a440c0c0d0500001100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 125437212 1250 125435962 125435971
    0x61b151e070509180606041d090c06040f0e06010e03010213090506030d080f07021f02040603060e071b0512071104150b0708071a090a0201020c03010b0d080310090e06 73
    0x401005036641c1c140116114020000410f81c8019a0b1041008901c9a0410103420000c0540498502522910821314402400500c904800420010803a07031440a09c84068640400c41e00b0714a42440d010f054036800e5518003034a004144e445000c18010303800703040a820410320240c025516046402840f840c0c0038091300c1041149410f02e800241c581c0703408110305024101a07158103019071034081899100b0760005225100b1f610440b408181000d00b9036400009020001e000560764030f007007800090035079405030b00c801201001d10301407210440d0490b00712001c484010003030007008801d41c10a40c0c50030001800490034a0340000c0c2c4a818090304c00c4a65a4a240680c5c06008181c290300020200c1402807098040e001c0081c0900700001e01d2450080810380d020700900c4201001110541d40380070b9050341d8000055110707521440465030140180040c10303108130000c1140040c0e84020400d0200b40b0b1800a09010000001440c07442946010070040e2a19000030842d031645200280d0350f4200c141d5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 125438462 1250 125437212 125437261
    0x1206120606051210020d110c071401080f060607061509092006070201050a0203120f0414070608150406080d090305060c04150f0e030604081c0209061b15 67
    0x41c4082a60300705007903c0040300f00060000e004140711040c140000b90403124680300301c82c0d00d0340d81e48000405131601070301d05101e031540940186840d01e10100142124050564140149001004556004003805680c00070007034641d5980c0c3c880701d00d440c1000b040b110f50810084900420b001c03e150140750b210342044d80c49401a110041d0b95180c20f00354808885c5421f640c0060100000c40055100350302800100542d8012a1f040c0000d101004090340021125070301541030341e400300400d11401200480b06a00d180001e080841c0c1400002009400c000b014102c50040e504c40b160303841d442e00d40c05003000780008000c1c0c43c00328030303034180052080a40d40300940b95071041c0ca0100c1d0141e242c0900710303003c640411840202d0003a000c007080e14203520b00c0c00200300b40000f5a000301c81540b070030721003948183e202d10445135031034034400c5004505464a094040c4094814020658180c880004481c282184548880031009030214810b140407410b10001064421003420b101c5045420a1000d10503007904 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 125439712 1250 125438462 125438471
    0x105010f06180e01092304150f09170901020a0501020f04030201110d020a0201030b060903030a0e09160801051e03030408150109020a0806090a0621020a0e040c031212061206 76
    0x342042d03051040180110640400440010401d02550341d01c00342220303050680180c2c0d020442820b903560107001320307030a0398800d602c0040b16255000713500c07850a05900c112820032140a468031100032019401d060364030740d1500001c4c090f030140c0c000c100304510190320400a651310035400c0b0010010742c20600c030490105a1040840700c10711008262000c0c565890703030083c000076040ba00110054411001700c1900130008110055007502c050004200f440702e0b6846404c1100015014081c00140082c030103090b0360139500b01480e0704d130780c400c0d1002d0445000b1100c0794407405100c50810300c2d0760a01d9a01503814400086c00062101001c510076550f242040e04100490380d941014005074480e1061050001d0b00e03a8001400354070b400780701540c000303800300000581303552184a051445100c401882d0030304001c4851400c11442c0004080c0701610340018201c4841c20503940303030a9200c00d280001008266000c0760440d17828445c000703103a11000c042c03a084c41603582d50380200254080c0160180d40d0f55081 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 125440962 1250 125439712 125439737
    0x50f040f03050f120d0203060402130905060a050f030c15120f0a0f0204050d1b081b1e10260a02030103060b030604030e1e0402180307151b0201110105010f06 69
    0x41004c00b42401446007941c5804100c807aa40000c1d40004d201702c1c2c1c0310368207001038800001c2c8984110050486250005107070300b00300c41046a0b64001e984007602c0f40c01800c0740800f0070344010889000b45d0800b51013400883e1850b1000c0d240902410b01032190b800f20304c40c1000b01944a41500700c2c000d4641010800038003a501c0c400030700340c1c4514000d041e042011000d40302c0003e00714003440c2141d160042ea00401160f200e46086041003000070516510010000030301e5410710306011b002c0f140d0840201d10748900340204000c101c0010000d2480070622600362f070302100c84c41c0a00c1120b0208a54881014014030381003086000a400a00003640c01d5840c190140ca101c1c02c001030442e010340d8050700c80d92030f040440301c100301d02e01242407680c0400807808000e860070f1707480300e00140c108a000151402c0721700460b2000d151800e1820b60082203046a03600044180030303000070702881015030034225070076000803d0005079251125900c040110758601400020603406201441054411681d10b15510602 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 125442212 1250 125440962 125440993
    0x180303090b10031e210306090c0c02031e0f0d0c12171906080604081801090608221a180706050301140a1505070302070e0f0703050403050f040f0305 65
    0x9400010100418407050740c2d281c00060114100c15880307170071021011080701d603204d60781e20401030b006400301c5d0f01c0322801d100921960068401035500c5280040c4004129000a40c0c3d554060404913151080b894001c1500c0700140700302c6400080c1c48088800840452000070110000e0600c00e40d091a2054203c0039024424075500c42c03100c00c023203484005070311110710820007003044409500b07805a59450002d44507a09000300b034825030161111070384805031051841903414240d1a01c0d410015210414051242c001f0251074100c8030442420510300c90703512407000c00745819038000c1c0480001c0201c41c00e80d05d00052003148201203210008410803851800c2c2030351094035010750804900203100507c9000031462050030b0200b0700801c1c0011181c3d0b107814000a00c00c0c9020306100040340000c1d0300c0c00b031580402c142c0c030061400031030b032200701e00d4602001c680b1100301030700f150b08050320f5001060034184194241c2c0c000074100c0030380b540c1c0c40c1d0303644082c80790300080b502c002c80e2035000e425240178104d00c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 125443462 1250 125442212 125442241
    0x20d050f0a020913030c0b07020c0a030308010e0711030f0702040b060f13080304180509011103070930020603070201090b0901091e0203030306090907180e100e0c13180303090b 77
    0xb17516403602d0120060540c0c96880c006002000901140300b000c568800c196203c251010085000b80c880008650400c2a2500c00d03007001000c0f50148002452484039002c0f0001c100c88030380e1101103480361250010300c0058050204400c4483c0d1240300824036010742040c2a00400480141c50f9043c500d041c0e40790103403074403801103108442100d4400d06da880345160890700542d50214a8030000500099000e41207040b83d04103540880001e218400c061188903249a01fa04102c4241d083d16514a844401540e1064881c000f0081c065500840031500460003500080322955016494034154902415824021316642c501a030781200f07200660840401c5903d040804150003030301840c41c50b602ca400b03004103c1c0019000000c2403041c4100065281a2250408801049481d0220f46000b03035000403481c10410b994040303181c601d0b104400e2005800007070125083d900c2a034500009510b0900c03c0c500070800c078080c2d0305c2140a4510074004050f1b240d0701000545100d82d4031940c0c9a140c1c0c002c07200611 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 125444712 1250 125443462 125443501
    0x72001020f07030b070302090f0402070609030f140301090c051306031a0f0a0b131d0708060306070207032a0305010209030d08040b0109020702060d020d091103030a0503010e04020d050f0a0209 84
    0x2580540003145217a03200340c0003041d5401c4082c0011140041c044c0209080b43d11410050fa10207560312044410144c1c07140300807034070305403e142c010700c04a8030059079402032006101320705c00075030745501d0710303004502590036143c0740c4450030b60b0348031510350780c42d8017901034414070b035041504204040c807110040c42c01c0c00f45081b0380c0b01d026080e4044d10b07007490050030440e403020f444c54010a510000004181090340150b02011002e450903d440b410a068090302c00200980f5451094008600300a80640d0000b411400c40760003015107443c00c81d401c408203a0800e402c48941e01140c442100100a2003415002000a450280c04840744c80c00c408004039610402581e0061040c4401c1004000400c0c5903005440c1c607a00003448107140c00da031084218101d034019181480500d40320101d0006000d12501c6000d804007007a0091880c01a00d500d00030400d00c414010740b4041020310010409644075049504a20343d072003c102c8407003a034401001a943c5e000302000f2840b69603840009600c4612888000020 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 125445962 1250 125444712 125444723
    0x705130e0703020f03010e19120801050303090d020406080a05031b0619021c06080a06060501050306030a0b4318030609060e0d0f022802090a02072001020f0703 70
    0x40c036095508118a070700c480c0a0185d031641d2101e21041e091042032144210005901d610030841e09681d20f04880b0703601c1c880e1540d03400e2110a40040209403404021102084030454141c03001403101d1000034020704131504416200e2080950303c600700b0200000900e10301812601c0352440c0301014044994400b8211a41498002c521104000006460b0040c100d19210891035400364100c0358520701c11035140d68850300481c6d0240f0b07020b1060011502c26880685002c0c070300300e03285103080e00100c0d41d242e10031680105018080c60000d600c110b052050b140207a00034076520440620902c10324400e65608582014a18100030079890100d805200c4400210351184d03001c5095502c2d584801005181d500c0382035943d151150340480715007105015600c09200c10752605045c20600005c001e151101e080c51885d100880e0110001c034a580e101c141460072b590445417090a0359881c03060001900500d1700040500784661940840030381e50b811030301c0c0c614800381d0886030300655454003265150b49900c4058034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 125447212 1250 125445962 125445973
    0x50a14060316030828050a0e030a0305090f030a020d050a0201110c0d030813020d0c090b061c1d030c0c010f02060f06150714010515100f0f120c020705130e 68
    0x11341624081c04100404001035034000c00c88440da0860044a4803140000034000100320780d86139080b080c41d40d840e0074281c000345202c80481c0e4003e0054428462014869001e08182000c03955040280210499020b822582c005110389000d90f901e8801403004c9002c96510f54031408103600000c0c0980c16074070300401024000c0065281640c00a4025180c0300b0f81020509194015072664141c07104240c1c400c8006485a600e019004000c440c0b440c00391501c0341500702700c40a04000b007961074451048081c43c00007840b60a0402c6845c04005828032112107003c085800e030b1b0307000030200302c02c66001000e0701c82c06540254090300700d850705070131280040a0380f03014001c6103060070540749601c4c10b4a41d0204051070b140d000c1e2100710564150049030141691900708104940d4034402c00444045402c0d40c0070084c0320b10704400507040503034080c5071004000c05550401c103000d02c50700e84040074240482040185214800e002512801c150281c2400340302032020f00b20700d4224038840c0740051803c1001401 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 125448462 1250 125447212 125447219
    0x8040302030a2f060103050f070803270a03050d02061506030708150d050105060a08031603120b041d010b01021c05090a08060f0405160608010b030a0906050a14060316 73
    0x40310072540140e0384076401204107910b1000088543c103000340f0b80000c0010b01c00c0e03626525005240034805034a040580c1c1007400108203252001041c0d5004801e00011044d541b10300300f8500300304521070a541c41e4412036940001040c0000400e083c0400c16183e070940d03501e84da5000641c1440f00e00c0500181d002002000010315007480b400a140e00103807048108844403101d0300c000741c03500802c0001600c080e55514284032a528001c4102001804801c02030b6041c1420501c8118060421600103024014803c80030315956245038054960b14200620420042d0009031072451110340c0000b02141640c038040000700b070380d8000168005031880c885200a491104450308403120b0304290346030b0b600102d40d00380100341e03200300f03000d018821501003480f094181340a0034581e1a043c0350b00c1d80060b5a1030290414010180e00030022070540f025402802c2d502d072101210301f80108040c41d005000540740c1000d210000c0041d07003150134448050f0601000c50f888440c10180c946100100500ca501000d09080 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 125449712 1250 125448462 125448467
    0xc090603023f0f07051605010b03030309010f061203050712030b030a0b0a0b1e0f120307240903050d02070f0b072001020c1b120a111003020a0f051615060f0608040302030a 75
    0x4006c1c0a202e000081001e0f05500c0c04246550420b682400459449080281c1200840e100314402041000d441c0581c18000d5200a006440b03201000b610030300480003010f030082e000b070304038000c041c03000340032100f00c04000d0900da001e0420503104041c02c2410501801120f103488000b2001030280704d0141189001d801c401c000c40c032100381c002550490782006489607098024800f030940346001d0406000d0036140303070940c84003003015005c46180c007910340781180000c84d41c09400d60b035010403070010059640590342840082c1020511000b070504d40e110301044040e99028a004201c5d1141c10b12003090541890904c1c1e00740c2c055000c48480c3ea03407040607584a105211341c540d5101d0f0034040d003404003a08810424508107105441c09458107007040d42d00408600b4504200703103030390445107030443c10016580c0000f001050001c0b500010001c01007104420a403000c0b13140c1001a030300c90040034068609408003009046948503494008805c10f5000902c0b902903003180b80315541c9540034615260505105 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 125450962 1250 125449712 125449747
    0xa06210504060203010e0c070b040b04030915110706020307050c041d100e10060e040f020406170601031101020d020703032102030702060603060601030c090603023f0f0705 75
    0x258081a006800004010a05446181d001e0750055201503641c0d0b040c0130a0380100a40a044900c20003400c001c4080030034060020320390025031001c44180191070714281102c60840c640c0000403410305999101da089a0080255100092400c003a01c1040d5603400d420303030700ea009428010b00035030040880f134007562605500c280d039055103c68801043c40d070441405450803e445603480520b0f66114820300342c01e0020441c2d10504155100280035980c20b1003402540c2000203840184054294501c8104540d00c2d41c00220252104082d4030310904500180c95a94410030700c1300b0342c0d02c1251418840c0c9a03510120b010081c025041d0000c04029240d0b40c0d045906c00b4011403980040c007000401c005400c44103000950003a200c0344e0092010342059070405041800262441d03050601c4c1001a4126680042e050421100070381401600d0f54a8024400000803408020400b046642d191140700c90645000782520664031202e0884544d40b0550000d1004005070381c1c18010450078480740348400c0c0c2c0400b8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 125452212 1250 125450962 125450987
    0x1050703030f0e01020a020607090905060a050103050406330906210804030b0c0a030506030705100e010302131205060a0c050f070201050d05010b03011d0c090909070f030c0e070804020a06 82
    0x10001103043d28041d00500f260040040d86006070485003d114903241d01c81440b034040d025490b41000141030980c0001e240c0e4400e0308c0751905141c0c4507070025042c044541d00c4560880f0440c414014298840c80c1d101551400c02e061002c280b20b0340c40303000304540741c0c28458181540d207101c6035188107442c08800d1040104114404031900d920401000c40000e00b0644a41c2c0101d0310400107988920a411015003a81c0000342101e010340e1060a0801c070325030ba04200400307088800e042c01030120250000403001b0303100381003111060b8130515a0010301d1021708650500d409005405031071031070319040c0101c81528113170074210000030014005070415842c0c070401054814414100103140220480b0f510013501e1090740302e1400c0c02d00c00310041000d800903100d012220603d90910641516010144003c1070240020203400b170700c001d80010780303912410000c120203801d114595092107a070740e04d4500c04140c060b0041111280c82c7c04013090400c0d014520f40381c02940c7c0100319210b0a41800c00840d0344043e13050 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 125453462 1250 125452212 125452241
    0xf16110c0d080c0a031d1210230907060816090605130312080601020d0207120b060f03120310141008190603110a0501020703150c020c060c01020901080f060105070303 73
    0x1411107296042012101c1e1505c00e448504106480050914240404081c224091440c441d04100310002c003082941d461080caa03000164518080c0c110003842800c4154000e289100300c080c0483c4400000391361046580c556603804840c1c0e01c0c1c0e03818440524000303000b00d011800d0314400780200b6028501a201e00c16000200111035a41c1352030791024203240c2c0003118007241d0060180009942c1c1442100b8a080507030004110440c9044141a10328605800252081c80750b03d010031340940c0c9040180d100c50300c000301250703d11070120003420b903150310a41c4e904514004144000070f0140c6642000c0b88042ca000b40561480c228421054408920081001a44007a0540c03000c4807044540308240c06503000e0184c0e440e5110540f014044800e01e19004203040d5032181c002040013801c4c2400128100e0052503000c60a2011103100360b14020b01c0d2852590300400c08502804602815406000481401d980300031070f07078940d43c00e000030f41300050b201103001500803c80000464000d030001202d543e8600d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 125454712 1250 125453462 125453467
    0x703030f110a0e0108071d09040516060f0e0306060603041b090c0207050a0e0906011a0c010f02030412030902030c0402210106030504150218040c050d050f16110c0d08 73
    0x15038141d402e5100c20002c00205096010100b40e5580c80031180b584054603003807a5040b28400e00c00071401019400780d041c8502ea5080c00101040414003501c50079040011040c0c50380d5481d090080c22144000c004280021800100030380240b0780020207901400c0044c1c4210701d19120b0352920000c01540070b01e000c4c01c4414810700042e8100091040742905034413a40a012281d007000b04000c003c90705a404105440c0641081c84504c00000c90001c0c111074a45801c06000380041000501c1c030f010b03021007552070794070f045a0074a0280a64006501c10380c49a00102407400d043c24081d02100c101030000383d05540505048881c0d400c0c542c2c0101901c52208258420561403c2c0b52403d1612098001b2000282c031141400104650555404c00743e4421040039818080c401d0400782400e00300800c20386c80307140c403400e0424140340120b044442d8002c4540c400d0080d071a0419a00460304029121801449882c810a5001da0300c0f60040e076004c5100307540a02070b0f152030501013101a290155003a44d860408 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 125455962 1250 125454712 125454731
    0x2151909050f010501230f100c050613030e03010c0f082205010c02070608012d090c0c03021605060f0d1d210a02060f0c310504020403080703030f 64
    0x204440a050412000046041d40c10706003499500000c008804120445481e602030082d03907402d0040c0030100c0305075406c0f008d02ca20000700f101e14079a040009002400344a0074042c0689803412400703042802038171840780c4950104281802c0360b42900042d400289002c000221091046203d65048928a00081d03540c500002e41d207940c42e001c00000301c9040c0e658a0f005040c454040c4044001403540c1d003800e2186624290140500458152000c0700000c0036a8429180c1400081620080d06000908100005a90101078101c0150960907000752007030f501ca0001d01c4c1200f009a200790342c0017804207030030160b0041d8400910b401c000e2200c09800d40342c010b040c204a0a006400b5845082031300208100301c01d1400114010105402041703040350700308010b541c2c013a000545540c1154400300201c0d0503540b02e50750000c044c001c82855180b400e403188100155000a40b290140f03400c2442e2401002e16516400c0200b244030f1480010410740081c4481c0001c2400390340101d06101c00d200001c20302030030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 125457212 1250 125455962 125455973
    0x1e0e27010c0309020a090903050f0d090c030b090601090203130204020913020f040f0b070f030c0303060b210a020304031b1106030f0103231009050c030105070503011502151909 77
    0x401c00480003e81e80c80002d803d40c50040c000000600b055502000401c0700c0340c130000c00034400e628103484581000903504401c011103034800940a508500362a8000343c907450144481c0360705694a020394800e07580046410304182c0300b00c0340100c1c044419182d02070034950a0002031741144c0d00340742d800681d45031003d8036651240024002d00610002c2550703142e0510100070500003580e04070760280c03103091100100040210340b4101c0c5003038060400075816001407404802a0070710303400240b44a407003c60549541c1d03800030084402c4100008480100b6600c0c0d5540c401203020449002d0001200c0800c1c50749440d0411501c1e00e804c42c040c42c1802c598000d0340000c42c9190b4000e542c00590451110010001d010602814484e040301881d400780d01061030740145075403401110049680d00f0b50710100c6d4000c000341041001400710000c0c00900291601000203042c0303420134410202c0440c0444140781b049407020415044680340309407420174548900c00508208174030442c0f0075011301e50352a045400300c1d0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 125458462 1250 125457212 125457221
    0x106030b010f030302070602190204111603110c0d050d050307121e0605040209010e09060402070f05100b0d050d140705013806030c0906070213061e0e2701 68
    0x1c2580c02c140c15680380d0300d4001c1c80c1c002c469029008540080d010658a40350701c0c0091002180c0403200400c0d0b64145544e245401d220309110103140540b0100c03000201600550760f1802e0118103010b46a0300303e080b00c180518002c0d0000f001300706401401071032000c18010030245802241d0361070540249080210041c04462004d20f401940140b02800d81040304518000c00000d054199015030030a10b008001800954003201d4035446218034000184460300e0719819a0385143c0c0245000071022664101542c580c00e40340d500c0d001031410500058090300301404c40c0d02000d07038001c000342803646282a0450390307011500c19060110a0400129010078024042c2d6030031140c501d811000c58400c5120003c12584c0c690129407600622003072400741541d10345040d40da2240c283c1a070b4903626801000011098421070030000d6022150394000100108250302c0f00d02940c404c0d40003221001c04c80301000d009a41c15129028407466010002520425078900806210000401c3c0145000c40030b440142900e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 125459712 1250 125458462 125458469
    0x1106040b0105031b0f0f0402160b1b0306090a0e071703032401020d0806030102040e1306060806060a030201200d030b0f0604050102030307081503030307120b01080907050d050106030b01 81
    0x1102058010701c814902130020040030b001ea8070000c6030f000300500114440c0080241c041740301d07110000c0b66450351340781c0d90110740303e4440304240080c2407189072806842d80310080d62145485c181861080d01995400c00841e0302600c4010003010480d41e981841c500501560800410a401403503800100c001400c0c4100b440074424a01964480c581244066102501070000081c14900c2c8000c07e102c1ea44c000c910414941c40c6403400070340590b00d1101281c060f10403076110008640410b410400549030550940c00d0851042c042448921358903400955102c400307940c0035600c42d110324010401980207003078a000000046000c11100214006004c2c00c00000661280c08241c4902c00c15049103044007a040c0000011070b41c80782001c0c200030000359a8003000700350070305000c0c65030081110300188013162003684c54000c003242d03540d00c0c01e500001c0001f803030490710307544050412619552542c02660043d2042c0c42ca100200110752030842004180e22460400b503c80b035595440100204141034081d074080c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 125460962 1250 125459712 125459723
    0x190e07050d0b030a080904020a02070b0703030b01020f0c0108010e190f060807060c0c03061806021804050c090904081e07050c1f1b02220b120102040503070504020307110604 76
    0x26040710748058815110001c12040c402e4118034104030000d900e49041c1c1d0714150f0280c034016110b104100303003031b8a0400da5400545851340f0200e41082003691582040d41011420ba09540035800b11620300c5964480560351103020541420050008808458031f5980c4800700700303001942c852405111b1320031100d0b5006e01050180d00c820701400510020414031006103420310701072410303d1040c1c4a42500c00c529000080003607403a07010203507001400c18a040c030b400360000710840d514100001340d80406111003207a83c1c0603d080c8400183e4070800034084e20102180a441504142e032559696182ca5100c0c40880e40c0314202098180290190340000d404002c1c8200c0c002d102a511540c208403d40c2da845100782541800c18a440d500e05501440f1b914107090102c0742e1031510022840003902c022100d40794503c00090100e9024040c091a402502c52032070300341c42c0e607a103d00850f45600d00f40c1c4940d005464050b48810000c21060034964021544002289004095000141c0300581050003c2d10141c41 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 125462212 1250 125460962 125460967
    0x913050402030c061206130902060406030e0c01210c02010f060815130f060e031c0c0e06130b1305030114040302120324130c02010e010f050103050a02190e0705 70
    0x110304003040f60303d101100c12201c50b420641e070400c003d9071480d00108110f009214019410400039455005040380f40d50040c40c4076112615010018024410b40d2100105445413a05c14030280d40500a01012802e10129440f4805030842c951006051f2420f03003082190340c0c804005d940d1441d01d00c10100607040010241000d10b0030b4450742d001001000c2c00c48c00e1076600e525030080005051100c0400703003e034404004a80c00111051190071030140b865640b2240c0d807803d9820380714500f144d1007504c0c203890b184c0701d241030f004010017403010301d00507140d10038100003c9030001d100c50900c4002501c0c80c22003e07104948800c1c0c848011a003510325071160144a000e40c00184801c041d0144180c56000c0f840180103030441c43d0440b4034030300e00c0d00c0d01212607044180900f81e100154986582c11040880b8501090191030342a0900a0081010915050b1130703510340303908000b0014035070080c14100e0740c011000b448107034903580030003114500c002e60003034800391480c8002a41d2020412100c0c4a45455154143c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 125463462 1250 125462212 125462221
    0x801020a0e0406060813060e03130e0907030305030a0e010f0207050304060f030209130e10320405030405090c1e03010317070218060a090e030403050d080708070f0302091305 76
    0x1841d07449031000141c401d90a0031414402c3c96884941aa0300280310152000413100ea410403100400d454000b081c2c5c03501000138807030041c41080800f10111003078103075103010360395030306494940b1a203490200400007003040000c1200c801060300203850074544e190000078500010000c4200b268042c0030300311500c0c5c00c04a82000219001a443d10068916003400d601d09520a0001040d804d038030710150380c4060b582c443c9550480310800500c0740d02c41c0c030900e0410103000c44442181c43c00d071200d000442c0050502142101441c1c1c6a01e0381e40c02142d00900440c2010f007048200302c03607841c0081800b0700210b01031010031f4600c00285099164403c10350b800c650340303504500b0080c10f0701806100d240b00303444007000b8010050300e0f011a004e011b900c1c0390f00182400d031181800920018503d41c00407801c54100b80301d070b041d50303400400240201c0b8440d108690b4889405141640c026000320790a4010805510009411502603000545040a0ba14006180c25200350000e46040c040380070441c2071640d21010007 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 125464712 1250 125463462 125463467
    0x1020f12090f030f100b0307080c0409060b0415080111090901090e0f0303070324030201020d23041710050912070c0315020c0d0203090f010e040e12070506010f0b0f07030e09010801020a 81
    0x801c0140c030160048c110090070464443d54681506035928029559050500103200490340509407084004200380300100204a03035400302405030003254100d519001d094105260300c03404840b030464028040450a80c030700702c0304c00010074022064110301c2c000c18814001e050424001144254440c0e1400980007448242c40d03035072001380041d240d03101c2040b0841403000d40c0e0000307410301d03058001e4a01110031519610905000c0c0400000c0616808000f050210b030040c2c180017103070320403d096021100c01d44145804141a2041600c00f080e440e084240700e075011001d4403006211031806800b080e0162075981c0e450202a88403920843e825650109180311700303000034400480e801200b84001c0d410f001a280002c0d40c90341005840a042c064003155104850b21590409500103142400351450308042110021140d800340000311014042d00700040790341c1c90030f0a584010b451a81030924100300680c1b40c0582c8a5000103c03c1d010700030950744443d0b07aa540c2c000991301a0010702e001503151017004001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 125465962 1250 125464712 125464721
    0xd0e0604051c09050a0902090f0a060903031b08070b04060e070e0108060f0c0405011206080d360302010c1e03050405240702060f13031b0501020f12090f030f10 70
    0x100d003c024510000704015078a202c044000c1d210400c0c0e005a8480c40140000c40d03101242c07000035001415200300180a076006003100040307a010fa11504064011901401c0e90a0016440200062000e02011011034549d07011a0341c0f0511a600c0010800301c03082e6018901089503011440c02d8882d0401031003400030501c44c80340c1245d01c440c001003090610b59100d41c0c15000e24082c0b5410004060340c5140d8194403500080000d21030802035900b0f040300e0090080042c845000d0b0107506480d02450050910154419119070841d4207070707032885160850340119820039040d48151010300003104243e0900096114002019100740c0ba5241d8807450001400725500680340d059101220540300182c2000340318040311401035045503041d13616503002d66410218001c0d011460040c20350300700084200800c0e502114829864804107808036940d42c0d004a81d5403e40186912041d081084051164487c1c80042c20388900c000f400300140c3e0300c2c0000071078540001c20402c5a0311313610010403a0b101c0d0140d03206 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 125467212 1250 125465962 125466013
    0x3050a090308031f090207020102070918060906060f05030d0801090f020c0607020a12020f061b130803030a0b0906030a0f060b1305180c0303072d030e0307050301150b0d0e060405 78
    0x421b50400d00981c00103900d4200c18803c84680301c0d15242c0245d02d44070341d1000d02454590080041082c03c0e800c2c2000402000240035000c59803c000e4808243da103000a2402c1242c5020707521482503a00301110f1001a1090011402119030207000841c90b50314107206461049441c2d5004020100d02d60a040c000c0300c110b00301c00010f5401c42c50601001040100381315521a05050400c0d40c1c040301c0500056651103400c00c0e05541d4070b5603610100d000680400114000c000705c12040c040501403000f0400c11000c1994090380c56405003801e50000b0300007000084195004007000561802d81d01c01141503104284220b41d4540e95520400559103507120030340d018503c0d80f02c01440800740743c2000c41e42e130b4820980040d082c5000c494600c0803100c401060001c008403c402c50030f400002928020740741e01d40300c074000381c4039000c0c00c500850b540c1014421040143c43c0110320188d1503250000700c5c030042d480300800ca0302e4103031030782c600030303210300f0100f01150041d03208800910f040f41500542000c41e401000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 125468462 1250 125467212 125467229
    0x21100c0c050d08010f14030a020405010608010315020301060906030e1515010809150712150b0703020607020f10090206301005100e01030b03062d1303050a090308031f 73
    0xf005000c0381c3c242c001810161503070b04042c1142d8106a50000e494031000940007503010b802c0c41c1c00491a5940800c0307090403607114545d55540c20f000d54109030182e000034040da20000f030003908200000c41c400e070000b882c0c6522440655405461461862010a0080380c110a071400603420700b183e02e5030b0081d000c80d4032440c503c1c0076080c41511070050b20349440c0301800400410107a42c000c250020075550141103481c00003031036111415030350b0040c407059801692041e03016008080000312900d0001c0340044500b4200750142144640070944078000348079440c800e90304070341c0c1031004030322080c400c840d1100728560441820041c24a031810000031444003d04402e80c1a260b42010080380d01c070105d555205000c141414624802c82400403402010800d240a506200d80d4080c0189054540c8060040c04581100710354000c0d0301c0c8003100084070068070007142280c583c042520209106001600ca55070071482d111220b03541d1ba4803000096041030b5501c2e070300c2d0420070611407441003403041040c00130074251 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 125469712 1250 125468462 125468477
    0x302040e040320010c0306060807080610231602030d0f050f030a0e03070b0603070909080d0c02010e06040507050306010e01181a03010c030203090f0c21100c0c050d 72
    0x90040c41040c80c0508000d05100340340003641c828112140442403c044500300820000000c00002005803a0074410f50022426400c0402d40036885024154400c100243c0300f181030101100b01150300703220014441800707075500852000e50f03074101c00003002e000008480d4110003d140b4010141410241e40244090010f00501490441e422205071140b03a19910a070707940703c0da2403900d503201a10780b590f070124050000060150400004610072401030360298115652103844a101e03070308075400a94041c24000c418051100c2400141e0080c3c500ca030624400481e0b81c010f41480305181110941d800c64054000031014440c40c201040014010405038401c01e5541d454a90740d00c1c0c0050000300c1b841c80c01512507800c602c60b80c0410a50001100002d0001c200e1280b4104004000b5001650500d0480c098060400c1c200c0c10001500c00c9040c10040041070704403202c440d40c542c0301581c40c481c03060030300910051401c0b0f139402d03110322004901d80da20b4103040d00c001490810f08015203800b042080c070100c2e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 125470962 1250 125469712 125469719
    0x15010609030b0f09010b0d030302070b0f090705090a0b0a06050d0e1501120f0507060905030705030c010e1c0b042a0807120302011d0a0b07030b0d11010c141c030204 72
    0x1520ba502c2d800070070030810551540c0311200400d000d0008090111f0b0424648440e22040580c154014107820380620b12200c802e0300c451102184000040c1e8017020b00d0351240c0818042c9282c0050b00030307080003c08000145000d101408241404c859034070682c0803c01c00308038852822102c3c01803800b21700c808406069280c2c08114001c5a101060080503203520030041600200300c4030301d60f203105040d00034049858069840704001d1800342c01c0c1c01042e00038050380e440000c0343d00707002950f500510350503150b58080205510a0100c420360079422600c4003940200f00303e0200e00305880c914041c900400a00c191700c040d204040c40f4101440a010805520706003040103941c601284100641d900c0c12041201180142000c80c00b41006001c2d02060864040ea0810712060010740180c40070701c50030700744030f042c0d642c48003c0d01100e001b900c0f0075070000b007007885140002d8402c00d440e1a0300201418050981d1145450b050701040c11060340f051654448551503403000c8d0b07001c1440780c150540b0702d004e43c9010308 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 125472212 1250 125470962 125470973
    0x50708100e011502010e1b0f0303030408181c1208090f060613110f0a020c1819021b06070206060d0f1b080a0c030c05301603051501060903 61
    0x1051049240d40110f41e0900b00c1e0491003034024801c1024494101c031000c080c400c403408100b813080300029109071404008012141804401d50b44100d42081515042c540c500e0807042c1580a200e860b9684078850300d08100c10f11940c14449030b0000d002c0c4100183c6001d02107400b81103041d000c0e1a26039a580030403072401692900007100d9611150545d0b541081a8495406031b010340503800c152031030217002141102d4030310660001303840c851340942d003110b00710507004043c416024440702102140300000d00c001149409550b0381024085001c0f0801482c04000b4600086480706c048442d9016400c5003040c0700900d5410443d4541000d070440325400604402da580142900d2100b10003810543c00c40070407405154040308800c0204034003410346c3d035a100b9514100901d060b0a000031294401802e00105150500380301014071480f688000049040761401204052101104c040c0020b1003002003070b5018002e400d1001e0003c5209900400726403038507413490818a64160024400c008100e83c0401c003140 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 125473462 1250 125472212 125472239
    0x601030303050609280e010c182907030e090c07050705060a171806010806070915140304050c0a09020406020c0409121404050406031202010e07030b1b0702090a05070810 74
    0x144048070b43d01c540d48045d04030902500504141c400c0035407034410204c0600f50080482c0c0b92a0924100007101e03140c5940c0001520421020340041035807104105c4170000c40100010103960b40281440312040501500207180700783e0840b83d2011004001c5490002c0110420a00b8044c0000702d4005081c0103c541c1e00604a0581482c1c00c1c1d0704803090800b20301315030049030f00c20742c41c4150381c02505c590f903840e038104075951038003510307040c000803501000010448600c0003016119a110764941c94900c0015a420500d03802c05081a40d850080218515041d61803030358100007072642c03140140e190f034a0054040d040c2201c14210a000780d04150302000090b8100c1d042d68480744050814103209220a001d01c01107016640001d40c00514104012042c041c2c41c1c4514540a49698004d000c100000c8074610f848294910000b4206052040490100340422001e90805648200340c1d508040f1240c0016503248419103142c1c0e8003030b40d5001400301c01940140415400b980c035000464606140c0b040d0b119044 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 125474712 1250 125473462 125473501
    0x10309021003020d0e0d05030708070903080306091e0106030e0c030604170f0d0f051510021c0302070606030804090507081605030705070b0907050f0d0b0604090809120601030303050609 81
    0x141e4002191000711383c0782d0340849996007480707048034000fa040c0ca9000c1d000d80c0c01950100c0124080d4030014003024421030a40e030a03268071070030041c11911544140900d05101030102070201c90302c02100020f03080d49080f00c50081070348d80d030082504036018510b11b04020603441b4907400f80d0040c4040202207659001250300d0355a04082351a510300c501589800301e8080c0d40401d0000e50708080042c012406a0b4000394000c101502c103855009090200304403001d03c00380d0402c0e015800c04100501054503110010010343c8260802501c0c140700f541e1804100c9480f5042110a100c0215003880300d10641e1003210340c4000d85050000840c186407100300c0c5408404d8503503904020b40000007484851040c030549001503400710032070b4110b00f4010085a1a11042e014050066a002c8882203640c94152555801203410103110a82a12100e09201c007a0000c40c1080e0b8484804000d680d200d9180c03442c00c21061410a07001d03201d254118a00101074a0300505403a00c03410035041409103102400c2c2e08419030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 125475962 1250 125474712 125474717
    0x6050115090308180a060903060f060315091115040807080a2a030b0109090308060603061008040c0b0712110106050622090e01021b0714120f07230103090210 69
    0xf1340030b500522141c00f50640900507003020260b40300084141d08042c0342000c0d05c0c800c050500c845101083d0301000c46045100c0074040c0d0004039004042041a94401158240510140f100741501d240100b01e060007000350100000000040400000806001101c064216000035280900141c4c4805544450801d0030703407551040130383c101031800c006840c00402554094003942d90366070b42e0701a040003040120000d9010070203010006200345070900860b84542e2009180402d000c0d407210307046a24500c010001c80b0701400020010800c44480005425400c0c49107051140c401440c0d42e0081020005410448050381800001e0281e581c4450030f45034010000314180c050400620070140035042e66a12010565280801d1241d168106400508401c4885044180c08140022189a8a881ca4460104c004080601140385071410750818100300451341c049810906400031041e0500340ca5a105214400c6202072080300984410304e100000402400e08006000807034020407801181c01100b8000c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 125477212 1250 125475962 125475967
    0x90e07080c0a170703020a031406090118020403050a080307021501050303030f060102010209041121090d030209060c06010e070801050102030703021c05040305160311060304120f05090907020a06050115090308 91
    0x225100e032220b243c4503542242d00b0415401c2082000d0000e5100351000000242003410b10305c0c075048101885405103d0180c071070a800da28203015040750b841d030741c082e20259540800c80040440c1042022543e0341b8000c060080c0c0c2d0307040102002c0c1c0f9000035080e8a280848000300100700c0b6680110550341c0c043d03980802c50b000d554030100102d00a218030b00400c1d6100740742c061f855101900030700140180340c40d81d001004040142d58010189580100c4405006030301a40c24208514405c3e009000b0f440700c0900319608240006030840e08008098204040c0d0252410070414440d5000c91100d004140a000ad14a8a80941c0f0001d488202c51719954880b07200308110782550307500c210201c400039500310341a28912000c4a28440d00c2c0d81c2c091105840c000110601c2c100d0340e00c1c1140441c0d02590740000304036241a030685090721b0f51150721800350300b84002844990800e80703c802c8220721400e40c5a0160400f4074152822000301c0340e040e00082644d103203c0307500d901a0f541010003802600e4000401a4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 125478462 1250 125477212 125477227
    0x70803070f020a0330091a0705160e06180f0609070207080307060b040c0207050a030605130b04030e100206010503070b0708040305010c051e1602040e01090b011203090e07080c 77
    0x1100c12409504c01841002200340000d001c0d5131520b881d9043da200e0305407000b0340c020b0200080b5605812402605504444030306800300040280340201407451140007a90110341b5a201081a5910340da48000000d072000c13000c00500b850100241c0e150050f038844c0b034020600f01400072103031007007000b2300c4035024a1244011410381d50081100c40c1c003c00e95001120760303d082c945080070281144c2c1c203005008509141d0141d010b1030001c9102030035560050300d040700e65441c584a050140202411f840c0034100e4482001d0042281c43c4c010511840c0651184402c6281480500c0701c8000180440c8007103422580047c8000d030781c08101c100407113848200144d00d410060600c40d4031071090f540300400e25881c040580c1130880e00400941a040e00541715490071095006100005200e1010f07284008049444110010310f041e5105c500b4030784c5440000034015289940303e42d102c54017a0000029040340006000425511460304009804040e40100460a003e00050b1140c1e030007500b030728035488001c254031 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 125479712 1250 125478462 125478469
    0x506070314030c0703080108030405010819090f03030e0606150414030f010e010b0102070905040c2312100f0e0c0d020d06050103030503010504060801140601030c17151002070803070f02 81
    0x4000c201040d059542c0d003400e861104650b03002040c1240440c111000000e207001010090350110b86040e102c4240c00d075540001001c130024928000d0704000c0d521401300700030a0344006800c0105110303440000321300b40704420035440c01c01c0003044e0381c2c40342c5400d408020441c10706605407012101d00e0f070140218440c04500203420402c80c840b0000c1c61b503180c0003029244440c150400c5050250a8003621641a00e4619410035500c003110080c1c001e03140540b0401451381c036501c801000145040d0045021400c800010b060210281c041400da544800c2c0030710003101c5540304424448203030318010040344502c0d20415844d6040d20b4461071140c1c201d50030310301c1551034160810380d030281e00040402c41981c4921300034000c2c0e002030140c0f6000d10b15107000403541e10014801c3c0383c0300780890200c1d21650f07541c50004401608808070340008109110f005801b00a1485001d80d0060492030005240d4504a0082c80074072a400b1101800b10341c04040d04100203000442224040354202408c119400c1050011 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 125480962 1250 125479712 125479727
    0xa050402011409032109040c05181918050a0507090f0e040303060308070b1902070506040b040c080d0507051002031003080706110301150f0305060a05060d240f06020706050405060703 80
    0x200d1480070711510644800300b031000c0040c40c0d030240c121808c11100b554008111618080c444824082c00013034118031840f0302d806021040101e5089078140344c0e1036101d082d4920410b49800341460025102d01c1070060703110917802000d901101c285043d036046481c18521a44850143c46826101c4104c14081401d141c420707044040915000b404d00b960320102441c022500001c1103483d10030f08a01c040b46061103a0f50707402251003140c1c1020060140c0d403030f1504e03440ea4991000d00304031240b004440700060001c01c240312004400c1c8103600e07815201c61660620900308411081d000d8035151040080141903501c441c5c814096070f0b0040031840d01c409580c904400103060f0300e00e5641031101c0c0403000284040d44070210403441c448968800804c40303a43e100550940ba01554010b61108008606100700e04064000c4d0910304100c0c58040340c0300600030504000d00911403034080c800f84252005200c90020403402000030314561004148a07131501d000108a400380d401803511070400040c03100249445041d9 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 125482212 1250 125480962 125480983
    0x409060602031c1103070e040f0c030603020a17120a090504020706060501110a050303060f0109030c06051201060503010506040b0a11010f060906081f0207051c0c0b0a05040201140903 80
    0x1040120035100d50001c2e41c0c0360050b101030f60840c0b100f680311038204081400341310100c079a40c40c81c0303a095448640c026908244103031300c403d4000f543d464845810285500443c8140c401c10740380002c055055005101079241c3c80d40000e00d035070b1912015800c42d070100150f0350260a00442a01d602c0d085001021150070b1600d82c4215030260020444509003d0306034400c2007128800d80b80c2c40d10a00c11a09003940314000e01a0181036a0400c0c00080d1007030600061404512605260401e4001d031242d5494402d205d0f81c0c1c00041c000703074020400f50000031081e117038607000d4446070900a085d50302d44400a04140701e5401864000700010481310b8401d401503003001c501c044d8010081c4200e5078008055802004284102050036061080002f622030000c11503036a606903010003100c1081514070807102a40c0400021640e41c840d1480c00d6007009100880c5102415090782d9065120f0700130f0801d80b1101d00082c3c0080c14840c230300414000141e0304220000d11540d402c80c00c507905c030f400110000e03052120064 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 125483462 1250 125482212 125482229
    0x313060e060d050c0909070e0a2303060108060105010e030307050c1c060e0c0301111809180709022107080a11130b09040f0605130b1f0507020102011a030a0b0c04 71
    0x213000744568241d0280844c0c000a6845000d9603894290032502c0f03040340074410f83c11044054003400383d5000803210a07a0904080480003904192001003407901c0002d80c00705141d80c00c01c10061000b580e200c03d150840f0340d0114015800d107a265220580c4610113683c440384141c002c00c03110081c051422014a5403d130300500c00b000301c6203640c8140394441a440702181d00c01e521b0300c64241c003c0c04592041c0e030303445004080b441810400e14400e000e50b0700800b4000c80342005da00107869150707420410100780a000700706400340e200d051029004403e40103020540c444510302ca0100014a540142c409a00c1660303084080341c510cc810200d00c8403072003100c0300e10205100201011507501d980d0130017004000ea040d54108480f808407040c00c0b08640f41c5006265001c4440c145485402e80250840d01104000400600086c2e40c0300802402d94110140000c01003540850414155a0281f14041c000100c00398100b101c190441c0c0026221000c1c0d010042600000c5008a808441e00f0029200a41001d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 125484712 1250 125483462 125483471
    0x6030109051f0e06010906020607140d0921030e070e0403030b0a17070303080109020a0e011815030501030203240604020d1103010602030418020c1005040201030207020901090c020f0313060e060d 85
    0x1c10845054443c00c68541d40852000d802c001440c52000451a10a800c90369407071448060b00f20500b040340c0c0c4000c503d011241d40390300c2d400020550408501080e50304030b428240c100d103500da4015040d185d02d081040320030b4104200400115144041841d4440e0b0316203000161a08004001341e410311103504182000d061008100f440040b000540f00143e070300a40301c500300c903039840756180180e00c43c441c064400180c000e8071241c2a9402850890710041000380d00242c1c03180c230f980303a240d09103844030080c40003e91100010400d5080901035401c404030403000e0300e403070007090b9100884056805091103000755030010b00783c540702e902540401d032485d0503034070550303569607660000039501d800034052088200920351100c071143e034241c82181c820503046005040b0360620f02660390020a07004000f40e050540820a00e0f0044e9540c0382054040c1804600015440380f0307100c0024640850843c5850455004100d0140c071802001100c500b154050b203000e40040b801e05000c1196406030b07001140450b07091 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 125485962 1250 125484712 125484719
    0x1505030f030711130f0f0b03010b03010905070501050306061c0c12090201090b0f0405040617280204230403020d110c011b02030109080309010504020108060d021f14041212030203010506030109051f 86
    0x2500007e0a00e2000c60083c460020310b102054200c0380b10620040003580601002c0101e5401000691b62050700204298241080d50f0700c2c40321074800401c00c0f105c04669075803407113650703a4000c040c0b40042d482440080101c449640c2c00030384001801d0040281c0b1607400309560071999081070441e0054400900280301c041c1d07452201d2408d5a03482201c0d02110300406080384890f501c201307041d0300f400a8168104400712440c0d028000100030701ca0003089818009041c0e285020b00130600c40380581d10940c01007d8817030440c54010004000c00403000c01d80d40100e003281c03c1507a840303407080a02441e00b0040c000c1e55181d03880000e00405142100901d940d8002c070402000400642c81300d44554000c1e258403030035130707540410840c203030441c070070029800105c400540c140043d0b035070781c40c4a014a0a00301135030790a07a06140c3c03c2540c2c009900c940c80301031300720411404108144081100f54501c40c1415801d55050a000076401e020500803400307c0c5544d04000f07203203401c02c002a04035100b030105d24140080d84 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 125487212 1250 125485962 125485991
    0x4020f0303071b05040504030c0807022409040f0203060607020112150605190807200a0213150f1409040305040b12090d08091018061505030f030711130f 67
    0x86100c0d0b440318820f400440041d05040902402c0d1096606558114030209182d0390110329802010040e80c004081d0b20101d1000c41241c140101012a84101d00d52100c45000030001a5807482c5c0b40e150700203006100303201d0141c07503400544100d070794242003503084449081c41460040a803520a000c0f4040c41e20340005080e50001e0041c107500c0503250b01300312003c01000040d01c0340303401650394100003610617015034075000013500202c01500032401500c0c40135419400048208a6030644101407d0f924184030001c62001e8003024003c203010b920340c100c018500b0010040381c00392807000c580142c100c4400142094850800c0380c01505c54032500545071700000ca000b45010204031040710b018422582d00e246110300402e0b10f2445201000014540300c43c0114003400905065050309404169100d02c0200043c43d038018244450158468149020301d8907042518080c4200c0c0e02101c0d03034004000040c003083c00b8a800783e6200d0b005880d424140d125205401c0000d2483c600f80c0e1039954944851055030f0364 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 125488462 1250 125487212 125487233
    0x60206130303020c03040b040f0b0a020601060c050a0506010b0c07120503030a0e03040f0803040f090203040b22050609060901060f0305060a0b01092303070501030b060306040903030e0a051507050f030f04020f030307 94
    0x40340513031194274040c1c03200210701c1e5500c58081d1840240e404040100105845004241c0c1940c1c40b80c0d041d038841c0b00642e690a40381c580203030402d031070080000c21707042560581003100d440109940c00303500b112000c0c5a01e4082e200e11001d0050ac840d030b0b44540c40c0440074a0301f0811540103040440d0b0155050356141c1840d40c59410034059000380170700d010000900d02005001740c901940d000340d0014102c0e01c409110442031002c440003410440c44110b004400300300180100342c8601d071454003401d030b2031034011105c508680e01c0b5081075030050401b2005202140b8001240790b8000038143c00054580c19001c016501106242e024814000100d11469010f019116400d00000710a0b0102c5002640701d60055007910f1724042ca17541c0190080c0001130043c82c060304250102d0b030113070800103215880b106e8400c0c00c14a40e81d0b0203a40540c05800144e41810325640195400322841c0307855410402004c0302c44120f40304c06044150f80c0035044010138190f6483c1c3c0700d41011584001c003129a40c3c145072803c241c0700d5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 125489712 1250 125488462 125488469
    0x903070f0f02100504051c11060406080f090a0b16140d0207030e01090522090209090f0c091005120709020c100501150203040b0d0605060a030506040b0307060206130303020c03040b04 80
    0x2031001d01c0c1c0c0a03c80500610684007034070340c02000d1070113440d074a0380340079080c00b03480e102500d03a080c440008544648902005001400c0380c2d03505d0140354a8a007185d641100000381c0391135282d42c03000702c204010582060703410390808a541c040c4082403001c420200d86480c144a8001042c4400140a041100da03560080200341d200740c03240c3c200711039600011b43d0115001c0c41640c0d00898000c002910610080142c0c000600203004009400102e640206a2160b4220381003040e0381e0003000c141807680300c1000000740050085506298910305907481806c2002d5612130301b40201c2d07031307290400744500c014130450000d800c01820840d201e02540394150743d206d80c14003404014a1400b0004215042e600726090000f40064004514080c5400300f5124164820303070170340591030741e2440c02180aa40b058001c220700b5160380c0e00401c4908129040108072041d00075001c3c0700ea4000103040212940208060780c4c02082d185019544c0c1e982ca04095000e4030501150980a000005000ca961141e090162054 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 125490962 1250 125489712 125489719
    0xc060b04060b0d0b0405190c031410050a08010c090308070809030a11040605010e0604061404090e0105040b06010e130e0a061b090806040c0b0d0e011817041802030903070f0f02 77
    0x14a10076040c007048400990342c84011401d0403407185031f05a40d40e0800f0043d0a5189000103041440c074844d0414404140c0d00b10b80703c0c0d4050041003040c0d2070f160a00501515021000704150210043e0281c8150501e01c8002d1600c0b60100e03030755081c441003801b9500e50b0703840034007660100350140c5854000c41d08842d010754801c6141040210b10b0394840c401c0790b00c44d8440541100d183c1424020240e5000504140106c1401801c20001c28084601d000d0034800c92151030012495080c5494201114000107044a04221100c4002c500caa5a2482c420000b43e5021074001840c0c00c41c490304600380080c12030080d10b41820058491842041e49400b04d103106c02c590b48000350390b42c66030345240d118101910301500d50102e55805005000c8030070b008019202d00060700041c0312104d04901403c0d5000307903400b4a0103d86014281c030520081c103101105400c06401c905203010704001c007241e07141051040d145880c03540440010b54504082045031507054010003110100f22881c602882007030b0150070101e02 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 125492212 1250 125490962 125490971
    0x507120e1e04050a0c0203030402130b0d0b040c120519170f03011a072609040f0b150405060a050d0f0e060a0b04020a1706010210050a1505090f070c060b04060b0d 71
    0x2400381301803140c0c4015164590145103543c54039020009900088903041a2007583c0b40c030848001d544100300d42c43c02c5131080111113131900d0503040c01100d000040d8407441051782140007a500160001c02c044140d0b10042035907000144e828200400c00d1008411012001000014030401403141480914121a004082c03112003d110100c141c1181c0075908009000c2e001100403200800503401101c15002403221074281000401ca000406a6402d111034001403030b80e4180403015414205500c4071680d82d00078102c0d140c14600b4010480038807032185010200315001c01c1c201c030200002d07006004030010003081440400b083c00384484c0c070f0381c100342c45540d10185000c12210703807402c01c1d0090b41c0d148140740d1100c420881021382c22904203040107103c0340c11030280b442e04402a05840c4500b500070316000600040961201900c080c40040700d800c07041c813070820481000455401110000c4d0b200d2081e141650f0101c8052500c2000b0304601c0c004e0a902a08040010451112907405010018081c290510 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 125493462 1250 125492212 125492221
    0x10e01110a09150e0d0c050f010f0f050d0912050910030b0d06050a090f0b01050a0501080118090813031b120507050915031b03010c08070507120e1e0405 67
    0x61003440344041c404046120035500b0444242c21a01040800749a400c1603202c10f92043c000030354002004400b15151400c3c0c02c824800c07420501c62010314154282008803054440c2e0390058203004840b681c007401c000e0002034182c42890b898110440c0103a00c86903800c5400070b034140c060003d810000580e80201046404101550300c0f038002c4480707207403001e030407112410500c2d01d504c0081c24001308420b17022078a9480c0c26000500d05088165941e010b400c01c40055414982000003e60b040d62025040000c1140140304008008080d210350103020701000a0103d59882c06120600490701051101c1c0b105c21000018001c0f490101c061150320024032841d460f0702d500369000c001803081030262055001d00d90030300c180e003001d5161503004100740f0b07151042541c481e400a46450040c880700b540e0080030f80441d0070581024041e110302141907052424483c0303030800000b089d47c000c40d400035081400e40c5403100c040d13501985102031110b10241190129005a0454000c409030700042c29001e5443c160024 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 125494712 1250 125493462 125493491
    0xa022709061816060f361403030301090504031103040f06030b0114030601120f020d0b090601020307050a030807031103070201020304050c031f0e0f072706120b07030f0608010e01 78
    0x359050318011402090605001d400c440051045c0c2203282402005496640f0fa4040d03074900c4001100401c42c45c0c06451000b0028610340000b5600042440e480542850f4450b50040144c070f05580c0c03c0900010345503903e081c11503101400e19041d413100d02000074046000402008030300151040c40d1030030300c601c6417080c004452000005150000b00181480460205e41c810f0800b015a141d0710030001c0340d0b000d01440e0100487e4400e59440c0030450b91040e000031035080c08008c99030700c04824000780d8141103198641d2616034202c5a0020100140000042c41c018025402040520400c001140c1c0301d00c2c1c510741c041c3c002e42c4283c034156864801c2e036118840900c2e0000300b00030481e082d440004855a904400c2c40040d15204d052003001e40201c0641202001081010000900d20100c0503104507458a02d41038404402d0b1660100031810007000340050b40081d0f03210301403507a00005c01d4103242d641050840060421107a0101303007a04100300041c0688054000441c80c41051000f04803120504c40346 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 125495962 1250 125494712 125494723
    0x30c06070e0904110d02060d020903060a0608070b030c0d05040b01031515061d18040201090801050105150c010914060118061809020303040305010c03150b0c0a0227090618 75
    0x1110342c0103aa030b00010b000034400910803224001d001d80302298050082d80000c1058200601498000e5030100701607496141c20880070760000300303c2c0030420080b410900c0e50340d1034020f14003610b1101180007001c80c100e0042c0310116609a540c1020800240c10709192582120303000380b106641441d07203901c4070308001c0340601c1080002c1d8049892542181e14000058072500d02d0822450302803003182020f17600c10344400f1210300001c000050300032064036040c03001408540064114100304da14007070060141e5107410b40d94645411900b8800785d100e02e6a50000c1d405043d207080010965039407405075105075100040c116069818410024050481c5105a50f08035444e82c4a030840040074507034034843e100c0d0f40e0f50110199074000303010781b86015106d40725103003559164420f100000f1340d120303000d40342000c0600d0f518014207200c281032407401e06c10986585d607585071795101912480a0094215600c100e081420301e54002c8450f081c584e521f400700d1402d80310034080358411540c6424003188c00d4100c501050 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 125497212 1250 125495962 125495987
    0x10e030309090f060a090e030a090f030c0501030213090c08010e1f17010207080a020319050903100b030319080907050901030b040f080d1a040f021602040b06160302030c0607 76
    0x84100b46a0352040e05207500d0101814681e040715030040c3c00300711480c0f180280b4004201140045a4442a41c0c07801030174070f0780c4c5134020210f41d11082010f100061210a03000103c840910700542c0320312025072000301400d1168400a03c1d030b46400d24594406400080c42030403075203498803100302603403006020550080721039001c950003501500180104020094040408110140018245003090362040d00381e0303001249600250380007103078003126003d501c001450320480b20301d00700341040421b10109959444600b1f508000f036464406c2d801e542e450400940b1014000c1c0c180040c980030781003201500400d825500d1854a0082c03840206190030000465812203912002c900711a43d01c0ea1a07441c5d907081030b18400c0fa0091400c10a10140d80d285015280d03045e031011900303800ca40105402c20044074010740240822500500c0f90030541425000001142c81d016240811000344080011b8a1840b48241c0100c15410f251845401d1550000240525113041000c49207152200001075489131052034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 125498462 1250 125497212 125497219
    0x170604030801090e19140d0c11010201060315091a0106090512070e01030305070602071b081005070906050d0204050301090c0519050d140c0d140d0e030a0303090317010e010302010e030309 82
    0xa03c0c00c117400d0300310b0b12140801d00402120b00021802c003600d03410036550090a2001420010403070b000e21030041c141d850b0001c0240000c1201d40d25641d01e280d11403200d1401282e6183d590b145281c20f10100c458003140b05421075013009020340e1600c0c800340100206c1d0242c107028016a0040c601d000900080311819a00100000715880e0b00c0e556084482c1d034004001196899000e002c264002081405000500d0a02c0302da1503c425040141e01417500d0074140d11405514208000d00c51580e80100d07a01064855038030300150b071040612401c1000c0d1160303912094240d0f107070000f044140314a1280c1d100554004581807999400222103122000c02e050003180d078461442150f00002802c040798940340c00d030030320b01615007680701000060352071181300d00140c80300346080c0c9000ea03140700c050211050010881c100001100703480c10100c2c2d0344071100c10004060581e039003500001e00d8020b800b010012070645104040720741c0c40300042c00c0221428401213000c075140c0c035544803607890701109542d45044080c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 125499712 1250 125498462 125498473
    0xe070909020a030803040c03060905010c030e0a030807050318070b070204061a0f071112060402130603080301121106190305010509041a0a0b040e0303061005040602061807170604030801090e 83
    0x10f40700d44c01103602c040e0080b03900044114000000601c10301507542e11900803000041c542d405c510307002e41690301c800c0c45c4040c60b80040020720002504090041e410a03903510781140c4a035101d807000d4030700c03540300c2e01c41030f6592003087c0000458090304001045c1c0c0314400d40c0c2c18000c065540220000f24504160f040c102194184036000900350248090720710f29006240e14514203410b40042840360b854a403050515410440400081d802c00e110210301e5101c03009401c2115502d55181c100c410301040c0035284c002c3c0c0c0095440b40510000f0f80c5180005100241007542d138101b1038006c541032141d41e049420100e4205400040d0918029840743c3c403541d001181094100310810080c407616400420740d029a40c0e413a01d039030145444500c503000c5080904002035a490034140d0811000340001d81400041000401041c0202c503408160b06d03410800d004401b025050744200300b58203000036a0403160b1405410052040c50700e400107513090086000303469020180c1d80b1031040c0c07426074500703001100059004 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 125500962 1250 125499712 125499719
    0x20d06080c0111060c21010e1005032e021e1e04060f030b01170106033e03130209040f03030515010f0e1324060206060904120507050a03030e070909020a 67
    0x64200409011b0710602e0416030340d0307402c0356403100c5160080c0c01030784131400d0400410070504107800f0b000d005840e040380180041d80c1124120f43c01c0710120b034418142500d80c500d280201e480203406980903000c0c8649009025000c1d803007603115542004c1d50741d451b5200e106d50042e81142121003120156040c581d2110540070180b00154064004019410b04104182c4100e04014100da00e140380079019030f55011403145007220140c6140d040300e5a044600418561011243c25480e1030300031001c00120030019240d544d00d4881003400340c02c0341d001941101004d030410080149038440180c000e07101c1e80b402c128079164601c0c000414100d50080030301040c2420707003460b0014001d0000100c18840104001c0d808251a075440b030076521100b4514a010700440d80007a200c03400c8000c070b10081c1c841c502c001d1540340f07400f01c002121014058009400c01889103140d95100307106804565120340c01804440d042030340c900d0000c0003080801c0c3e12803901c1c020048003080000003405940703401a0003d001e8802c0300c1c04d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 125502212 1250 125500962 125500981
    0x7080405031b0907033c050a0518030f071b030501050906160c020f0111010b0a030c030515070c06090305041203120605100507150915050105010306050609060d0b010e04020d06080c011106 82
    0x1002c2802d902c1d091030031020380e42c6c1241c54003c80b44541d050080209281c10030007136100c2030404104050400e504144100c883c00742248050720b81e429041508000044102e2501c270f00c2402181d00080c10799420031081210010001a10030700078100c104034070f090b985840904854500f02c1d2000254003000c0c0c0040d041c4950310a0300f8020038a074450b4000180a0649000100e400c01164821901c107038041804006018050285603050240c041552803a854520300c000e140c0c0800304001003005565112680601d813140c2c0c20f8a001d000c185c1c00d080052021800c02400d80412846141030f0103007040d00104041c1011118003c0d40a500d4071181e00b1700807150b44001240c11446201d0881c9680c8255020109d00b101680003100210400001541d50418000400340c82035078101d035000d5030341003081c020140c031607400300d038030884404c18006021070f901e00040343d00101c2002e58039407090000c142c1807900c9080b030f40b0800854144008580038800c9000043d034083d481c50210f182681c2101002614124 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 125503462 1250 125502212 125502281
    0x121009030201020c010e0a060609060f060c050102090405010605030f0a0e0d0c05010905030406050a0906020a0f1101030b041a040e0c09071412040b07110a02130207080405031b090703 80
    0x30300c00c1c0005801c044c1000281821202a0319544025510010b500c1061104130b11920001d0b0146440900000c2d05101c084000c10074548907040400109020140600c0001c2d4160385440070020000d0181d943d4030704004001e03400603100150790000900125a00c40c4062051400342c462030006805c1c0c01c01080c0342a00c815810706000d940c5952aa84005d0005405000a001401c283d0701d8803a12410241d00082c5031116039001242554000358003a000300301c0c020114400350fa800f249030340c41c0031043c03001200a883c00c982c951b030300a0b040482c8241815540c0c103280311884030550301005901d012603040e03580c4012280080c0e8201806101082c0106d20460840b0365015442c0115840c008182e840c0030400c41c0216019180492a50b0600c100240e000651142d500c8510300108004840c1307800141c5050b4078003d08000702c65000074948100040c0b0001e81d401001e00030156024170300d10f000b0505054400f0b07100036100b0a031400000320b000e40a48980e5035507040c3c01a6211b0140001486198000d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 125504712 1250 125503462 125503481
    0x72606010f0b220602011514090a050c130b0a1d0616030c050a06050601090834050a0e04031b12050f0702060703031b020a03140d061205030405010e1210 67
    0x51070121414641c2269001628018070396075000088004549101647c0b000341500705182c3d0100c000c1d2080c003c0e958100103190089080000081c150301d0710004025184640100070003982c0e261503001078801c5140c0060040009140c880780c03120102c4449144560940740f5003558030078411b2180030001942188076014072486400d110700b08081c2034031490700d007004040c0704892150700c800401499507407060041000301f203401c0041031155211a81e03500c400d1441c0041c1183c484500d100e805503e0203a040200c0101005000540e80170340721101c02d0604101190241c01043c48a80c812695242c110082100707076410018800c400030120301c2c00c1383d82e80e0001c0300b4040700b80c1d0288180700240e81e401d0020b00c10346100ea100043c0d030b003000110322422110440101000c0d504802c01800100b41c00c1b84040007404100548155074205081000c0000d128542041440400118a80f400c0141c000000e0058660980b50824400c0d031044c02c00000030070b0150a414250007150080c41c41e144180c0126260703 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 125505962 1250 125504712 125504737
    0x6041b030804030b01031101080c18011824090303050a0809030d0f090b0601050306030a0b1b0a0527060706020d06080303070e27010510030905072606010f0b 69
    0x4080e92078031681000c0c0c215800544003031001d4070040041080d0010141c98081d02803c1241082c504102c0b092036601402c0d030840140b411860520a45a210305d8908405c0e040108107050460789910f030721001c42e03c02c2c086e40c541c09005191000d0180d0f00500c94541101d41c550340e282e20385500f00500711410000070b0500d041350b110a02000c08006028001d045100f049c1c410000380084543c10410501c2e070014143c141808810414040c41e0303203000c03d0500c0110342000c524107040d21401d690408003040e1003291900003002040b041c000301da02c2801000003130f00c0074010100581c5061380d4500c901c0c48580500b0341c8488100062400141103802800341500000000580180d44811950640d40200e407481d000032030103659001c5c14540101c0d105c205070554500d03508500c5100d1540f171003076241806054800d000080b0b4142d95640300b90001c540c202d51210075204101d5543c084140e100c4242600e44c3e00c08680e8121001c495480010442c0c122400499100b0000e03140140384145503001c038104400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 125507212 1250 125505962 125506013
    0x3020105091b150c100b030c010c020105090d05030408100b0a060807090608091c020c10050306030312090f0706021f140c030a0e0102030c0703031407050d0f021204050a0605010b0c0604 81
    0x1030035136081c45004000c186034880860b4040c6110209030409244501d943d060107056802c810150340d01c40140d410744035064030000003000c194113003035181d405140e03c800ba15228101c0ca034000c4558580040356800001c1c1c9d4050207050329030b0003c0d240840e0032030341580081c40c00d0004103d000d00ca0180141c0000c40c11069400c580400e10640c600f600b031558104006d40d00104100340141001d00c10007800c182a0303d003c908600300341740040d45900c20180341e0561310011201088034054184448038070710f0f444004450219a076200702079191a658001c40030380f4900d08104904459040c02120707a00544501d02014035501c40f940011b860b0005840d103050b007079441032045401c0900b44020340c010464481c1d419210340c50bd103002801e40384e0380200d607140c3e240f00009019065070040c1c03c1c0c9442d00000d45010a080c13002088802c024001c22991000b0031442c001480148440400c02d800d4443c0500014444c9070b80703c03840c460b005d2007031400d442da0652001d40050301084070000084103150080c0b56408 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 125508462 1250 125507212 125507227
    0x608040b1522060e090718050705040f0806010501140903100c1101020703090503210403080717160218100506030c040e0f070e10080c09030a020a0b0703020105091b15 73
    0x4070b152000e0601c000340d031076a0390070500415412100103584041130100400c28a0705010560301c000c2003044d4441c00c425200d102041e14140510709680162038000c2c900000107965500941c0c0d13580c1c0178460720303003c9514826045080c3d1031010803100325000190003440f11071051904000107180740d00c0031404001300016900785052082c0010507840f8020390700d40b46200e04200805050044e980d031115020714025400200342c0c0581d0703003a5000c032a0080d552645644050600d00042c01500040142002e00040c00d5606038040513004104e05000384c407404a00c1154500c21000c1d000152142c200508201c5030401c15860003200559100320000c003201d040507514501444442025903610400101c0142081001030f2301041860410108617403071000500e00e0040680b10355400b41544030a09000148400162010820081520b07800b81006c0c55650755080e050700c6e82c2e0052030048005508001c04241d80020001c0e0070064210f814412410284000040110b800941c00011003400c070244400d0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 125509712 1250 125508462 125508499
    0x15060f0605220e181203090a12051c090308100308040b0c010b040608010e161809030309050a060203070905040203041106070311010e0a060f2a09080a0c0503070608040b15 75
    0x2034007803d9404e50394610041130504550030280c01d0b185000c010b0b4424010000c69038400034682d4259a04019040240300c03442c1070444052141d4107400c0303401e01e0300001040d4000300d20781c030800c85107010b81d0318496161205c0800c01c11035042403201030606034091000f8001c9130701680090003410b041200024240c159400414180c6155600160b4680d544000c400011041400f01190068019480c400c143d400d01d540f2400707589082c50501904c0c2d0303551011004250003940324202080d0042d00700c81d506001c5140190213548122001400200620300004143c201402640c0c01654440e001c2180d000415080c40318503080210250304000c42e02c019540115001e00c41e6001204080c000341c1310201160900c0c00985e50b8459050b40a5860907204002e5400e03148855100c0540303052061901d00350141017114001002d810120b01405010520b008000c400d1b055101255815400d9550040da1040b041c0c0d51610101c5000c2c0c901c50441380040d9420010183c1240715003070042400540c00c0d01c8a080c3c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 125510962 1250 125509712 125509739
    0x6180512010209030105180703061d030c01060f050d020f040906090f080d05060a05030c0d0c1d010807080a03020d050d1d0309040509190803150d15060f060522 70
    0x396501d950000d000c5001e42001e0141c2d40c6d10040600c66141111001c000c1d0b190303200e61a11000d0103690fa5030260b01c031520707046401c00c0344059407013040360f48801845145034000c05541c85110740c91074060000280608004a0030f880d0344da001028581c0210b100c0381400082d0034038a404650315980d4240110020b280601811280e901034107900303481f4494091000c0c06c0f2000504030318400c140030041040f89030740006000c100418141d8202041c400e062400c6069100d041c2c0101080c3c1610340403c034180c1340781075202030480b8044403c64040540e541c40042d10350311074a07070140041e00035000030242d26000350001d282c2e10b0160000000c43c215040c2059801200400403191250000070f00a155880c09002d05c5c1c0c2c1203039003007011380014101040212282030217120020280307a03005c000692685425680e07000400c50103044260345810614040c8402409032007a61140c03850418041130094610014074252005030b19268503000c0d400d1702104a01b501511040c3d04c0028210300454200c440003070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 125512212 1250 125510962 125510989
    0x50703030206010603111c09050f030d0b01090e100e04110306010b040302011701060818030c010e0607020f0304050108130807050106030b1911070209040203240f0c0a09061805 77
    0x241600c3e5040c5180201030b103450881914202c201440314032041800c0085040200e000c00c1800500300101e0f12748903060601560035001240001305010462541c0c0b43c024001e081401d03078501e40ca540c2c031120300f0000140c086e02e1500e041e40c2e01803000c1c4801364110b07170402d8200f80180003580c034070100000000c0c074222003608956071041010404008550b0000c41200c03100646000c8191958100300c0c00a240050041008034800d12400410380204018000c0714440302c804802881400100e01d001a521142940c020006101391040d10016420204c01d84041e21030507500d150664445a41c5025035440582080d95442c0d8101321900c0080c03001d1149000a600c0b86960007818604000000512000d500035080303c0c07410a0004800300f04020b04413210a6030441c0d12034031070b46460011a103042644070122603070581c1484c82070b16201c50f400d000c620a42110a030582c49070369990601609005006d0120081100b26505200c240e010380e1491004044aa8003002c01d1595440040d000116002 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 125513462 1250 125512212 125512217
    0x1a15090f0f1801060605040f05181906120803010503120313020118080610050a05010507030c021201020f161e0201020c100e040c05040f0602030304150507020a0f0813060f02150c0705070303 83
    0x2e00302300e8041340c20404001000211007401c01c150305c0c90103c0551000080c10010f540c0c1704030084c4003403c0007070b91206024000020040720808807034940011664030a0180ca803213403045200d08010519860212441b8103030aa0341c4440341152a030040d1861051589520741d9000c0010010030424010000c01d482243c0c0ca12488003010725010910041014580083e410030004001c5000481c0e0400391220109034103946264000c121890358900a00480b4100284c0c0040010070200e454202ea0005841e64050307400d02c15045510103074200d410380081c030f0090250b004044200341d039240440c061048038485040c4007611801007800581114400e0580c01c0100d940480c0070b00a0054120802015042e03a0004510b5410302c0d440c0c41c3e07c0d0180c40d41c0705c1c1031820745600c00101345c1c620038881e51610f0b9900083d4400d00c80d91038079080106401407000601b4070503584500003811781c41040402c07803e000d00d03006040b8480584010429085004101408900703007007054034001001040f82c04003c60003503 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 125514712 1250 125513462 125513467
    0x20a0f050a1a2a0403020901030b10050612010e060d23150114100e040c0503011503050c0a1b02120105090706030501150f0201091a15090f0f1801060605 67
    0x51400c45650000155880b05a07000d290400a0340c694290070326020040c02c821040ca000c00c100c152803498401c5400c0250041e900740000010403465242c41405404402d0f0203031041900c070028003806000341c190305889200e40038010005c83d00c84a00c0d05400c500c1c040d023a500c0d0701415465a59003000030000c0340d200f40b0700590103002482014490840328005900b40300d00c055140103821004151011811841001c41c0905459080e000b1a0010034009010f4401c5c0700e1008045005840d5030401d1250090500d004585025454071903c241c0b0b12400c0e000500d80d0500c21016402c8070713000d04d032640311902c035142e16200101503565114050703a404003510000ca803925100d28035034202421341d07001d0000c0c5801c1c44010320000c405241c40083d0603d00340b4002c82c2c40b1141e40001c0f80901581c00000c0c2c00606c410246080021484500b6440b0f58503541078204400700b06800d100d170f50034040340c0c0140c5c03111890000c5064850350303266294100d140c07a2191080c3c02c2c0c4007031a403030854040c5c5d881a0081b4600 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 125515962 1250 125514712 125514733
    0x30914012901080609010e060a1805060a06080402090109020904020c060f041101020a03050a05030c1918080a0b0109050403050f031006090e04020607060527010906240e07020a0f05 79
    0x300207003006404400e02e000065403e040010a50342c60040c058411400c3d44540007400b01d0300c4100ea13580041400340e1800000310301c018030032001024182d54560040305440307404034001e80112501801282d010301544e410b0703131a02c00010000d40020085035032254080002204c0d2a5040020074001e103828000b85006050500c0d001e004249061402410754103c1030b140b40100b900001a100c04039524241280d50369200d0501c0c2e0421b100ea0100410340110704445614502d900c80b00d03180c1202c1c190070082e403010f0313103c54000b80d90b140071801c003c2030034116000600403200aa040290014843c0c18400d0502c070300390400c0c10071604211121804038810b14010001240c0c4050b6410013011644c0803044c1d40c0c102a00070881504c940d00002d4000e0f62550041140500c041500b034030000d405111041004901c0003540c1e01034420b2050a581c050b05001141d15044100140f001504075940c0c201710781a0320f0982031107011400142200d0079401450410b0000c501c900e039003440210b00c64009880302640 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 125517212 1250 125515962 125516021
    0x20306040e060603030322171c0608070909050a0b010b03040b06090105010e0d0212030c0d200c12070f1508090a02030706031d100501180e030a03091401 67
    0x9070003695403035221409010050703c2c00700843e03030400401414a29080d185201f0101b61511100c0e0007015480c0783d80d02d45411442540107005070301d880700741e20709840740400e030b01740280d448038003841400303400ca08410081c40b84240d01c0210702030b118030107940034001e007503c4000c000e8809900c10720070720b000001000104112010380981c02141151140003d504200008005540c0c083c2913a01a8a00346110415503a030712541503440c0000320212540d80701844202d40c0c540c00341e0030a00c0d020400c0d548890000034039003582c03440d500c88010000e000881620040140c0a01c40d4a088a480e00601c04086801010884607402404a844420750b2070200d80a000306042001000f4020075080f00450600699000c110001218010725000c1015006d180b03442010042400700d00710f0b584200d41260801031110f80001c1e040701d00c00030f005184440b00d6511304041e60262100203a298004200c49010030303000c0e81c022800b4a00906440005505c440c580c0c1d8215115512040500384182d070100035200b5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 125518462 1250 125517212 125517221
    0x200106051c05030a0503041110030c030e06150411040e01030807030801080a0b06060f0408030c0703140607020304090c0908030a02012708030c030a0b060406030c021903020d0f0306050d050102030604 87
    0x400c0c8407420307000409515019101d01030b074009401082400808103051001d411010185d0f024018021500d03d2501c10010740108003080e00301000c01d082c92088c075100f50012600910407106002030b0004080084100001003040b00005058140c06120102d000e00d0321065540c040d5100d010201d039030700c2c90713400d000d402030905900c5030b8081d40c414100c074400200e41c00410340d00082c6c1541c607141c0f101c8400da219482c40c003452b00528500d22000c1440ea030751741b4000038501c0440f4010024503076018a03100c07259403039690484180b40035038000c000030401083c0d6980210500505403a040307100c26120a2040e0079079112140880060b9101c900d0b4000c8040702400d0645014941e15589050f403a030743e0b480240c513000091484248240c0840081d241d0351943c0c104220b80f5800910340703940c882e00c810020b001041c0340002c0c5801440381402c0c1c0110040e0f104440a48150141c00030000c08071503110403103141000d8034890080589500380021036444c0d11500800692003140003507102d00d007080c01d00040342c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 125519712 1250 125518462 125518489
    0xf020a090203060f0f0f03010218040501050111060f060a050a180506190306020706060b040e01080c030321100e0709050f0d1101120b09010609091401060801060f20010605 75
    0x1074410000e0004031344d2450449540c0b0304003620280081c81402000030141c01c2251140754055000141084609000d25160101da0750115410851a42c03a03100440b501d80d040390007a80c55a02200c0490f40e4880010707049503000701d0003440d1140381a03d80d404143d407d0090740c0901900922101c1d840d0038407140d401407a90180d01039a2080e13400d60b401c072014014050078172014005550014020081c0442e03a0048005008101c00d81c90f42e59a46101d11a44000248206199070103582d4040c603091401204507204500c00c6002454450303404100c1220110b0040c01401510401403030005000e021844154401c00c0907442d80980c0c01d1600c8103203d038030322112000a114a003500c1c0f8010004514a030001519202031800803140310300403412000901524801e02d41c030001e8400005403042c2d03c801da4070305a0300394201c00d1096401c000d50701c00c014a400c0c0500c1c004103203460010311038648a42c00c0701030358400b40d240000302004080400d0440101901111070180d450b0308060000323041625106064 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 125520962 1250 125519712 125519729
    0x30a0311011d03090d030908010615110304031104020a1b0305031e060a09020a020a05031602152706120f010e1b040504020901030e030d1e0903020c15070b040f020a 72
    0x1c80185142c1510791081d034461610840d108903040c41814482c111190103408084c000308961030300e48420000b40100350304110002943c0c2070702c1d0050300d04080140c07012a907004006c0c148201a500410020750441c07031a0404109100e035400811b65402035103044580c2c000d884255490606541028600d480001464242041d100c10312066071140f2401e40d04880c00040e0068668030700e114102e040003d01400a02648008a84591a044003020320204207100b191444100300341c40081410a01981d41c1c5517000c8d139000300740381c1d0341d0541c54030485e9030100006001510340780d00000110f0410a0940c0c20080074a90300300103022030b0b981070540d65000b0260301301d80308200800b0004000d0900c02d601480f4040c42c0c011890080d240d000e40c0003d072480c100c0302c0a03242c440155001e07000007054501e600141d1142c2945110f40d900c600e500c80e040100740c05501800000348828180b103148024550400840142000190701241586080c07900441c8105c002c4000040c40d030042100c0c0711055006001ca = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 125522212 1250 125520962 125521001
    0x9010513030c110d020a1e060f051b1e100c030504020a230d030f0e060f0403030e0a0b070f0b090606100804030306090e010603020a0b122202030a031101 67
    0x1c250488038000000d54064203585030b00c016040880c0311242c0302c050080d00b1041c000c0f00401c005290030341000407656101e41545002c1d5403240100c40210030b0350200f8000c21020407060038500d50300e4408040c001814404c403104035803400c160905900c50541c1e420240e41203610540329810190103500c0750384406160030320a0b802c1640000b80e500301035100d44000015100c0300ba00c411209500d8071041c287c0300811140f00c680090801410581101d500701d00090011420000e89284c44000d0315000c011031039580e4106801c5a600fa100c100c12103a51961007100d601002a13010b2401c002440c0040c4a01007405200403a40340c059172440003d040510300e0b0304210704100d001d86442050301c41d0140c1c1e07131518102c1500c0300d08040d0300400d02500a840d04034203141c0c3c0644103460541100003240e01c2542d2484229a48400302001d5000e180070214103244c500c00803e500b00e40244900f04c5082413811804002c020590020780b50003404072003280030500b29107c0000c4280c080c0f06080000081001100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 125523462 1250 125522212 125522251
    0x40b04090f060f051207030f060c02010b01090e1503010f02070602040f0603060803070602071a01060e01020d03021c0507050c03070f0b090303091509070e01120210210f021908090105 80
    0x50391500e80d005560248614824407000d1170801c0080900854224110b901c0c0b040c90b504051001e400c0c03081e058400b45d0b00b40100f4600c030307510400c0100d089802045440036a0307112aa200001d040700c00c0304456240d9261004a40c00c0451407000300385451007404016592849d00c10010803d40c03041c0d00000030b142c58a40c040000e104040201e400c4590711a40c0182d07203001c00e1034181304810301c2144060f0301109000c000714210b42c0181d550f81c02203000740c08480c0c544c40c4d4900c1c11402d0384610503440000ca400d42c000760b030354405141c1080350003020b1b40c14034508254004100302c2c9113410055003680c01d5500c0b00030a03402d003c01143c8032500007100d81d0245d451880c20105a9a031400741c442211280c0d86403034006024000d00b800020040d0540c0c140041041d6581c4a003200040d140031000c0c0e00c81d60130008442d4445004102108038982180f004422a40c0300345142d00051034020440d0180355000c0152410880c482940c070307501d9100e1a20341c801c10382061008107084880060880031003d036203d0101 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 125524712 1250 125523462 125523479
    0x1501210206030604180b06120f1b030c0d060b090606090d0b060a0b0c06041502070b0106050c030f0408100e0303060312070206040909080a0f0206060609040c03060506040b04090f06 79
    0x111202a016149a652522540c0100e0001e00f64441d9000c43c0c030040d142c8090130085004005030194404442c00c00051071100310030381d21120780b0460318882d40c0c8443c0c0e81c0c00c04200d9454030b40010540007000d90b240032803d8408140040c48400c400c650390b82da10f0075000745034035200f041d40d904030106807030182c00e2102030408200d5000a80b840500108190b07400a0026601e030507150000c0d1552203840c686030310002c11000d9580000707031011100003d115a1500320b00403180b0a44142c16003000400c9081d91030700400b51200d601c10900194180003c114641c499140c6d00000d20003820814002c200d504030342d1150108454486012800d41d40082080c861165400030341c542d00d5014001c1c03110341d600880d200184613841198482c6031411b040540100904c05944040c004054081e1512448810340031402c03600c448040b600300380d121800f401b00c02911300301276000c12085c41d1039050002d8010b482c0c0000422941184e4482600b200c40000d0074849043e460103a40319109800380140318075410b0030585c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 125525962 1250 125524712 125524769
    0x106020f07031709030c03071d0105190e13050106120b090d020c0415030c06020325030503010621150f170616020703080a17130f030807020a080c1501 66
    0x3840000c0d00013055181241d5014800814194401012a6a031b140c0d1843d100c05002c4030f050034440c0f0700b40014000103031410400c200301100c0c1c01c5095030b02011402d00c01412445038014103907036041000d1007101d01c0041c000b40301d1080038000e5581c44a001c1c03a031902e851803641c1402040307041150050b07a9003202550f00021002000c55088802080e807100a2a00545040c05544081c24009902c0340000d0180c0d00400100011000450f1048207082c0000a0402445492800900041080004000151142d240c0c41000140f9000f9500d408110074445419a1085d40034000b041464904c00c01607405060901d900074643c041d00101c10143c48828582c45e0034004007e540010707155108410028030920103c40910381c41b04029844040c429402004e005030010500351280c56600410204484106501c2d200d540c0509a00d581c2c034010b540480300e10401401182c158810b000c020307400076000c940a00003240480c0d000303003542e0040c1d00511101a0040e8491407181c1c000c1c0c1c2c0c04161801c00e0510 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 125527212 1250 125525962 125525993
    0x20901090b19090c020c033f0c01060503010b030708060411030f06130303060501050405130e030408030d091505090d03050c091003020706050f06010c02150405090c030106020f0703 79
    0xc0c001203084045010810031010082d41c019180d1030b0601c00700d407414a030f5124191499180e421612940c85000500d40e94084080000060310049481040c2c0c00d90070507200c030285601141c00c1c1081c08004050103100750801800441140d449075000d02c50750509100b49000040c084009200700c62030188403a454400181000d0a854082680c03803107617480030491b04107080c00b0541100c5071403400c0700321103d444030100c20840009041580007d1a9845541030f035050b03500041803482807040e002101002840000d28002042c041440001420b100c00d00c0541000702c1c5028012408250303914144408007000400841071518182c01e04c6a1070500180001c11103940f0300b0000f55136195184103081500030b01c40300a0b88440044a40038140368550068500c0512900c420303c40394454519015510804031501c1b4006290018448054a402804818443c0e91010034034901034583c1c0206840300f604440381c15960400000400080342d0420003503032211140c1002d0003100713007151764504610100340b0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 125528462 1250 125527212 125527229
    0xa0504051b030f0108070b0316050903070512030a0809010216080a110a081c0c2115120203070608040803060622080601080705041a0108041a010801020322020901 71
    0x40004120040e1080c030500700ca01820709840d00d074580043d0841c0240320900070102240162034001071281c03807050aaa001c0e034047e2020790410450701c0c40c200d400c0d41050260030341c10702c01c0040000f0b0949501d58240c0c003008042024560300c0310072040c0034100d80c0c1d0103015201942c0c410400c000540b4410941d041c46203a120401c07940d10a00d09000300c4001034204410708440c090500a5810401c0041c014507400c0300d400c01c0c03032140000f000c0c424002c580302c000e4142d020030652080c00c9c101c0b5503402c907024404810110000b420325000195811f201440d604802c2044250303eaa62003036103000c00c40003005000601c2c00035202e182540d01c089c4180005002140140c0d030125001c0480700400022480301076282a0040145a854410b81e50307a1000b0321904800b406403020210b5542460301800004044190800020300e01500045522003402403080e150b80408207400d080300000e017802280203281d0318002680f00c0c10140071801080c08145422401e00301c00c010f403440181c9680d05407504444160 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 125529712 1250 125528462 125528471
    0xf060c070302191d01030201030e0a03080402270a1a030610060503060a051002010906060923100e0a02072d0f21170702030405010c080306010513090e1501050a0504 72
    0x6540c450f03800c035030b50041d40341c00000000c64070541d8840640d0318100c900076601401191150030423141c4030903000c4400f50028211100103005401c060041f2100c20400c29820000511050450300080c40242d400300e001c5a192402201d81d003582c00e03e81200400704a0141c182c5003003400007141110030920503d0248800440003417445d03942c3d400510000c090141c0030b03d078040070901c0001c9c000c10001004440c01882c2c56008a1440114841d90b180b01104c280301c5840500082088001c18a0051401809a84608012400e00828082c2600450040e80050b840341e0036440c2c80308904181c4a0040b6245207011031020640301240420724000340c0007081e05080240354103020000f80000c0300361412111240200e101001c1d8802e9880b8411404448041000d450f411001c903220312a80c0b10303840c002510105c41001080d0004c00440c0c00007c1410850f1400800d6520681828010790101201030396800114105003410b0184843d28090104050407035814000010119080c500505020381d43d06c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 125530962 1250 125529712 125529739
    0x40b01061715060405060403050a03090b0c0a03030b0609040c02060a0501060806010e040c140a0504090b030304030206090907030902030d030204060f020106150507032d12270521090f060c070302 85
    0x8800c200ca016085c003030007165465071642850303a80c994039500c0031030000d40b040c1c90000c0c024003160191030700a4030040242c03151f00c1c6551011405040422525540440d080104901b1a40c030340c400c403000040550060b003881c1c50624011000c41d0416400f800500207040d04101c041ea902c0740380c000ca114001c9500042030340716110121441c3c01044502c255007440014020440c07500709001d13008035071455005003d0700c2c8040b0301781a124040d07440000d4010a0038410600545050801076610850381d19000412504680001303180c8420742c0010300210354001814000180d00c828222400050340c0024000c203460a0703101c0400603142e011080c01c0041c0070801008040c403d2030300009144c41c2100c0c0e00780200094144c0c0484070443c06103078020070358490482061710781a005041e0022003007206910401a501908500001c1c9c400049407640100c42c0c00d88525640242e2004080800e1411191114146018070198850320701045119100c1848002801c0d800000c500068a5042d107015801005 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 125532212 1250 125530962 125530969
    0x903170712030e0c030f060112051204030303050f0a0e0d05031f080312010e07081f030204020c282105130306150902030f0a270b040b01061715 63
    0x180c500014040d520780d180c00328120364181c0082200b80c2000040e506141c0c4054105580e0742e01041010943c0c6d040f620040019401d1240000c2d065070241c4142c0d4003605454542d21507a0340b260300b04901095a841c14444141c02500030f441c0d000403000c208028000e0109111980c0300382d2654500200203000000a0031030344110081380200340280302d605403054441c940b40352290070042c40300301540d420900024039111014052409102c0340c0e00c4840640e210300c413010390901d040129a407a441c0c03440d01d00000603183e0344010304009a03440c0180508640c07000c034140070009040e480c41140e0b00d150b040070000c03801604002041e9085405071607000c540d81401500c140c001c228054031200c20341d0703030004244007071908500000c084c4600b10200240e1280540c1040303000c1540d05c642450344182c00105400c0040e40014100c080c503c81074804030740040c1c0c1c440c1c04c401c00341d03004440300d4a809040c04104a001440c182c00b41c40c4600305503000c0c031038200c07295203200740041c101c00380700e80380182c4005d003600d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 125533462 1250 125532212 125532217
    0x150d060b030d0908120a1b110907081501020304061b021f020304140a030f0305070507030611070b130b0402210a030509010815090606070602040504050709180c090317 73
    0x61014098510102c0da155000d002005284944c2d40c80c0d0184040c65100708440e0001c0303881c0c841c620307240d0300314101022109485a486110084480c904181038921303ca0b56000803d41c4205c80c66507178400c0300d1801141c0c44080b0405440b4441c103640c400e1000340b12458011446e00e1400c00d0138592900301590f60300002c1c641811211f0b0034500400e200c29010310440e0302000800a030340c80c0c0e603039402c0800301e04002d0180151051102405c40410131020b440000e22036070003801c800b80680205c5411580f04e49a031000c641c0100d022034a02c040000c1c0c09410000a178111903400050303152410702c1c40d8000d841c2c48e4503443c0d004000034400d800c2a002e0fa40003442090140ca04140c00c6030407039498030031900d00a00181d010b071031824049600780c0005012006905141308507680080d1420249445039000e018090700216022181640c0910006c05c440d155481001c0c030400055032001191494000c03c81c880c0c3c811100c805c0301d0b10b424450000b4005030010100d004481c0e02200818400040700b03c8800304d030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 125534712 1250 125533462 125533481
    0x11040603050307120206160c080c0601080706030b0a0513020a0504090f1a0d050a06050601050403020607050c040c090b0708030a180c031103210c0109141506040203150d06 75
    0x54604040401030080000250040c18410100c000414819110907031307480d0000c40f420960004081d00c591182481940011480d6209020490612142c290700302d040110980100355140c0c0010010817041e43e150090118103101695201d0582e8241008103032034030910402503034501d4000541911091254007102d0051201c40c0c6d00700000c0c40c030091900080c04001268113021283c515842d007651404d80d82144c8425171000050858407004d0352003001510004008034107004c400d11000001d43c44200c0140700080c0300300040c120645544081108079000c0c06111410003020040602403000440704640c181a00480c2242e141d80d66200920041e2511406e5a02c3c04101d140785002001141038a1030240c0e880303500c0c450003000402d01815079810940c07042c420740040045a920790038500c84000c1001d51180030000c242d01c041d82e1100e0510201c200c40c0045140c1c000e4040030300c00c500124000d90420011a025855402c100c040b0140850241c0c4401b40b082580c1c590103c204200356020740e465 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 125535962 1250 125534712 125534719
    0x6090312030711060105011418121501031b080a0609050c041d210a030e030403020301111207051207120902040f23040b010317070503030a0b01020f0a0201020706030911 74
    0xd80c9040200101514103180c3c022405100c0c103000481c01c1e600400f00350b000c00e80d0b141c04090a044010740e116011080d07079521107800c070090701e8440c3c43e07400b801d202c0200c1b290560b10110340e007075142d031928000c4240200260701404907504020702a42401113118115150007040c00f1074883d05504029003044580701c1010340c0315103440071014011101400004181c007050040d00c07192220201e0000b101d030301d079a2a44082100c02c001c2464254002c0d80065910003488044034141900c90303010a00310341420410300c2c0c0040011800c40c42d0f56182c20b6180340c4c0071401e45099030607d00c0c6408000c4100c00094403180602003031288070b030025510741d4417031035456400600070f1120004004c80350340240307420b69411304a0401400c0c4550481000d07090140200d41c032890041d443d03031030f680340c0450071800503000d84d40e0400c040000c2004600c08001544c05115130840c002002007980b000685441170b00d9071448580d800550003280545c2e0040750300c4044418504011810150030304d4525150803504159550 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 125537212 1250 125535962 125535967
    0x206040b041b03060e1608150c180a180b0118050d0609050a030503010e1f0b03061336050c04090f0c0306140610080f06010e0a030602090f030a0b160c020301090b0420010e06090312 79
    0x401036a00c103300010a24910410003840d9040001124403580d1500101042a081c00d030400060070080340340c0054a0280c0f80005030340ca01543d41c10304244080c2c078150006000400107010500740004010340010348580d85100b0400392103000741e82100c1da44035044400780080b0024032141c42e0680d641014001d4410100200034516a0101800ea26070035150484049a5003426491a50080415259030094020110709140741c04010242008400c06c50b510260a0300e5500018100b581c00300c00b552007604042082440c114100c9a2203800a014500c984c07034914040d0300e1940c01c034090700d800c0080c00e1021019039440400590705107404002e6541c00104400002003800b540b0360141c4a2600221980d40d03100082d041015510035011401030b08501c2540007040d09118191090b100f0b0a8080c00d208030084041d4002a00b12400707848107407071141c1c080080000704002c4040b5958150300b21b080840e80c2c0740203840001d000e440a241c0c00e6024500025402016a404001c3c010000800d4500c166 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 125538462 1250 125537212 125537219
    0x14060318150a0c0309110402160b18011b0c260408011e020717071a0c07050606060414011206091503060c0206040b041b03060e1608150c180a 62
    0x229800c0440b031200640e032800c3e0141000c24880d008044045400a0708412224480007c00000394404490031502e81c14085000000501c114020b51103510f014981841000e902060103081d14401500c003080308035081c903800e41245d0442d003000c0c2402d4225184004420061442d2602c10000c08140c4240d010082000076071902c054000c048503e07180f480d41c070b9041c1c01c115801c50580c016400300400d08280e6045010761070111101030003640f8000e000e180c00312a801c42280d0341c0d0000c161404806003c0020700401400010412950000e506803807c0740b900f844d150460301110b00c105a0f05040040f04015061440907039045030004c0c0400e0384081000e010543c003c2861250207210031641c6d1360428440302c0c0ba550011987c9441140c000050111a0f659503488040000845803200710708044448080080b410500c2031002615030000108980c501e40e0814005011090b4002180d0f0342c08250040d07450050605005e4024601c0c02401d07131100da20468a82002012054507034000c000b015001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 125539568 1106 125538462 125538493
    0x1502040504020f030411121b130501090905070f03080316020f0105010e1902090607030c08070b0c1306080609010312110303011206050601080114060318 67
    0x149459122030005080340c2203802d90608168000c0100820456a060b444000c01d13021030300030a21010702a0001d542d240c0c10350440c1c0d000e21007040c040b6919150694100c5203020351103400e00c155038484c250500102101c81080e2040d108141c070010319040080c0345c200640e034004203030364515690704001021140b81421600118400c41001f444030100c20b1243c54041c00703000d441d045560070310201c40c21540302c05100044646104201002e496610401141c800c280d15007803800311680103042c40100b07400b0f80403020f044034441e0010480b51401500041a11080c0414400d501c0d030384401003164009411501d49412070b182300010300c08545c14172030142c541c140604c0c0844402c500b001c0000e00715002a03020b0300f600c0d20031800040c204031040c0511640120f0a18200319903624140e814003c000c0f105802e01e0207807500102240303181000c003442c544100e01440c101c5003d0010b107c403a = true := by decide +kernel

theorem cover : BRFrame.Cov 125359712 125539568 := by
  have h0 := BRFrame.cov_init 125359712
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125359712 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 125359712 ≤ n) (h2 : n < 125539568) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
