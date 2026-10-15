-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4853
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:56:42.331209+00:00
-- url     : https://prove2.me/submissions/86dfeb97-a383-4540-892c-4f14778d61bd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 872661870 ≤ n < 872841726 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 872663120 1250 872661870 872661893
    0x40b07020a12050a0309150c120b030c01050703090909060207110f1e150a08250f050928260a031b0b070306150c150e0102130b0307030b0a03 62
    0x4020400041010200b640c025007001106c0307644074400b82c00c0e0403511807014006091886c01400091400e811030b0488052620550040b200040c000e07200c0401460015a00c0358024103040f41000f40d198400104000c00e4800c0c0c400d4140704c3d100c056a280940d04103d40407040402c081841144103a03049030603941e40426210b6803071503451040c0c090800910005420301c0d00c82c404201d003100e00140020b52aa440907610f40f00d070000982c41085503038004640d424413a2046180b0011842d1008011241303030080000d02140d0310014581482030020060728034040e407008504040700603000c1c2040c0b001c014015188815840300d892048004030f038507400140e03079042c891006028004400460341480c03c100540d0030f03c007900030841500c5410300b8240100244828400c80c08000308404c20351089611490002d800550021030a05922a0f000c3d0004010310440ca00c5100566080015800014101204100600e00030400300d86a1400706006000e580c0303140340d11880342659890910000e494080312 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 872664370 1250 872663120 872663153
    0xc0215030609011e030618060c0203030702030f030c1c0507140903060402040b01180e0126030307030525020604110306040c09020c0106050904120207080c060a030f02090612040b07020a 81
    0x100301d0803c50b01c4c07001c08801c5040e4001914090070051442c0e0740f4541400c2201140780301c0e64003005146d00c9594226128001910a400140c0003040440c00c0801210301131a0031202500c0c00714517102c8804109000d072000000603a0b02140c50350204101950011850609900940900b80c40c0940c95000651101030040000b0311441d594550395440d41d118030303040c849592408140000f401d84412201c4d01007039003442144190200100d28401c2c02100040075070034501130100031419070712118010b8025140c003c00c8030b0014408070060742e1002042c1c02d82c80389010215000703012b25040030308040a5410414140c240039902001c1403100090ba03425400701200c07400d050050311070140b00406030241c200c40d40425407120001d400c0c04280402164090400100c81d002c642d40039690782c030015110180c800300700c5c0d408401072200c0c03e641c3c0e000b50000082c410000c6001444d0039020000503290340c004181840e9031008040800007003102c1c44205a40290249c00100140300142c1c2d1598070b40a01100e1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 872665620 1250 872664370 872664389
    0x30b0609120114130c05010309120809211201080705010207182c0c0406030210050a12020c03030115020c0604053102030709170703060207140109030c021503060901 72
    0x440c9150079403c0d4080000d8070f84901040105041c0480c0c541c02e540c000305420354142034080b41c00100c5600078030076400072035031041d00a189502400005c0d625a40020070546950240900c082c0c22068282c80d6031201c108000580d50301c80c1406114400714040582099800307622104040c8001c0e81c00085070011a00034400203103202804100e040050b05140340d2280c01c20712804c4e018500149850400f8041280440440300511818400c110503102c407403001a41140000141104862040004240c0b1101500f4045628491072a00750101c3e4050340844900d40c10120051000310080480444001040d1006005115540700054060701c100d108091284485030045440d4802003418038144da03900640c040030810080310094040e500c21510300d030010301625008a12041c041040b0080d0082490040140742d0956580c000290301c225402c4e00c620204030502030b200e2100b4060036580e11301c01d65808056120300d1050000008043e14480304044041c010000309403500708486045505450 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 872666870 1250 872665620 872665639
    0x409230c132a032018010e030a052407020304080d0c14010203040f0c0816030f02180c0d0f020f0d1d030d150b040b0a3516030b0609 58
    0x15800c0d0180340c2c1040a030a1100704421000c1e105078042e40485150b000d8102c428241e044c0441c400151071117402d84040d051840404070345117035442690000e50980014084860204a90f111240741a10140454100c03031869000c43c400e1071640000c0940203642d900085040070704061416880b02c02c000400c1042041c0c4103074000501c070f8185009240000c0d650b000315564207140c00d020895034581c1005941c00e8100c0600003482e030800041550007528518207800f00281946e4030314000140c410426a1302004001c400100d604041d10080d002d40c24204816980d2603085147c641910008408003010034418881e40000d03020160486800304041000000d0a00d1036800101000030001c8036a12180301c0491502c050306119880340c014080d0481000d002c0c580c4c3c0300b03222038052055002d56070304114207119002d9514080c030300c800a00220354128203034624182551035160981040c07050244900e41043c0440001244242c8103040c5951400344003052050012038003c1c461208458004d0b030850 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 872668120 1250 872666870 872666891
    0x203010b0306251815020f0f0706080406060801020a0c0302060a06030b040b04020109030b0c090a050906031908093d021c09081006060f08010f03020f01030b0409230c13 74
    0x1902c001c28041d00c039041810200b41c94201c8800311741d0012010002522a01001800350000007036841101c02c210002424110f041010441e42c08134041c03c12a042d0384c943c3c202040065003030006e01611121641e43c00b10701c07012420024034005002e8000a08149440400c2c408114804034065010703411502030307166a215840100d905880b16070010300888e503441c0a00c6242400c24000701100703601120300034016034a40d800c0003200d044c140c0707400fa03055100c1d01680c0003103640f02c40030340c1b1590702400030b071814031a680000c100e540481a038038140c1941102c01c0c2007039a541d205111210781d81c0f03a42074246403480c0c241029564808110194001d40e00c2c0513080700c4454840e40555001e80440b9045e2143c000d01d11300d41c0009030103a406004041510500740116852040440504136114210307840700311495502400094100f05081030304068444003804419202c41c0103045100c4d2180340c40c149210866040b440c00c114181807591102d030003041c003045199841d2064140041502c0000090700307100c5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 872669370 1250 872668120 872668127
    0x6010b0a1d0604080c090c0c0d2601030b060310060b0d150306150302120a020f0405091603081207080c0f0a050702040507090305010c05211512010c081503190303180f0203010b030625 80
    0xac8442c00f600d9140c04c01c001100300800048040d00a110076011513040311140105102500c01038001c4003010381081c02600c61000c440c0e00030109880e0002c00c0300a0080e181c0d00d8480994219102c20b55244080d844100118104501000b014107640c5018001070600350340054040108400541c1c4120f440d000803c0700d0180c1800b0a10403410035a190814590340d03441e020314150020460922820401c200141e0700e6070003041411300c6000300380744051404002c094a010950403449802040007020b101010040e1524401c40d80075507001e44500301c0300340c40d601d0300a003501c0591805508000080c0000201c0c004015082e140c0594100c0071103406a480b180845514403603600da05502002001034601c01c042c2c190b12003004001966142a0980d581c5c1e41d42e503001100120312241c05a0001b9030300c0815203000440607400a100f0718001c212001c9200400e441210710700000c0c2c1d20603410344071210031480c09114142c2c10142c00e501514052401a9464030402007065425032021802d0b00c807101d020b4030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 872670620 1250 872669370 872669417
    0x50f041508010c0e0f18040803090a0b01080a11030309060711040e010903051908011a0d0605030304090e2a1003020904050a06030b0906010b0a1d0604080c090c0c0d 72
    0x16000304082e110b0040000d0224a061303081d00c0c040d00540d0b4680d581420003400880101c03c0344035958003117440c0d0b580d41d0145a40001d2400b08030b402100c02660000380c10389401c0e4000c0c0b0010b002030a440d049810916400765800e00182e1181c2c0c0100000c104946410050b5044140c002c1e04188001d242d19001c100a0111100b0246c0b05519281e030a01c20550824040c114281d2044080c9020413824141a19903e0f0203004885805084000c80140b60742e000c0007c1140c001505804110f944e642d401003032540c0c1203a04040135540d290030707581c40c44101c10070460b41035009030120381070b409410520780720700580007008039401590141e80d6081030070700a80444004042c040e008001d20300c0d000004c18010b00c001d01045035410240b03804180440800294581a81d40b15441c4500e45601c6103800d56510708000d46d4140201d0582c52501d01917921807010f4802400803a000e803c0c00c4da082020810400c00050607070440c1c41c0b06100c0c0304501100001c11007015602070078a482c5030105007a46588855 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 872671870 1250 872670620 872670629
    0xc0d1106041508100b041a0c0105040b01090e01052511060c09041b02062406070620030405030f09010302090405100e092b0504031401050609070306050f0415 69
    0x184001000100326861400302440b107841030b6112036050b15404580c000c00c0e1000d00c51041440f1082c0302c00e000c01610700c10412050800d14445d18504502141140c0c2902c0f02210242c82c0d030743c00d040c0100841807079800340c004400d90001c000c01152411100c040100d05107449418030f10340140b00b007030f060280507a6031980d0a41121044130b009181c4403c11240e244e101c81401c50003503081000ca030006103100310380d00b04003c6039900602a190f48125120711682d501702c00440566034400f5a030100c03900d4600042c400b035805040c01041000c403034034031030446004201950b184542c00300100004034074007000380c0710100a40d0206941d1241c8243c0100c010b40259919030b584203140c442070200020843d201d601c21140c540d8502c0d00135079581140e064440780c00403442c00400f1440c1d101d0074001c40030030a5806003d00e550501c0c03414251030b038032140070a405400300d104a42e035555090100078034022030101c1d84800d241c5000d1003140d0922012030700b6500d005020394081c0d43c41d100040c0c09003240074804000303003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 872673120 1250 872671870 872671879
    0x5090c150a1e44042f040f140f0702060414031209010905010b010f0e1908150106021603021018080d0c021302032503090c0311030d08090c0d11 63
    0x61801003d01c08007158011004000b001d00a40340403c020550b1030148543d810030703c482c58401c0d00801a5521504100e035894075000c5601440e6140c2c0e03140d11880521076485440020201450707400b101c00c5079409030171100c044910303070f0420454540c00941c41d49d2040d402a050030036801e4441140f491401212154903400907203000308050b10105501408803039000e0300090003071008150040d100020300203032003000200e40c20182d5015080000409900034154010180e03030596400700b0b00d040c5494041a00701100c1014010400d45504200c44061002c0f05044d01c00b55a00e143e000a04c0841c80b00301003420f02c99810a032680350399a11100c1c1c00100b003071000b960200f00709030100620001145104038807480301c400414062164a1003075034410b40c8054620b1250001035011042065245461030b001c164403581050005403852151070000c6104040d5000d5182c1600c003014104860740101b1000c00c1510001c20142500024403e03610840590724481c2c1f04406040c181031050110641c103400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 872674370 1250 872673120 872673167
    0x8010608031e0903011b0807030501050901090b0f0301060b1209060601170a140109050901110306030d03020705030f0d050a0605100e0f0f0d050c03121305101205090c150a1e 76
    0x440383c0d0042618134807c1c0d0f201100340e0f42d4101700307038101d40c000c1c0291500084008010b004411240d44510380e60b01c00108020300135815040003a017914001d40080100c04e402151080c99114011070700d80d001f078070200c003501c40d0745071110000303040d410140300800022940d90041011a0815400703840504100d212442c450740e110b4628030f016107416682e031141076107481d000405555040c01503070302a0100901900e8074400e000c2c0210040d420656058920703003c00c012a07543e03103046000a0129900740f51011400307260102582048030001d030301841c09030945442101129a11540d15400701008840c0c0c98104e140d23031030201d00440c0200308038607040101c100c0d0420602000003131080d17000070110122080403250500b00c058a0042038000041101101d07024001842c01c0c3c01070841c115000d161000c15044100d4400050300c030255105840381d0000710704451180ac1c80102450340e89070211055107001e02d0f501004003111881d25258512103080d034400c04510344070362079081104404c004092003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 872675620 1250 872674370 872674391
    0x5090d14010c021c0915030605030a03120b0609180c0d090b0108120c06070833330f3106031109041503210908010608031e090301 57
    0x80c4042e21400380076106103074080e00810090714200300084166502c6195591806400050005d030700b0700c0403c02c0c161201e02c08034454800b0494a880c0f00e0017541c0d0016000407003004081103c106202c17090085400b00480585034940d0102c145005072600000d813010303a50f07070390232a440e800707260002e000325811310751001c040c44000c0d9241ca040c4d81ca100d064074100f84648408458900c180110f0000b1600a03600007002680241c03082e0303500640901c8141c178032491820101c3c44218803c207600c1d500c811051810007a900700070b07800c01060410800d0010315540710307003840303040c6074000c2c00c0c0018074410001e8568205296401038030042d0b40d000781c00303410003043c0e4902e0f84000d60b503400c3c0c1c0e04088401c0d11000900203202c2d004040e032400074000c02600e00803500d001e100c05800440501310200c040c036034000000842c402c03540000c0d031080c000e101c0c15020b80c20000504090140e80642130076810402e080c00b40310004001c4400744244803002c0011014540c9000903d030040340d01c0940e06510300000c109 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 872676870 1250 872675620 872675623
    0x114040f051306141e09071d01081c1e020705090903030108060c030c071e241a130b1203130617040f02090702010e1905070f120305090d14 61
    0x1030209208030f0303041c400d83c41e2484180404000403111034000356800d5402020403502e036250b6035002548401502c1066444412941b040f074244064070417102031680041280140c140926080e481200c060344c0d8002410640050a540707480c0441019000910050f00307409008225080050030301402000e01407810f4041c580d141c0d0001d2080c3d801c00c0c02202d00054181c1444800c5074850301000c000389080c503041e0f03112031002c203111042a08030f01c00d00c00b8059000ca40e09106000600000180c6105103214900325481070350000890003071741c3e018074251100d081c0e4400052600301003010500082140ca908001000000c03064102102800b00040203082c2100104500301500e0294036030041e088401c19401381203031000c0b00c0142c88600c0543c3e492005103880440c19410031814800407940f203440d840050308002014817001e0001e8801c450b0f41003000070610a0100604074401e144032480d142100c48a0354502116004040106c0090003e59a594000740d8490540e00405001f1075a00004c0e4401e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 872678120 1250 872676870 872676901
    0xc1202010e19260d0507050c0a150b0102030f040e06010302090a0909051b03030a030f1d0714040e150606070b04230c280e070c170306090114040f05 65
    0x958000f074105150080742c0001084004074003c61006030f0b0b2414a00c0d440c00310040802800307100400404001e501400c1800f00601800d29014694280c0701001c40701d00314049503082500c080c15900b0600c1040c6040c3c00f150141d508403511055400980d07a10072004800910850050550000307000c100802c01c0c411550181d014180310f94225140e0424841c40c09604410205620b44d00d544204000044688290001c40d2a0761102e0404144241d50010039262400c072104606441c0d4000b02003000700743c3c2e520200602c0c02d002a038040000e1402c10000f1511340c00d00340b07045c101c40500c280104440740c8500d402c40f5004c540220a00c00c05042c00d00d451911a540c040c21603490500500b04003003061004182489090801410481c042001ca8035004244448250006038046112000210380d209141c64070300c200e001d80d0382c103000e140c09844d118004c424556590b801180d014402c10403113032141131444c0d0648000d480141640c2941c80300080180840300b041c0350b0340508104c01c0c0841a0314100a4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 872679370 1250 872678120 872678123
    0xb060304031211070807030c020414011806091112090f120910032d02070507150f09030b010509090109060606180504020702030a0b04081e07150c0c1202010e19 70
    0x60119603072400c0c143e0b6603030080301400ba0040c5820082400068081c510384a0788a20280c80824400b40c0c40c400410034850907440400c0c03024048031016181e40651050b00c0140000c2c0c0c00070842c28134412641c480754019003c80d80341002080011a000400410502940050f0681100ca8220602d450f0b03210030307044400d17000d00542404016254041c00f0740075105d8120401e0300c50000b040250b4040075404400c0c55449000b8613420842c000209000340154006070406041007846140190001801854030415110401c005000c044c80040c01c0103096504480c0104d030340b0103003a207034059054010f0614050040000d450988006901c1d0b42101004820200d1614400402544d44003071000ba84104070009500da042080035074002005030041c660014000d0010900301030710458050900500d0280d02070510300c0200e401c03030401c54000c08542c0080c003025014802c02e0000031014090b054101d0000309802c0520078001000da10035804015904203800403980e0314038212841440f40c0444210 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 872680620 1250 872679370 872679407
    0x50d17180f220b010e060d02041d15063103030809121608041805010504110415030506040f0c080f1b0301091e11090a050906010f120b06030403 63
    0x1906140750804a110201842c500c000089000d0184404000c040c650780c210f0501c405105000d440ba126040907089564a14500503039586c180074a556401c0300f511102440340300c0310380030009071040b480c80c0b139540d80340d0030745005883d48002070301150010071a4990003c04c076001010b00926021704140349049a0184e1507226072034548641c5917484030000c4500f0311550500300010782a5101c02038502c24400d000d45900c0b8100343d124598592955111540d1a98058480700180407500c1c00784900840140ca41c01e8079441c1510b0440304969103165030900100703150f55040040e9194803160002c1240803070a0b0801c00542c0414a4080d06120040e02d8080750780415500284005401e4a40301110440d050400d5085030310303245140d4090604a002c40c090b600160015450044440c090201d0039a00d00c02000d0315500c60909100c80d407001d44c0e014038420404030080c0702c2643d8000849035212455450031800544041200402900c801c40c140758002c040042003105269001100c031005011103807 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 872681870 1250 872680620 872680639
    0x2503030b1206040b01050910050f0d081c0606020c010e040504061d01020d0e0307050703140a05030d0e161505160c0e04052e0903110105042108010f050d1718 69
    0x3400d03c400301300100c0752305408041c803c02c18802c41c580b60032002c102035801000c020303810009907501512600040e2940300841821130508101040d6405000c020307100d40c1c401030a0a42d5941d0001b0040d0110350603090003281d0b100003190901c115900510503681081c404000910350202d105070003540120b031454007007031a00d1b04100d180700011046841c0c40750400c000f003480d50704545030b0740e09910302100e10340c3c11445000c80324800182c3c02d00203040c0a1a910100044800415039224106640519000b42c500650a4140145510916a0104040da1349801600c5040c4413200503404100150b019140e0562846d0001d11951205c07030840c42075101c1d070192680420949610f0340000d200c0807000001e59407110120002c03020340e03804010068001c0c50700780d13001c80c444c14000f03085890699050318900d85481d40000f021080074240c01031041c1500c1c3c180aa5854450080750554481c01100d1040151118803814888081d858800712125048103695a080c88501c8411441801104501075503620 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 872683120 1250 872681870 872681879
    0x1413060303050306011725021f051617180c040e06071e0e0f1c05060405071d040213020903030a050c0715080a09030219030203031b2503030b1206040b01 67
    0x1140c2c4140582c40c00d030252080903501200101f64055440d194004520400d04900100ca4000384032019503050301c2800600b60408400021030100d58260440030300c03050503144405100086407080d80510002c0121021440660304e55040c4102e50150076405403c2c40246008854040f4031213009000700d841d62200c02007034814603d01c10101c02240d0300441e0039045142c0703071802c04200e82d5003440c0c801400070a0945c41000400441e0244820a9a075907004900b040100300c01080408054100f0024241c0e0702462500081503501004000038083c01d02c000d501c6102010a0701a24260040102601d440b0702111400a0003500100707100c086520800344001403081003542650107c194903910340c40030356940035298008d004601c1d822011481081c0c00300800d00003c0c1d00c00801c19200341e015681c0d9003407850300c40500c461514102e01d100c010800081441000128180385100b607481e940a90344609401c2c1500140712034640240c202c0c11040070600140710100348a886035128451601480e600c4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 872684370 1250 872683120 872683157
    0x90c1401030606020a06050a0609091203050709080a020f04021e0d0b09100306021308011a01020105011d04170c0601090207060f06030c090207020303040b070b0108070b0a02030301141306030305030601 88
    0x240c410f500141c0c01081200d408141540c00241d440041018080340040da2400c51608541040100340d80100340981c9602a16905000e040e4010360303203207018150542070150064540d00f0840c4000e2042560310083c0403da01c485d01a550a59407002c1d40c400c41901c0e4000300320960f070003014012086460280180264504401464003d105c180d2903e4006030541d40c1c2d48009511031000b42e1404108020700103040c2200f4000d590102e034a81002d282e8900105002a09451044e0000001d00400f00752a00c1541c0c00341c64502d07440380e00a04d48540203040850310540034802c040c0380c00598002d60700041410041d40d0014070000703103c1e64042000041c240407035070072501c1c1404024664004203c0130011605aa000f4004003030000b41540d24140d5107181c0000b0036440f0900842d4064012801000400401d1003084020012409400d151a041e010000c0d164030050107902d0311420b0101900c0d140352250404d03003c100e29078407030070800f80d43c40e4180905079400480c0d2080c00512030055451145c0007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 872685620 1250 872684370 872684381
    0xe1501050a08010c05030c03151201240305030a180f0b1e0c0a0212030f130e0f041a130b0403021510050310050403031104090e0714010203070b04020a0801090c140103 73
    0x1000d695850868647c0c205654544d840034145020728082405100b0003a42c80c1c40480e91581200c0000148441c04100c2d0460250300e03000c83e201e15a10308040407c046500402121042d418901c1c02100f1a49401180b024070942600b182c00000c088400c04603100c501070000705400202401c224a005c00001c1c0c0508103842001c180032510341019441c0c03401405c00c1410005e440c2144800d89003414844800050107420103082c0030b0504254820821852041642258100441c3e1381c0b0308002c4e1a180d2106081440c207180005441038072000000d003014014201450380a5100e26840450704080c1002561501115500080102d440c408a41e45601100b40182103800140151403482c440340821001071400a00c2503041c1922910f491a80700e000600a00151200c0300e40000d44145d4002254600140c42e000400180400b0021321090707a000002e0702c9249030300c140c1c00c1249503998804590040300303a60100810f903082280c1c07141004005203620b41a41c2c8156004103041400c88011070542c0d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 872686870 1250 872685620 872685641
    0x80f0d06031b03051e07092406140a080a09060230090703020105030a06090504210504240e040507020a030315270209150d0b0108040c090905010e1501050a0801 70
    0x188240c059056452505006a50b8001814265500b1b01e5880c414001a95005c0000d13126100c11120003144191507030116501030080c5282001c680680115500d07007034441c0c0100302e424449110b00040c6002d2054110300d051710b40c400341c15508e86280401d034001c0c4503100d1b00c081c0107e2a0084900c103c2809641113584507408100042544510b10313001540c0325070000d81800481a19480003180d40e166601a80c2e014601c5460700000c0301040e08511542000c0c5221910704001d4100800c010140a00303900007040c04042820044000466a094541d4040300d100203411600305810808095001314081280300e0090320280401c00c40e07020907484c0703205503001e42c50429892807501c44503442015100c08100d00003880061808501c10009105506010302d82b03003034050001090906540710780a00c1c840b0800a00702200c0a051941d20855080224012052940c3c1d4662000702404003d4000440300410007043d9030b81c0022450744a01e03802002d00a05000324030800c0001100c200500c2003201c1607 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 872688120 1250 872686870 872686873
    0x312080a0b031203061203094f020a020c130b1c12260f0103061a4002090301060509160804140d03050a15060c020409080f0d06031b0305 60
    0x45e43c0d11403c0007032404501840d090f40e840300b4403c0143c15240c00040700713045070700d03080044000800d0b12030301d01d01c0901c03041681c1c04150b1007180109400700034805203501d00010300d60158071001716034012441e1840e41801d550b400000c0c003889098413106503206c8840400c1c01c0e1104000c00f8003200c8192002075a0610061620040d0540c4824841c400c40d80c118250044d00d03402440c042c90f0300d1029500c400180c03095441c6484140040040002505c5407114907104c1050b00031030b00c41ca040000e142c0360403035150302401c6c04030311650324401c0c0d1074075074007101080030b40b1641c00c0f1841041c4010002034114070000c50007586040c00106261170b110240c10b2180c02c0c041822a12090080822658a9400780c012900040300b80603038102481d0034444500828410390b00052603141c00d018031030946428824550701c00300148000e0154a611060902d072071601034801154051452403c021f1030300c22903a2a110b00070000c640c3c007074100c00d43e800100849004101000c114207540131031440001032032000900c0ca = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 872689370 1250 872688120 872688127
    0xf07080c060f0c0307141902030319050408070f0504141003060f060314061506040506070318120c09060614030f06010c05012d050c0f0d02040312080a0b0312 69
    0x1e1a2000040c06110115042c10f8100b0701e04500180c6075811814044074441c1074144029000708081100210300114262140c001000380d4021a0f1248a43c01c03144081c0c42c1003e0000b0b8070f0314050801c5130300919509080701c00603541c5106411810020b0b001e5107100d241080d031401c00c410100301500c0e01422401d141089020b00e035070b4481c0b00802d1a0400e01d8521511880f001002c107400d03410a90188000c907000c1e29041ca4100c07200c0c5034250f05089001c0c8111030502060081e616290161044541d140c00e110940703810340d0004040345106940980d500080a01d04042084a00406c03a821601c05000078482540c407841c041d07400800008101034100c40c1480015005505481c106070001c60604000c41000082d4580320b081d9004600c1081c5844c45404010080082030b0404141041e5131030000c00c5207051054001c14144074203050390107081c1000c2200780c0700c1d89041d0b040354020350f070012040c0106122054040c104100403640821204d150110714251800d010418007011621a02014074 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 872690620 1250 872689370 872689393
    0x605060412050a0b040c03021306060206150d1514100b0d05041109010f050f04090f02090c0408030301030606180b284412071a180f0708 60
    0x5251181d401c09503568400c401c03e07100425448241c00c0d01840c01001da814942d03056005110492008201c81091a403a04000300b2805070b0100301c45400024180e42081c00c81141e0b80010000350741e148002c1d100644c2c00c01e940c504c40c0803075401070450b6419124604040d94902901c04880c0c000c502c01d0b51000230703081280c0c4000c0c00d480c0d40140d0b403052103030400d807201501c43d0300800c41d260401d07000100c0b0703064a04028480c519000a00f2050700c0001c8400f80440f40071a40d9115410f03500d81e400074081e01203480412086454001a10041c0c1600340842e0784035a5242450360141c00c080c81507040e007034030550080300314031000d00a840a004d00075240c01800030010b0305280080d40e480380125030400008801046100100c04035480000384c5800b98151344c0034001041002c0c0b02c5201c1e00800c10344c855116888401e0010864000ba8400c04101c603440d2403041c10035104401204082e0048401c03660b0030820660300010760480d480c03421204a482d480f1a15800a90700c803458059400c2c9035225141c0200f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 872691870 1250 872690620 872690639
    0xb09030c091b030403171005031b01050d050711100f050c070305071511070303060302030111120705030a140106180806070914040b0a0b0304031b08120601170702030703110106050604 80
    0x44d00648030b4545414182c400f16804511500196a00c1002d01d624040030015031500f088104400c100e041000e42e040380072140040c00911030f102c0701405054960700041c034154040c0c044e040f03000800750103540e00d081956003410014141c205c000c00e40382e464400410080121310054400440d0b05444851800341e0a498060702c3c000e054400032112500c0b0b90800114460720006407807010f129490210700d081c154410103080d503002000341c3c080110288444400c0d03148080295170469501e051480d62034403551420400b40401e8191403056500307100001580581c0040c09080440c2d41c90024062191181e04180e100c1800f030307500c2000640004814410b00720f69200a0b070103400e0080000072150f180801081110311207500c065403214010041206240c2c00c500f8911074144c001c100d1100b150082c0d911681c050084c1c40031724141c01300400004d1316a0b4080c61800c40800b8a42d45040090b107042c0500a6490784183e40032000605a4010000844814082d06090340c1e0002d001a040c50f080a0080 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 872693120 1250 872691870 872691877
    0x120f0903090d1e1e1412040605030c0d021b1504080a210504050c120d0804030e040902150d0b09160c0201120e06060f09040f06020c0c03070b09030c091b 67
    0x10030011240022030000111100c0482216004102118112a0450802450392540307042250b078946c100401101c08076050138112030230b880f441d003091900c3c2e0319541d5040c8014060440700444161000403404500b0280400d00c02060300c5000442d501e100d40076828001004040c0c0780280154024402400b0142c0600055a802d80340c0c0507101d00d03507108083c1134405840c1c00b039505071425008910009071508024061940713103460a0000e0019411140004044010040020741001049040c03000c80b640c46400039540340d034000b00100320894080e000052598060422001c0f02031801c41c0f4203000c6d00344591000d12a003440194080340c0104110166002d06101504038104034242481f060102624800c0340036118001000700240d00e00b220910200001040d402485850944100000901011101850154041000b40e110004501200d140c101d0459607560306000309607000c59221022005412138801c2102143c0d5050510020b1100008050711465200e18180c5050a00e061144006 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 872694370 1250 872693120 872693153
    0xc0b0408090f0d110306060d05060a0b0f060a081006030b0904060e0307050304090b030607080c1602030c040f051005040c02030d090201050409060803190212070f0c0b120f0903090d 79
    0x12000c40000030000955464070440b01303ca080025260401060034200714407940802d007500c40442841580c4c071526568400104030444c4d950f11408000c845464402d139510040750040c0c40c060302c401c1a0440a000181c04455083c1e054620500000e03490340709009800c20010050301c1c5c400d254999856420261078a140c0c0c8001c1844100300c50000903004000600080042c41000118050340400301400c0032005003030002002141c1040c0801c40c408001140c0d410444000c2c02c481c401d20a2001c42e04180c66407259903405454503902c004500740701c4d0451480707444250f24034001c40e82ca030800c200c210b4040111100041c2d10500c1810000a40b580c0b1000031940141031040c01d00e5070380e903d08000eaa1058101418541000c40c031a60040f090791109003403680c2a002078014024031400c005140c0c01344074000f510400a1440c1241440010349080016181003003d85c0d03035030032912001c012111400e0391202e813150366150019000e80c00206c2555036807000140488480c0103103448045143c00c0744800d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 872695620 1250 872694370 872694379
    0x31506040b0703030237020f01050708011502070f090c030e12070213090b010b04030614151012020309063301030207050309030d120b03190b190c0504150c0b040809 72
    0x1b00c00d14140290400101451000200701810115850003401c040d03407084800c130720340e04040a01405039080700b451410f403984808410600b1402540c00c0f07140000c41d0344280002012180c0c081140b00864000d180154041e03281406403003111308141e40d07160940404c40307607440320501c152401450035441e00c00a119000034007040d4414992142c5030703030b05401e0f4000d200300c04d0001010000c1284601030201481103502d8030324914540000305460054640300000d11400a40080c0441035000315941c1034401d050760811500c919113003c04980d583e800b9030785e02c0c1440070380900184406000c10300c80001d80c01c148001152102c2054015801381d041203008807a54001409503681c15203081180044215042c0d80703036140001202280001c481c00741690b5030098020f0903088210a103012108807400313501c09081d00169480c0003038010a4002e00800e030107101e040444142d10b0039800700190040c0d411448107a0302c10002d202050b15413580c8210020550040d820006022072140405031412102c0070f031 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 872696870 1250 872695620 872695657
    0x901140d060f02070b0f040b04081c1a12070b040509040303110307020c09010918020f0307030c0b04050108070f1d03160e15010801051f020a17031506040b07030302 72
    0x1940e48040d2203103209040b4202e0b0707000c24203100788421000c240750480703001041ca01e01070420340c8840a500b10000c02c041c102010016107070344100080d501811090074071101c1040710b071180c4034842c1945010311038a0746c030a0600b0b040400c07000e01c0c0070403003a0880744809000b510389450201030080c050700041003503007450780e01c1c8042d00c080001c2c0001103100e103003e40c3c00390000c004208200010f001060300030000203440c040c0d4050841080319002003120f9011141c1000c40c1c00034200180c90304c00250801814640442000280d0007035000c050810340c4c600362188603c40da10301004440c0400003000e43d1000845140c0c004070704c1d44e556400c1c000c1800c0080d0694142025003600100280c101e98852040d003404101044080800c0b0b4016580481003480c2c49011549404000b0720110104146042554000e0081c1c0b00c03101c0c020014104c405611105950201e200c1007140382413500100c81e5810003181550201542c2d00e025401c032000e6520703210900c0c1c203088494a00324001c1d00004500700c20300081c2e0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 872698120 1250 872696870 872696873
    0xf0e150c0703081504091b090e070501051303050d051902010203040c2d06020a1509051f02040e0708041104110a0c0c1e0810090819050d0903031d03090901140d 70
    0x34040ca030011401038404004e084181d515400f030406080e40708e011010302c0c043c00d980b0507440114081040301d01c01d1074243e032100c0039815049640c40e0950310040c0980b2406c0c900c5080c1310303008070140c99010541050503054103d822001d9090b4801194018242e222400c81800006112060b004401c40c2406940010303111200031580c80302801d80000001d42d104003d0300d400c02600c040340d1540c16041c0711041c02020203d5417140d5a9880c3e8030a0b840c003250302d04128000e4078030240d0540b0008c140c1000d40c040207003000400a8460101510243c5030b44101407034a103402d003801d010b0303103d03c0c1c81088400c900c3d10303445480c01c07034040096040854403c030002c1c50015201098030b41070f9288c0c1070041022140245072407541c2d403815040e4441c16295504040b1040c0c0440c0d4040151250000c1d018065000c10429000454082c410700010a240304c0ca0483d40409042e496403000704441d00d2030042c013141900d880750f9540d481c0030f030f03803125a4040140c00042c4a41100d000c030210720140d003d044d0070a43c2c40e55 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 872699370 1250 872698120 872698129
    0xf1e0501030c0e0d060506100216050103090f0b0c090a08060f0103060b0303040302091e070f090b070809040c120b060f0f25060222081b0f040f0e150c07030815 70
    0xc4ea40700351001510741d401d2007500e1600c00500548011280024041d0007100324102c68114194404d9038103040d600c00042c400d0084900c000c0e010f055000d50560305034034000d400d01c200c03500a010f1080c01003001070380114151800103402c90141d2840da0429106a1855440302c000d032402d079402c00e0b01030005100000050310381e0100386021308105542d8041c800201071018226030b03c001c2030b840070441ca01c030400e046681c10108010545210f0300074941d0707510050030551500c1c403658801035045442d240d007001c3c449500805884401c094101c06120450b9020204905030103101c91000a03060100030806c00c80b0140030080010107100708610542c2e1160060401d5214100c240c155501900000e054030003958022031040c5854403c3c0c0080392a40c10034211130b50320369050307001180c0310344407980b40c000317554824484400300c2e1070080090009501c03400c0d040d8058000b4008004281c480c503c0c041c280020b142070740d10f210301c002c0c400e607609040c080d0301e080358410401740c03800140d0840c40304414402e0b180c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 872700620 1250 872699370 872699389
    0x14010234060e1008160807140a08060102120a050429040305030c07050103061404091b0807050a08030a1b0602210f1503070b090102070f0806010f1e0501030c0e 70
    0x2501d8030b458052210950601c403074014450101d4040000d104101700a091070130664038034a411a242540381507441c0d801c180c4104202c800003219400002c00c103502000c0d03102c1e02c918400c0c5000c0c0d0076540010348045061000740070303c3c2c00d4080800d100340024810f003a0400d0141c407100c404840c558902039071000c44002554031a4200751110741000803500c01d03000041102400400b0b0038a002c220051030141001c1e174080551814902c00c544940700c400c2031203072541840540010070844002003903556034009503a007859200d45030003481c00c0580000c1b908400701c10348201030540c0c3c507402151008503803101000c1d000c0e81800c81e8640c1d130070300812500d8445000030440b418184000c41c1c0d21420002920b03402464024906802c1e0085019020b110380c40114071002201e501c03800c10f64940b1290030041c0c0c10540d0a80260040e1544c01d2000601c0820000310035040f1510641c0c1e805059440c4c3c2c0710082c28011107a40c814140e030407540200704035482a84200e1844c0400e2400001c54014440010200300 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 872701870 1250 872700620 872700629
    0x31104080703030914061b031306020607090f0b09010f172706090a080c070e0c1306050406021510230108071106040f0c0f090f0614010234 61
    0x41c48030900b03104041d04801c1480290003000e414030050081003000070b4261059142e05041d0360312000c41c41031441c00c01c00c155260100082602200c032919041d00941d02c0c0c00444210000032903410000403954134144c00e1609903441c0d00708142c606800c050064924622072110001000340744040c90210320b50070702806008001408003000001880049031015641d009442ea5481d0071010030301c1480c900025182030050303401080e9545410018500c503050011a600850444010004210041035010300a24451001001d01041e880c1c54602c01c8035103004500400001d0380c811032000076001005004554000007041407140c0094039422034000284540490b95000e005400c04400c5540c3c01c0755246e54002210710b44030325004846030342266201c0d0040e1002d0302c445508a650420300900a180c00003409806101c11200da9403110010024010141640400d0303142c5900800c1405501c4c0e40d270070740382205a0040500744c207061030052884078108100140c070790550518040980025010300c0040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 872703120 1250 872701870 872701873
    0x150417060712060b03060d020a05030a060b0306090106030503030f0c091f0e06030606070605040503040b03040b10050906090c0d06090f060315050903160302030f0315010e010206010609090c03110408 87
    0x90504680240c2860b004600c071140c002d003400800d10000915606807a40032808840c600031162550010409004858100b140c241c0104d501e8082403001940041040302c1064049443c156140301e1320343d089920354040240f80360420804204569102c9020b00c0e00000d117400b02a18000081c4000b41c0c03c6080881e18070425020031094011b55070700446c951010a005641d114a1461f080002030190700c02d0090050045565002080a10004005480c064040a101c8550700d081c6814070030100c550407500c1722181d2907a10303804115803c1440805000b09000341002005442e041d030f150f5102d07005945110100d0346d0b14400054240101d000c2c1003040a501c04c000030768207085050a0400300200794914401038205410f00240e10320010480e41c0091009034130000005c0c0c18070742241548a00c2440c0707102d91780d02100303004071042c20b00e54061b40c80200f6204e801000d00414016a1100c10910030f00020401c070010400952286801011301c440c41441c002902d03414003a103140302500035800c845a01d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 872704370 1250 872703120 872703133
    0x10080f04030e040c0c062f1b03040b032202030309330307090602070513050408070b24010216060f0c020a0803030a20030703150801020c060403200705150417 69
    0x82c003500d0301c01d07100341550b207003401884006001f040596403c4e078181d0240c0354200002d503400d001c113100c0b800790149009600552350748607030b82c03140c0381c127a5003080c3d0324224071307102d0580074019100c40c0c6d040080c4c0807a4080e02031824681711100300100340d018106c948521004020242d15031751840030580743c040466010885d00c0e4241000001c0c8840072a40005003554403101c0184116504c413032401c016020004004034155459141c9020346004001d07000300814011414000b01c0340404060701488051703c420f130000388581e0801260f40781283c14184408000240d414030156209800f14004540c403810803403488a015408603043c003101e40e10103420f03608003005101814076940035a100228501d4401d01141242410841451102802907401d0540d50220030103500b800028203001040414021915100d00206547e12200100d4003200040d400c0d03140d1107540c20a080e400c0c00305980701c1c030090030024100001c0c089081c0902c01e10380b0101c0c1e02441b0009548501824080224803d10080e141 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 872705620 1250 872704370 872704373
    0x50616060506100c0807060b120d0e0a0e040215040510110105010f0b0a05160c1205010b0402030c0715020d05072706080a0c09080111040f0510080f04030e040c0c 71
    0x11100d01600e020f11401001007008411940800c1e102c020503001284240d0303444e00c5e407600710000c02089110940202c503880585910203408541840c0d400346c683c0300c8100b84210b40f01008209442801000702442070800450094102052103034140d40d1480340445c0342c10303183e0001812004040c0034400c00100c000c40c80400c01038080c06010300500b09000380001840c103100307102c0c10f42c2c090002e1450401c4400701d041484826141c80507034005400800c24001e840d25110723013441082010b02c00307940365030034000080d00c9030074540300301c901c03c290441c002800d180e00703030743d640807880101500280055024400c100071540c0c1442038501614179034071144030080b0408010113844440c002c010402143e03d410401909400404141d80407002c401c002481180c01c11040d11b4114030382d00000355a47c0703003420000b101d910741d03402001513407145100c00b011907503190300b045820644075141c1000505082c01084800c01c96040c0c041d0424820308003101006000b402003011070701001403000000e90845800c40 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 872706870 1250 872705620 872705633
    0x7050706090c0909061a060306060a090f0b0d0b030c0112090c051c030f020a050309010c05030d2c0129120303100303080c0901020c13060e01090203040201090b04150c020a050616 78
    0x200c000104d2036051006c944440000380550000a00550103010300180b0700c4500751007400c2d2600a410090724201040f5280c5560100c284c00404e1305144145c82c2546582035840c0018101305580816991440400c00701004c90300504170600085a20051404000c5000d694601150240130034030111150b40d50110b0400070a1401c5442c24413066411486110000c15008800c413400002d0a080c6225803081c6e0f03103480d41ca14450340e0002101c0350301c1c185074050800c641c5102000e01e0624a0101030082030004400e502325040450300e0001010700c038040700410103615052151143c8024106214114110300b010b0440d4000c80311205140303005c52040c42019044000343d9080a500343c1750301d0070a0300340e1002030f6658513030031146e45c8104012001e4400311a115001400905009168003642c0e50f500c00d507188c065081541c00301e0204984034030204140742541c0c29601140d110503050b04501c05100c80640c0c0764420004160f80200440d80d0208031500c2d040d0041107030350080180c62600c0001d03414100d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 872708120 1250 872706870 872706881
    0x140601120309090504140d17060a0806040b0c191106010b03011d1906080a0c0e0c030c0a1404031b050316060813051501090f0203070807050706090c090906 68
    0x65408246a04080820742c0141c80342c00743d4081600014403521607003804d04854058906c9480b8501ca142041540d15034400b0030544030748814005216551280d40030048820918010240e075940b202000402107010300898581041046850501e0007082c2c0c10401007404080420402194400001801003d802c00c8250f00400c800c14409056504007900944114241030700481c0c104001808501040707820720449549284054042201540d90004103403140032a036410340d9042c421000001e480912034070300c00c0c4200e07620b84184c0e24540c1c841410b403d658202d046a401001a60300d00d02c2c4558465000800240d8041c030807580c800350b03152541003144503803074005034040c0c0c1041051801314400c48a092003955402d0805050b180c0d603d525090404501c10005400380c8154180040100f0001d242c2a05946172008284214031140c040390050744000e42d070389800541448001140380b031150740544444c0380300b908007181d02210340e180c2c0381f0401d40036044182607541d141040c0e0104101840b40703 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 872709370 1250 872708120 872708129
    0x130c0602030301030807081e04080a0215070203070611160906091802010f05161b15020d0207050f060c060a0f0e0c09010506160803070e09180c21010603140601 70
    0x41d40b031981580d80e26100e60103602c1c4000e06444011a03c041d1030040c0400d018115010740b5000740e01d0b5551010030302d540300000401a8040c1c80d801043c0842d034417280c001c440c0070a1700030b00148109450501e0884201d109003100c0c00d00d83c040d201800c0c080741e0030441114008e02060038003044180c24850000112112841029045010a00c040c00180d0300002c500500b292503081c199140c04120345041d404c0f200c441c0300101130440f000f0021200446110001c01a07410700400214981d1003200160380c5c0340030325000d140160b400f001c82006580390840a41c0001a80078166a05049030400202d150031000c0e1034140c80301c1e072181880180442c0c0b80c4105803507102300800510111303003a0360204402705011b000341805400c000610090b4944154042c00f1031603801640c0c00d680c0d140c00c100050140c040e40013001d1207041440046043e07000034040809508100c44040c000c42d008840402120861002d05030341045400c90564040810030f1052034000c5015241c00c0d18100c0d441400d25080c030805810 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 872710620 1250 872709370 872709373
    0x915163005070f110604050d0b07081b030a091505101505040b09040b010e09040c0f0b09060909250207080d020708030708090604030c120b0a050c090d0c0509130c0602 73
    0x6510100d080f081d20401900e4000f501000da00c1d000078042001841150085504030800003005810440d0000440e40718032025910a00b041d140d0504001007070035104500d0f00c0c1264140041100700070702d42e20196503548604410802008154401400d87c0e030125038081592048030310403c1000402400c2d102d807000d15240442c0f4290410203280114001c2e4a8010f004a0392075410540c90303405503103405260304000700300744020700e807604e00044014224082d500064100d00c6c00014200700c24000d840d550300c0f004000608010400d010300011070401001014621203c100d0316181411108001030300c2c122903800341c2911410019440d10348203401510307000f1035000c10400c0000b19801700036180e40aa016000e5a6107140c070f200060700303034040c503000505030001e9036400082c1071904120321705407948100300c0d00f1442c0c0e41e510008401c0340c408540d40c90b088081041140114a0001041000c1512030441d0b20300b5031b500d07400403400d000c50442c0d0114500020800740824080405101002000d2070310 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 872711870 1250 872710620 872710627
    0x41109090c13090b0613030803010f08011103130f1202101505010905220f060503190302030306010e0a08240f0709091d0105090115050103020915163005 67
    0x958036800c00507449004255581c6280100384ca83d104000c4910488500108a120b1030b181d003040300c0b155200f8070480d2240d803040703400081c180e40c5c103000304101c0303003070884045040da035400c05104103c03140400b00f01c40001d1045481400614840c0e10016198810b9000f01049800d01d804041100c50201d40c81104082121041015070f03489818801aa1400e444841f000e0003000c0d0700b0162107041c0300340044500d003820403596404106510080858004078125a5074180110005035612913000020f801600700b040040ca19500131820000c030a0743c041d251040c901c0c3d569948600348046505c6144580c02c01c40701d480e0245408560032900101303070201000580c10030303120160a540242c414270a049880b841851010004280f0703081c04494104020b109910380010303001d0081600c0740c07000020290850010401303512a10966079406006826007059900075004403089030010624240420a040d42e1440010340400b545c000c104000421020400500380409a003011043d915008204061 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 872713120 1250 872711870 872711887
    0x2d0c0c1f0b0418030e061303031e05031605030c0903070e070e031504060903031d07060908070506030109150308071103070b03041104050711070b040320060423041109090c 75
    0xf1410140066240c101410049964404a6000c1c06040c031500110340a002c400001d0640200840c038078140c04098090b4005650303c4182c50350300058901490082140e1000072150b4006c40c001c41e004845030080c1800c1081950000b03103003819907080f45298200350b105000829400c01d4800f00340b80c07030480142c251201d000d1740b911040440140702600c0c285e26a11107005260080d40b000407611180848001000b0313402031815510000c501c905070000e46681d1000030207030700c0803078414207507403005000074516442c1c46040000740045154603200c080c0742101c000300040e441c030002c12905114010400100030454101402d011095200700c80c0c1e034508004200018140f82c08500290400301c500040503247d01340c045410780c6010504141504c249100800c2c004000c1000e40100c3c1c0c8a48098861082c80c412044000c00c884810150041024803045c418401c0b007070080085451080c0d06a00301d014100002800d07900341802200b40102c0c00100c0040ca41480c008a640c003155484000c2d140c002413 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 872714370 1250 872713120 872713151
    0x91707150507020312070c03020d030e0108062b050f06092b05070f0f050321061e0d060b06030a020c0105062d030102070204020d142d0c0c1f0b04 64
    0x56582520580300006d4220200940d220341840907540241201d02940300d286070103000c003040c280486000c500c00c4000103000e407916104180e0343c0d64001c0d80c1000030040d404110458813000c141c00b11600d000b84502543c03514010000c2920880c079100040a000301c400f010b44031060601000705d90300d0900c440c4080b2181b82c0110482c0d048550084051140d19400d00f84180e2800d01080014914040092422400d1071180c0060203130b50300b9162001d0241c0c46000801c1800905c0b4140b20400011078481800c4c54a000c3c05c500003058011030011502d0114038000880f40d601c1143c00b42079090707010401e80a02402485010340c03240042e26402e0007105000684013441460400d0f803640440074040168142d1029019208010742c058810740d12810041c055001800c510a8120201b00c80703100004d4801d5802426882a11f40030a6208071411240802c03004100c0d009140c5804e94204011520b51504108111840829101901c00f181080c1e207024800b40c581d005400d500c07071400c107212070540c07425 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 872715620 1250 872714370 872714383
    0x19020309061815010303050a030614090103021908070b03040309061d10030209271014010c0c0e1602060702010905070e062e0201050604050c03160917071505070203 72
    0xb000c1c401c40d403218841c000c000d0320b40b000d00341e8200d008050010000007095040009000d000450751402d0010036160807a0030100302c040840d150b44800c841e00104054204003c5011004000c511000d40d129164880107191045940c020b02072100c0000400050583c442003580107071110f403900d103079040c600320003030b11a50142003026072080d0382c1400c0368050305d402503044844084015005074a00e04841c0941c103110382001c540311100512840004a920301c01e95204002c2d2001020310b0041254188011643d100801c1c0086841100841d00400c529200c413a50f64400c1c0202c412100d01420082d500a0030500f0107048031080d6070400552130f000075004070361601960003080a43e4940d5071404001030f907240480b42280e002e0507410300d000c024030920b51142c0c8503a01107030b0002d0102d5142c1c0401e10080300c00880704082c3c81d900074030100d4460030410b03440500501031071034011701c1c43d071721360001109a08003124a07105d160300202c0b0400a0000e1103400b44c0111016040482c140764040d00440d48525 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 872716870 1250 872715620 872715631
    0x6050c0405011e0306150801080708060606070303051e040f020102010e01060501270e0c0c1b010c08070501110a020703020406080706080103080a090914060306060a082e0c081902030906 81
    0x40ea42c110041c0f620701c20b501040c0100b00500c08490b502c494001c02500041c03083c00362111500421030085013180000900c00c0c0140006803103c2d01d01210798404030003c26000e010800443d00302ca5010180c80d01c1c804c00c0501844c0a2640c00382c3c001150f200190840e49915000001c0e130341020020401aa08640002c104d41920a80d1406800421480c00341291150300248081000801881500340403800544480d400a404850b500c1d10041089a07031004580542c500040485403440001744108016100b4a0710950010034504070b603100000c410f0300140c4003080140d110301020829072505010381b600400b000c40241110b00d04207040103060706014080501043c100140740c584240c402c001100060144982c01c00030a81f003d0405600248259617591103449100b010480d640791100c840b2085682802c003c08002d5803070307400554071144030340100842001070f148264034003660b80503044c100d15030b642c1c44004604d003030950100380703c000e100040400d603c14001c1000c0c40300c0001d85540c102 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 872718120 1250 872716870 872716907
    0x305130302060a0b040b0901030b041209050f120c0a062109020303030c0a20010c030e2d0c0402040b040317070309050906151209010f0207020a0b030612030705070306050c040501 78
    0x21301d060b8041400b030100c4c0b022054110741c4240002040c06294000a40258403496031032071a801d407000101c4522202e80500e951040701c40c200c0c4280c1d45014103180031101600800c0d144070008440004d400300400d079000c000841c0e01440a4414214554500500705403030001c00c000481050700801d541c1d000c020710000800c8800601c107603440380a1a055080715003e010f200c010380152a482c0d0b4060710750190214040780c1445e800600c04403001c2101644800141d0301c400d00b0a1105240140080c80b104007055640034102014034a9122400108040c11000076030b1503940c1c0c514602013840049400420038518810b02c0b2040000b40d20090340d01c1110011580032080b92140c1000880354050201110140000040c080b6084c0045064282c800e2103028020004a01c0c003004007801d07440b071205c1c001e510550289080c0008036a90f0b0140d6007185d8060700d400d0441051040c4149103603c040000d039100e038406002002001010300510368440070071024141000d10303003000030304800d00769043c00001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 872719370 1250 872718120 872718131
    0x206101d0a02391e030313060b1215011a0d020a0203040905040b041b0513150312120501240f0c0501021306020f0304061418090114010305130302060a 66
    0x80c2d404450310000500390011040301c82c03c502e80c00c41599062442c14009401492803461a448102003c1c0d0456404640a545103a6a407001100030300360050003203480c20703600c81c0302298640301e0109200035000703004004c004c801d030035040d44600c0c03240c140c0c41444d002154620115101c10420143c070b42c2e1002d00c840c056180c2c50461016400d50003a60803c960980c6070008110078007201440c0c1e14007480c01514081c16544402d80c980714501c43e180111070300700c4880d8502c06018182544a03000d070107800f00aa002c0c2c1ca85a0381c8800c2c01c4190b411040e00014402c1d002c91000c4582ca100d03841c01801c03403150718291001d403604000b03981561389940206200201c15130700c054900500c0315106265205e00215070700c05807480344002034105401160700620a079190207152100000c12034080d1282078484000c00504245c100c45d181d03010020741d01030409100b00d00a95910b035050003a0207020000412403110305914001001c84100809a00f00c001c055400000465000719003250032000a41000c1032 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 872720620 1250 872719370 872719387
    0xa05120f1c03060b030c22120c05040b03060606161a18060a051306090501150f060f0216030b0903160302011b050a08060616020303040e0105180708070c020d060c0206101d0a02 77
    0x11a5541f0b070741b00781d011a200081050410a51038103550643d082104c00b00608150402410b51b01c41e012255030781c1005080004202c25444208208407952003880403450f68000660064980c013130641e00380210442c1e040c8014500c030024490707941d00c260448420000351400d0b10302091a010581c50240c041e507680c0e442481480b50030740140107151060000c80103400e81d14910713001c07504078601c1000001259106801803a070700c0031a6440740d404031108140041410340d107907000d02d044050300b80c07a800d102c1004400000c400605456284034000e07000060034000c042452040c408090003a030042003c204180d40e0801c1d000400207130040c3c000c0e9055a210304078106000000d40094501950500c804200020354001c0e8221031410f841040e04c4bc21141d180c51101c001400000b540c4600c0403514003000180006d203e242599030041c0001c0c019800d19800d5190207086480465240d40107030001300c2045100031340640c1a10050258688401c919501c005980c1c04d9620003400720007200750005504003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 872721870 1250 872720620 872720677
    0x105071e0813032c04060603140c0d0204150e030114091c0513030b04020a0501110607050702060706020c0c090603031812030d02030106090e060d020a05120f1c03060b030c 75
    0xb4400300b4411102904d80039651980c20904150040c10321484c10003102040391032082c051803e130062254264682500c0d01d000703040c1e140d00408041d240700c075802d00c0300181c0b01010900303103114221151a106110000b803030515096400302076480c080603c00c0030903c80040c00024541e6080d550ba00030700914026070803811240c41c46021a2036583d801da00c5008410f01200d4024580564422200707600c12613a541d0040d030344000080d2900d41386802c548001001c040c0a107004051681c8000d008604d0800300e0743d81d14003240c0060308000540e1344180281c0c10346003001081a500650110015800c01094405580380d002d6030f05119030044929074403903040000f0030810b0741c07a9001034045c19502c0c4c0d07850b09001800380c3c00c01c0c81401640c88162020031450309040303c241c007606401401a0400720308003828840301981d5010348400e01e00ca400440c041c200420300505103407604400344200404a54600101610041d42164521420070818009a5641403044500c0941803402e80345190340c6000014 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 872723120 1250 872721870 872721887
    0x12040201110706030f0e01090804170c09010e01150c050714130f021201140112180f0c0501020d08090c310603061413020f040207050307050105071e081303 68
    0x6840794841c548000c00c4154264100404410f40d91808206141b00345000742d00381c40d120b1a010b03050340d01c05c02050115031444001040401602c0088445462001010441c041000da00100700e09086100511154904400c3e4032180601803404013240d01064680b203880d034140c0e1042440c00c3c0c1c15600ca090140e00c0c1c3c2140302548a900304020004200104500400f80d801314800c00300c05040100040f404c18017280e2001c0300d40006940b10100c0c0b59811740d69500030159805e450f000007109541070000109080e909489a901c90030b5681441c0b4544400686000601c0f284082840144002c11209010014800681c5442140e5082100c0b0300080304e0609500304414003d044500e80d144510350104a40060b01203901c1000108003414200100b600070b0350081e510110f1240131007032030b44054544400024540b02004200524200c107a03a01c1a24550040c00d0854070340e51680100314071035420144100d40000c1450640f10b60480717055004140110041020b42c2500c074104280060602c43c0c0000b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 872724370 1250 872723120 872723147
    0x50f0126030c070602010c260c0c0123010605090303030c09120a0506090d0305220606090903080a0e0a0f030309111c05010e1b0d021201050112051c0512040201 70
    0x2520ba55103a81410781e41c072002180100d002641c00c102c0c94031500ca1091030900c191482c11801c13902c0c68a2206c0c04c612102802801c9081d5011003845918a40c140c01c2c81140c05044410004440e0b2022512011101c600141d1101041c820207018443c0a51404402c83e60b00c060517040c0e0315078561508001401403900900341943c03a104000100f1301b0000c00007440303070081440030201da01c5511407070402c40a4590860364060304562012060350762030a0f4110303103008c06204e050007142064850701c14000b107074240a0140c00240c01d4505220006003c0e1003444480b05024014000d58502350720346906554050304002c080540e00e50306801803241c0b0403901c014114004040381c8440c1e03010204900480c89103182074a00d9441d200701440700500001754200210184040c910b01c0000ae001001503582d100b0406a8104086a90010003600c0a1007040c0c064400003000c00d240007440c3c10842c0ca0003442c0f00784003001c130044229541c6400d030860265804e085601d803e0907502d5541d880100c172a00e1a001c0c6c0c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 872725620 1250 872724370 872724373
    0x30a08030906010f090506010c030e010210020315090610050405100c0203100e0c03010b0a0530060420010c02060d0f0905030d18080733020406090603050f0126 70
    0x2800307007101c0c010031654100c6101800a090690b1a05d0307404085400544413180400c00b49518000080e0240510320041c28050040e02c0c49400303a000507405907403045442e1410314940c41c0c00708072149400c48016812200c2510304214503076100002802512442c01041e01c120001005105a188150f400381c034a01c0e40513040d00c3c6003688200c1004050f0109103044502406107080202481c01c0511407400446802030031414950714140600500341100341d0b80c00c0030418051007480ba100c850003d103d001b14400801401c1502d4582040103c500306d80d0702c0740e03102404e080c121558580e40681004003890301160481c1e81e54000740c4900006000c4128081c620504000a200600030b01101405012041000501410340c0c440b0401f101d0317010707006005100303410610210000c1400c8404040c0c140491021640c14a060042030600c40d80c1c0801c582c00e0380940004040c0840d90b4044481e200814242c00c09212500340704840507c0024140158205601136002c4a00416045142d042c0c0c280240f00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 872726870 1250 872725620 872725627
    0x304260d0e030703120219030506010507051e0c0619031109100207060809010c090b180910050420030601030e120f070219030302030a050304050705060c01200306060d0209030a08 78
    0x848464407500014004d801090014035600c1c010284d45c000c07101c0b1820411803200307001c03505034819002411b004d00441e040040600594002903010450b40408602041c01c000c04101141801071404140390201400381c0003d014005060381040300d91000028603081c045440c940021613500d86005091076a64401203107204c40e08400e4001c41d40d01c0a544080d07460f16a903540b00b090303803401e81e00c00000803400104844020452021860040c21001203144041c201d005ca552000440315041945c240c0b242e006407000c20031a034034041c4548680301212800c5082384440a00040c080c5010041800d814940c41d501a00041030091110b000d84110340f8803015203030340401c00c10b50259000202e080f03000e119890321044181000c0c1c0840c0382100d615500645c904085601c2c01c58854101420407246841a40e6020903a81d503400060a000541c81d07000040d210402d2280f9900c106500d00c9010398103c080050000355181d280c00c55840c01443e8030003685d1412401e003c01e191488240300944440c0010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 872728120 1250 872726870 872726891
    0x331003270515270309030a0f080f0f0a020f01200a0c08040603020a02100212180c030d030e0615060405010f090503030d0e06010605030709050d1a0403030f110304260d 73
    0x54a8000a40c3c0c10000b403020b140c1625040c2da681d01c28030300030b076a050b80501144400190000b60030301c130151198140e141404000401241c20740c1003001e10511902000c10255111581045118079000302c1c60003d0190040f40348000c0c1503c0b00c0200503c504020001d07001c2980c50040c0e6404214941c0200c4503652140d44280040080d0007410b04000140540540024481c481c0c1c000d98005801010418450740c07225110385026489007a942501ca000b100000400741d45c0c148002c0b0f588a10680b8017161103611203036018200200249001d2580311890200103050701c5200c250780c2a40c0382800c102143c40e41070b1105841001c95544415458400060800010400c0303400c8401d509400501b22400d598031900c090b107040c00300700c401c10005002d42c00208054900310443c004010700800c040943c49070801074200001004071002d8001c6500d9030b2103404c1a00e494421101800c20303503083e8600314202965003189100454942901650040e048403071081e458004407109074618410401044112 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 872729370 1250 872728120 872728141
    0x41202010221010f060810121a0106051e0703020a11030115080d0f0504080303061e031501081b13020304060e0a0318050405060d0308331003270515 65
    0x1d0003410303100d9000c902c0c001a061b00994805004500d48400080d140303040c50000344142c2d4654106480c64079044581091400d0f0710210b050181c50f065407455640c001200715a80942d2495960b610030890170080b070400300350b0101c1c043d440c455201c2071411a21a8001c002805030440518a0071142c10304800050003e80004503111103220b903440c0c19030082d44120f0f003950300d80118821100320342c00c104001040740c0f400d1280d841900303108060084500c9800340c0031034549090360040c019840c1c003040c010301c40800304100c0c20504402406000d414810b000380401c0030100b6040012180c1e0381c0200c082400c108698001140f41c91020045034882d41d800c5c01d00408107042800f944007201032821010800781041e000e40c500c074884c05000c5841416265804460542d0010308035010071030468080d0442d0602e001940045e410f20000d56084a00c400b000c001141c00c80007281014140b03801c2916104c2c29171b002104460052950103000c40104a0403c903040603011440d882ca400e214034104400c1d00036 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 872730620 1250 872729370 872729437
    0x14070b0c0d050304020d08070305070804151706130207020a0911070b0a060e040b18010c210c091701091a04110d02032806140603060a050408030412020102 68
    0xc240c01215061410440107468502c001c3d0340c007a40003203400710702c0b40104e00103000601b400c91091900d5071920565445401407a0000e4001070480484005603001042d8818107030070840599501c40c24681c2802c00020b940305a08204008149801090000c150f6585482c45070050040d1401031000b4de1003000c04035400e500542e0101c900201010200d00300080c60300c6080c040d130301615001859610345403187d9094802c014600000106500b1050507068000e0240030044071040c0c48107540c0040c0e0b030b0001d41900246c20341070360074589001440c9598507801104c07070044545070001c01e181030305d40d070007124090420044083d0405581c0c08500504084001d03040744280d00440c4100a010000c00400008040c2c40e50007a504d80c0c00380d020301d8840060411000443c103000301c040c65035512541d444c402070320401c105240000001000b089440d0805004040c0d101034010810400d5241541e078001450001a002a1001d0300240400f60b034933001354110713121b08030940c613056401d409a440e04090001c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 872731870 1250 872730620 872730637
    0x10b04020c01020a26010b07050a021f02010e0c030a171e090906060304120e0307080f0f070e130303050a02070f1202190f021504050904080c070f0605090d14070b 71
    0xb800c030300c0c00c201c0b6445c44103d905030380036480721031400c1646060340c81d4015411000c016036142c000c0c500b244d0700507680d131201040fa417802940000c42c02c06104201a00311044440700700f81c00c3d0450080c1329080e90b401703e2844041036224045c4284207142c500c0e45040350242241c02c40c9000f522604070f100c5042a8009880c1040c801c4071542340c5079070381406001e5680419100201004000413040c03006030300400b0004900c4d54041e04641e403455440704074078034000340c440c00034505420000c0320030000201440320314003611110113040c3c030505008000d841d5044000d1805000c159880c000300f801c2e120290100c42c01960040c0547c2e0401500b4100b01000404204207100548540dd4011041040e8990b05000640c1c00c05148042881c1907003d01c01d05141b061071062600c10100070220300d60707554540c0c8501646c0611407440e01c0f0440361044502c0c08902c0c1d00b2104001421400410000e1307404812258a048151440d080c5801c542ca00810009082d500c0014140035a09005c6122010741e0003601811 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 872733120 1250 872731870 872731877
    0x90b040605070c140102101d0a03080a05061813081902010e0105160516111807030b0307180b010c140115050901080d210903080603152502010b04020c01020a 69
    0x3d641da005a002004080302000e0b0241e00706807010911100303554030480e814048400046000007800100c98104440746100300c0c0458012814450201183d01c10345911501c19200500c1010310802841400c0c14010240600301c15005600c60402031f0304010786580054007100f0b40308205803090080c2c040c040000d81c0054640c43d01c0d0014111010407544020403da55840380c5103011960108022a034040c000706461105180d0031104083d21076071040030440e400740d201c402c01d60400e45c20060a465944d80618843d40c803082d014441d0065908220400454624000861319207500c0141d4002c1641d000141801c0c00348005140058419006071100c64260207107a1140c9031107000b0801c03200002c0c00755240c2d5601007003c031100a8012811268161100c40815a8080e900100c00090701d101000c00c9001442d100148482e0303040402408000011904211006103044014047c03032030746006207030700d0032600051040c450074000e40c00034480c04000782065507111403c0c4180d0307010398048141d2130b001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 872734370 1250 872733120 872733143
    0x9030c05160506040501031a030a030c170414010806010c020901030602030a0b03030304110d03090329060105032a0d06091a310f0e0609120403170307090b04060507 72
    0xda214030101d08151580203005600f094103000044004100704a490b020304002140290b01c29a010082541082d101341d80d460f0880c2c0080c904868030081c2040110800c2100b48018058001c06030180100e0b81c80130729201d03a075643d40c82e004981d403015001003c0c0d0400b9940340003005000007500110b1148a0004051095150f018180b503502e12040b240600100940e0010080f2450315040e0501c08500a2030b0008100361240c944000441107081042e401541c0c0b5580c54402c003040c02540c9070320060900b401811131070100b5056003034144114040d07640c03140b44103459000c0c0c0c05038415118501d003a0b4504101c450303190240503000340b4134803900403000c0306900002c00c560718084a03080010056480b03d00242d07204842080a88000d201d0130007a46916403041da403204086100d00324414000c80001d0000d410041d4803241088840e201e401e888800c1008244040b0b0f900e555514105071154036001d94a40e903541b02152801a00d81207440c100310002800604254401e000e0301c0d0b6180146084cd60 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 872735620 1250 872734370 872734393
    0x90d0f060c020a03050720121605060304030c0f060e010e1e0c0307090507120912080f10030201081506040f240909050604060503100f05090d080103080c0307050109030c05 75
    0x350380c1c0842000a0001700c1c10004100007440b01d4901150300036038036065101039240240090801a5140701c018020b07400842c00c82c880060b00d000d084020401612401d1460078103450007072006441c00c4014105040141c52442002120781c007c80300707002d049000b00298484081c403d500d032a082e02c0204000400c1804c524441030001c51000e0400400030000c165591070301c0d124034060030001708048284a01300407501c400c082140200007403584541403a00d07080d07251602c00b621004024095441c003d942d601044407a48000a141055a409081040d00765a81820b41c003140a0021046c0d504140080307400600d61201102c00000e6850080084904500c501207046800c0f0f446c203000d078001100c200d420031000c0026403001da00000c0107030021422503200c030b0209240c40c241201c0140d4540d0f441c810220504440d00c1810307002544070028001c0c1d9900a80002e10074441030002900751440094010382c1c618003042104c0c41300303a101e802401440e155003009480e84510003015251409031554440 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 872736870 1250 872735620 872735623
    0x1204120212030c15090a05062508071202071502070f0203070b1303020409020112090323041202010f1b150e0c030a0b060a0306022d07170f090d0f060c02 67
    0x43d90341900d400104081004d0b8910201c2e00e480c09820b046841c051480642d0110306c0510200303100c1d4100c4600c5200d04110007a42405008405884000b040751312001d03c0600c581c020007102c1d40b04070b41d00001d40c035942181000188080d00101303a000e000d10003c2c4090802040400454030640218213903001981d0311080240c0341d10485030300e2803103495042d0b014001860305034405801c050040c586003500581846058003246d83c0480240c011400c00502110700c001c03006809050619a020300508151030200d904009048115009050015480d40d20790680e1050f000f241692a0b240d6541c1e4500c203160030000100f00030741340403d00d01820042000380044001418210f40f4202500a04a2181d00c0d10b4425020b030002d4586580010005400004200c0d140043c060100803001001c0b025400c03541d00d4480301d00c2da14080143c00009200010101d80b40042d0040b100d01c004c180e90303603592501e2402144034072403224112b41c08106031381e04805104101d0210300b041c40c80360710108250100c2c890240d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 872738120 1250 872736870 872736877
    0x30601140f03060c19030b04050a0b040b0118030828030e060c120a0b060d020c0601080c2704020d02040c02010c092306180904050a1709061b120412021203 68
    0x10000c1c3ca800c02141c00c2d001724030810440e8070201d0b40740001c0c8060b400000202a07030004c0d92882c07042030f190007580c27050b0324103445120140b44003403e00c100d011401d800320828a2046210203000704001041709034142c240f5400203040407003070581d41e0368140b20b6060064014840741c541400319205440008010802001c11110600b54440c000f02082d580c20030900090b1034807006154105009001306440035510380007070019511510003802c2c0960420b10080c0c903190342103480511a001d810030004e00762810340510b88c80c2d85035105070318107641e0b22030000ca51100301c0194001e401510380090b555980d5419803001e1003080d9144d81d0106990b0317440060343c1754401084051740c00c04c002545a00c00c6890444014802c055100d00c1c08100041c00c44009844100c0495083d605a0082c03d500c4c0b04200062540c409040680007540c3d0034940030402280b050301071040140d4403481d00c04955408807030b04001d01d00c0c81032031083c402503856485040c50103101483c10301c128021000040c40d01c941d080007000741e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 872739370 1250 872738120 872738131
    0x50f03040605040b071104050c0904051308070b100b07080316020d020c01030f0f02040f0810020a0e10230c010b0306010308070206070f12021501060215041b05030601140f0306 77
    0x101410f182c02c210106040b43c0c000002191282d02d1001d02042c00c2d100d50003200d21480400b0384e0b440d102e030802c07010702055440040c6144e8500420071018800542900140c4550036080a5801039655030040317920402100d07034002445807000400c1001c1044030300b4004501c00c075207556a051000e416000305a9840c84a1031010b409a0040c044012495209501807020500d45400103d0034441d4041504204c1e8040d070810420b03411002070900c110501006419245c0c080300e48110720b070455a0710000d0996491101d0640304c4c449000300542c81c1e43c0305102649400a044405c01c800021400303c10520380c2c0b040d4400c0c0c02d03950030440703002414500818000c0c12a03412240b404c1c5085541da0801c8a03a030b01c0f00d0b00071559260580400004140764809082640716550018008802108460206400160710080071544803001e5901c6910340441a1900158048200d000300e5201009240c0e92280c150000c54141c4684400099042c3c05011044021101a0343c5080b100c8418800e05071a404101c40 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 872740620 1250 872739370 872739377
    0x5150a14060312091302070c030302161505030615160b06010c03092c010e04060501090207051f1d1509010c360902090301061401020a0b04021203070b04050f030406 72
    0x3940700905070f0f0714000300007440e4001d00703403407a0b0a210710004007203801004069845221102c030900826804021082903800340304d001140ca10700d85020f8654124000020904011020000c80c1154071000405000743d00d952112031703101d041901107026400d0901c1c03010b9410b2000e0b840401c0065024254001815416075144004141044103220b44115801c8200c00b00300c1c850301e0b1032004440c08540890291007000410711041c28241048016070304181c02001c441441001060005030001644041100d00c04855603900d0030b01c2c9041c2001043c05a064600d00c07061900c484510600c049002034154012040c220724944641038014221440000c92002145040d050075a061403d00001181040201c04207a0134102c1c0304580069041240c0c0004600c41c1c01140d40b8a5500d028065080600881c03071818083c0350300440000d40e1045510000381c40400c2c01c0010600b591244081d07010520a0041100d40d500c0d080c0c5440002005c040350309032014001c202c000012440044116000c5904598 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 872741870 1250 872740620 872740633
    0x2060d0b1e011205040c0f0608011701150608070c02091e0a09171c11091c030801051c050d0804153c0c030b0103201b030705150a140603 60
    0x40c0c9482c004e01c1d025009450402c250180001c0e000e90010328007000c2c0a465035141450f526000b82068a2110460704003010b9040030603034600340445c40c2c5404120341c91440d001c2c00c1178075144070541d0880381c0600040d411031541400c0081070300030700800e0b040105207604508540d544d400e00b0714040710020030004000386000d10056544010700d0340a080259895000300702c030b2f8040120002c08850a05940c940d1035880841d94291a143c02040e40300d10b541c600d20543c1041d0700d15500141301603c140280792242e809504601a50704080f851005100d42c03002c01c4800c807400740b0102034a0300c40201c3e0222141c10001020051204042c0a916500d00c981c21401c00d0702c90039900c56480d0850382031060b80d40da1000030030700c000c40c065600600368040b0003514001503132600c0000042c250340c0003114521401050840369000e08201800f01c907205070000034001d480f480700e902030b1800c5115980b006446031041c00a420036140c4580c0d00f19014008a407401c200c402039001d8800400013049a601d641070b00b007030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 872743120 1250 872741870 872741897
    0x100509030a02210706020618010c080106030c020102040f121e11010518310605090417090a330503040f0606120606150509130c030902060d0b1e01 64
    0x307020140700c103000388249490420744000c42520f4145a82c4c00b01006030310040900586074202c00182d820002300310007c0c4402e00b1468000b8011600600c10003080580c2d0f00604d800b030600c00c0d416a0007400034600c03400242d56882540c001410410842500d400201840000389110f1403042010341541c40050445000d000000640c1c20703070400341c0704003004203800b0000021350360780710310148031848031182944201c0310398030901c0e48120310800d000311550b142c104244901c0d520b00c203030b0580c03044e0301041c0f900552509035030820301402000c00b002d40044890382c0109004000d0025541ca050755112002ca243c1c001c40b030780b20620112110104080340c003c00200700071480708400181910302071100891140d5680d0003641c031610f00f0000039a94550340b03041c203000d03003041c0400203c4122840c5c9030003414002e40100113224082d00c4900541700540d64003440c15014069049400322230f4008000725124900d41c42010050070440140500c585144904a07810240034600c1055400701070b958943c020800 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 872744370 1250 872743120 872743129
    0x120c030d062c10051f0e040c09052808101b20010e2a030d0207060c05070503010c0c021c03200a08030405011d060603030a0522060806100509030a02 65
    0x60f00206a00381000307004a000e4850050f1400114071070004840d1200700740700010019040039081c80d21440c100120030b1034041c0d200380c1400984900f00d480c14007100201003801031030003031841e00780560310a03d80000b40c104000b0904032103d41c2450018064481040c640c030f030781080c4003007a100204088040007241e4515411090960010142c0005074402408099524000012a100c0300c1005030000d0300c402c42003010074112000c1c4064000746924404501c0c041d403910a00e0007208104040d003e050030621000304520350042001170000c01170101c80a400405c0120454016030042c280b10802c03900340241c96800c0b03400030340c0541e1188480007900e4585030700e03a1043d4840400d40d01c0b41d11031140101d80201c009500942c460300000401e4032a03640040c45104034204c290a89800c40810000551004401c03a04080d01c0ca1174450b503101da045190b012200e1a6a8402502c1d989160780800c603160824001030041604807441d03c0d00003042001100d40703101340038000b0780541002180d040181807 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 872745620 1250 872744370 872744459
    0x907031512080f2109070f050307080d111614210616030f050c0c01060512120d0617060718140405070201091403040906120803040311120c030d06 64
    0x80d0309203a500c0c2850880b540715120162031840c170503042030600300440c0e9544480c480041030158058482c603854850000d448844090440081c84440c85544010360700c2440015089884612140742c0030352150a25200544140016802100602c030304006100510780300b510140758080c020455a40c48100c064214803182d41d03280113042d110350140e814013443d40a402c1c400c1c00b0b03616280d42c86100c42c0b0012400d407003155101900031514800300c103000b244045808807040d001c003600b10356035880200c40e400041000e43d00c0f003104070700354184550082001143e000d008160b035955086018690707965008641515101c0c88801d05410414451300b42815041203170f009009000000c3c10300003035156000c1945454821207066000020280a000c6161107543c000d0300104035082c0d62a8121342d00c00c0358030710003e003000d000d02011340300c0442002c0c010850320400306101d00400d6101c00c100a0001d03aa900a0041ea018281c00d0010100d104035500c40c02c00082c580490342800d00600b03c03820301c4481e94 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 872746870 1250 872745620 872745637
    0x7030f3309140a110f12060a03060504030507060c090b1b070f15020f06011a030a06241d2b080406091508040210030c020c0907031512080f 61
    0x8154000030300c0c0c0c61a8460b0303008046411a020002c0e00e03145092030120341011503040d5080c807050051600249486083d0f411074840240307050000c1c2c544a00043d4803141c00c1c1d100801843c146800c010805034094041d0074494419682440020707011441903507041614000d80c5100c400501c121545080d01c2000d079802c0c0c82d404416158869200c0e910703001b5004140d080000d090b01d10504525071240e040041c1300032280b86170043c1a56504008082c4454130514886907400c10020000c0b44104282d03500000003820901d000c2c0304074826006e2216000441d42d5608400324901c828110380c1400440840b00c0c188000074020324910b400701e000c041c040c00702c5001c0040f01e452850801c40024400d140200060708560312034a003c2490003410101c50100d6018100c01c21030100140001620703000308003034041c40039041c0826403015241c1c049240242003011182e11521240911032450707015402040300e13103e216500080340e40c503006194070a600d031080080500104014800c40d810054015003002e0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 872748120 1250 872746870 872746961
    0x60315021605010c0807020f07080309060a050d141506070506040b040c03120c0606060318170f030c2d090103090201050c0a0c050a1202220b090108030307030f 70
    0x184400c1d02c41e203003100c08841090012880c13620602c091550104011342008102d540201812410221107070b45a001c1e80312980c1c003496000c2040e54980d805201a61282d440d5804c040014005180e220352451100352242a900600c1034501021428400101c400590f0460014003440d01c4035960210301d0311004100751001e55a040c40030001032985200310304170100c6955800040f40c1c0c0c506040c411134080c0c0c1d03c0441410700d0003401e07203190700182c441c2d141c0b4a500910300000000c81816249154480d141c0140001c0200008101c1a0040700d005050100f409450000da011919a02c081c070102c0c078030088074100d00041c0a042865840b0f40c121141715841850203504000c00c201e15546445d02402c000c45107050500421b006a04201c0000310061100c02500d202d113400f541c0100781c00340300807215414017081031413840d040e02c401c40e040f012012101425807d111369581c02c3c540d480ea04203030b170394000090074800112400b00c518041c204c003031048501319020030034100000010111180855600301d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 872749370 1250 872748120 872748157
    0x8070e06131b02010207030306170d0804080d060f081510030b0a020f070302010e060906190e070803040e0a05010608040c05040b041d1605091b07030e06071a0a06031502 74
    0xd48045440300080b20403140c0000da114140c9141c003509950b26908000d00c441d1010a80342c0d84034030001000300d007501b15414800741513129801c14010f0b034800e804840325980d040400c0020403940c4400082c0449800c0402d850702720030256101200440280c91403007800c1b0342c002041c0081881050f03465040002d1410052400811003100c0300c035608250015030141c0d43d100c2c0003400d071250604c80c142d841501e810103000d452800f40800d40701d0703d8008444814040c0d0381e0442c028851010002c1d00090401c050481e61580d65809000001030401c40d103150907117041130000036825000b130440398029640a080351500504103411700000300440c082856100b500e400c008803010b034801074a151000100c0010703000082007101e040000030307550750055001d42800f004001c411401c01d001c00180d002002155a0741d042c0a09003103588440001c2d40c0d80d84a60002030032010082e6240c0b008008070751040c10700406a84041c6442c0466155210241000c21000703520300c01400b5643c000d10900c041c40707881c1b551 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 872750620 1250 872749370 872749391
    0x10b0c03120109020918040308180111030a05091006030203070b03190e01060603061a03011203022b09090902031507050403050316020f120c0f0d2a08070e0613 70
    0x20480001e03400a00f80c02c0d8002100340d45c500300884d90303000b00c0c0c0b01000103183c6414035075030041140b0401044191484401c2813020703d201030039041401501c100b400003030349900b0b200c0708103002800141c420100610800a4007444a000f5010740800c403034004000d00b008a140c12902503584d40000c090384402c8010b0792140051070762907c100c0c84c2d02c4203184c000103001400c201c8080e0032140310307400020203541c0400c2d42c904440c155100b00c0b415604000400b01d480c244519007640361005c46200c500c3c82c1000088a444150840940210b0b10340c00d0380d071250542962004e010040341e51005000e90582c001c129203600400c20055902d4014006180851030190740740c03038103410754201500501c4400307908100b00d0254038120a0700b81b4143d40845080000d0844421079954400600c540f44d40110001e05c411129981d44031240c1854541040d8a01207030b115400b030410f00018800d00349201452601300c041200790780000e00d802560410a00c0000b16124042000180d0203010382c01456213849204204 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 872751870 1250 872750620 872750647
    0x2030712020d0e0f011a0f22090512030408191b060506150c060a0e120705010912031b031e18201003055a010b0c03 51
    0x102c610040c12001030b5400e610f03005641440403502044e8000ea041002c2c10154112144000742c2e0328408071121f6240815a10100d003c50b040480c0c281c0608240710440040d55166403c00c030b2a4a00c2402902c00340001c07403d0100150000707541c00703003480c04103110445e540c1c0114000c40c4040b448905100400080d8108110542485800211140d6894a040c4141c40c10280807082c030a04001c44040c1c03c00300455401592408001d040081c40c0d900c600d400e07441010144810040e030000c03845c2c07003552019075003000c0380030341401107003198801107901541c00315901c24400d000c121040109041c1c0c001100b450b04501410000c80c11440c40f01600300900145103051260340380c0030442501c000f045100d00d0501c00c000e00705480c400480550308110540684d81c50981c00540d00405007030005042d180c840900c3c102149001c000d08001554440030318028460389900d4280b0928802d806501c0c0000041d0100c2c4c0f40000032280c2c81000094005100140b00c8001034038215000394101c0381031010740074290 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 872753120 1250 872751870 872751877
    0x9030c0902040e0610020d081003081206030607020609030405101e091e06080406020a1106010e01080c0613120512030c0a0906110a0605100905010e370203071202 71
    0xd0655600050401c84075440c2c07811158040380890355608603c03c805006500d90044808800821036850009610200c41d80b4018005d1900141e0700b41e10755200f201155541c1c0c03000c0e503810f0704c2845076000041e10b4901c00240e0910508a04c0040c5081600e02414441c501c19180010410711040c0f2040b10401d05d07141100310840e548a5940d100c00e0b6103060100034030070000c400c0001c20781c8a108800c0c0315083c2c10640b010381103988500010b0350f0715400c800031a1581c03442c0140880781c0c0a901d0002800402140300d84e41030f181000240e0720a4079810741081807501c91aa60722417403524285d820021659a1882c00414030b0140013607405c1e419240300c4084880e40100c0d11200103250200e640200c070390b0300000410140100303044ca20f0a20741c0003449117556021030b483c001c2c0510344401c0018105222900c2060041080f0b810a022a5071298460202201d00300ca4440081c20a175031804241d40783c000781d02d20603400300d0040744401040c60400d5000b9520080107e401d00ca0b083c0700034101a409403006 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 872754370 1250 872753120 872753129
    0x60a0504080a110f180103150e0f0f010c0504050916140304031e092d0803040603290a210b16110f0c040207020d290708040f02060a09030c 61
    0xa0b404103100e0b604000f120b1034054081c0c0c1c041ca0405d5101140d108145280b07034156500711050180c5400594008000342101100081940c095010350f00c400705400155040050301100c000c0c000c0c0c0c0075080b01100d281c02035107d500d90000415021032003a050107107081d05166860314044101407050781106050f41d04c25202200020001d40e0030b14406603a110203101148414600724000710303e446200a141c2204085034a8000e101c4040740c8020340c0300940810007070014030140e80d15a503440318054002d019044c0d050f2500e014001e111038444284d40800001030000a1030031840724104511511142c0481c0035240981d174840b20b18401142c000d248841c42141300c070a402030b6881c0c0d42c45009101440c107031000603aa520a81a03880c6408000c41c154103114800c0e10016103900c00c03400010072400711104081c00e27144c0c401d81101003400c1e001498281589481448041c2038480d0234040703660060441c0d0250120900c03075010001445c0420007040e00391400d04d0010f0f0010344070b40306c00700c20b034103150320 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 872755620 1250 872754370 872754383
    0xa120504060212100f06020d0f030b12060109150b0a1b030e13050a0b010f09060c1a090601030201020f03040f030201120209150901030e160b0307120c18080a11060a0504080a 76
    0xc0c01c218507003199a01c217002d840188040c1c0a0b40d442101d0243c40c4900c00200701046c1a00e420b810105a00c403200b6954254001c10b04030b40e081e5a5a801080003401c1e006da0300141005c82e10008192280c1a50480b6414410740e40c40c0034240001c0120710400c181c5c0400118100010041118065a116400306010a000c600000b609041c100c600e10112a030b8102d00034144086000440e41164021030150b0843e032a900344018902000e182442c0b602c4030980000001c80305080601203000300018072903042c0d038401e03000c403070340c0f1802910503582d02e004511500844031070980042c0b005500c50510410000980a40541080460740000c0c1c10b4412044000c041c28201107414aa907603814040e087c4040d20381405400080303902d00c40421400303410300074000c441e040007001c242e0b90740c4140440340304503420102c10040c0c3e4070b080400a16946585402c5026024540004505000301040f0052407541c0010f40b070b40c01c0c18100b41480555044121304c001844000e01000528000074880c1e03442c410b201d0364 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 872756870 1250 872755620 872755651
    0x14010c030f151401030e06010f030308010b03090709090c0305060702160504060b0f2109030c010f0e03070f080f07030c020306070f120504020d080f120c0a120504060212 74
    0x400034100d5205100c0c41d18401d05120b44030750400080030031a42a192080503c55401c01c011006a000e414141808002441010300028411a00f00d5404095074801d6407800d4a80e682c40400c0c07801c40c0000d880c01c03141d64018200c10010440e043d806600d103184141b4592700016503e1b111281080c40448040000d40c02844010300c0102681d2121307000340208036420003441d4200411502c0500072511000036420001520300005850150307241c414010004d011071081c80e110762170341d0300d0f07800c64040c040456003454448000034039240620040c00c14240021410304c550707a00c03a8580b0ba0500304041c1d440c1c4008022040007c082d684c01040c8641c040c1e1280c20740f01c1154810300d8945075008205004000c2d2007200485000e13800f5801c0094100e03c1480880c407522640001002c0004003e80181174400c0018001c0d500c10300e06000e48591a00345600782d425540340da04a0040d84035410702c100014035206991303100144550300c002e03000f500507140103051150020480b0f50b801c0701926841c10607004e04 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 872758120 1250 872756870 872756891
    0x1202010c08090d021b0f0a0b1c1b270605040602070801020309070b0715020d0506040b0103062115020c0109020a08010c051e1e030105040c0e030d1b1401 67
    0x74500760b044071004004100d0000c034404025214001d0045921400745c0050000c4140c0c0d40c1d00101100c2007500400860106a0b500f1419801d40d001d12130000d04103454104070007090314188690203840c1508038200c60340d0426070008480c0304022820003110040810fa01a034006035106550004c0c140c3d5465030743e580c5082040107490904c03a0b07030080e10543e00402c02c000080390302040740f80403281c680c840340380c0300c030003910f00040040100c000c60040325101103106100142c107070708040e009035000d030350402049180e10011804d40c2c0503800744400e451131511030448190702d01002d01e00c05900401c00c111000c016002100142d034002d00103061075030345882240003946445180c60004050080c0204400022000c0203031060141502c4100c1106540c49c0b0b01d1204664107046030103000100703d200707455203102c241c840c00e503030405e000d403a0049240c1042c5640c514020500702500c1c0000500515038001c10050444110355680403c505c0138070b04414150019501d01414801402c10400100d00710241 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 872759370 1250 872758120 872758127
    0x110a050d1107090e0c191706010509010b030609010b090d1403040815101a040302180103060b030109080f0c16170c01050403022101021c140601030b10110a1202010c 72
    0x54200d1041149062501c1c45461030000d44d0b540703240320581c1d0a4800100b8500d4040280303406e40e0003030143c1803400c22441c10340d0728007180072030607074100b11a00311144e41c032242200741b03901045034040e401081c076400600c0802301030000342068000051400076103a1055a03205e00e1984070110451141d40007107400d2115032018000c0c1c0c81c0b400105000e0100c0e9151442800202e030790b8a11070021602290500a43e0342c0b40c841013103402450b00035004c0c11050341504811440351100348000d690840c07620140542900e018010021490380114001d801c01900444640d050341c00005524000d21501c2003180c006280e0090312001051102d070340b0380b40340f00ca1000650405856400f0b070760401208000c2480141d540800d55441000003146040700303140c10300e440c0b900901c91491a82e1510b0005804402a02c1980c0c12040c100e101030704100c548c03504c80f400150182d03102c0444480d407140c50100b000ca5945d10941141004000c95421205400300d95195850005101d0503103c0050351114000b200d070542 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 872760620 1250 872759370 872759383
    0x203030a0b121b011214060a05011d1306080607051207090e0112171308070f030b0610120c0905030f0d141810092c07110a050d11 57
    0x74140c07011500c4003503801d03840742c44500e0400850062840c1c2c951801c0716900c2860004050640d43c0300400c0032030140310003191007540489400c0e200d028510004155544510f10701010707a0b61404010303500d109440c00b08007883c440c2e1052100030903a00c4a0000c0d407800300300042805004c5a855040d0307107114000b001012214014803070741c140501ca6600b040001034007684907045480c103c00040e681550f628241c2e003200d00310046003101e8a0081180b50082440c0d0022a003103961540881d40225515038070b2555604841c03001a2003103442000081c100e0820485000103400a480c00d4241907692182030f03822910f80300da902000500c0c1078014490b034101006070120f0310607210001c00c4071060003a00101140402803c25103107403804141c13030302c444284000d082c803075000050a40030406041200180712902921524084444521401302c1503c2da00030f469280c028a242c0104165951120039200030048000c0410036200300049500464414050103890489542c0c8071003849000c56005803a090 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 872761870 1250 872760620 872760641
    0x16030308011a040b1e070c0b2d040504020c0f0105100906060c020d1101030b060705030a1704050a0b07090513200a0c17070b161b020310200403030203030a 68
    0x402040306104c00c4441c0400e80c0c0c6404178000e40383c207901c8040d04824172507008203d40248180b148000c0481c20000722000f914202c03516620340030304881d03219882c000921035580c011804001c200418422820700f6002843c0d001c40c481c0c202c400300780e0324a41107130842c3c0c0110f4048205c500c1481003400184120b02500f4001c0c020303444c1c4403000c0701d4640c0024152458080c070050040560400b4803505134003e13000b82c40f00240c01400302e034031100b0034203201e40c69030322404141d40059500b20411b488104a0400a80034980040040440c0710f0710b50303220000d2042c0601420207105c8203050000300d6940d12400422070103551180800c0301801c000d040307441241c42c0e041e4403240b410305110020805900c55002100c00c0c1d0464500c8512420001d088525441003a20240005d14102c08002c0b08080d004801c50000040e86c0d038841140b100c00d14110500c2d81c14010007985500070034035004402460303412040c024640c44600f1204d25604140c41039041c0c1c0503501c01c40150700007200700700301a50170b8840c0f0f85a21 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 872763120 1250 872761870 872761919
    0x80c091809010c1419082a0d0f090309060324031a060618060d020c0105040305030f01080304031a090c0a0906050a12080f1b0109060b030c0a03030806010e031603030801 74
    0x2004001042900c0600c03c54541c003000340c0d03800001c00c220b203809201b0966220709281c41c60010a0100d0101f42c6920049000d0100d5042c00c0105081415503c078406606806035281422507041881c100d0180c80010500314030004148400d0b90810140e10030180107500c19030303985101000000000507600002460b5900c42c56062184511000151051400081c0704803000c5a0740c2d041a80c41500902910709410044d605e88410401003681000c011030081d9068190201c160303907900b072030555902c66404010440c8940c001e114804161080f2230907001401309042d2034044050502003820b17411994030083c083c5423a4542040581080072806d80908840c059030000c405041d00d40080c0e51007200c10744c8144580020b01c0904202108140e2612000c20000900c414200c1d03040c0080908071043d013141c803d000d0030a9480e914605280254120f0343d054032101c845070355400054607404080d08034650503005100710501ca8500e000702d00405107100ba12159082d504025118040e410086054440b0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 872764370 1250 872763120 872763127
    0x70c060632150a030905060c0403051b010c030f022e060501050f040314070b040f090b0904152708030a111e07020d0b0a0b04050c0406080c091809010c14 67
    0x50344420961021408903a200640c1c3ca141c03400c011402003030b140c48041c10314040c1c2414000308040c0d482c02801102e010340c0c00c0301c01c802810644000e803191a0221140403440700c40e80b620000c0d010310060300c1e054110b401510726404120005030622000c0300e02810300740302c08071f1480000080a02c2980e002c0e08003803809500742113404101d103082e4400e41c08080d00018841d1155022490304100c001e001e40703012441a9244c81e9907204006645065000780c4a10390705001090361a4288800030b14451504103102804204007031780b0000040c000c50280001e400166040225006600e92024202510440165a4a1030325519110403101c400c003141d4a0303018200711758a601c40000940740c9441103001e410035038a8444e0720005590914a8000901c0ca5a40004000f01d200c100d40c048441c0101c19207080c800384d51929501038040c451802508003146807031011580010090b03010f448003100151112a080c0251520402088801c843c1886146c0d11001407480043d40080102a00c805030300c8403504 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 872765620 1250 872764370 872764469
    0x306090c0d06020706060f0b04050306071b0b060a0918050f0d0207030308060a1a0903070902030105060d020309122803110f0306150d15080a0b040209070c0606 70
    0x260703100e407214064021900401d80c1c00511000b5809403000703000000c0d000300f841c2c2d40c0d00d6407070f1507542003407191a210340540d000160b0760b24098029104140610322112640141c10744c0d4803122030310050500c40c3c1104500c100843d40d14440d2142c0c11205071300111410120701703903180035403505000b9184400740350459a54011810340009801003900e6150522903417580e03032000824485011680542d000c04800100c0c1d04907a0581d10003401898401e0341500d4039a038854070301c50260f1100f0b10589400040801c12452184034640c06150400001400c0e240d600f403001503200d01c00d8209110031120000b112144503c0c54503040c50b0348589030100e04040c444210003507445815030044407200a1380490000c0042c985640e08a038489000c640ca04c152030f11041080f402c1c0c402400b021400f007407104042040852003000c0000d04481d829446003000245540366404d00502c00406803080082c8000740744c0d03070300025580380100400750075420301d03d0303104944030680085c4102290305c1078001404003041c01503 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 872766870 1250 872765620 872765629
    0x50a0c081618030605011401020c03030406050a020304032306010e1303080414010f0617070f03081b1009020906090708070e0d1401050402010e10050d1107051b0306090c 74
    0x1a8000d007400c0c078415250125003025540c18007200c01e00e40c0c8103000304001000704070059203e203060301c038100c28204150200d1001a80c3d141207120ba070b90741c168418041000b6903440756004008064861068030b05140c0d41b503603000710303242001c41c42c10300d40061076100c0d0912200803c103940c01031050308218181424001302d41045c1d41030810f009420025484005820f000d408658500c9400c26039008010201d40c3c1c14a4100410460140c0302c0d02d01c031545002c2450400c0064200705a420000d202820381e4510b03a10001141e209400c140d1016007040182240c2c11401c1c07102c12000e242d44440410a001d45204224110794007c081602c2500280203100f0341c5d55000d010503a102007a81407040309951303a40d0000310340e4a82200001c01ca003040d0402e202e428041904814060380c401e890f6900d050b10010204003030140e0300c110910026100b40258840702c0d010b50420441c041c01243e18a25001943d03c4143c244040002042d0610301a40b09462050804111140d03001e8000809030060b00205400034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 872768120 1250 872766870 872766887
    0x80c0406090e0406140916050a0b042306040305070e0a0603050604020f06090d1a0f04152f070311010e0c2106070206040b0a1404020409061e02090301050a0c 69
    0x803400b281c200c000a41000519805417489141620f61404145040d2502d6a96520800031344503400c0c1e003010000806041ca606440240d5250012084c101402c0251000c210300035044080c2c1441d8415000400c2611444014000b0f0b6000d030001e0b0040c5400c2000058100300040c010a0006141c80000c0010032400b00c1c003a500140c0c115038040c0881d0340e01000680c10b0082550740356101a1303001c40c40003004a030380b01400c0300c02445a4800c03601e1346d0320340600701c600c082190301910964131158040510704650b8041000c2c0c5503448040284010404031030b0410400698801c0020b1070000340310000d25400980c2c0c1c055404056000b4448040100380d03080e15440c0b081c03607650080c44003512041e80c0d40380b10442c81d0440003c40d01124113038070308628000d41d03a6000b07580a4032000d80c140049855440039003c2c501548015000014054450707074240801820400e0302600c1180d602c4010b0441c070710b041d92154580a4840c0300160b251500202010300f1503034080d000040c01407510101c5a030064012003071 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 872769370 1250 872768120 872768129
    0xa03080105030d3006090905010b0306040816080706021c1d07050f0418052512030804060e060108071a0c06180307060204060305070f024b01090201080c040609 70
    0x42d114855005000313907181024a804200083c141040400c2c40140784e804a4080d6000750020b114458410040c0743d1500703425503020301450f00400c402d03101d446081004034a8207128040b001d02c0c0c054141c42e03407801c80e00400e903002141c803502d400280d4049640e000315410704a55410403040b5a40580c01165a1582807007014000d255240c00351200750340b181d000e00d5100318440144080000740d0300c3e0064442092041841082400000c1d99202d01642400c640c1645c03c42c010039195030502ea1426a00d598008004a41168540120030074191060014a00030709001c40100301041c103002c40c00400e909d03980c010290500081c01108094040010002d4202c0000302c61f400d02d561441620a0843c82940d8028004038000100021010390591140d840f03044580e40c2c641c958801080100d840d60304280801050031032a03080072204945284034a0000a240b040c12421a071968801d5440d840d5441610015659101910025940c001750201d622403c42c852a81c5042d080160150440049008 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 872770620 1250 872769370 872769407
    0x513060c05090939070302060c030c042603161e050309040f02070503160209010b04060e01080c1324081306020703020312011e090506060702090a060f080a03080105030d 74
    0x81090304000c1c0d44585513a41c0b00788144100c4440d0602d04544510307072100e04101e00500c15132001403101c040342000c2d00d00403580303c0d000c90b02d40303842d091105521580c0e2040e00b0b40c040700d9282c001c040d074020070002410280250506203481b000d00d41800c80030341102c165910150b07580440309000140010048030f005c0d40301220000f89000d542c5010130001d001d2048010101d10000424901821440b4141c401c540d2003250f0f04102c0da0b0301c0d00704008490040744145004960910341028843d03009908003a031004821421a04100710800519000c1c0082d6000052804200441800d25041902030307000308031440c108103440b0f0034880110039070b407407e645003c0e00056010070208201741c400d000312100c3e022840307600902561204001e0383d5541400382c81031810b0741c100200051145240c02441d00c1458010309040c03d041f215002d009075100002d1000b4182e596981000c120402d0225a08000d06103500003003040ca4460300d0302400620040e04558070a5000018595440750320541c1841c01807623100c0c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 872771870 1250 872770620 872770651
    0x1d07030f0510260d02100c0327030e04060609030201030e03040501140a121a041508120903010204050603040b061305040203030403080d0209131e1a041805010513060c050909 76
    0x801031414a85009420054044c0f51920030b0780742d50006920b490b00200200410984808a000360112100f06c5030300046094004d0b07412181041400301e0001d101c0c002d08044414038083c0700010100c2e00705800c4040441c010341c6040c819564144203c00d418905d6400440c0390504180c0042d1070407400809100c000c0e1800980742d88841e10445161404c000b0088040c031a402d9044520340002001216240c05145002c401520600e41c4000c1c040440d0030800103402e102030310200b01100c07039106c8122660150340130030001480751980802148035a001d0300d511151400c0400800210b00c108012480d2414140024131015a0b0080100c4d012a036000500d03e9841900c0c02c41d9030043e0182102e01903210506107000c40c0f00e0100d5400c100042032900745004035815603003c00030112104c81c084040b860801b40024000e50815034440300d0380820100001070700e15080e50301c0b40d0940f1070882d07050031480c0c1c10100500c01c00186029242c22441981060f03070800c101003000c0307058010010b0292903190380f9071 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 872773120 1250 872771870 872771909
    0x3190c2c0c03040f0c030606180516141c05010306150f050409110d0f210507080903010612032c090f04030905211501080a0312061d07030f0510 63
    0xf44900c2c01043c4e44160404005d9a1300d040810090410384200745204081c1d011036000e0304181e10403148241c10109506a1194418904440c6140d81e000349104070501042208400003480c2140d101004540002007225811468a50241c8104180032001c01e01a03040c207012041040c603205054850a45002500340c842e0304140c200001100300454004006062803400e100d1040a12510b00f0301442e0a4081d00303505002031604009041070400c0014814001c001c0000c45481c000e020808000303002241c1203848140351525079070202001c0300442e0303036111748520b000c480503414429445500c403060540e006107c00b040640038020100b0702c0502401c8000342c1018002c18210004c0c00c0050031140d03141e030320024200304074504c4c0c445401c968818048000700c488910050300307041e0782041000d424804419601550b00056251140301030f9501c615000c19040e03104011401200c100708a100510300700200080c0840307400b00324070090135040030100700aa40e126103845c0225006000740850f000c4c3d86 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 872774370 1250 872773120 872773133
    0x2706020409020a0201091a010f03031101060902030106021b040501181d06090d12050705070206030702070b030403090e06011d060d0e01182d03030b03190c2c0c0304 72
    0x65400c40291903102280030f18143d42d05502140034680704010701031001400c0c902081c02c0348400d110340d084003100d040092000074421000c810240040c01c0020540702e8032249840182d0b00243c00180c0140d0101103040f41406402034410724101d0141c030200503c0d414582202c00207044640544051134075604207960045000c03402400140506040d520503062401000d030321a05400300c6d020010f440300d0306a0540180c0ca100d200d01904160f2a0306282c00016030900c40160801055031044d0300401c031000400540b201c1c0118480da2207551039403007540c12301e45109041c0ca1b025110380d0421601101c5130005012800b030380c01c8040012544540c4901c01528454050141c09000f490700b542800440007111982103139605805100c1c4140d074415000780c240c1011203007403203490814210701c09061000030a01a0b441306808010140603195856050b6928842c100389000c011122200c5001080152040d00054244031669005800820500800c4400a07640019103849888100003000c1070030800d4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 872775620 1250 872774370 872774377
    0xe0a1109150c101512031b2f04150e0103030f090e010b0901110d090b0f09150c01060503060408030720030a020706120204050f0f0f090907060806100f0c0212010e1609270602 76
    0x41c404200d13801410a44100341500d4020248c540c003640c05c1044030f18110158100010503600581c10500e0706a00c0e40d181245d01030340720100d4105006074145c001c00c3d0601c0052040303000c1c0c44590862075032003603c0300004040c40d52098a20005404c40781001d0b00d1603500c200c55404842140c840a919004901c1d880c82ca00d1240c040416400f10564101030000c0c0c2d050700203810112805002004150380d240c06142e254001250b001301000001c0001940e180c0c0917103180f010f50071a040310060740581e504074403803075039001204040259200d854200405a440360048102d20102603096050a2405011600c40d000c058040792144411908500281e00c1d020350040c0ca8400040c00030b07245080c90062540c65241a0262034001002140081c2060a080303003c40000c1d030746582d800440c2002014200c60340a618482264000d00c0f0310385080401600b4020a4801d18144010f015880c40c1019500303180324103540700c3e0307904a00b8680060701a10780c0b030b000da0100001c03114402940300303403502e4000000c0c0b1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 872776870 1250 872775620 872775653
    0x31110230f04060e15040e13151d061b0f030c221802030c0f0d09060507020102310e070203041e0e0a1109150c101512031b 54
    0x6004100000c0c0c540c4d00c20b242004400c4159103044d5400d400117900303400e51080e4000c0c5800c082c41e850104101082e5803a041d542e00b0b02840d02c440307103d040ca003505d500380c420144170700c601420400303c1d00e40c108105010503a0444101e103954040e841c190b140c440454000c1340440f0805510100c00182080c03041c00465220111001c84034007045010480c1801103590b500511840c0d4048179030f181c2280610f442120300070703500504d18900702520340c400c45600307130301c84512140250307140e208a00c001104d60281034090070041d00090703105c45120026000c0140910417545400b074030340121a0480c030304d00a054050f20440b40501c0150f6a0b262001c0e403461003140e110f000205401c0084003a0740103540049015a111010707520f80d9503e541300110141c2d540401c2400f02c02c0303410844030505180101c0c2440c03100c1c00c090016418103040c10a6182003400c09100d1110440d1a90030403076000b10051441000f0b815852a507125209803602c2c02001c43c3c0c0c0d940c0481c80e02034042d8186d01c0500c000e5029662142 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 872778120 1250 872776870 872776897
    0xb0f040606020d09091415010e100504140a05060a110703050f01060e060609150d090c090b09160813030c0209040c050306010b070f080901170a0603111023 68
    0x81c0e603480000f5a40c1d0540402400000e0f190710002c148040c0c9402040780c0036080b682480e442d6110304209400c038800d02e40211341881386100d1041c42e5900e5055080c801c83c90725803241910b8a20340f01c642c0d85601c081c0503095215141c0d03000300b40810394814068035003c501c6442c040310081764001c2800d25165681e0400782c8540300b11011180f80942c15046041614100e00c0c041900b03423174030010300109000310602280c0c000000100c020000f0150300103411600500c06012951140b80d071a440e0340d1506070340100300e11036210301c00d2205c2814000280e60700012404070342c1141018020303005050040140c10308103407683c0c4032031401c00d05204070380038441103800800840242c2071500d440c14a034805845502e019000340b40000a2034485202030303854043c3c2180c20080480529924402c856010354501810300420202c0035404468101e8620300c21541094000344080c218200f4590482c908060303544180c881e032881105c55640480517100055a80480c501c20056890003504d8130b010f50500b50014 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 872779370 1250 872778120 872778131
    0x4080601030b09160e041203020d0906060905071b080901092d06080603030d02130803040b0a091e231f091211010507170336100b0f04 59
    0x707004000200c81e00643e14801220781c2481800e0380c84054800354890304000c0485e0740c0010b8082080740d4801d06110708146001498440c0c5840d0b810100e510045069481d0f0755194800e1110301100e120701c80d0413101c3c504050340c00d0864080143c1c50003110440003402c842c03011406450360f90242c0b2000c0e003d0030305000c82d070140c11441c00c002002c0b04529000d030340c04244581070004420313000d8100703240a1000074010350700c1c1c02100d400a002950006011840c0c400404000181140c03092000d40090015070001503620004504020160303411900601201c9090888448082081042410844004038400b400d201d00e803070f00d0080c002c15150032590700500f000001c662705599030010003052000c2916400d15072030300c4d01c51603021100f040d0402002843c085000c03900c0380d8081d02c05810b00e03602c14450100031000d0101c0000041d00700351050030341e242060070000002c604010442103030680d408a56003d0001c000c2c411507071032000d16215030550380c0c0d4840d049641d484400c400b544100003d00f05214 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 872780620 1250 872779370 872779373
    0x15200d0513270524010309031b0b1e0112030305040501200d0c1b060b1c05061605120103150204030204090c06110a05060f0c0c0105070804050f0a0f060506060408060103 74
    0x7880b1408240c102a4507000c00100307007526040300090240010000600b4454290340190014401c11006809100240e83c5065002c2c00105080c45014828101c04030300b4103020003e00c0a81107440e840444612454005103c1e682004218003602c9800d0b2070007286035242c03410b12500600e26030801d070410555034025201040074182c0140548a803604007000480c1249004650040440b0448542c61a21440c6403010405941005440c0e000040044412040c00d500e07101c2402600c0f101142c0d15000320041110728100c0d0050300c06c0c04691070070400c0c600801c01490130910401404014018404486100301d5a006907054502859029204010860a60074540d82c001e1080c0f00d4080001c09103242070281400110f000c013507040d0701c10b0041c0b0007a110303410280a990002005040500003d0103c03441100c2c1c2409010b0084010752103812050a00d420315a00704040300300b4000c02a4040c00c146070002e10701c84038000496402000005050301c6080020382d0b80d20695010000b1403041500100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 872781870 1250 872780620 872780669
    0x3030e100e06030a1b0c0c12051509010c0e0108010815070e1305041506030512030705090a091a091006080901060302030307050601090608060402061b0a020a15200d0513 74
    0x446244c104188407580700003000c040b1611b5100b0728000b012400c0d0700c1c0e001c00c6424990a100203c1911950654000300f0500ca114464500100c0d801c1415a45403981070f006c03150404c3c20100139030300a1030301141719810031401c1549c0701030106074242000c1c1c3d03110004400d02c0c4100340e01901036034001d2645036801e143d1000d19024200544084c1c0305021403140401020040384521004c1720340c4034000d80084800e0b20085a45504000d01d4102440020842450f00e55107100400000d4480c0a00004240c0d12600d4458140c000d21181c5501030511081404202c4400380c007003004440e03d61908540b16600c01d2a86c5001d422160720094051001003400000c210012441034165844c4c0b10042103640e90b20a5100d68514081d94003075000039040102c5101514100d1010694001007070480b40c1d040c0c942e0f03010410108003030707010302625182c00f21444041a404114410360000308602860641d00d40da00e410380b11800401c1010921000050885202e080600e2620082444001081941803102ca458 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 872783120 1250 872781870 872781881
    0x6120f0d052a0a080706020409140a1a0913030207030b0c0a08070c1205160b07020c010e03070f0506160b01080c12011b050f2a1603030e100e06030a 65
    0x2900d0041c40340a410b8808000842a940c1c00880d40c401090b9462003503c904100e40e1040c41c050b10a140c0803c0080340c64800c0e401038550003422510a03445038981661540119902609854000c03440c90040740e0440c1d076a000c459405c589000b9104150550b03a150a80c9400030300d80c0010b184007003240c10810640464000b400d2a00c00c103883d02036495440031400c4071400b21864000f001c44520095200d9014410005041d618841d00c2c20788800042c192115644444210340c01c5005a02c42c40840c81c06592000d00d03140700d0760050f030040420320b04000c80d09610241a0050500581d400305a482843c0c0d0020345e813503d0f01c4c0d0040920b13400d03561030304465a1204802e117002d038050b80445018950511052147c004803540942c94000e10b000d008608544507804a10303100b0a10909101c00010107a613030110042030000e204030a28108420700c259410f0180c1c509882d0700c1b0f050b140e0010030101ea0402c0c1c014180e42c8013140c80c01c10114002d501030b901444a0580b0503000440407042094052296111 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 872784370 1250 872783120 872783137
    0x504050c031006140403061a060c0105090c0d05060a02030402040908030114013c0e030d0512010b120703151a0702030f0c150f12190513080306120f0d05 67
    0x10418603a40f1000281c4951640d00110703032107031808210420200b0615402080074542000c081040210301c1c00c005032883d00480282c81082e50340d0700620400c000100640c000d41003041d04c0241c2042c920351506602c03520001d0695120729000000030781103554030b900c6003200135840b548854803542c6401401592892031105540030031550000c10480101002c00d909004070117180e008881550081c030000c0c0a40d0080300d00c01800204502c6083d40da80074400700503040d10640c0d84a894a0040891f080403403c1a4001c03a000402044020b000140f07184420b44d01c0000d5042c041804036880241c0450a9510342c4140855012a07400701003542000000b04a414000c800706c0d11180300038252207440b0b8402030000303984400c03000c0b91a0103030300703084018101412651240070304107811405a2450301d17000b21000e581c0241810095442007440e4482c0345c2d0480120740f041d100401c69603a5128892102038026881040444040d1004a404000c40c00340e51422206840c4c01d90070340940500a80c025121 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 872785620 1250 872784370 872784391
    0x406140c0c010c020a080702010f021501080309011b080a0c0305070b011205010c090f170f060c070c12320703150e0606090103140708030406091a070b0402190504050c03 74
    0x1080f6074052000510074002d582092000d4500b080941c01540c1328410034555000394040d285034411f26a4030406403900030040040910394440520000400c4003c40c0e450200038522a01c41940105440500783c9810b0404c5003803071b260714141d6040a07900350203100b10080204940d17400104000d000d100d48000e065100320020300c04034564000655464402c1d010b2843c440541c00c20400c0060494040c03000b03040318500641e03118a100400c130380c0c1031000845500c010380e800041c0d1a01008100f001c0c1100502440b0300543d00c521265461010070740c0343c0218550326410b0303103440e14200704c902000712880781065011244500d07581c1ca06241e10a00520700640305929040741c14461220218669100e1180240580050307801c5540c0c0d01880f150030414070840e40f10711003010803c16000c00c0140042c1690b6101c100009181410303024010154509500902209000c101c00003883c500700700307410a82c11180016604211111728510300481d600c03e40d409401c00c030034000d58029890046000d19018403 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 872786870 1250 872785620 872785631
    0x2a090a090209030d0e04021201080a03021c02100911040f0f06090b09010515070228060e031b04270b0f0405060a0b010c0b0a0510080d050a080406140c0c01 68
    0x240c0c24401c9000300c4910540680044c040c03011610303c20410b1030000e1000401c014184001c1c2c409050442d03400340c0100f47c0382c1d8003991052052507010005180c00714555902d00b04885650b44000b5141c0001c0b0440e41941900c8110610800112039408401c0700c401420801c0000040346003440648041035001504a1405078089004000740c0a040560003019280c0701ca16483c0006000345150a051400c29518081c888400180d840300750180101881020714045058900220791620b40194031902c2845000c40040841e9140840e0000d100802010100d0344560342d440801c014200007624290078054180f0515000328071140c0c0000a503004248038406680c03482c1c100072034407500f030341c000e44a9400800011503545158108085940f010f01d080f201450190f61000c1040409940750600b19840c0c104109400101740ea80b0001001103100a02d40c4440a03400030f40701e4420300802e0400c2010210004080c016036820640722003803020b140480d07a00c2d02820070790240c0c0140784d88003107550a06 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 872788120 1250 872786870 872786879
    0xc062d0b0a0b090130020301150f1b110102160b0a0306080609061b0c06070e09160504091a060a0309020310050411060c0c0d03050318030f0307082a090a 67
    0xc0040e100f0050701a102e00d05450003a07613180034486071240c0f022071060075201c8800302d980c0700360015500900c0c401035030364904600114041c25880701003022038100140740c00c0c02e400420300c070b01c50082416040b0300310f8105010000e00403401c10240003000700c1ea8141612000810019401c02028182e480c1d40d010032503151109240d40d00e9180a80781070f41581c0c48200480c081010b02c68015000241003582c0354644624908143c0c103241c0f0840d840070101d0014200014181000c40489a105035202d800f03a00035038091401030168000e034014403c00d03d944000b20710341240c0f90701480400c0d0381c00600d9a51600c5940c100140a0821104101e000e0b0091242e0ad0310186014003c00b40202e90111018207642c110105008558200c3c803c1d0317013201e00c1a010300803000c2c0c81c0d2040800301c0a00943d201d41c4d0b40d02d8054910302084d4555a0396050703c0d4000c01001e10f0844016056a0b00001d4500e002c4280751503078030f2103030101b4041c45200c0340c82880580346078504055180040054803030039141c0400d1300c0d40c0e8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 872789370 1250 872788120 872788139
    0x61e130f06111b01050c150424020a08070f020703050f060a0e0f1c090b0a030509010e070b0706050a06031e050601060509030d0c0302010204120f05070503010b010c062d0b0a 76
    0x2108520f200301c0d480d2064041d1158050400b030104200c1c00c6003120340d03213030565020481d80c0b00c1c160b40544080460031044601801c440b25202d155010720b08080d460f010024000904135840200a0401c00002d201c110103003c0c800e00c003d2001350f4000c0c00b181c0c48015450070305d83e207482081d581c00e83d92a142480c0e0007040c60000c206000980441030280140482c01002080c00d8145140660200248800040707007200084e0050548100a60390018151500707000803400c6800510325402164001641000030035003900490304456402040401c00d0380340c0f030380e694021302000c0d00000d120104070140004003c12981661810358000d804403880c69980b000140c030b451048004650b00341d08916100c0050f01e00458100704200d10a100052800740c1d10384016074411541401125561042d00484090060803c0f410340a4070742140200400000071001034825240100c004004031340b02d01c40746074030a028409840342e4261400251a00803081d0003502d008003035101d03030140718500100c0046000c1c80c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 872790620 1250 872789370 872789383
    0x5030c0a060206070c05070e0703020702030d050f0a03020c10050c0c0610260c031207061b171503100b09160f1206080a1a011202061e130f0611 63
    0x9654024280c0c1340c039011805c8802d0390120100750380710310608400160402460b48050b208030820741d801a1204141e104060030550000b1007001001018040800d10704500310071548080c0d03d03414016a559840c80046003000041081380a240386080108001c3c90301d010010050008000140d0b107050755a00440f151502440c0143e440000b460480007502c240c040f00464000030413075089400001503400040e2621800010501d09040080f80410810085004030a243c1600d82c41410300c0d07151001004180c0c0604490494181461f8008a2106100080c200c020480040c003510200110559035030094600c1c44141800f4107502c01c000b41003290b542803014040c1c10142d40d0800150b1013464100c4044c81c0348815080300e903594510018145508004081b0101e01c0303403481c45004420000d0315203090780d05a00101860000072251001652a8011180101c80b000032465540300741400d984200c1c06012144112480346000100b82d1a04080244049410b665200046070450203401601c903103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 872791870 1250 872790620 872790629
    0x10912110d0210020d020c0f0d0f0302091c02270415050402130e150414010e07060c0204020708160c08070b0708030609040212030a050903010c03140f04021908060105030c0a 76
    0x801c2544601c3c2e11000c1900209020440b410003d4113011303403031103468104568882020850383c042200009401e400481c605072a04160400b10704066440c40420180d00c41802c0c440c000d080c0520884045580b07800581410b8142181c000008030440c0c10648041c080607035041c3c07590541705845448482050241921860317000d41030418005e200252034001d0030500c0c580ca0341da8010f02e030507001d4241d0b06e2840d4070b102d9401407800a103100d41804905003101c82d05046004517800856041c0001600071200000c0d2641c1940e00690303488960034042c00ea40203402d041b41c1c112841150f00d00c00c4c0310361042142c0581d00700030240c994890703586880e60302074850208010206142440010541c2c0340c446540750340180094071110740c0c88144c0b8200740c2198007511116000c01d03030100f904004c0341824800c4c156000c00300d003401c1105040444222042c8030000740001c0406a84070001400c40d00c681f111482880804400c00d1281921840c003140c07194000d0003140d00a104021445c03590f45801000d520854 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 872793120 1250 872791870 872791873
    0xe0703060e0420040b0d1b06090f0e09100c020a02014805190308011e1e030204020f0a030b090f060d0f0b0703090b0a050907050609030f010912110d02 66
    0x10700f40c0c40304402d684050f103441984240c0e82c0b080c00089072112030b030061b100c0b4071510410301246030302c3c416640d1030811038000394200030400c035013405540010f0001d00181c520b0180250400d40d1100d021510b0080002078000509081041c004d4280d41c00043c1281d045101b622303102e0000d81502d01318018850f2034224000861401540e043c1d080080180341ca4800c50700301c406c9480da20454035960b01d00300d600c004400e14003080402d458241544000049d000d0403003000008000d0444040303c60300d00da000d014001f8104a40e92402d081d040f403400c130000040d40c6c040e0055441c0c0d01e44482212441e00281042d40220342492841c43c02880c003045201c1c0705c0c406012248085031a801d062022410380810115060714543d4864408118002503e510442003581c01248040c0c19140901c1c4d900310141c400b4002038200b03002d0000c05040803407984165a01610299280d0900d800000d29221405000b50440d510308034a420a010048441c501647c0081c1c903020751003020300300402c0c1d80f480002401c0005 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 872794370 1250 872793120 872793143
    0x2030f12030a0b010c0c0e0f0a0515040e0a020a06271d0c160c060e030f0d031104032301050c070503040e100801020309100507020a0f1103160e0703060e04 68
    0xb11a040e81c81164840d03010725100d10031201540e6014213817070141d08070112540c4d00c0c0d0200403000350015000c035844820a00240100d040400684501c0c1200c151128401c81d141d03c0c0c11801201d04005a9802c603070014844607820756a01e038040d02600115060349908002808041c3c131840a401c2c81904407809002d104060450204115003408000340c00d80c2c203d100c04100e00f1707004400390005c90b00e04c503001e0900704000a1904102401c40c459550025000707800509545402180101e2810500e2440d0300f4082241c1c10038107242030031071281c0d4000503d00c819954a40d44880c0200303044440301078003280208100e40f2189881c80300e90040d0000240b0552041100384598a140520150014844c80702c0203015500c800f45582680c10407200403000743d00904080c04c495595015064000010340042d00401007d9140c00c0000ba440540280079480280c0ad0a480c03070b24100020203009140154400989131141c0004160110948806000a0801030041044400c1240d124002d69200030080003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 872795620 1250 872794370 872794381
    0x3012d090f1209050306010306020a031413300905030106330306210201080604020c0c0d021c0b07090b25050a0c1401030e1c11071d0402030f1203 64
    0x741c500b04545582d0801000440001c1c09031030800c00240614032825016071580541c0c2e030010111040101d400640c0207890301482040c42c1c411600c2c51406421a10140c030003910307040740300021140c09512140e485100b0b61840030f4140d001a101d41a03030400c4000380141580e4074070710720540b80030030789407030310a00d920408404151040d01e04940c1030f10f91f800c0c00719070183da5034074202212220740007580103c220300c031146003150b80c010a015404001210704508081800c0001c0c3d0b41c40c4c044505642c02400589000b100307642c0d07101c0b484200030b956078003000303200d1803d840d256202290030346018010070211800801c45030301e8a0141c80c040c08401300743d0701010000c40c0040c84070308481081500c450080401d400f000c184061103900c05031200100c4940c00b1002800010304640c988130415207103800c50074010301c8254240034003401b20402031a01007071141e40d140100d4140030240d0300110259011000c00b03014125a0341c1c40e0b070311580c001c90030b69039031303000c1c040c0c80710785441c0302200402d02c2c01030070000030740d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 872796870 1250 872795620 872795633
    0x61503030a0f090b07060509060907031106090a03080c0a052413080d14010807050102032712060a0b040b0405090706050a0c06110432090c0903012d090f 67
    0x112180c00c0c0c1c0c0f0300010360360f9640c01241d04a6010754800d540150320394040001007002041416003080c00c10000b1b20801d172558039440b01011500152238400c60000030080d1256559200380d401641d0400c49181e5911202c010303c1d035a0741d40340142200d090082111400358072042840c4400c1070b0391404e41460b603a03951805000004502c45404594524040c0219440d01c1740318440d810210304000407000782541800a403600c1c185240d40300c2411580104000141c103d40032030004035120b804000c0c2880100c901c000104810007000d0920000e100d44410070407008000d802035440a14240d8081005200c003806000035148100e070075007841d03401000100207a52050000b0004034142c1e251555050031107644007400e54840e104410010400810240038520300020302524817184268400d400411601c0002d21307034514101d64030300c500500d00003d13030812801c8040302c586540003002044806a284803042114510034000446007500b4408420000900d00c12180e0310364200120034146079480d0340d40d2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 872798120 1250 872796870 872796887
    0xc0a03030801030627060b03011104261908120703090b34030504050c041b050307090b030a1d060606090402031009150305060c0406080105061602130608061503030a 72
    0x4070310710186900b1700041041c8514501303020b2032080346d002c80c841e0030700d0081509607900601114001c02040004202c014907060707100540c6000c0e1180304e1196004181d006007805401c0c0107900141c0d078810580d00401c80c040c2d00612011f42000d00303c03065501c40b003004404880150b40010030f031400e090b020801030708842a116903842c0c1490000d0300c85080146408000080302c200203400b190b1504180420010140b280701c2d81c00740d00390760800c011004103106008909c0ca41508005000c0c0000c0481c02070752044a414000d058035503003103a6242406e4899100806040600000003e00c4008909880401040040c0204c2c4010035590610045608200003035002810402c41da41e04400c0005400d01e10780190f050258004110800407441e50410030b040180080041c0c80a12040005000c1c80b908400294151042543c419450703481a00301e049085059000c080d40c0414110303200c88080c19160407070703426500c118040c0c0d0180d0b01c80e921881c0c85d141d01144480ea05803c28885400720602c96000b4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 872799370 1250 872798120 872798141
    0x305070e010c0b091e070303140c0d0c08040f0f06020c0f0604060e04090f060605030d050a0206072007180c05040503070608100e0c0306100c0b06010305092d0c0a030308010306 77
    0x141c81c5c03019000107000040300411503d4034443e400480040050580204010b82d0000a1207517039460040c03482451519052815009018014038050381020b0240030301c19103026000100039040d0041d1074000034002500c5074842c140042c481c100705141c4078202084103458091002c0c201600b045e0418500355514030710b00301c00d80d1b04035503130f1452100440c000d158003002c40d81c0511030016025003001c06250404426410500520204100100001e035001400a81c00030072450040301001c103814080c80c0d443c45611001010748035600c400f00d480b162114943c2c680c8003500030b0410203400900d4003a00c2c14011845050340c141c2181500304052801143c02e41e038024040302c0c40c11505034031540d180324801005d42e258804040c0c0801000b4450501c0c803100300e01d012081c10405680300f59a1350314800000c004188a04064035a404900f000404021002c443d100944a1061503142d00b2080c00c1444100b1901051071722810b10042458103040b10a1030a803078260b52000d1050707085868000141510080 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 872800620 1250 872799370 872799373
    0x606070f11010c0204020415090f030807020d0609021008150102010e07050f120a081c0506130f020408010e0303160509150903070b0708030a1409251a0a0305070e010c0b09 75
    0x243c180160786500c001c10103429800103081d42c90301c0c1d000e8002c217909519008a500001d0078070041c4085601a015210f140703030704940441d0500314914040000c0c04451340001d40080034403202c1c0b0711840c1c100d491148100f8070b0044900c10303c12440b004a0a890035081004482e800c80602071259080c25880b1003480c010103003060a541414114803460300402c4641030390b50003404940340320100c0b94045d440d0503503030f0350702d0f81845641007600026201001145603415003580d0303000c1600740e122254050300c0081c440c100c02040752101c8030340026207035807080b40d20160038660003084034070b02d0f4044d4090f103443c4a0060001c100380902102030b401c80d81e02c010001a410f02c50340c1000142c0d1b903514001004034030711881c100368481c2481d02c1e03420103441400081c000e143c0715210801840d204002014440b00b04c01401d0700116054030306800284410b107800159032209220001041c0d0140345c0002c02c941c050a85d0208000e5a6241c0c00301c3d0840c2d044104c0c9400a002030a0840104005000c9203800c510602c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 872801870 1250 872800620 872800637
    0x90a0e1803040806011701020a0503130f0c06050a120207120c0f12030b01110105011a0702150c010e0d0315060521011e06020c0a0e09100509060a050606070f1101 71
    0x358007480c1d42c00aa000e204940e001e6001808841500813202d0b00203190b0000a508000f050100682140002008aa031100c0c03070b040f40505000440004042268115848094554940200800c07030361010b2481c1001c80e9141e60520024013051007103503405904400d151010b00034a0400b01d0350240c06160948041c1c0c0b41c0c10f2810042500d482d00c0303120140032914001905821032001406140e44000240d20b5645050010054800c041780c0051201d42d104c1807695803030145100044002d2680803103101c141e0001f0407050300e10b0405520126544040400b142c0b518140100210b080d2140c0001d114180001030800308800e5000b1005054055150740c800c01f105950264000341400b000da0101c4403c4028024070404200342044203405820701c1e01c060803e051000e400701e5400403051080c01d00d00582c0c0c600141800c44203003c5190f1611060400780103030f08120400310303519502502e6a01e001c03860a0082241e40ca0240c040344c3c511540141c060f601c0b110710b83c1360a0f00403c85072030aa810701c11130302d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 872803120 1250 872801870 872801911
    0x2b09140d0f0201050f0c01062103080604050a1d03040e010f150c0c05190306050a022b0e0601090906060905190509010e0d260705070f02060d0608030903010c0203090a0e 74
    0x1500600b1607640c500000041c161318142c52701c0410030074140784002000c9010f84a80220f984410f070b082e404002642c1c00b0540c0d8440352411402000560908403001403c060303500502800403000700200ca0440c180c01545036218240c603180381c005032207080907803210a030030006154081c0d00f11901482c0030340d280000d0141d50707a000c94488030840b40d650000c01802401801088400e00c2000d4001911407070442c1051481112602c415402a034103c0340c0d01b440180e00b04061200d60031140142800e0020b40380103581d41c403204805400c40003400c0740e56500f040da02140700c0ca07181c4501441400140c6c4030300a031070a82401d9000910001d0f00791a841e548030508034a1040081190022810859403403814024011004c040114542d44000c00100300b0030060100c219408400c0c1c4004a0b005045100e0202c01440090769505c9800e224490890070508002014400030006e000030340d009400900000d0701c4008100e8491180f40000340c0c1c40150907000384003c951100445510042401b003000642005 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 872804370 1250 872803120 872803147
    0x3030305040206090a0b03090d080714091519030614090c0706090b1e0108010b090f180d05041806030b0c0a03020d110705070e070815032b09140d0f020105 68
    0x80d50403150711b419002007440810001009103441c8010b81c1c2c640840f41c0c0c20841002002044030010640c6021030200d41d00c1490798910450010110281c03a400341c3d980141440040584003140c0a180441d180880004019a52002070902c4a400900350751003561680e26060301c03030308185070680308140d0ba0170b00071000401c5080d101d401035100c410300d04042c1541550300d284236401600016040c0e418119110650744801501c00d4029400150303140740341c1d0342d00c0c0d8594042d241c1c846884000e0300c0f4200300041003c0d00302008001b628050716201c9108d0000049034026034a45100040c03c0d081000009459154070300d01828026082e450007526148403824002d00351003580130300540100001580f02e081110410a1038000c010b10411043c05180420000c0c02c0074100900b050718260340d070b8540042c13a540038005194600340c0414415500410700003542b05407041030f50603901003800380d400800ca6800303001061910744070003003041800c1e6025640f0f450b21054801000c0307062000c18010313540e00480 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 872805620 1250 872804370 872804389
    0x12020a08390304170a0f0b0c0c06131a0714090f04060902090f010206011a070f0b181009080715090b360d030b031207080c0c0a0b03010303030504020609 67
    0x280c1c40110b4a981c2800100021507507198007240041c0c3c00105180d0004944203200c5048603013200d1880d10f0341c0d640055030f50440c4075640e41002d40340101e204000b00710210306004030710300e4044d140f42000f0541c4000c5050010200b50b072800301003814141d840c681c0808420003044003030b80c060981d03910480d0f040003050560b4032070b0b0841d102e56030b008580d06c1d40c142007407904480c032004240300030405540b40050040100040505400d041000080c00b5410300044a485545030f55020a10514500d4420113515502e44460041e80c42405040c45030b003c0c4440b0b901402100d0b68100100601d0314816603540403400802c8103840005a0f152010403012480c02110b587c400c201da0070119010092401c7c2c210042c0c004080d0354041352070503012448038460009081881c1c8040da00300040c811403281c0000f441d140400d051140300080c0001c2480c204003600c03000d00b0034007800100f100d03150001001040809421805507003072038a070500040011a119401031a003190024103a0b5203400002000304a0203034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 872806870 1250 872805620 872805727
    0x72a0218100f12060c090f170309121b01020d091806091b02011401140441220b0c04080a030c02011d0618060906130312020a08 56
    0x2c0d145100c031028803105005d4200106050701d030038000d16007031400080401d819401001c6a11840c00c0710040c840400b0401c9400d044d01c014440c0300680081e405040e616907111880f00709080c0c1d142e600342c01c0c070750001500c030414100c20341f500343d4a00c0c1081080c00714140c000c0082c5961945031200041c40c032a10b88165513466005115000c1e14610808000e0700f90b480490900200380507590040143c4043c2001e0300440107412100420340b018070400d02c0d003c0074501c1c07012491913540420044642c810b80549a40740c2c0c1848140784140c0d54614910055100504880381010803540e000b44000810a151045d40501c241010b00d040a8030383e03010514100082500f200410500c01841c420342da040704401c40c6130744250041060054040c408115540115a0002c89549080507084000d40c0c0b00c10a4852152015090f40e450310f40100744904504060300c02902c0030b0f10765411076084148041800c034405074000095500c0c00140700d1004034101203000305402044011840d0700380c070310150803030b96102c0c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 872808120 1250 872806870 872806889
    0x150e0c0a0c06051006020601060f09050d02011e051e04240c0c09020a030e010213060e040b130209040e0d02070e06060c010f0b011803051903090e072a0218100f 70
    0x174107011001e440c003041a00a00148881d541421007029400300b42d14068030820b5a12032240700340343c40144e03505480003c10802074045004c1654010b03a1103405091b90485000740c000a2900c414000b003607510450003100c03000c542414107d0701c4424032880c10300c0340032030514001120140c1a04d4400c7c2910441d0050351080743c0005410792915070600803544019000310085103070016005009540924601c600014040ca00004410307171b03602c0380c6c0111007421016180320540541c2100d16002580038580c140d100791f20b4610342d00d0034000000360002c0140d40302d030002c3c074001e0f042c0380641e24080d4000340b08940c0403104202519888000b80070b080018446035001040d0b50702280000340c50607004108040014134045000c0000c03400001303d4001406011250750315085240c2012900d14007140c214071014003181d4140300c0740075072101c02c03d4074001000c01014540b0b1a0030b24403501c410218500658000384601c500c1045201c03107514107400c00305100340c07400002d58440c503044103010103601c640c542 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 872809370 1250 872808120 872808151
    0x40c1508040c0501110a0b0a061203030905070b120f04020d020d030c1a0c0d1503050f100b091b03090a02090a20030103080f0d140a0f150e0c0a0c0605 66
    0x4001d040b101003006414242800603d40003044000ca07075070b07003140700c001d40392106a40102c0c01c011400d902c010081c0c210340c2c0e0070047d41d5403107090140140840c441c04840500c11510000b0302215100161005200d02694450f0640c0f04c0d181c154008580c041c2c02640d00c20f8401c0c0c0130400684c0d5100700f0300380c442d01c26143ca10b1880385c41d00300044004506000b0000740441a01009101c1c544407044820910b0016000540052542c4e00307000c1159060300024124807480c2001c13000500005040c4804420740740b404e1000002620901803c00000d4030745924660004181120028080d8041d40c0e00411304802c03a00041c000b5000180c0d45c003000c0e1a110741e8207682e41008031100502072601d01483e21102e24042c42e5501d943d9594500d48198109080070a20215616001c558682c20451021a400070140098140701144030010b041c40a00c411842e4946081400f803074180c0e0306124104c50b40075000891540d515071036031081c0e510403004c10701085098920320300000e50f80d21074070780110b01ca199440d40 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 872810620 1250 872809370 872809373
    0x203010f090f0b090c0a0c1712010b040b040308090105120a02131a07060b061204120f020114011517130b07080f01120f1e0507060309051203040c150804 67
    0x40702c01c00340104001d18200f8143e40c0c0e0f20746421a1164001d1800d610300c680d94010030900b12a031418a4100034500280032800d080d55a003007002929440d4038480b03140038941d980745400e41c2280b10301d12800040600070b010804c0411400b00160040322418104113241648480001d02100800c071116000180c1c045010002044001081405000500101c040c520110003c1450901840d68020450b68588024008076101d030829a8980344d9000b0207081c00341064a8840c202c0d501c404003c0001070195a10206407a105004141621404001440c0e0301d03420854030100744034404405000780030700020905480b10400c00128413a01510310312808a40380f9261006940d02c003c0d01d0441006032550a01103624140c100440c112002030103100c646003072b50726000c2c460040001010b40811051000000c100c0e042000d91020640720b8010307204c03019100c030380030350844004c0030002e4201c1e84184002c007100710701d070350095403c14000d40d02c2d0346076296225a0301d6002007401018400203102c0209100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 872811870 1250 872810620 872810639
    0x80a0212180d1404050603070912050705030d080103020d1202011b12050a06051305040f02090f0603120c0304140f06040b07150c0c0f030e030106080307050f15180106090203010f 78
    0x10120b40900c3c10300000550000071140b540103074041d003442a030000010802c0140030746003903030003011400c00c003000c00c40c0c0d40d050654840700309100e024001e009050f0080c04040c420706249040e60340c0105496104103868580700f002d8600ca409081c25990b03180d40d003401e00f9001701c04d01000c20919942e0402c040110f030110205542c00582110360823410071206000c150f40b090250100c0008505000031603666606040204181d84800030f900b0a1075031017803100441042126034420700080d02107074406142c0c3c40070048039103f2810022a0383e0410300081c071418028003800741c041480182085000a084c8002401c1548550311004980704001141d02c100101c1d0001035450b180e40001c20000841000301c06841c1c4500301000902c040340b1800f0103010140079a0b0046140c5d134000d40208035064862034255540d52051b0000d0b6114400c80350b03211211140060350b102001900914600e040c0c17901004440101c40c1464458115522802c01080d41500ca101440c003c2ca64941058252450103400d035 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 872813120 1250 872811870 872811883
    0x90f1103073606030e280501060509150301180309090c050405130b0306070504050901030f080d050c030a0e0a0f0f050703171308011a0910170307030201230106080a021218 75
    0x1a0207406c4a21a4036040400d10f2405258101e16000e40000c900c251a2041c01400c1c250019a8400340c014248000e81d8400303082405103d42c01e400800120b40d0060b00c1c00403100b43c58000030001450040240800c6950380c0010090b580e050600d6800e05071200001a183d203115904212020340c0c41c540d0592907c0c041004581182850400e030b03107018100004140c2c00141400080c00c1c214040107100104a43e20084440300380140b0002c005900781051400610352041d9030041c101420314401d1500c0c948041400ca0240380c2c04800580d003075440c0d0b07941e400d03a8150356205450310b0141c0c0e42d001000c142c034003400400c100e01901d0041c0d80d0301c68540c0401c0034400306030800695a032404108000d41c01c010842c024400c2c03802c4030640419941e00903032060800780c0d50012030100d2850407031400c1c2c407a4008050520700e403194000b400081a0f403d110641910a00d40860044803204010400a40504503040d04001d1000026103004256405401003040c195250100c08185c0303030390175446072014040b0303 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 872814370 1250 872813120 872813141
    0x1e09090d030605091033080906280f0209120a0b0a02030705180420031b03060603070809010216030809010c0201050105030307060e0f070f090f110307360603 69
    0x43d081641054032000f08400414000c00c2c50742c052180034140784c2d070120b0340c2c1c070810030401241180d06d0614414004003048002c0d13821840c18466040450f07605019044840d6689480307581c440746100001080368064100581107068080d0b08200c001180d1f12013140c08182c078510940200a11102da1801a030300d5003005107031607100c600c10b10900c50300075802021070b9031507590256079040020842e00004c009007125112400812012405426a640f02d0b401543c4648aa020036402d40c010f052a2400184021506ca40c1e00440c10000102a20b0180030034641002c550030006080080074486006003219408003540815041800c002e4030990901810b00300c030202d84001d000c41c2d490403010071750700e000d43d8000408030303910b41c0034001e0b0f540c0d82000008020503498007103990003031791150220601c02c0f0343c2c0154000b4074103004a81c0c3c030005240c021121200b50880a080c0345584511341160442c0d10002110040110856082003c1707412060100b1074034120071605000700c0c5800405004c85407074031003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 872815620 1250 872814370 872814379
    0x2032a04081b0a050111072711091503101e170c0109120312110403020a0b07030c03080a1509050a1409060103030c03090b03010810111201051e09090d030605 69
    0x1c2c2d8400e15120320b188802120f80030300740342c2c072500101d200e407034140b0170309070401c100703c030011b1120500c00340e0089050050a10220400c015003a4110359001031849282c041c207801180d04041d282460f4900303001140d0015001205000164542c660a43c51a645106048109240d010148080b0b000d01628a290080c1d6000610b0300d0400f00001901c40501441101036040c1c49100b244141030080c401c2d06a540e070301c0c90b010082c1c2010610341c80910342150205902910700c0b00c3d00032071141503681c02c50741c0b6241c00da2264411406969000c40380c0c25001031900d1402915843c20f000d030b0310f54010a00000d400380d0310000c5000d1a2a4000408803800d004100c2d4005103814144140d10801140041c10750f40c06161000c40b1810324102926001500e903c09807100318004000254076801280b82d0980c1400203c06000070443c000d0713040200d001c1c00c14003660484a45004200c64034040d4a07420304461022040c1004550000c00200164130444d00782010f80c1000e4240d4048551511034900a0101110b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 872816870 1250 872815620 872815663
    0x403030315170703080c01181a1305030301120303111908060d0218090c030601060503010503010c0905030d030e0f0a030c0c0b160f2d05061605070602032a0408 70
    0x14031658a0f8410320003d03260103400102c00651035001c0d0822111145500342d1450002e00d50b10301402e030400c1d58804907695600030004548548100b13a40c151001c2e811100660459007009001110429060f00840c00d05a03602c1e111440342405001804611a400c03242c030459640c1e0703101c00340c0f42c2500140814414000c4031f14404c016540d10906c4107001d40b10900610242ea5a80749062410242e40200f0380e161103644000a01650f0050040d0b043c0c400581c02817080c06100d560039201e518040c020103038550414a2200b0446100390321a444000585080781c0c84540002c80e11424a10148810390008050a42260510030645000c0004010780e1021502c0e205100800340b0464a500f80d000340400c903031902e410148842d04020481c4000a039407450520040002680d000000c409401c4600d8002c21002038007410800c02c015049110350744a45250007070560352070b4020350006003070f4441c0c1c9020b43c2c1d189030036605e640c2064901c002c80c030461698440c2041d005600e0600c0c985521850880d20341c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 872818120 1250 872816870 872816909
    0x3050d0e1903080315041e0c030204050109061112031003140601150c060204030512190201110d09080c10090b0907060509040b180f180f2107080403030315 68
    0x8409007088940210030103450f41c403541403030345010041088080d0300c54280a440140d02c0c45074440c00f00c2207045120304000d5a0750f2a00203500b40d0255100719400b080000004000482c0640060b20b482c003a5070054030042c601c000940c103002d402c207540030707600020345140030310420a040504025496142c8020141d0b50301d070041040104c64a14102420441c5000d0020100714090701034a003d9544101075860030080708030308106903084000c040107801249000d10000b94010700c6a0300c4007948a1480b546401c10310300b5038002400c1c81c400c0c11140800c007004001301041c01444504206840e15101040c80c45190800c5408088043c0c61740c0d0082d084001c0c2006000c3e000001c132841c82c5001e0328045501001039002031007022034120110980300c9034400700002c0700121405180f140040000c0c0030280c00001c081560380780d03c15945400d2aa02c42e003414620148079803007100703c6203443c0c802c0b140b41c0822540c582c1055002030f4811000701c0c1e03c4489954024214020040141c0f109500940346000e80 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 872819370 1250 872818120 872818159
    0x14010207060908070b0a0c0c1202010806040b0904021504050a0305030304060c02161a0c0d030504020319020105030f040f150e07170c040b1c080c070b09060315030709050103050d0e 79
    0xc2e8840c1d521700e00d200050081030319000d00201c02ca419000060080300d180d0316030141182d0315800a0482c005580400003691914162041c840c2040c006000190103945030350a01032015040c09a248411009100000e41a03035017841a00103103200e41d0186483c1d0409250940a48080b202d403801550001da181121110280c0059021580103a408801300b1031220352845aa204009450342d0502800e085c07002c2c15501a0401d901440c82138085074084182c025040100203001c0f400203000900800102c0c1e4510707180101c85030824011580260121600d80c0c0c0c030300024101c00c1002c00301039140d0340507620700c19090020400404e1a000504038194902c0c00305509c460803401018841d560391210b41405450f201c44d00000d0000f000f0419000319100d00b842c5010340c00108418000740704100c07012508944100c155100202d0113041d039415500c074404506541807604040980611400d600007c41507a03074020b0600842c010000360000c200b2000009120203403241c107080c002d0440d50180f1014800 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 872820620 1250 872819370 872819383
    0x10c0221070210080c1201150915020a08090f121c2a060e10061a040501091503021909060305060d050616050712020610090b09060405130c14010207060908 68
    0x1401d11305500c071666104000d07030b501d001e8514010502440000041141209042140204011501e074062055507444061103c074440c4621480141c10002804002800030030141032010740080c810541402c00740c0c081101c44030b0031000320040360320440c03145ca0050804111590302c2c0405181580840220f072000c0802c00403000840001c050708940d14000380170107a807107081740d91040b00544031504e40d03e044150142c03203580a401d880000d8412245440407595040380d00729641070b10360070811031401c80381201a400c602d00d40824541c080208007030032400540a0380c8a109a40c0fa00f100c881d00b400ca004086407001000980070301142c02c40362020903400100168004100c18540c0703031010240c0c504a51a0081f0880100050031810207844c0440c0c0124030700f8418048d0701720300030f0595511511902910380001403241c0165052010509a08054104e80e906c80c5c10506019402c08940c0d07240c1066503065440522140031030a02110a50790500181c0300400403494488107035070608816545450 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 872821870 1250 872820620 872820649
    0xd1107080303042a060804030c1a04110a0b0322030908060c04090f050928080f03090d08040f1203060b1201090b120c10020c060a0513050a06020309100e03010c02210702 74
    0xc02527001003040b0400c00c1003203000e081116203034003a0a091501c885003080419130729214a03103515001c1401c6030b5400030340344241d410400554683c20301044241c0fa108075610160100724200f40301107401c80c41046024003c1480641d610380d07407441c0001540072261707414614030942e814503042c01310192001422081107442d203410115403043c030307112044040031482402840000c000c200c10510f13050310801396205501e01e0060311107400e60381c4411a0f40d840708440082c282d54504061001203041404544180700a904002034090784070603a0f558030b60800c0340c1041c90282d80000512418800e409007642810040e80c104807005c0c02a004a51600f0581d40c0750360080344030021040200740300700305a104050010341011b648004e0003d0044c0aa4020420940300c0c8040301800140e40c140b8240e05821a019a4041c5045c030308031030300300303c000e100350b403150404c2146c41030f944089507400703200c3e0444040094004240b004080e8080250f90880001c3c0c820014000b40400409a00c4280e5404000ea = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 872823120 1250 872821870 872821877
    0xd02030307030605040515220e0604020315040b0115091205030c120a1b020609150a03050105010e013608300307050d09050d031a0d03020d1107080303042a06080403 72
    0x501e00000c0300111100000724284072704049a0000d0990b01203442c81c06507000398150b8424903e180500b40030074a068a0092401c0b5203400100f0820003407154203881d40d0024a0105200d9980c1c4040c98071050300c80700c095405810010300750f0410300042005404406007886003d04004810380040c007408194a10b079121b502900c400e200465070344d0411503529610042041c203a8070505082c980c41500320004020104c0c0c901000440d0781c0d07004042c1780302501d005a69504c100703411440f20300758070741501d03002c1c4010001d0400e12070b0000c0340d0918800007506540005000c4404864100285014001d5081492814030041c94401c1c0f6040c400b140c3e807110702070400540d2002d844c03880304c0051640f010080c01d94061000c51005070395050b04a5800600345050f805110001c0303030100320303102088001c005c01680c80303518400401c034010300042903c1342a42c001c0e14440c60343c0315955421644115421903505580c0720242c0b0964020381444d4140e14980000001401d060400240064070040d1015050 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 872824370 1250 872823120 872823139
    0xe04050117011d061911030a0905150c030c09040b121c0509101b080301030f0c050f01080411010e0a14120307050c0603041e0609030e01051216020f0d02030307030605040515 76
    0x600410745c124207100e900324106c450f136a141140045c030082c080b843e403c881a0103032002030304140c41040d140c28000e49a01014a145854900643e4010ba2042d82c80301d80040e151509900c0320b50300c5000d9404669104c001400c4000480034404da5400020b1002c40103101062207040070903121500c821050010905009101541c1c0d42c006081d4203d0710303100201300e00c8c2c00000100410000701038140f0030030720620301044c041e034032a82044161200c1c40c142c2800035005c0000103012030359034446e102c0000c50605140007e20080d07004900d00d0b4501340c020710070100f545208030302c0c00c2c00d203240c0301032818240401039401e00000d5500c450702da04092018911458020011a00380403020750740810490b16070780c81405041031403401d20042c00e5000411380c041101030f030000600394080d10803999401a041100e65203030b0342e49101c0100c040c540c40741110451090b40403140d840b50302002040303141c100a030019612481c00700c0005003070b902c0c1c80e0013241c001c80c1040240b160a02603003812088110084440c6840e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 872825620 1250 872824370 872824411
    0xb04030e0d050c030105010906120f02040b10051b340902040e070201060506040807170c0603011e0602031c02030612061303080906010303020c100e04050117011d06 72
    0x558214880c40607620070451460300041140025681460120940081c0816aaa50302440442d551445401c1010743c44059120002c0e030000c03c140c7c090703840188005103401804000c64009402c4058040c04030b600000c91188090340034051040c05001d600090480c00900e81c4907842e18840711240c42c1d0f014407515080c0c410185912402e001800903d0421134940f9a54410300003644020f83e510b8000d546402c00124041c05e18000322015505100d004002c01072a1107081400500740300c030b041b02d0034040c5901001c02c07580c0f202c0066000344400c507d151030034100140000381d5150a41e0168066600c01c010b19030200d6030341d000c1d0301090042c5140068807070751080040341090f41c00112080e01da00601e410814941115548410894060b60340c000c039658070300e5003580d40c84078280405005603100c0b0000440354070380340b0a44070f1881003d01d0410982d100000c0428155602a004007105c0d41448000d114101780900c03403141c08a03400c8006c0d0b0340410f400b046241d19449c01801100569849002546 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 872826870 1250 872825620 872825627
    0xc08070303231911041403011104030f0b070c0308070c050307050a0506070201180b0a0b0d0b010305150c07030906050f040803130503070602071d18030c06150a030f0b0403 75
    0x304040407002c4820400c1450750000c90008003194209120a04885000c01142240c0f00b01c0c1100c84025503038074074150910701c0403000e111a14890982c151f403252400003c8881c03502c007410041d4482c5243c46041a05842d103010004401005182080710b88400000800e40c401004c0d40c000100c2c3c20000381811035800c2a6042d0710171290080c00c98420180310004105c00010600e1141500d0ba00820980c180e501d8686004106010043d110200c1ca8012864100e0700d030b401003403c20350061056007071107000e603503503541920240e00c02e440c51b40242012442c070345428a40c01e87d020f1115500c0d18030f812050b80d005004d45600e0700450082101c0072a042002d840c42034210f03400703072400c00c2c101c0b500c41d20102e6191081816500980780030b402480000145039000140d91015144003044c041d81c04109200152041500103107015220383d4100c2d000519005d090000f01004030040c0050100f91600359922644169451311007070040011000c00c1003c04c0000300602c24a56104441c41d0390b945403814108d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 872828120 1250 872826870 872826881
    0x1a070f0e040f18110123181f0f020606060f031609030f050604020a0911181908071703030f0a0b0102010b06070303092a0e060f0306070f090f0f030303150b0f040905160c08070303 78
    0x10b03a101c21103107403070150007a0004012540b1480c00d42c02c0b200c0e5680d0745020b0007064023b004e814560540c05001080086000300d90000104d440c40c507080403c5540c944403850184e03001e03082a181da400c0341c0180015824596600d201426855106005840d1140c002c0000c5210301045d054080201582034141a680d00a4020745180c45100e040036041d20b0300700d559155240c41c400e072004440080c104003070891020090303078443c0c540305443d40441e40e1803030f070f004025148048480d8115548d0300790660030743d40d50780040d0010358040d030b0b00000c1d8046545003103403c0110054200300010a000c01000d40320f50004820300540d1002140b14446864080110f0610000003e40c940d050240348104401d240d230010301d0b1109048145c0d0340c80e804940e02c001070b1254408900070030b107403510280c2d07062000c24041d4102c0380d45281840790412000b5030b15201c2020303a4100c100815014a400142003015064902585800c0b41c0380460403940001c0e001005003c40806400090800300c01152000070325020f540503 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 872829370 1250 872828120 872828149
    0x14040903091a130e06010509010c050c0d0606080607090f062a05030712030e071a0c0105010906140603060f120a0507031a070f0e040f1811012318 64
    0x8600011540c6089490b540041640050412804000103041c0c800000039074003558068680902d06014040112003a07018403070251124420301400000f182c0b02c42d10102035290140400140081c100700c0a5801c0c0140580070500700108404280180c1e114141d25200311003c030300b040e80c031100c00d000c0040d42040c15544010440203007050550103000001c4020900726105000b4030400000400003a0104c2e00d48442c420000c3d880200288414040d01d24011003100701c140910381401c2c0846c202030300b511401d0308507541031740e01d40504019544a5110060040008554150940c58190041114001241c5007144075040111280039207040901210a00981120944210360713140c0c20401c1c225841d11601c0d00e181d030015800100200d03c40e02941c2d41e2900c0995a24010000340d00c1080007034210700100070989075950740c5143e01d4010209001130814800c50828196584000015040400c43d0303c020520007410b8407070405800700c40c0101e41405141004c103a042107204404980f03000000001c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 872830620 1250 872829370 872829389
    0xc090b1203070f0210053a0504301706060702190519030503070f050f0703140f0601060c141f0203060406091802042a0c1a011404090309 60
    0x1101ca0a03c81120030084902e4020f8400c4040c00c644440100c03081e21074080105040c1c512648034160300c12071100b8444400515206000c0d109021840c100201c9106440171120107040c40100c030354000c0130b80540403040a501c0300c1450900074030640a0704040311508542c990604120015003d0f503148401d48410342d4000c0c100081a465040690003c80380e14010340d449508500c81c0307446e928103840f403504156540100594280703800d66a50b81d4040c030355034038122014000c9880c1c6141e011010030120000314068840c0c1400c00d032503200d4142c2012140b0b44125200e400c403030300511040d60015100501d05500514810300360302d0210301d0b14104081c0102c03007072803c0e50510300490002216000795000302802c86e02008216640c4003284225440c030600c1d80500010344038010003602c2c0070380c44592008403d442c2101c0c807445070b0b00c1d044010340003001c55002081c107005901041c817200c020400800e000210350491194105a05a85600540c02400744140d8403040c0740d00070544200f00f004000d014008 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 872831870 1250 872830620 872830627
    0x303050606280909060612182f0d1115190804020f0f032802040f1d06010e16030b0d03031a0621060a0e0c070b0903070c090b1203 57
    0x503060000e42e4003024040090459100400d0711380f03461040e0800c0701ca507178031419441e1100c6850b2001500c0c40c001e044000c034181d101000d000c03408003e00382c4103032040c1d11202d00300880c803107503540381400100e03a10b180200c41040d0703030000103404c5a00701c444d0f44c9000c6941c16102817240851038014800c0140c0b412000c10a200d44103100d541000c11607005a10031200c5041c00c6c1c2007681842813515810254550551091005815010180400c42003840b4051102a10350101da00440d0a031071000f40300071191030350f585a2110704049a000f2050f58658540503015030352400f268001034580180052032001c0c14500c200c0c550758025031003a24400c001402c2c0d10411a40c03400d010300281149607086801014000a600081c64220115801001606c000c04480c8005680c20362000c00c0042040e41c12129161020812b1030590344054030420540c1001d80e5102d80900d000c100c09030002d06180c559910910412001484849951003501d00403540040c40c0060400001d001d41d003200543c042a00001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 872833120 1250 872831870 872831917
    0xb0a18060204060305010e24100306050301020f07061401060c02060306060c060702071a120103080a09050a03080705070b0301030209060d0c0f030507170c0a0e0901060e0f0702010501150203070303050606 89
    0x11782189040303a00596a0318016552010011580d146090701e00101c00c005880c00403051501e0212140640803516000034410f8540d00803e0881c0e100f0200740041c00b4000ca0007134100046130003001b0592400c2400b01402d075250900c0503001c03100044000307108102c044002146602d9400c10782c0d4403424030302c00300c4006061a210183d2500c4c068040e50508501a84a540c0450340380d40858501d00400c0603100c100385c0c61905e460340c55801042d0600100403c4201c00100c3c2c1c2e03244c0b01d000e00658080e1211984d95900b901e4001d03d03111090744411401e00003400100301503074038000300507403040081d501ca5202e41e107185400c403c0120503800c102c0d1880e00100b00072040c440001030310400d07646006100074503034580d541500d50740c1d00400c40c40c3c1d030301c003507030000038847c00c0307800c0691641002a200000c12135a880703084140b0401011035900c4011801d4400f0130003a0385d424003c040c0103050218481031040e0069400a480348207841014051685500c00300e44251681d0049a09401880ba08182004100c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 872834370 1250 872833120 872833127
    0x611060a020a050d060e06090903180d020411040e10080c09071b140102070c080604021023070602190306030c090e0c030a03050408120f18040b150409180b0a1806020406 74
    0x40c1c4641d8060104840082c01c192790000c1228420b403a240040b012400480081010440c0000ea0490304035031204601d0454034109009030010b0440c2c40030f4440e0034a00303405c6007904c0300655480700380d032580001032070313541c940b503151000e03802c603840380f82040509040400f0100c20408403600100003500c10900c0325006072065018015441c417807980440b41aa031055a42d5881d4020350303000e5406440403001000c211300801e2020517005803040c43c0c0d01c03044801d0034210115041410280d40142d000110240f802e1b071442400e45840c01c01e41010402c8a040d52100340e207074012805003100b00c83d80c1e40034030b01011a04000d0190740804c020103d907401802841c00800c603410520a100300c0c3c2c4106400001288203000a41e101840303e034410034140307101c80c1e110811400900080580040e51000b10034142c0d2525605448200b644030081a40c0d076143c24200d600705e41c0c5100c02c02c428804030440302c1e03002515418200360006540301e030102d40844544040404003607008001042e442c40018009076480c2c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 872835620 1250 872834370 872834399
    0x9121e03020c1309170702120a0c030311061603020c0a020303041e170d2a0302060910110f030604150801090309060e010507140f10150611060a020a050d06 68
    0x10300f580d50252150b19500b5040690b604214014000e111500c0950410052140601007083c001003001d5031106410362000d04098409c141aa0707030304e4840d4030a006154200c04401c0c10011184020001e61401c140c8003a01c0100d583c0706902015000521002c040d9020400c00c204150014240e07551207a4031698000f20b410aa511642c8000e0826070009501034102506840079030b18038090042085034035400c2350040b07207121000d216032200c040306003040c0070014a40d150b00d80c070070b400030701150a00020b128900004051041a41810020301c0c1071035242541c00d03904840e030005d022076101d072510b5000401400c40000340814960300160002140c1005410104000e8002d485600180f525000106c6002c8200c0d120f16000c64800c10540d00007070b688001d41d0302d80c03c98050a0300c4c2c2d03c0d100449214103002c0c11602a020594442142e03500c2410f81904d840c00034080d1303003407064000107031140d0f1980303c1000520303004c140307940031034034001441c0540100c0d840e80d5030101042100c1034443c1c4e0766065000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 872836870 1250 872835620 872835643
    0xa090c0309060c030e0706031e0204030b040203101a0402030406180c031208010605120612030c1e0d09031209120303020a0219020f2412070f03050709121e0302 70
    0x10f04000d0301682040c06440750396510904480540034050a005068010b44142085411403000075448082006818806000614440c18411001e81494010980380944144044040c586800a0880d40c0900c666110945100545002d40c803540d850401070000c1c907900351185600201040b0000411121201c980c05891040000580038500420200d03545c107024020302002c54030811a03d1035400360b02d80d032241d014078004c0c080340d8860341c05074081e070039500b0016103003809a2180d9802e01810f81c07006011459003918034000c00c1d9403012440000c00045144c440546101c0050070103603400c0b48950340c800c1c090906480381c0c0c1040441460f001f0003e52003080800b0040c0030764a03583e4614103209010700e13080f90b002040080c081c2ca6074410810601c0034400c018020070800d21603100da040c24440904030540130468454071034076114a0240c1034a405d01d5100c8209032400742000030650700804504155110408140720a451910f041a480300e000d083d0340e011a11803103140020943d001a101034041d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 872838120 1250 872836870 872836883
    0xc100f021c090806011a0a1407060915061a07020f1c0b010e060306100b0a05120408070b010e101a04080f070f050d0b1302180703050406150617060a090c0309 69
    0x26a03880c3c45181c000204072021210b6840d00b0440c40107a14401c2c3c104079140040c90768234074a86016940d511084640469045610000d8450400b220a030707103119800c0100b19142c10007095a19110b48075016100315038000340f1070007030703540746108036100c04c682008110068021a0b40740c3c0407605048469401c24455021104a10000034805040110b0220b024407069140352130b0503801e0508000f5640c0181d4424007c1000a0100300e90303808203489920300603030080d50141d035106c81c98104050300c0b20058125811400c036140a0007003418000319100704554844690140050720803d4039060703441a0f50040d0824414402c102c54261800301d980c800302c80b03190f0300341c0c42410f41e00c1c0203102d0303c004508409400c4585802c0094840301c0d1040d0780051480c030003462000d29440a500c24038482c4810388860f400259180d04110400c00b071440342000c50355040607000d1f85145003450042c6030103258034001001504050208090f030b140c40e50001c016156400083c845010050300003002001c07400c4050703540 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 872839370 1250 872838120 872838133
    0x5100312050306041b23130308040503010b040207030503040602070606090e0d03050108120a0e12030c03040806010b16020f010c0203012405040e031e09090408070308090c100f021c0908 81
    0x4640e5500c4000b07481105c2c9841e1a501250030b0740340c400c11074050a82c07030100c0c110100045c109400907061808051803040d0825502e41d4100343c1810308441c09098861b0040d803040190402081d002000d40c0da015500034000b50b914100c520b4190b000e0031841e4000b000117424140c001d400003001107845000b000c000ea50030001a03071307141051603440c5c01d03103039200254600070017060f00780b81e202d010700014081c0090401340400c0c2c0d0310702c10545580d210880c080200d41000c01d040c0305400781400310500402c1c00d094124180b030f1860303102401c404801040284104128904882c0711703401290b00740c0c0d070301d50004e0080084e00280c0b1203001c0c01c8401031420301024425864082061b1406100d92800d003190800254200303101c40d040301c991421010000c1d0320302c4030244161402695945040743c4101d1040c00410748514035441e001d00914800b820b00c1d40c8540040e46000d216807200c00c00b1205140c1c051800d15880c16110b607080c0d0820b5040e040f00a14081c0d400d0b495000e19402c10301800440f80300c0411202e4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 872840620 1250 872839370 872839391
    0x108100614010e0a0e0403090f080f07060f0c0611090f150307080612030c0114070e010c110604091103010e070503040f081c1b02010b03030a120510031205030604 71
    0x8840c40341c0101116160000460781003940b203640d0141080d00701034a1512140c1c3c84401c44001000c088908600007003881c413060210000811009004121510050141745407401d400741c1c031801903010b03043c1000f16000d102e2851511880f4062a1150404010003100300ca00d5500c403810340c4401c040b64042c2c55140043c0d05207050005001e8414608203001504546494404a03041c1c00060134240e402011a9981d14022006100600b08203149800000e04043d0300c900d12000e0102c014190400d01141e00c0584c10542d800081c407907940780c4c4c8512a40403001c07180002031080c0c02107070001d210303072458481c81d41c42100c040001581641d03401c020868856840d030382c1c200e4441c0f200311401440c01c8002c009460000364010080c003607000c184d0185d002d61301020754558040b10302c49038144400d020107409402805030288241522248190059841c01c64040c0020b4445004038503441c0c1460f641e400040e039080c0392400702d6005540d0050341c110800541000c014880d40042d16118815844c0c00320820 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 872841726 1106 872840620 872840653
    0x1d04021207030b0f06310b04060302030a05060405040c0308071a070f0f11150a0207020a3b010b03040f12020f0f0102032a210108 57
    0x3c110345000c00704240c0624030314000b4010182044804400c03021818402e8410404542c090081c120307041206601703048551081c1500c0303030081004130b481c56050300103500a45030400700b071045440d10420030084400c2590010140a5400804c20000b81c0c0d00303001d0900310340500b9130901003008500b07034080030243c11100000004c510b51101903005030448242c0400c442c491403d50b9642031005c0241c2c1d5141500c074a168032030900100015100000c80e0115100e40e98054005441e0b907030f50743e0143c10384a442140340314a241004107031040505141104e404200c283d4510400c00364a4420a0440c55202520682d01d0004c011002e0020a12420000e80d440e44103900030030060000e1290903091640c090324841741d07a401001400f08020100108400c0d8085026011000c0120715403010007a115508000103030602d0307600300031480001ca6075100d040b00c140c4070540d402c411660a111 = true := by decide +kernel

theorem cover : BRFrame.Cov 872661870 872841726 := by
  have h0 := BRFrame.cov_init 872661870
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872661870 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 872661870 ≤ n) (h2 : n < 872841726) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
