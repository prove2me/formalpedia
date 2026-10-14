-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1625
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:55:39.883909+00:00
-- url     : https://prove2.me/submissions/31778f9a-9533-49fa-a493-71b226862bef

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 292086330 ≤ n < 292266187 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 292087580 1250 292086330 292086409
    0x1b0904050a120305070912120509240403020414070e0409020d140607020c0607020310020a0516030804110904030c14031b011e050603060703020f040f06050c01050a1802 74
    0x11142d40015540c905a136000d000791459802c51144003602d0b8a081f000124040700c4252444a030b40b51081d15001c159000c58544503081c0344510381118026403071000ca4003010040c10890340212805c0c002d10003480480482e84c041601c1c03040002d841061038070f038a4105508034400d518130140c070b1001c031158180c8400681144100072400d02c0c0d00300000780f00707001360304012141c040b031300407a07030146011920350000743d84002d0b003039a10350603c0d0041900740a4070302a20649013803810891710711041580510f0f0040600c0000c960460700d0200b40b600d004180c1c01c088045510a690645a900a03000b99848034203030340c0300045080b10244030401c0103541412410380804441200d41c0008500b58201c15245000000c403800140304013440c060802040d40d40000d00182c100105081c010f0351040c0c2100c0c040d006129541001030b051400040010340294031030f008102c0c3c1c1400000030055a02d802e0520825900448146a500c100003e1010003614094000008031103030003a0703d0071039640c101ca80c40ca0001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 292088830 1250 292087580 292087613
    0x7061103091506031f02070c06050d050a1803050724060f1212050a0e0303041d090607021e01020c06090f1204050a06031e0623031b0904050a 62
    0x801807150722581000b600c0220b6040030141c0a440ca01000440d80d980c001017080b0702d00c0800b140420b000d14002d0381c11a03200035000b480144446441c0c080c0500541c0c84042140b40a515040024039450a42e200b044c3c0c400100103200c0c1170511168804423155002280240c80710b00010309031004020680d01404500141d1441c041141442c02403050070620440d4080fa04081580d4039442c00642c6000f039031040c543c8641860350300d80b803c888044070010700800c0f1a64040c40300040100d807c03038500170b40040074203000220102c1583d0700c040c0d1603150081968000b001d0303440b0f4240035400311090071213042d80500d0f1000042c00d00f6440072444e4682241510301c4003d98120403060740403600103010b1294030020406019113132918041c0858026411449000300f09a510104500c040c001d0712410b84616400c110148255078440c43c4d10a04014000c060b0003480035a0031508520341404601e0154000840c030903d09540304003400e10658010080046a950080c00d000d61b0008064102a44204 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 292090080 1250 292088830 292088861
    0x30b04061404112d010f091203031e0b01090b0306060906030103060c1803030e01051b0f101506120504140a06050709060c050a17090a06030e060c040b0316050706 71
    0x604030f000610000c1c2c03402e00c0c0e070002a03040e2420703810340001c130f20070314104c0298083c41c103000043d00895080720b030100e40d40c0105440c55100d90080e0103055254010705140c090b0f5001c40c0b003e1340404101c2004494005810601040038409e0070002210030001469000a0207800a4904148200059407590007608102c800c40da640310443c0b889580725103121103035221040300c01c801500b185c5025140c03114101c4468100500041c404007400100ea4074004621207010495072003450320308010b510703900844552912185071545000d42c54040190140440d206030316098416404440d4480241c10000e2044d2407000800001ca075551004109010300c5a024030800511410811030007004045150700501c03c0004c00458103022610200b0841c0d00303180d0010000543d0300c60014104c03441d0151064095020401c2d4000107510368054100800c02c5040c8819280d132980c42d0a24800c190003640528543e081e0300b400081c0c0750003043d0304034014000c0c05041050400d80140e84120990784000002900c8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 292091330 1250 292090080 292090103
    0x9030a061d0304081f060e0112060f0f1b0801060914030f0703030807030506060f040e1314030403021f0509011815050c06060409030509011b3306030309030b04061404 73
    0x4511542408402c3e801720200103101e203900e0500c680c0c0001d4810301a1449500000c40c5032010040c2c1c0d075019441c81c031000081403140c40e44801d4880000c10001c54402e4520203181c008501040c8192042d9040e078035180c80b0750030100d0602d82d0312030f4003510241d003807501846089c00010400b8010000321005602c203540b4420076240401c070040a40c4d070068590381c0200700c18058540368208410a50303007a16645884501c8940c0d8950800e140046003010180060450b1801c00c03103804004001082941d00955002c840e01e25162200c11803801c00e4941c81000036424400701d840e0b0743c8a99881050b40040c01d503103e8900303031a41214000d0040c250f0b0b0f0840812400110841100828041283d2200b4105d0f010042d0076040d440c013414071707c039440740c0d03504001c50001d00885d028010030141c6402c139000040d1661003c1d0070041d0400141510031407240c0020444500101d41045000745001c0c2d0f80c1c10781d10004050710b0366950601c1488050003c0350142d440d100340c010703003202c02d8450360301c100c2c0201300d64800c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 292092580 1250 292091330 292091353
    0x1718071a04061b030509010e0f10030f1116030509060705060a060311060901080a0b0a1d0907080607020a02040c111020090a120c0b030903040302100509030a061d030408 74
    0xb12144030103c01c2c05960201a0701103500481035602c41d034800c2c20000b0910200d03000003140c052031036180710b900c02c554454110007180c0c1170307020f4850401c0b100c4080218035548105084c2600131000c030310b100c01c1807201c034020000344124003034480400c0c0500402d081085c0c0740e0b01c46e8144001101c810072038035542d003020003c1c08417210240305050401c0d2a000e20b0050340c82c3c0001d080321001001040e005494036100642c544910341190010481c1303801044001c040104140510442912149d90070304c2a500e001ca0101004102c0c030380504074917002010900000d034240000b170580d4100e68420b001d00703c50324101e00360b0b040c4096600703d1a0380b0f1001403984c490b40403556500d130010041c00712048050082c04016150080000103443c400d014600c1e011026141003805403449402c80a02c0d024040280411040000064016039100b2900b2001000303080703004a42c0c901540101550581c40b805182003c5402c80d48410b0040303091a085281c1c40000041c1149142e215a0207003505500c02c010a80 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 292093830 1250 292092580 292092587
    0x6070209130b060d1208091006060203040e0f1e060406050d080a0906110309330310090203070f05070303060806011502070801090f1403070c0b04050405071718071a0406 74
    0x1030340600700b1900358410000382d0700d030a2905c0340e84002074002e001c0f40a001c1030482c42c04000680300071000700420320410340c4408000752290464031414411298517004a40304200c444103140c4102c40080c98600034074040c0034021013a440142031160004d9803030b04d0100301d076102c402d260802540038291180e9903a44484001f060000545d12030803c00061070314190300c0351000f1003110760303240c0102e0300a500c0c42154031400e0f405c4035107040e8444000b002c602e6421100c0749160061072090103010660981c60b5900c1c400031007607210440700c14000401c030804441405000e0006803000901903d400160241c0702c03070106141c00c5082e081000d6a203241ca41400006504000c0340000c1c101d00c0000380301454196030707800790510759103200800b0a9040208007d00410030002d03181c020350000e0b03014450030783c0c1e05041403240c2d2050007030034003590071300000445180c056041c1951050711007584020a64070144e40e072090700c800c40d4148890f40180000081c609828040048a00b00034100441e03079070b494140080c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 292095080 1250 292093830 292093853
    0x40902270d020f06070311010617070801050115050c0a0c090b0f0d05060105010c2d03030b04021c05131a060909070b180604030813080c12030f07020607020913 70
    0x1e1040207441106401030b295524039500110382690407a031104814542580c504281c503111340000c0d842c2450024220310f007004900101d9051b001a5515a61910f4005099030000d00a221246a04120004985110700300a000fa03286100990b04060ac055070f410540502940c8004801038031405944120b20b040c00d207003800c170001181e580f4640c1100d43d0342d13103031144014071815050205291203103090000300e20045401c114041010014a0003481c4010039541c0e9982d42580020f18020110b402030425100f10b0f8503118031801d000c94281d074003041c0c0402505000b403c1d8450900301c558001d00080403c4007181e43d03840080c034030b001145800d00c18001200c400800d8080b2951040d001045250400c00131140b180a0f115580c0760380c130704240003042040c441d07588010301c840d6000800c0e0b944128107200c02004c6c0c580440070341d4040062032041107481503550fa50100c540c2c00030080c212005a548000b032510a01c00307024a070501c0041d400045400d501140c988800c80c080f41c0c5039204008007810301 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 292096330 1250 292095080 292095157
    0x1d0c090a06030c0302040b010e0a0f08010c080c090f04110d020d14041e03020a08030108160603020309070e0603010b1914010f0c0f030c0c06090501180b091005040902 73
    0x108030301d40c5103840309044840a40f10290080d5034a0940c881c0c40c2c1d1080f0541c81e402c202c0030f09510304803550b40181d4800b0b090b19100301c10746540303003012003c2c2c0144204461409000003180c190300b4182d10000304000501c030321106a40c465500d001c0b61020307034400c10182603981901c80005132910030045100058884240d48503081600c001e00f000005050500c043c074000300e120380ca80c00000c881d0301d404d0b444c01c43d039480e014024220100002400b01d40006102c0048c9411100c0d0380e81c50b035501c00d0160240d01041d0313400c00c2541c100d154203124108234004215070000c40180080380204521b4080380c18010740710680c6030b11400c0c5540c240044000e2030b96a0401c02000e10b00241001c7d040c0c1001405c0c00040c0d103004140400c245110750034107105a100d0b00200e5042000100d0546d56608003800c0c1c0c61140c801c050214040d100c00300500911801018200d81d04213034420b01c0e0400c65001c0102c1000100403a0003401070501001c50303403081e144050318504e6081000c0800241481c1441030b0701c80d814060 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 292097580 1250 292096330 292096351
    0x80c1b060114010909060608010e04080c0601091b0807051605011e0b2b0b0a14070e03150405071401090f0905010302330a0302071407031202060103241d0c09 69
    0x100b00116980b004235541100d0f80b190004046448034609038541c3e11680c40c005005100b810000b00d91150300c0e611105c004600144442030803000d850f003e46d030541d0100c40b54400709009100c031a035107198440001c0000d03881080000355011108843e03034840380c5504240c0d4402541c94680b8061400c0c291400c0444101d00303d4402141101070249842410032407070001c161016480104040340b045400c00d01d01c205c0c1551103000c040c83c2c07040707000f40083e0130340a49600c01d01c00c0303089a0304510745043c18580210b4101c005400d9490030841007905014500b08481d042149960002442001e6a605580a03094100c008120395255004102e41460080c510007d100c0c40b2460766401c0c540c281d0381c081c9864403440c000707549440386400107030002c1c014200050080d810b0082c3c10701c2013410201d056400d40384584503115202e80b4007013040ba6110403d020082041480920501c264081d4212030310f80815040008508601040c000603140d001d60001108541d0020700c2c00c040f58070305403507243d40c007401001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 292098830 1250 292097580 292097591
    0x4080714061003030c110409030e030105160804080c1204030605010e012103030f06050604080102030405101103130213090602091e1c06230f0a0606080c1b060114010909 74
    0x5070501e9180b841e00c402070901a040600a00708501030510711034642004204110420300b034140a17103040b030360341c00b03c0d0711079441d0000003404003070b1401d8504c8940d00260750303240e615911130fa19801c0b56840b202e0380d40001c2c4100c481030301c0f1642401004001071482043d0200b00ca514240c1e0380121760310180c000d00c071007500c8044a09103018800c2054407403d901413502103030010403440c0e241c0003407410b50005608060006404558100150019800380707108504403000100d40c02c1c003a07011100c0e00320b507003142104200046042c00c0c2c010840d501c074240c0001c01c00001c60101105034022543c06c070a0031141c080c0c000ca03594601c3e10300500d0070b8144ac0d502441d030b269480480d034001800c00341848409a45013410380602018040e503648440350448400701402e26284003814000300c4020112000000000c000c4001250703040a801030004035009912400310035103866006520940180d4100010404e208a09103079003642045014004d10030070601d004400041c400040410078075400114000c0c1c280b4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 292100080 1250 292098830 292098841
    0x6101d0403090503060915150a03021201141305010c020705090115020c030a050601150e06040603020304050f011d07050111061b0417010f0b030607020a02100207050301050408071406 80
    0x20a900095004250881815a8681c0740507038007040d1076040b40c0d4151041c03204000c0743d050000f89448690300f603212080f1095441c000144200312501030364a401801c50602003005080640213000480c00640010130386c00009240101114811514104010060b0804009200080c400d00700c900b8843e1014202c05410000860f100c5581071280c00702803071042d10301a070310340c1c424043e00c880c1d802c3c001c1c10303070300000c4a034113105070b03280020701a0000940700420b644144030300550030030741f070b19201400140c181850b001e016002500000d20a82d514025a00341240c030007028851880942c0c00342440d045042103d1071007a1030f0601c0e542186052014034103070401502d0b0001441a0700041260070f24130b10904500d24107036035015a0740140c0207000801100014808103412000809108040402c22100500101a43d86000f0f9a0407000340e008180c0761400b60a080c1e0107050340903070a004907540f1780e80e07070307008607084a4080701d00382d4100102262460030030201502c680340b06415080101200d041c00e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 292101330 1250 292100080 292100099
    0x2a03021002010b0d1104110c010c110615040c03111c0609020c07050907020f0d05120703060501170718060c0b06040621020109030804060c17040b0d050a18140610 71
    0x8001002c0c10001d45c0c800b110403d40d4482d0002001e01a09100e0261210b54884804c0d000e84609240720010820800c0c40422858000403514810002440c0003500c4a44200a21004000703148000040680b921300c4000201303180001880c500c681882103184035010050264121005c5800c1400700034010410039500800014101d016103c08445498041e201c910043e0300d8182181d09100c1103010b080c4882c180181c1003000b405c60f070740680b110001283d0b9120790441c00c54038940225404203400090010a101c007804a0700e034003402500b0324110100344c5c0d406c240980d5220381d004000240862178060104182510070030b801c4542990180080f500f01095031a540a00b12144c6034400030502d10780041d684a19040002580c01280c803542d51a142d81005081c09140030b400d4500c1c2c1c4c62075070303098290040c00c81101e08031504103050701c0c104610019800064071001d082c000900351180e041c1645004034004040855124144400c04205d18540c05410610000c1c0f0a1103080b10300700c1e041003907401 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 292102580 1250 292101330 292101349
    0x6030d05040311130c0c050706020327040608010609090303060b070c0605030a091a040302061f0b0f0c12030f0f040c0905070215041211010513020103092a03021002010b 74
    0x240004250801060b40c004241c10900f412483c0701d5460500d50680c0c201500007458586c1c04d4000c1068403052502c45206a99910504041e001c0c040b000b454100b090041c8140009003021000b800420155640d074126425036620b034100742040c0740c0c1d486400082581501c1100d004051840f1414103003036142d00e49041d1005984152421700000100148200300c5507030040007000d500c512080c2c1e008010240406a0004c111001c90252040301c000c40d02c484003d007045400c01d409205201c15050815030001c00d00c3d040214282c22641c802c0c441c41e60350b07080500c480050003907250700f074507100d160100755015680e030003901d01c0c040c4031002428440490489091003040d0340c3c0c003540104550310340d032004a2800003101c050000d040f5480c41807004211050510090501c4550759440801030200c6206088890a8401000d030b81c41c065814001035010b5045020614025440e007529980030040d010395000009026812990b4020300a00c01c52030180f0301c0c40d000c4c00b45840204140d01d51480400c91294 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 292103830 1250 292102580 292102583
    0xd0809010c1a0c0423030a0201030b010207090e06071b030804032019050f1603020f120d0203030a060b0405031905010b0301111902010c090b03072a0b06030d050403 72
    0x10340c1050002d100109124030b9201a40222103035040c0390030142000281c000f4012184d2504c1402c0789101603006280362500340c89401006464803c9442d0b005400400f540c03550241940204100003c400b50988075181a080342840030344114505080c0c004c00c24118076100c030103048041c58000c1d0120344e2002c0699401a8982012050b00d07044000d1032907403100944140d00c4601c03c0c40c208202d164801c021504085100c0d201311054013030341c003c1468070f401c0a13000660300480280b0080025150642081b00c00e010094203100c181556001458104121000042e0150b400081486404100780c0b00b0f5000804621a007036013003d081c200044d0312807070005800414500079a41110a2200030b600c11442410000c00030031402c0e002210b4203010b0b4100e68604c0000e90705818440508600600a0011001d81a564a10100d003030a40034a002c3e04003500f403804020512040408103900c244d0409040ca54000c0e805c182c050303076403801101c0079000406450017038114520003034006170040c06a40559 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 292105080 1250 292103830 292103837
    0x3040303030f060312021f0b0310050a150608070207050d030815040609020d061d0408120a020408150f181e0c10031e020405010203160f0b10080c0d080901 68
    0x904100c91010003900d11508017806010400e0701190344036400103030007030f03e001010346844402d41c007141e0020116003100c820181c0680110345034040d02c101503070103154081e040f540c00240ca0900c1d00c07180801c0380c09075080300001c40c40c40001d00010f9501000a80b00505003268031000749040f65a0081a42e40007401c03038002034a0030401030000e0b0303072190010341c00741022060841d16030030070b092400080c00c12841024104980d00d0840519150703040d04444c440d03a0020b034282d04e0104507254034140e00400520160340140d003070101140010041c8511410501c481c0303108040ca00304584503801c2d05601400c980c901d200341d600c08401040740801c10b008040ca401241c00940b0904000321401c108903940c00ca9031090321180d88610b42e94140e4044481c01d089030440f030050121414516089100320b015a9015034010b024504541c5038004002088a20400540010a1060362041d01140c01a2900303503103640801000e05c25607204120120a5036021107049040e5415600d4850b032911481a080303040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 292106330 1250 292105080 292105091
    0x6030316032105180102090a031106070b04060902040e1c05090102071d0a150e0f0a020c15061306050105030406020315030304060f03050105060a3e06010905060d050304030303 77
    0x1c0c1405001c900d40d00802c0c1000c1107050070401c10503071006150464142c1c55038034022800301e402c110305100b84c0756040006010f4004460450312460034881020003030b20b91041c820001c10000400d00740701e090046204d003c0c0070070340f000e11b441080181d80d00541c040c01c6940c00b40c0040114522200f41c11a00b09556042c140e42e9617607501c0c0101e0800d011a00031511034051001100c90202403201300c00d2040b6403034441081403503190149558400040c2c46502202c401d043c02083d41c090792800b0690b000041e41500502d44500480f40a00708207407410012507200703034141044020700b00a6009055036004100400055080030000381c032034000a0000f400099022000803010090140c240307024004c024100d0b502c4543d01c0d400109801ca80701c80a0380080e08040000484d03040603002c0e00d402e030105480386092218120401c00404409904242040800100740782c8d078a100d901694400100090142001c1d40c10400c2d80420703510041c0c4a1401050303282030340310110740084140d074203490381843c000c070301c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 292107580 1250 292106330 292106333
    0x1406040507030f02070f1e2607120206040303050609220804050409050d0f021f020d0b090109020c0c0f010f0c0f15090b060301060506041401140d02120109020306030316 74
    0x10250a60490300c11840020301005010499002e13038001841031220b42c032407c1682c0c0740c0c101804501100140f079920101c2c8080000d200ea14080c08441150b40040d0741400b42a40351010840d250030f80c0d88015030420024401855070600846502c050152003080f11824800c03940e1000c1940c03001c030861026803030009101008099822100148001007080c40507401031f0606c285c50350403041110300440d04d081f0b145d0804500100c0c2100404140c01e0368103807880d100d0301c0300202a5110b1200264000c6d5100c05000c11a40c490510380d02031304d00c10400603240c0030000340d11460041040c85540c0f082c48091120240790f03078080b14000e00380c00d043c070b031803c0845250f00c3c000400605400300185407604000c3d2043d00c0384521b5104c02c1c81d241c020030b01e050316034a900060600300c2c1d080d402803d4120b40100401e2100040b1445142003801040c50f04060b460419a140f821035080741c50326410a64000412940340d100c0c0c02c540074007405600c3c0086140d4142900041d940340310781700600e071520f004034440c00e0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 292108830 1250 292107580 292107587
    0x90507090803220e0705031608090606090405031c1a0103061a220305030702100c020d0620031911041d040f0203010e070911040e0f06040b0d050c010906031406040507 73
    0x100001940904e1030300701309201402c41e4104603482140c10500c0540c10340514400c0c00c145004000e183c000c0c1c2440d48901b8140940c2d0200104143c440340b1040103980344906607501201d20005046000040440351031180306000722032034040d06c0c109400d02d801840a040e80541103180060781030613065a501020243c0784c0c078690a2640c9000902c520703000001030003800700003000003a10845400141401260041d92110075900d000b940042c4035034540c0d00090090381c4003403080c909007940040804403c0300f00810603441150384449c02542545190000202801100c200010040915050604200d0981c44d4100c1c1011031080c2c450300303080880c0511004900011800c2c0d0054024002c5844880c030580e6215803e01c90072102e2840c1a410007803544205040e541078900c80c600c10740c0a030703c0b080480444004042c28065101d0350355005500b190391220980b40c140d6200e0301c00741c031152100d5800940441403950009003854200344004070403801078120203600c0300c03003110002019121203d044 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 292110080 1250 292108830 292108897
    0x20901090923150a090b01050a0b180415030f0203060901050c031902040f0b07020f0108060f010c060608071503060501020c0a050418060f02130506090603040336090507090803 77
    0xc5000c601d0301d1050241d4140349030070070170b0b01d40d02030311550340070341d80e50310500810702042d11541506010034414007a01000f5042e0041ea42c1000410204128031005540042001150b100b12000c482e6071449000314241805250b92003034641000700800d14081320700203450720004212041610034510800b41da0082e50b070580d03024021414003101c0c00f6842e0f203601003041d801080c05030310030b141f0108140c0740f562003140d80600c114805071480465840d03580c01518000c21440045420b9a2250703008240c2560030000d100050280b1030000b03080c062202c0d009022204035410032411900440360725005500d815034240102c82007610009031801c50040307079220140202e00c00800c524204a058211550340b03030003800d6684900384510100998640800c21030b031044944d40c41e0048814000500401d00440c001001000c0c07071118090122140d86444000002c07100b0fa0320002084560240140d60031840746903444509414165107c600705000a42e9034014558000850380500d100344a42811b4400d02c1c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 292111330 1250 292110080 292110103
    0x3090806070f020f06280207050f0c0126071115010b0c01110301260a0f0b0106080f13081e0c01020304030806010804080306240c0109020901090923 65
    0xd039042428840d900402d01c403010444000113214015030015010130108940340156405100c10407074030045c541c0c10300004082c2c031030070303100507800e010990200e1410300c5513076603500015000d0a0b80944500c000f5054403140180100900440e002202c403444d58604115080890b9040c803407149201c0320007080c50072844016101042014000028400758210050030101c1907000c004d101500d2110100b0360140800d02c6144254403044090140200c5400326040da0400d0100c00d5030f446100c6510348a00009007080308032803400d403000040054584c071100041d08881d401014068030708103040040c0e40e40701c8440f00a0403a507c005034080200001d00c40d026078402c4910301454544400480d000d00030b410456099003c00c00b64400240e05621500c5440d1046a10054103415270725440280f060150340388c0314040d0181c0301c0c03981e810300312000500680a2103110600103e02c0c0162441800600c0c44180d0000c140d4900b407c1010000039064600005040e484500000301d000c02510541c1ca8200d61450 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 292112580 1250 292111330 292111333
    0x1a0103080717041d040c09020a0509060918071e0305010501020c010305061f02010501031203110d0507021005010b0c07140607030809120301082a0a030b060d02150418091707030908 79
    0x103100c4414008009045c42a401415001c02c52903031041000142d01c551150800041e0080010303010074a8000d000e0b11412101a0500f03401180f00d844100c0c0022080d1004008500602c000003441b041d151200041504145414000c40d450540041d40e20a0b46044082c141078442e07001034820f456000315191141c0c00b404002c0020364007003202a0090030f00f0b00042d2034094807a400340f480705000c0c1c02500e40e88102c408c45d0743c0ca01070040070184000d2401912034002c601500f2072404c419150b6002d414040e00380a80d00958420100e40f5052425005900000c4041e0510b00520000e603030306010b0f10066038150501c28410360300c2d8804941880012441030b00460b001000206210b000014205100c0c0940c600042c038481080c05a42c0d03520780f04030441940842c0c0b00c002400050034221030303c2d40007000a08210103144176940059041e80c0d042c5022902400c02180410254103000258280d0a60b00c40301040850056100c58402d0b0a009c00006c084c02c000040d44070405125440a4005114840 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 292113830 1250 292112580 292112609
    0x5042307030207140109020604060503041509060608060901050606030c0d0902060a0306050109080609060420041b03060608013506010305011b1805010f020a061103041a010308071704 80
    0x310094000d4100c000300f070352180408a40c501c264441481000328103500100041c1c10103140c840e0884940c0c0c4020b0080703034561101144405c0c01c454600864040500c15600420024203040c140c0785807040c001d244e1003150381407100b88045a1035002c11203801007888101c02d596110a00d01150140c0b00c1050001c2d0881400107001a030a40d25501150598809988400342c8a035240c104950342d01c0251050101f0360024008100025044a4407441c0480c104890f41500010000000c086403840910010250380d104030012007564544242030280a05091405a9504100d10101c0c1000da01b02e11038415854031030305000007a240003041c90321608034011a04150784910700907010304000803000c0100c00320b51103099042070003291007048000c007014a00410b1490100111000c032009900790301580100403882c00440d440b0f00624114901c03c07803139241d5905143c0b414080070313102c0070000b07003150000b04010302c00203054904a0348407a400841c010968810f923960100c1c2d6118503404030803005c2000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 292115080 1250 292113830 292113841
    0xf0402070f1401050c04060206060108060126090d0201020403050307120507170a0912080a0f09090e1605010c1709040b130b0405090721060609020f0414030c0604050423 74
    0x640e00c1c10700b82101c00740240000e4403803440030022801580150005038010500050f81c1d94442d0328400d034000014501104040e02070100f000700313001451181200400e4000400c80164020400510801120f1000b1480d140c50341c1c4501e42c0703038040c84000503c901d40040000c00c286102da01a120f1090300043c0c070b8001e094100b6072642480e4002411140404c9804800040d541540c480c0b00040c160000c094a00e0320480e00b0048800080d8200c1200a1100030b0350041954800c070720602c0041c484040082c02070b2150200c1400c030344002c070390050b81000501c00e8034200007a075000440349003240000b00e150301c03000c0c3c1c03034000380140144403960b07500000c0d01c92030301690407207540014803a00000d40d41046075448a691641d110701c030f0383c003da110f0314007180084802c5620110154066600035a00000d02e10380340d102003410b0764040c4040c488613043c003140a0080c0c028050303610680c400100d00804501c0c8001d00800c0840c00341c0d10415105550312a01c2e02f413140d0713085103084002c0c1130781401251189442c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 292116330 1250 292115080 292115093
    0xd0f0203010617090105010b040e06041d0a020108130f0308070c02150d24050d050328110f1b01021e0127150e160b03010504110a0801050f0402070f 65
    0x361081080c0f02000501003000164103225a60503258590f42c190300d41400c0038181c1d410702601a004c6034006654044444a011180d04540c1800140301d020f8a102c012600004000b450040c00d5401840030740d03020600010300c526600b00b074056060400c04d00340da035843d034180c0b0105031515001e0f400c81004600800244001c0009081491400f41c0c1041080594507604055548002d1003070309101c01000c050000c0c0c50301d02c0445503a5031045c01202e2034451144800fa00c81c050700268070821031880340064014a8103c002d048803d0926002000040750210b0455900c03684540c031020340008119102090b41d05c24071000e0800c441448400e541340d203902281c07600070300040718040d543c1c0da545010f980101c810344040d8001943c2024001589582d0100203000074840301c1301e40c81c01407141c1c240012440c1e0041c0c3e24403000342084208140c40e5850142840140c40107085101e00085040156846542c1c011040c0c90540d2005c4e10601c064400d044007180c000c1c1b01e0480b02a121080030500401040603 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 292117580 1250 292116330 292116347
    0x9040e0715032703090501030f0b120d0e0105030903070201210c0f030b042a0e1009052b03181e08010606080c07030806030c0603040303090b0105090108120d0f02030106 74
    0x41d03a81c440c502216400b00f4a070209402400007000100040e100304060343c80b0350031005084018150001e01c410300e4070001200600000c3c7c0305001500b045241c2032802d0b03044900200204800e00b0b00c0380c51882c0920001d900ca22031003a0081c14844401004210b1103a4594a011099031541c1e00300a41d1034105405040204688440d50001e410f05511400341d0130036010300c5818000409500d082811020002050383c2c0300d030a01441000020512103500350b492881807034042895461340f0498500741414807041806002e81005061444045504a601d0004a0380390050f003520780700c0038540c0c683c1d801183c091603650100540e2003002504100030750b041429074044520840081141310350f42c510070354006d841210700364585441400944c0210f4001c0ea00107902501c01000d40d8081d04148000602c80e81041e541600001d41d04c4c10b5180c104a1698446e90140000306e0711f8aa40d5850300740c00d140e0310034150040e06654200030070f6100c4c40301e600b80c2110042d109081d8055480f0368482e00d00030180c00c1e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 292118830 1250 292117580 292117601
    0x160f140d110d0806030f011401091103150f040e011d0606190509070302070609060209040f0b10030c020c0a0b09031c141b0a080d0b0108060609040e071503 68
    0x50100840d1000d00a8224181c0c0e04560000380866400249064881d400000c000c2038240c02249081c480410007031084442440789002a180702d035040032010f0048821011351280494000c1060269003000d129268085031000c0311929181515174010034094000d4014140107907003850300030200c08000e102c0c20b150704503204c1c0444605507220004c0007070b400c1d8111516000d10015980c14451800c208840b03c4d8841c1650501610380103195503110100e96265809850b000c1d40844c1c6030905241c42d0180c0b9103001804501807059031070700030001d1040a0081d4014050698406007681041d00138002900045801820341c040b00e07a4a04841e4240d03401098014030a010f09803d015000d54040c00428003440c16603904800040c010405400e241d01014402e020307903d510628007000002003000c2e15045108951181e11240c1c41d0b41d8810a0311503182c1201d0600000500300400c40c1c90303d406440e0150b6080310081006030044030b0141c06d2841e00e40056048801c0d84003e60740703080e0583c126403c580c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 292120080 1250 292118830 292118833
    0x203090901033807030506030f06070f030b0d020109090f0b040920060c0a0f0c031e03030b01170f041b141f02031209010f09030e0907091a160f14 64
    0x3030800180840d40480c80f0308407404801c0009000c14140d40c4607600c4036900c400c0c00303400c403042c00503807805641c9401011945200001d52642c2100704450f032500840c86508000c0d100f008031120345a0028104460382d000d010941985c0d0044003030090b0443c1c000909031a00600108151f05250903c60352254110440140c101c01e04802c1506a09040c000c8500c102c03404409441c0044440c3e84407000d5203044001a50159000039020010900e401100e070a9a224441446901d00e000d28018003542c101041c1e26041c007640103d48070f0312621500c0c40d140d200d900719280070b403e87d440c1d10382034480980c1240401d15204445402084075881800d451741340c441d08076403200900c403000f881e1441d250b40c64100200182c00c1802000f42c0024001d42003a0005204400811004030280504c0100da01050084d40010103404405146003040801c19030001054603141480e241010030004c1c1c50007241125183c0d00d10000b500040018480d0b40e42d40c401c0e070f4083d40d40c2a201c0c9140c02c3c92010000020740c20b0b03000303 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 292121330 1250 292120080 292120133
    0x409050c0f090621120d150602120406080408071b0306050901020306130207030309050d0e090a0507021c03020415030605040b12060606070303090506130c0902030705040b0a020309090103 82
    0x40b850718001030b9101c0d0300000c0003141080030b18103109656501c0343c5070f6048070340301e18860900007000e0a00030b0410382c000031200168408030b150307841e81e002c94164041c109541120f0140c2c052491914103c4007628204c0c2841c03021030700c50b4981400580305280c5d0145c0580c3c8184801c17a07110001c0d00c113000c12640035900c140074503100c00d11114200c0c803050340e4295008054905030518820180c000d002c06a009040002d00c140705501e441d810003842402a5001070271031850a0807514101400c150410320700e03a070801483c608400040d5030340da42680710011004000c45422803861098040714094100e513030300b03110302c425040005001340429000301d500c01c80c107040000c7d20a04001d08082214000c1c0c0d002004c103030301c074030040c00758a9000e48020703030425444d690703104041401040454003503071501c0c8250307100c0030050030714138445d0100f80c0040c900701e4010070600c4551a480810766043e1003445814a5079500300400903441e51041d46401070f000042c0704000414058200c03014410600241005c804 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 292122580 1250 292121330 292121359
    0x3030a0b0d082a0d05090d060e0709020405030d03020304110904080d0c030c11010b0d020f030703020a0e1006020d09090c03020d05131e02090c030703111602030d0c0308040b090c0409050c 82
    0x11104c91540c40280007800501c01040e0703c4c03405803110030710035005a600003a01004c0080681c01d0070199005058840d0300001c0412150500700074400f9108440c0c9001c50a41c1016910f01e0001c1494804062149096001007000d202c80303441210b01c0031a031003c0812407a001071401402400c0c80000403c00b043d691100d4010f6107006000d40950700b00010944035001801303900300030781c141c078036804941c040c442d1007170210060701c40144445c09002041c42094040c0341c0800d640c003d07035150340c0202d0115009601c06510352170300201c005040e42d18210000c1601e000c000c1c001c40086c00750310402034109040609100e00107500f40040d14070540203052030030780c0c1281c1e0320284c201010b07281d00c001c0d041720218000030300300343c0070707c010b150804554600883c1d00c000303440c4619000c3d0408544601c4500724000740004514042281c46007030300b0305040600c00d5104513200580005001400540b40c0c0420000103100703188103011b60111000d00502c1000140c07106c0c10160f030340c1d03450780701d806024113045072801c2c6 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 292123830 1250 292122580 292122583
    0x1021303030f14070302030a0305040c08030703080a110405030607050313020405070e0123250501060b0c0d03050f06060a09081608060c09030a0206071a010902030a05070c030203030a0b0d082a 84
    0x8400d50340540040d4542803423102d04500400c001401a00c01d022444004518100c06000801103140240e0b107110030340c00d004030100304940b00140043c3c400002004200030a40300494081e40c004a64109242c41c0c1d035031190749011682150074020f50003440d1404010b0354a4002c001d203e9440000c1e82d56403084040030ba19001070111170300b01c203500d4460500034003441101e029200002242c80c5138007040002020354516007903a00300c0c2c03c2244800340100300f43c0101182080070707a1241025103400c2c801400c1691400c1054000036000c40c0c00f4140014200060f01c0c05050384400401910702114080c1c3c031040d0b1304000c03041042c02101040d029200201705502019401d81c2ca20b090b00a020388100c25881d803c018096010340c400303e13140d0000c01003409900221140040c008c010100700982d49103404e5403e4400c03620f0040c401d0041c82464641440425400419039038003141c0030000240600b542ca000400c241d01020000301140b00000320640743e040f0001d141c603002400310761602281c008801006 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 292125080 1250 292123830 292123837
    0x15091c031806081902040806010b04030327050402071103060a0c11150a09030912050304060806180412140315040c020f3703030501082a060304030201021303030f14 72
    0x700d00180e0f040020480c00440e966018440b040c07069030043c03406588408060070014241e1142c2040f42011808100345030f00700604c02c014202c9440ba502c009072800c51498050b41a50203040d0180754085000401c10a01d40d403c0201210020115403141c5011010200a45162135042000402d028400c9400c080300181005600602c20084000380c0e0b10030440500a04d140d1f0310540400c07040d444001015920390032100072a80c01040515a143d082c01e501400e50318001d00914001c281001c0c0c01d0b00307814000c0b44c40700d400c168060100380b0200f641034022121500e1341110030050384d00000601401c1284540142101d41d07054509021402c10004166181c120060154041ea0401a51301c1000040c00700d401e1008102c40d00d02c210041501a01240b40404041c000c5000c00e40d01c0005011611041020041500f45036110018003640200b4086000e007540c0189800b9140100c04181018000e4041d100c1200c858640049030341c0e56803d00a10041c44160807001003040115a83d81c403460180c1203 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 292126330 1250 292125080 292125089
    0x302010915050f0a092c18030319060503030d02030a0f02071e0203160602011401090b01090b09040603080304050604030806041503021908060903090a0f0806010515091c0318 76
    0x542e0705100c3d0528450b501d5070300241c2e8060030410104408030318207044440040c44d041c1043c074071064460032140400400c2d00040c0c209581c41301c201c20070040d0720700c0010131258000c041c0c80303c4107644000d401040c0080d15070f9030065503041c08042000d901480c2e072079000c1e40c420742c0d12107401d00030a003049005508a100d0080c01402d00d0414107480100d209084002d08021807001c3c0890303440303071200c81d510401520030340c001200503512121000341038200f030842075004d8250484200b008a10001c00031b030803064213102ba8600d480380840c6511756a41c2e203500203001035400007141962481c061134003584542040b181140807034800070100d24141001c1c440c089803c0c420312071070006103086070208180d1288480707914241e0b80541401244101060002c240190074a200a5440c0e00d0301104000780300e00b01c0d81042181c03c4040f0001c10800100040b100c4c112001a15040c0107090030382d100d0046440384e40c0f02103400c0f070b000d80c0c82d9081044c00785500061329402542c0c0d000700c08512409100060815120707 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 292127580 1250 292126330 292126337
    0x103060519060809070e040605041a060604060309140304060203070b070503010303080a050402040b120601060318230313030309030201030c03021c050705070b0a240e01090b13150302010915 83
    0x7414002240600c25140e0041044012a00d01c0c56550a48000c0c40104a42c1100c042da140c40500c001c00ca54a080c100b500b15484054204600d0704a0100d440ea0146105020425480e454440140f1500410740c020b1180c620040d6030346c0340d07202d5030043c1d620350101c0011240e181070400050001c500c2034064034143c99040c2d5034415103032141c03c10003000c2d110140c816680640d540c2200b080d41e907110340c000800c0c0d542820290900d5894144c025040b21101e134268210a920130070740b580000d841114108e0201511341c81524022400d8038041c5c518040c14074400f11041c2c02d07003004028150000c0281d02242e200b6070341031002040001c001c805a0040090900c2c02901c80017058100e1103c58004661010403031404074200708094541c0902c0d81c07401c3c1c80c000c0e5001d5840d02c9240c6424074804c007040325000b040503072424440c900084031440010500c02c00d590b5642d1003c5a41e44d5a51317204208440c114004814801b0fa5030380360340d2004094907880100c0c04075925943c0010110400c0910f410b0102c2c441d01c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 292128830 1250 292127580 292127629
    0x6010807060915121b120605031203040206030709030f05010212010b0c03090d0501020f0d0203100b0f0d0c09030204050a051602010605131109100c12051201060e04110406020c01030605 81
    0x60207544d0a20748407805140e09031200c0c1d9980094060721080c02010306169075190440004400c0c1504460086c2c204501030740110340e07014170220f41c0f802202d403c242d06980701c1d1b50b01c0c0c1d41c03104c045829500075000108070f504020460428480305401600c5c1c1d0801404091a01e40d0340c900a9221074402d04e400030015410038018a0002d15252841c8284d660103400058580701005466103541e600140c46a4030460740032081c0b0400a1403002c00070302a0960845103807402d135289020280134042c0d0800410915200d03820a02c0061158148500441c2d02410a00a5040c4610302d03030003501e01100c0c0346c42004407045140605502c14082c0d10119a0068046c0504030032001d110009080002c2c0078003d517103000c00400c00c02c1c0d1103080111700e1581c05031740c5409001005150504894800441c0501000401d000303003260b240c100d09440b8111140c6041250032800b0400220b009000010035260b0201340205000032419001300e070f105640e0000340d1781004401e445408010fa0f10300c030803107620726101000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 292130080 1250 292128830 292128869
    0x80a121b2f120d1115181507030c020c0f010909020a0306050315010305060a0504150e010f050a06051002060906070806010c120509040b120604021009080f060108070609 74
    0x10344410700750801d241140e25208079650108030042c9060321032000c1640100700c1c000303609501a070150505211200a4401a0103a1106403400ca1002d0101c031100d020100c2c018001c00010000c0800c0301e451412040703a1441c1001002e07005004580c0100058007030304c940000245810030140d2120b1030143c54006c0303a1818180c8810094010074081d800345691080c0120386582c0802c00e5900c080c0720f245003111590304516110b8113102c2d002d49032644c130034248000e1000007480c001200840c0c19a4032400a5606d0141404a014041060700f20000d5490310061041d8008240c000750b0030344038280c1c0c1410301d0030000c440880e82c4002c00c03103005070603800c400c0101c0d28580c0704844241c2c0040b8149004803403610b05441d05c8042c08001d0525a01280e000a0500407500381130240c5900441e044419141c8000010b03d20f030384800340100020701c15282e4a0911100038042c82c44c00e4003900c0450110380154409001d00ca0343d40c1d0003030041c0001803080d60380000720988942d00c01d905803a0813140c030403c5480c86 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 292131330 1250 292130080 292130123
    0x1209030c2403150b03010e0a060b0703020a02060d0204120b01060f020a0302070e04050c06030f01060e06090108040f02010516050109051605010c080903100e010b24040b13080a121b 79
    0x4444803403c0c20306032400007a49210100255002c0c02d9000b4030002281071450780c1008682c0240e001c509000014820080820f80202d1030f105190f030141c43c1107039940d0706444c1800092007160000c00c1c0c00660b02a00030b0500422444040c1a0b81da5516507583c0c41c5041c01050341e403400780502c01001a807118009000c46a9a0b007032103504070f4868030841d4442480c840000c0c1003900300312a424120000a00100015a03001900c8081d900094900c240341c181d40c0c000082424000401c00f03041e070705c52800100d01316481030302292950f40444004c034154400c0c03071410901802c0418000d44180c410742c0000c00c2c10f821212200c0b01250016114080025202c2da5201801e40001e401c1d0741d03041c02241c0c1074407110100c5000b0f030358003424078100018048205504001e80400c903001440c4070061084490412103010b45c0c100c806136907520040b036483d02c0d1405d1100c40070741c40350381100105001e078030020000c00c156203922589841c115107a030750188454412100741d481d100039018000d00c1e5100c0c421a2448d44 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 292132580 1250 292131330 292131341
    0xf080f1302040b0609060a05130b04030c0e1825140d0b1306090605370b030a05030a0206010f0806070e09060105120906101d0c0a09031209030c2403 65
    0x602404017400c0022050004100d904450001070103d0b00001e24040e03103643c1680c80c4c4c4040c0030740c5010390382401d0954450030340e4000039000b07800064501d10082151000002d0b000180040001c080b07071190803450050174214122210354220794074902102240d03c0452090015502e0340203001840755501c1c40c0c89076800d03000301604508096103101c6081c0e0200c3c4460041e000300f14000c10010130306003030404082c09034068410111803a101e0b401c03d46007100e41c08034081c800c00310300c5010214840d4070500001b42084101c2e50700400074400050f081c0041a00841d51034101e0340f941c010500780941c0e54101e80c4d10f80f20f04840303001c00500e0300e442103a05447c1c14000960041410302d4100d080503500913500d000b102c1f081c1c0d540e98803540207008000f08010300c040c841001c0d082c4505d180305000c030f00d403040c1d44403442c0241200104010200f002001e0300c1c80b9480341401190018180c04039005030220141100110f80801d561104040402060304240500c00c034403840340d019029412417001d032000b10300900 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 292133830 1250 292132580 292132601
    0xf1b080c01061712160f061a04140106180b0c01050603060106020d080601080a110c0c09090106031e05010e060a0603060f05010b031305010b060403150501141809070509070f080f130204 81
    0x4105c0c101a000c1400010010a0a40315006c0051102100708040900c46201840ca0340b24504052a0ba048120f540ca0124115542410510b1900c4004803d52014140a4004141020780400d85201c03080f815005640200c6041d0290307800390342c8444089841e4111690316401080030740011079042d5104520080d84030310b51290000b03401000c1c138124242d503407160341c010213290302090140e801c610305203c0c01c41d001070150000700f20b21443d554401030706000022040012281c1c10300b8030303024000290440f4500301230701c4c0e0640d030039454040e0203a001030070a40029914545004043c03003c40400e441154103840242d549103085a980c40c2e10f5801c142d81c400000c5501e5504c44555480c513445a9001d440954469808112548028203104080b900141d002100402c2d82540603a413585690388104d03109021000c51744030700d0b6a260300151030200703140c0c00b858004a56038200030106911081c80e240c0c013541c47d900d9a400d6103506403414617609080e120380107180900d039500001403406030710195068 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 292135080 1250 292133830 292133857
    0x2091b0f0a140d020d06090b0a090b0f09160905030a17130b041202090610051606180305070201020d021c0e2214090303010608070f1b080c01061712 65
    0x94014a46010740041240700c070707200e4005c904e40304010780034010380e005400c002d1002c2200c0070200e8005041080b07280300c1c50034040e66440709404c6d00e4a42a254880190000e001260203043c43c19444c4c81800e042e5a816000074541e583c0440e144c40d02182a4040c0ea030840d81801001240c00d0f1302542d946e11164090b640b02412000003d105552a0044d100422551200c003002c602c090041c00548c60000b401c051242c5901109172000907006000d036030300a14544800340d16028186440700040c05981542804a55108802010942d004000f820154804c0c2e00b80d4404004001050307070b03180d40d690701c2c0380c07040d404607450921a144900d641d8030001400030040704010001d21214504251b410400411107512400c40244c2030300b003108129000307403480006508e50340c03400d04d0060034440041d14220401000100000f0754900c00d000140d5881c1054000c0180c000162500d40800d900c040041c4016500342000043d203040f81c01e00180b940080311000d4160780350030300396040f0139500054902108 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 292136330 1250 292135080 292135097
    0x18021e030109080c1b0a140a03140a0210050309120319060b0c0706090b0f0f09120a02040e12040302040c021c02010606020c0a180c03020c0d020a02091b0f0a 69
    0xa540c0c09000d2440840c0c0116061035903100105002400c00c000b0340100c0003000d5074104655000c0d200c0b0045081182c1c01209880085404c0c040040e4030740e0400e03070001c0c003044181c1150800e41d030300c00710301600058400c60700602d60907050402601c880c0022034240205400032540d9080c81010032005640c0054410340e03810516083d000d050301101c2e0b040d0400407504c0300c04a03800810190410030000640f000e4145030302414941404603000344201804000712060228191491160180640e00b8843d0024046010213605c006081e40d620030b894000e07032080381032000180321201c0118a0400000c10040c61500d00b03409c503003c1c04050008035155204501c10000042082c000d2a13582240c030b844aa800442c0d0549441c5c1e009141085844032284102c010300e108002e004000c3e0f6203c0234120801f200450f40d09080c40080e0003d01404c2001403107802004101840c2d1f6030301041c2c01800d1842103c1d022a161944502000360548407230082074541d1040000c00041981103018103944c0c613481c50400c10 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 292137580 1250 292136330 292136389
    0x901031a040603050c0a080105040803070e13180213020406020a020d0f0204050c030123060a2304060905090108060903090909250320011d010203130e01080d031802 72
    0xb00c031800d9009981541140c120010740d1300d0850702d00001080100001e1040342016100c00b585480040c00d07040a00030801d50098a036100c20304801e505040300c180400034810b0159032501c481007400e004a21900c00500c400900100c503109541c2a0392f070540c001c000d0200294248035001190031020384441c820060a00c0c0141c0e518029584100d000302410f903100e515200040c00d402c0c403440d4802d501005840540d498a0301c03003000b074034265290303803600b00c030400c4090b0a41450300200c010b4210305512300046c0812811b810100740803c0324801d0312228034580e41c40102d2034444e401560104000d40080003110118500700c41035540151100040d5210301042c03550709580605c02142e0a002d0501800082013404000c82c545e010070194841c8942c0d00c6108000000c03d103100b000e11406050880700032240e0719034400c1040e40d8004001e90110b020b50358840302a5921070b4424410180c079482210b25100309540309001d000030010b402e280464041c3c0349a42006860000c03e00d46d01c5021201807618035 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 292138830 1250 292137580 292137589
    0x906090501050a02091008010305061b0c010623060301050901030f050708060405010507030b0907020715110a060b120a030c0611090d1b0609060801150309172203080901031a 76
    0x240038083e600001079880f008030061140c1468850300040600c0070801c01000414000306140d640302c100b000c40380c044c0008600800b24107021714041c1000035071920744013141d48880d03001c00352860440c441c480c00707203503005404020440c8000d0003150b400504040041002400b503e41588a15219801b611080e03034440120320314122084505642c1a0b4460080c001550b401d88282c00c0484003e80d020400c514050078041d644900d2072003015603420102c000d10603440d1040c1800b4000c41d0005041d03c845211134240700001d000c040f042070740f03d1254150030721b41c001c200140116440f035054854441c061001d07210319005204132100c0070020441080101c0041d5030341e420304038405120b0103404000c0394600190f040b6905483e0480b405210101406010a507000201181141c0345003890030b11007585c0002c00c402070214007000070000c4170040004442c107071060004c0c1500f040000b01c1444241409031081021500d2807202070310700c000801c081022940709070411000d814600388003400c58600360002c00c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 292140080 1250 292138830 292138841
    0x20d0e0d0206010e0c040806070c03021038280f030b160203030606160609020603070504030501200904050402012a0b01080a0b3411010b01020708100906090501 70
    0x64005070400b10040c0180382140318441d400c521080a03141c00d29040c814003556805d400361a02c024004035244000c1018800c0110711607143c000e000c00d01802e50b210003010010112001c0380b242044c41e01c010510300003840c2c4614181d0b02401000e01d03032042407910012103640304184008100d102190030104030307240860b1240000350300c140007610640c0b8005001e40e1200788954048411174008105011056a0b401c06503051030a10340301036a41c2400790300d031080082c050044001d402031004820001d6054204d40a007080340d0050000b406900f8405107200364103c1c0307403a00a00182e0007885640024101584101c4d440f61040c100203e1110fa200c842403544280c82494491446081020008000c000080e141c010510f0b00001c007262006a42d441009002c020141040728000f6522417043d40704600a010208455046544050b242032030000c03c02d08201000501d20340c01e00c1040d002c07551000801c2411102104081c20b9203030100350038000941880348080e90110344452500002c1402803054 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 292141330 1250 292140080 292140103
    0x60c160f03020f0a05090a0f09050d0206040b010915030305032a0405040b09040b060405060a0308030703060501110f0d110a06020d02040503061b040b0304140f0f060c04080c04020d0e 80
    0x20024a01d9481041020360f40880d105000340310302d1004215689524440c0c58000b100c0000104500030811084001810b0700c010141c8a441240e188045890300804c3c0c2d9805580900c400b0b0400b40e8982840d0740c1982c0344100f20007070142142c0d90800c0031074455405150000701c545031220074840b000845864a0200e04008240c1450010381088689054030440c00c0070101529146120314081d04c5a0705a903d00821150140f5240c0c000a61195160250a4051503008842d640c40c2d080c01c0e203009000345158002c40e800f0514419a000800f030340000c0100045000100030100104404004c0303c650034010800d170100d119580c2d0450000780c081c006000000f80101005032994a4203003018545007018000b6140b000f0340c4c184081e00d0103988002c44098600800d4502e81d00c1d22245010441286130200449ca613004420000e002d0403c04954441c90784c4d0031a04a03540c0f500c400c0720420452042d48910310307030381c0d020720a004141c0c14650007070280000300071000038031800d04a44148c10080040c14 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 292142580 1250 292141330 292141349
    0x7021807020d0809010b030304050f04060b0d0212060111031c15082103060d0303050c04180902130b06040501030515091608011203090303030f0b04060b0a0206180705060c16 76
    0x401070341c2e290b000001d02e51040981000340f03e0010340f20046a00e07032155014160151324600208150740e103458103c50014281000013641c1c0c3c1c010001808001d4000e29507081b6520011004034a1962003842c05099403485000610316243c3c120540d081c0000d1100040790b0459143c0b2200320390140f03148698401000d4100241100703811141714001840300d03040c001102960140280200c64a4015043c22001d07417509000031340e074940c00080d0b0100c0c05203500401034400148100100c2100a4001034070306442501c0070321032460020313800c8080d07400b0350780d007503802090030b00082265611030381041e81c0008072050200a005e5104011600111003218420412840009500c6000794000c03c1140100340c481800048203006550040941c076031440041c00b01a1100340020800050340c0c480c1d011560001c00400455903500c8292025070006810352002d8010140001e45410310031840303524070660306001d0441517042ca000c1010942202901c0f809074070450390100c1c1d10004030540d88000d400c4160 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 292143830 1250 292142580 292142593
    0xa0302070c0e13120905030d0e1206150d021201050a09030816122403050f0712020307051002030d0606080f0705071104020a020a0f150e0d080406020702180702 70
    0x1041e424141c000c1d440307240000d12100401c00e041429010311680d00da0300c242980701c0389910100484503507400b80c001d0769240c02928100120380b07802940ca108040c00070b0340c0c04941d401c01503484540390901216654051900b03200d0360110b91600c01100c2240a200502000d02000d00180442c01c5074412204041d0300c65450704418203040d0014085507000030079540845c81d40c0351004008203410301d10030100c0304240d2500d03140c0d481d106c0210500844111040c01c41100306130f52b4240349940d00c030640c0a0820380d024515002c514061042c01000801d80c0260003055403600d0700c4240084218207082c05400c501080c06030145610b81c0b030042d04010401c1d40d0f01d20040c3e042074840e6038402d0002034100024000200b1240c1700189154124440b040b108840058a4021043c016030030980010b42c010220306500d071000081208000d18504449034a010420641c510703980c41e03d94400821181c47c0108148000180015076680c00070502c0501c040d01c9084604241410190000c0080d906100903801c800c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 292145080 1250 292143830 292143833
    0x15021f02090a0506071106070f21080603010b0d080706060b12060406170604060902030705040e06010e060307060504030b040c090905010504020f0303160b0618090a050c01090b0301050607060603080a030207 90
    0x10700803600644421183d65140ca04160b441c0b00c1c902c00c6041c3c007140140720100788501400181040481c106812241310840702c0b040261820341d180d001e06407130ac003007071951021440a06051154201d5103c0c05000c44e442d0b81c7d2180c94060302a009003d04888441c0c42d000f0219020791003201070605019424032220050401c881000140d40f49074000b404042d088a11303100c070744000001d0344d0b0b411580208000401410600100303007000c4580d00800c5d0402d0500c841400d00b043c001070441e040340c801b604200e50980303030b401c101a241c402e1842000c000545c14041403001c107200d800159040b0348511000d02c41c10350350315041019100c41360029a8a07075919000c00c019030a16a003800503484c01140554a0110078001490803142d5004c80507000444803000a10300361680308036040066502c8200d124540341c4442007580d40e00d00c170f040486040c020302449400b40d501501900003500d80c030f000b0450440e8245024402c2d5a0010003043d69800e1700c0d03c50020100d45600d0051140e4030b01c3c1d0b80c0159540e40780f23 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 292146330 1250 292145080 292145089
    0x13020c011d0703120509090a1a090702030a03050c03010b07140c030a08180a0810090510090f03230d0c0c0c140f180a0e07091b0f02030a020715021f0209 67
    0x38001039010f005c0c00304960b95807541c1d02c28456a100303c56040004080c1c00164041c0e04003544d1541a58000f140c0806000550b500000a801000441c5d54203011650310340d402460f5074042031040d60202c1805201260000b4116501000c4045103042140c00720040400020700e0701c16580400e803107003071000400100340c480400c00034035021820381e5580ca00c54601701d5119030311003001055818082d980d80c01e0b0400c01000b4044e81d003052050250070b000e00c0c2d9842c01c1c42030021603130a0007100450074802d900d0b0038903043c04d09900a070107a6160420700f010184143d540181c80e41d03000e10010405400000800542d2815020b030140c1191648202a030080b041400b81d00104040124854203443c401c0d040c44202d0403041a500c480f040300c0100c0c024029500303a514000b020780003042400c1c01d14140c50144526415125800300095442504284032100c0c242c0e140d11031080424010b0b00070764001e0080060500742101200740c544100c038800d1302c40c103120a01d00301140ca9680c0119400062088151a0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 292147580 1250 292146330 292146353
    0x11011b0615052d0103200c011b0207030201180e161214010b0a0903230d0905031510081f0c050301080607031a0d080703021b13020c011d0703 62
    0x40641e90201c00c030f8900d151810040b9910340f90010303140080d01111107581d12a401c1044880141900408542d100d0310500301503401940a41c410796107000500c3d00ca04a06404014140303c050700a0046e45007150011901640a1901070601e10b84415002807542c2220fa085440f94141c2900410309140c02c050007048180c1850f030808207075003005080171450000e0b164040c1100e044000565840030481402d980c40346841d88003070301c9001103071007401d01c40c40c4540301003002e14a28002e64842d408500400d85401006000b0180c1560210b0b98618090030360440e510380011610a0780502d0301e594005091600d0311001c590030741d01c141104501c40000c0c03140240d00d01c0c0102400c00074195030400540c155201c2c0010a4003013099100c01c40c1048000342d40e23a0580320400c000d043c8510003092800e202130282c0c86a0002c500500c03503146040205210140c3c481c01c0804000c0c06141d107038100a108601031341201c00609860b559aa0855408000c45801e070028820007002501c2090f1850415101101 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 292148830 1250 292147580 292147589
    0x4060b09030304060e120d26040f0308040501090b1303080105090c0901050f0712080f0a09151a090117060c090604090207080706060609170c03060411011b0615 70
    0x24080c880155560350100980702900d105142c0030303000c0e5013000001003850300018444407207405410280b114030f641c800d40300f80009641c901c0c011000707100201c8000c0b900204480c06800404c04901d0000064428200380b50414050380000c241000c01d0b881d144404a41554808000d609104c0a1310030150011761450045c001102d00441c14586940069094420607a903d0b0402c0310000c2c00071036118103181911030f8150007006c0242854803100003e03094a03026184a0500d1210b40000780d503d001501454603030590003c004100500856000d0f4080c200a1000c0c5140084020a134012a200c20325800d008010748030b80030755402440790b946400d10b4405010000450710820801030980c40d06000c540881c0c1d980b40700140ea40055007444040b6000310b8800a015a040000014986074025180350980780d07111085102000520300031035030303000301c1065990141c01500009004c2400e641c5180c100050605200d503906003a0401140715003850081200d2041da01c0000107203025880742031300040e0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 292150080 1250 292148830 292148849
    0x41401090e010b3f03030106080603010e0d14040801050a090611030f010501080703060305010c0806030d02030c12030408040803030103080a030506040506031905031c1a0303130902031308180406 85
    0x14031188001c01d001c59108242c4034041c0e4100b116024540456a440300f0201c0c01040c803404e500e400101c0c80307030749075402807040c000058603d4010801c140f4042c4540c1500210620082560071582007040d140304450201c1e94403140e0041c003000030411400e010b11480360601c000002583c1c90f042c60032408540404107110304c261014070070130201e9401c48030950b05481d001d081240141d0380d0200304030050300c2e06d030300014000d50a0898100d11150000d41640c00f6007001c60070ba0752041e1482d20220f07036a000e08076004080e90300010081280030300301001590858041c00c2e8051030140c03641030080c515170003070f84101e0310301300002011032409915220b1301d40c10140854003403240d0305011001954440a800e00070740c08403505103540c010008204215004441d0400c10007540c245030041c1a07008007614056200040c441c0d10a03500d0b14a000b008032002d034449564941e0809081640f40002074000816080b0340c00601c640000102d03035200c01a00c030746e0301074040300701d0100c411000b40010340f08141c0c888a1748 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 292151330 1250 292150080 292150091
    0xe010906060f180e010f02040303020d0f031a090406091b24090506090409020915090a0e0d1d090a1d060118091e030f090e10050607060209041401090e01 67
    0x81c1d203e041c50306440d00c800301c200070942641c1c420810f40101a01795414060920014000040580115940081c43d069869049810003041000d034290f654880b20b0320805500c031240c0c071040349001d07072506400501890000070401321603500c54584440e00311140c00341f8034020304100051049948070070391840c031940362a0805000d540c8050a00000ca02a9034403801007c10091300da5140c42d4072010b00140c0090008141741400507c0720404d11110002d41d00510840000501c0b01c0c90074011408034002d4900149107810703586404542c99594045408011f00000b4002400c03036680b5a0060b008580408000426111555540c0e420f2000b940d004442c0d44c000d600100f00800b8070900901400007199001b14148015190400307030110801c148811b03220381c8401080905034400105e02000c45540c0b43c00c446c1039140c020070025114115007003c808418a9014003041c20070102400d0342d144500400350078000e009000030305480404d41d0140e0001e000c5e03001084124140c2c06400c01c40d408000c0200039 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 292152580 1250 292151330 292151339
    0x10806010e0721020304031b1104110301030f080703090f090f0b0906030d0e0607021201050f09070e0105040c0e13090605060a180e030702030615191d060307090e010906060f 76
    0xf500e18401c020400c01a40803000600380350080d0001500569010189810300d05c1a10b0040815441110160300482c40d0a0602d84c44038a940c08a80c1a0b80e0007100040040b142c0e541c80d00d0650340004000c508210380c0c480001020501e01d007411015044011000c07942d0360f00034040300d045500e1428030a104140403014440076450210f901c0400e07401078500040c028580748089666071064200003500402c010345120720592040d880580290826885082942c42c3d080c0401d03605c1c6064011840340032100801080740e4030300790303211107001485070404002c584045000101e4103070300790300782605040e1158600020040240b280581c05002260040703c503904011100d4403d8201804116005a48000008122404100b507481c0769034010100d8055281051800603400c00d00c0e18443c1c00385000c160a110b00c0c2e01d000b110b03d015520305001d81c000483c0c059260140411025102d25018000c40401044514481c01418090210080007288490107841e2540442d0940d6000c1d82110103078010522 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 292153830 1250 292152580 292152617
    0x1202221a01140a0c0c15051804050402210114010e0708012102150c06010f030501060902040e0406330f0f0506070305070c0e01230103050c03070f17010806010e07 71
    0x80f41e580983ca00b2001008541c0707010380281c0320720380201200340459060a10040c3c1e200c001004203840b1181002e00c034011100911060f0b45003a1002944031a9001c000f4803107440d00c0c01030f03113803404a07000003048408440c059041c84003020380182e107229150804200e292a04862003031300508011031404401c00e684100b01044a40f5050000d02ca5814808003800f9aa1040142d619a40483c815140d15580d909117404891744684400c440c15428070794005210350340f80c402e880480d8070b40c20340c1c0c070700d10ba88540e40c010080c0b101c111803c090500c07541858610038100b0300031201c08890802c58040c07803418103010007008202d5500644006000010901190b100c800685640560500f0700c50749a51072490400d820343c18a40020b44c007440b2060000840c0700450420f0b26400c0c1e90740c0600c8045050690044050741d0b0b0480310045902c00230008101c80600c0340d51140c0340d80c40c1d00d10700040940b507a442d100403041003c1e403048100340e2083c4010302c0449105844290010700c1400c3c44103600d006905180c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 292155080 1250 292153830 292153837
    0xf0e060d030c06090c06030510290706060602010b01020d0504060e1c060603030807180f030303050c0c03071a161e030e0f010f05070f02060c13120302060a050109151202221a0114 78
    0x501c40000d400901110741510360081c2d911142e3301000c103111950f19000000e00034140b6180c41c90040c4a501e000340c07640b50140084909031007896032211039404881040c4601703104070f2030400c007601148a00c028040b40c0c07a481040f001c2d40c0300c2da46900460820080c01004c0328084c0c1101c088941c1e44640410801040d08444c03022250301d420702186940c1c4404030041c4501800642c42000e000001d0050100407407604501d205100c10100d800051300d88039000f10141146110701c0c00412540303c00007035141402d15500c0f10020039482d0210710900340d1500b0b41e0400700000c800f42003071703034507424813007400e03510740c00b450b81e02c2205441c014104a4401200030b654001c06041c0c1e07580c94800140002d400c8040e240904050440001c1045040c4040e1800070341d240b40454500f202a803510303001080e1040381e8010a4420044240f040440303a0a00750301e00403000f1442d80403a84814038444490214441082e491040f402c03000000030645080602241c0030846011100d0402003896413888000200320240e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 292156330 1250 292155080 292155119
    0x14040e010e10120b1608090a031112070b0103021305090307060905010b100f021e0d08061c050d030605060a050a230c010b0a0f0e060d030c06090c06030510 68
    0x140c0300251502e410b8403000c08501d801201480750300b01c0fa00e0707052000303420740359024814031450802182c040700f00c2112000b0701920701120681042060b03602007449071030081c031500b0113401550001c8074260440c001650004030222140b15150340100198606804035500400061005102c40d143c01d00c42e8039100c0c0301d5000018002d0341e40d03440310024007009501000c03c0d40d0340940800d030302140c101005454804550354000061044031100341000001d0304000f09604032140080880080c001401d4a004100030036503604500c40b08410510400528000c1240700d020f10041c000040300c00a00500381c4500740c000c90701608080210380e1203d540b1900700c4802c55400e20344080078030170881002011010054084041110100e16521840c2065000500116044400042007a5500616160301409100d440c0420086000086180c00c141d213034180c18510903e0a032209188aa50b075808841002809607002264070b28180700564140c49615003010b032000307640f043e140c0b0f813248500300315260004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 292157580 1250 292156330 292156349
    0x120f0f101a1e030d1e030e030d020c0c0d03170108010902010503130206120a05060120070b0a0c0c0e040b0a051603230a0b090f0f0a0903050405130c14040e01 69
    0x3461031801c2c1c0600d1401e510a400101a64003403002c80400400781e0008403640302c0d074411000680f60340d9600038414100d201c603008000d107007080c01550b01e91000f500315041b48005030080103401100c80d600d010b070f84e11125200c1d8660080714142c80d809010300c002e058100e0030580e0b14041d90240545c4e04081a21750001c0000b0402c01850307120f1020860b28081c81001041da02d0f400820701041002d9604280d104100030303610260501d40044104000f508400e51000d40364110309014000c8280c0341c00181040400707820044000c242950b00d20403c2c107407591000a10b59180c1c41440104400c25150a4108540c0007040c0b110782843e41c3d0130020500045001c106040c0d0b00c0d81100c48640200d90746540e10404005900c020703123413801c0148040c115150a02e44100b00315000154102240c0d10124002d151969000c40c1c10b0340c40341d1700700008006441080e000e000c0705000009150350752480180841d103c64802040c02d00200d0780c0a42103603080c90b007607041503106100c01c0c8070710441c08543c036044a40103c0d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 292158830 1250 292157580 292157599
    0x31d06011208070209040b011701201e0304060507120207120e03160806040212010908070f020607120302130b04180216020402040308040e0907050108010b09120f0f101a 74
    0x2d0040320700d220f1080e00a4016030200304120500c148030b0300990482e108482c1c030005109000e07d00c14220b540c42401070301400b050001e03010b2001a0303000a040144070704d11210241118460b030b448507980080300c0440c0c1c050b4840007003044041c2c5c00495540703841e500030000d505040300d91380c07440694401601c01e40c04000441d10000340c0c59078204000c41c441d0078156010140644c45481d06ca81300c0a04850a9004416503a02c0d2100000144540300210340c2069086060504903a90300d4102c40c40100e0a0f40d00c003c0031301102010070b8000da45540742c0c4907580c6005a803003460700d041187c036004a81c0f00240012051004200707131814540040c00803c83d2100051744ca1380200008061400c1d02c010181d0417920214001c4200101a0b0050050361070060088041e55a2a0180c966403400b070701480f40000c503182d0040090840b07907000342480d00380081c0b800d514100d0300494a4517001d0042d000c4d1040d40c0c80b05d4840d0341c1000c4240a040b01003c50104244010740d58000c0c0c00848206800c2c00900400c0080c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 292160080 1250 292158830 292158833
    0x3210115031e0204181109090c0a090b031303030e0606090c0c0f0102120106090b040506091002010e010e330f1308030702061503012904020904090c06031d060112 71
    0x405120b244000d0354001103465075140c2011500c4410910340a01c0c81e18030f0803039000e00203a502020b0310740c1c815005010500a42d00da074141c2c42c981d080307920301d2003d1010381d0782d01240314070000c001396108805000843c14000814140201030f264081e160300b0b51908a4010f10806486210800c0d501ca00c4c46101c29a03190f01c070002080c54030070f101c450001e840d4404030b0010b12421401804074100c89103660f030350365104d0305e078010400302d84528480d0320341c814800c0054441034180000300289003051400005601c1710345003c21800c1d5850441414043d40129a5000b02440b0301498a028214503600c104450300e5250409000703080082c06180302c1507100b000040c5451802a011045941d0144804d07451f4108098083c0d070307820f400d0f42d04100741c040c41940041d0900301441255460f600001c07400c011003405400884030b2031850346095402c19000c10400545803590701400d83d01d03a00c11402c1c800c05030f28191000b02160240b6800d00a41c900c2260801c02840c000225141510341044620071018410b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 292161330 1250 292160080 292160111
    0x5090d11030c091e0711070e0c070b040506010f06021b04090c05030f1506040908070b101e170109021e04060f0b030403180602070317040302120321011503 68
    0x1944031865001100300100000011413503401c02c4020700c442445103040e1503815041e07424071503911764421307180d00005c01000250350064aa41c0c10504a6507500d00d000318584030101d00b00f10895081e10345511100c010401c2408900003d40280010b201918504802c1c0300c0450f048000a41103911642c0c469040346c2c00e2080040060004010050858400c000b0307902075180c0b125080c0748100450081c0d040001d0403401d0900408485680c40410945072000750303990404201b001920900c4014241d48000ca6013101e400304420015001c0040101501d180c00d0181d110741c0300c00c03901e2050590500d003613640140c8a0202c0980000a82c0c01c1700e5092110513400b04004110950044000741268200000d11441c1e5400960256010781d07695450752004049880d00d0408a10400b401130f400408100041000c4100014550350702082070351a1550780d0700000d980c41d00400010200d5003000600340020b040c00610798400820540858403030b989003110020b900d6103c80030080074917840e1100003009401 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 292162580 1250 292161330 292161343
    0xc31051c140705062d04030c1e08100618020f070305030c0f030f070f02010e0706050c010e030301080102040e090d05090d03031814100204150c03050c03070b061005090d1103 76
    0x13601d010717180c141c0454400c5100003540b8007401902c880700d02182e00d5076044403c840070740350002c0c07641c02e50502e000807046103540002c2012010020b024030100301c4550a002410aa0415103400706c3c155040c81c1001c4e1030007a9a00c2d100300d08034410001c0c1c00e54040036409071184503815040182c2c03295241c02c2e60031154410305240b800c4440000040201c600403000703000e4011043c03070b030b210050030403001d00a81c00c07500c024403102e00f40c0d402a40100700e05c80c070480040c100040c0360000481c00e00c1615186924641080e00441002c1c3d401040c244988880408010ba018804034010110402041c1003d4440d20880c050071f4003640400b044441818002d40203110a185041c00102c815035003030400c50161000c0404a501602800a001400c2d890900990701903400207203d00200b045000000e0300c16081c414021400c2c420180f201c0d268280c0c040c80902411070180ca03c504813031078036034100111254610340e41c03002d06c8800d2155107107507110105660366165002c02041041c0c0c1e8407200191070b050 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 292163830 1250 292162580 292162589
    0x210123905071a010e010e0f0105040506012106080d02031314040902030f0106030501110703020c27130c09020307051602041107060209041409060f0c31051c1407 71
    0x62510030f203000810807940541e040b0b5200c00014400d5989a1106401d840400e42e54038012210390300041c0918a49507010700c0c0c202c6070506012404542910340302c00a400f1072140141040d80d12030042108040601c603200c283c90851011314908442d08460361403210341c900501800110b41c0640403011386030b541c08035800340d4005003103400c0f801c1160841c5002e090640022100d550804240081e040e060800351804950f2680144c42908440004d02601840003510440b40d030078503500d40003d80d102500c505020344a0f400f0030884c990424208083c002501d5030040000501c100304002c1c81c00d6011702551403031104144071070720041c545d000080107024400c42c402d101c0d07100011114100305966004082c0300c40c041d40c06201c070008201c0f03020307985c080844280310720360031400020742058040e40c1e08075444000a04060f0401550098096890203e524001d0150502c02c1c44804040030203981d500003000219080e10744400c0344500e050868041c914024032140e105150ba000c1e0710018810f410241 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 292165080 1250 292163830 292163843
    0x1080403121104151d3d020d0f02120f030a09080d150e01261504080702120120070204021c0203040c0603050601020c011b021012390507 60
    0x1d80e224619030000e0391822100f00c1c080b4840000c10640d50740490a5055241e0008020080808060303c0c50f11484d030080d0703840c2c5c4072801b030f204200b202d0006040c83c070344840859a00a1004445044000d020581c2101c00c14065501108884004600c2c07401142d01e401b000410715600d0f0b41700c405500c4007030320640200401c004070100d08018000d034568000c0ca489405200b0512031300390380d08030708843c02400780248148424a4101401c81001e401042d0070210256030072200d421041c041c0c5250180d1050b40d040b161540001010030030f6140103841903a0030001600208100c0501c8005c6a0f00b91710300040c00c103402c3c0b402007900d506543d1658141c8291255480a80c0015603681d09000000e6000300e0302102e1044150703a001c00d546d0b20070b100c0e25110303400c180c008060b540c02103070054400e2800c00b1900d0441641c1c1030b0b0082c00580701c41513a10002c90054035400d103800304240c400011341d41e5241640c80c40103140190940140d0fa0601300141245071401c0341c0c8410000d40b6401c54240c811014040e040 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 292166330 1250 292165080 292165087
    0x24071106060d020111150108010b0406090207021302030402010c061416181401180b030402030d110d05090a09091419020a15020102130b12100b0d0b03031b030403021c02010804031211 80
    0x700388c0190010240e0308012601040034540b625101c0d4100d0150007001303500300c4450f90407140d15002640c002c58000d4014182181c1f50035842c0c0e43c40c000d6841c1c03050340306c042000100a103c0070105000030400c4c04142424042105030500d440300b8500e2004d4410f1a01409061090380700c00e9001e141211658440340e04900540c90700e6580d8042161b10075103049019128044d01886e40c0361040000611414440020300820b8501c0c19003140c55130414480039601c0380300d000c1d0001d4803000520500405920401203907084201c0e80d40c41d2818946a2801c08007651548640000103030b5401a54401b40c0302102210041100c0201c1708900a025201c0c65a02a00c0102d001240c00803003503014100181c841e4000c01030a9491266000d81c0418501c01c0c09000c00060007001c00d8180710390010480c020703029045a00b000d05880303100c80c002000800815a68100203018030541c02c104041c0c0180310700019400040001c43d600007030906ca4002c00190401024803d175455441071070300072050000758800c1042d203 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 292167580 1250 292166330 292166339
    0x3060506090f100e0612010314010510140f04090b07030b04020405060919090c09030c0f060c0609171c1802030c06030901060b0703050a08090d050d0c0224071106060d0201111501 78
    0x603640801e008c10784062210751207491007190f0502859102c1c0403843d0420340320620701210f4021920b00c1c02c0c445540420407510180c82916588200101103000e1103a07603001d42810301d806070485d00100c550358040d6004010074001c54844500f100d50548090b074039240c840c0900729210794003061036084100083c1c20085003405031507003c2040c50640c5d004101601c1c0c960b03625450b40c916041d15214007404110f100300da81c000b244065101c1d2040302d0040381d04000d00010000d114900d07620078100303940200c01c00c0004d61580c061910075580c1c0c004002e00680c0c1c008131203070006540c80c0b00c0e889400e4851800000040c4042c402904082d00900c0081d10f999120704440c6005441601700c010104001242e4078005044d400000503401c0714a0910b84038145019008220200a80751591046066208030107040c580403d10b4030f000303c8401483c6880c1241d6080420008010300d2003801c007020365078051400d000080d607034901c5455040d942404c10205540c14480300609003044510400c074980c0720f0400014 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 292168830 1250 292167580 292167607
    0x19020403080a050910051801121b200609031b0a060906140703090b010308030a060b0301080307050c01021b10030e0d0c061d030f1e0d0c03060506090f100e06 69
    0x14480030111070b0717101054044241141c40303010399240380451800810701383c041da500400c00802c20700e58440c4089103103880301000c4014160140c581030001140681a08003140f110076441d50b205442c000070341a05e041c80e898903603407400b8142c0325140148031820800e01a00b820442e405a0582c0140240b01019407410300c0c2008005401d000484ca03180003000442d050311074480c40800a0f40000551030f00d0b421612100311503000100124142940c40300041200080c0a020754000c2c40340000440d907440251a00341d08105031a10f0103410355100b0410451f00c0c3c1d420844c44107003c40180d8070014901d00f5804100c1c05008060b000120740c2c000e17503e0424100707600c4901d41c0c46040c02150144688008910102c00244481d10250129042888036000018000d0300030143c44602602021407411042c82c00c0035241d0100c5084d07681c1d199521000260359805000e01002000111503860401c2840c1010452410031a03e841c2c0c0328051043e1414070090041160402592000d0106c40d11140300034500c2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 292170080 1250 292168830 292168837
    0xb0904050102220815180106080a05070807060909020c031c09020306010f12024b010503040f08070c03060e030a0e04020a0203070210050c010f0501050108060a03020919020403080a05 80
    0x707001d03c000034049014081031101c150201d40e0300728001c0815100c1c1c0e20000810810107004000020242141180c00d00d209001d41000381c81c088010f000004018941586440490351014030b040e00250360811075541c210040008807500c0c8070b00560380d64003150010f070079486251401c4a000d8600c1d80c086040348459400030f148548240c0c22548180d880c1c060f000070907182071141d429041d0100c030040006091500d40d01044154600580f01d44c0b800501c5d48223040c0114030110801c80d9116007807900000c03c03171615107401c0e01c420700f0300a1540c00c0c15110548001c1c0782c601c0c00b2780101000219541040306061840d0020b41e080b0b10b0820030040301301c810580b42e6000c054220300248418074429000c0c900383c0308a400c00440ca4000790318091182c4d00340401c0414043c5408148003040c45654074a4000303010700c10055900c4640001c00f0b6062000140c8204405404070f40200010107082c00140c5408034640d81011070402c01c80c170049032840302c080180c8559040200300304000700b000c00c0403d8204014 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 292171330 1250 292170080 292170097
    0x70201060308030a062c0a0e01060305120c101416110a050c0102070509150d02060c100b2b032003190206390c0a1a06060703140d0b0904050102 63
    0x1803000403041c202c402800c504000e520006455019011440b0a91154841c05c1902041b00000c2b8101e0b0350f94651500f41030000b0000b441c401e40026041580e031409000c3c0d003401c6100e441003041081200e86840344014001401c6000703501415a10480403409450071810946c698000c4840a140302e242040d02e4100a100c0310340540718100010500307260070b07230025124107100741c408005076800340f0402025102e885030a80c3c010200b0468000104424485039665001c0060b0204103164900248042c105030700d10070310341d500c4c0c024100308445c0c2c00740115000030b6501403400c2c40c04050303080e60541b44600c4420845240c0e01c80041c0c912425402200e4110120a4a4087e107010b0755441518000011041c1d050910780342c802401c0504203101d45004122002c1c2c014042ca00780042c80108600e4220144010346507450f4142d4120300c0310400f0a040ca522103405d40300a803c0c0b00f03040d580030707150000c3c50743e280da081600030549520000381d983c08070780d0001c001008140c641c1054100035000703501c070214 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 292172580 1250 292171330 292171349
    0x1a0a0603053406050d090c031e0203070509010b0a27081f050405030a11071809020f010f0207050405040816080d0c090b03070309032d120e06040209070201060308030a06 74
    0xc908008901ca9550b200b19015522900e1901c02c6000d52100100441541180c150a003400040082000140901c181c2524020f9a01100c215801010f18040322a4440e5100c4c0d149440148001c80d560000d45026443c00c4c1800c458070a0140501164912443c0e150180400001e2000516079800100b092040e542480401851601104210181d800803100a44541c0c030800441c4a0f0500c942120110000e180e0291528651103590500d91400341128401d00e09841d02043c50a600c0d02018680c03035440c09003000c00407040e08000213500c3c0e10329482810f12880d43c0c1e1000074140034600301103e1081119222110041134180742401c07480d001006407a1591749440e000407000d6000d0501d5200361038209000034215680c1060840207070500b10030450811100001e0703503001c40404e00d000d034060000100c4036804240441b00013440b00302e45144803040075090801120b00d40b01d000c9282504560159401c01c116555850244c0c003400c0700750710003072410100004002900b040f1b0f510541c03d9504e8001c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 292173830 1250 292172580 292172653
    0xa0209040b0406050a06050d020d0c030f0c080403120c020c030d0c1a0c041413090503040810050c0301030f030513080c010e0603070f0305090a02120703030306121a0a060305 76
    0x707007403000300c8015020300fa40040c3d00150910480d0b01903000342c0303c00304034001e001d854008203080001c2518008440c0e03801080d100c0d00c0311041e0000c50300400c90360188514240312f451a280d28000e00c03c0410109422086650b02d8424043d030b407007400b40c08420380002e0f007101c03c0b4015040c2d0080c803c254000d401d8424500e0281d000460030503506141340a802a50b4005003040c0c2800a10720742c02205001385581b040c2c00d04078140b01c0d107089029a508490003030024684403071508000f507080010b12440c504506141008020b0182d110380706072070542c1d401042d031001040841c9001c0d142c51060901c8013260081c0e408002440e078000203007841c6003030402c2c2e0f22140c0010035501848030a00090b0344800c003086170400700c1254144654459076111a442d0220b40c08001c2c160080b40c0700300d5495a00c00c1264110400501c01c0c9034141c01014004d00c0c004017038142503010380d1075406584980c103070103403221003848000c50314411483d0070040107036030007505030b40044580d410200e42649455000500d00c40454 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 292175080 1250 292173830 292173851
    0x1e05130e09070e0408180409150609110c1b15030c0301030c05040209031009021c0c05030f030f16020612090d0305090c15030a06080304150318030507020d0f08030a020904 75
    0x10503080c4c000e5a0000c8250305040d2450b445149829841d4512038029643d42c1a060210303554100104454003c1d040006066007440d440100303031085148a00e01c81e4004000c0003220200010705801488001e1007000142120300000903a1240c0118441801580c04024001800c8210005504032481180342032101c40c0e031002844180d0040c4146143d064200c40d012200450690704241034840c8024030142941c10540b40340b030b541c840c10903005c0d84e0060008034203220034142005030900b0315000340021424070040711030b20f00d0355100e2030035080246030341020050210b4a4400a40da100c0c50801c0902c0054502218102ea0b40c1c0c650800300b00010741441c0115011034004107401610301000b030b1800d0200f03810f20864a5095001900f50f1207016a200400150701c1804d0000d0000b402250404c01410390801c0c00c000c083c0c030001c40078030400da03500d08180ca000982110403a402c05034162010380c0c3c1c10708642070000c96a1112080540700b64030010070010b403400319600615440030211030400c44509078 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 292176330 1250 292175080 292175099
    0x60f081b100c12031e0e0c0a030c1712070308090114040804061b021809060f1501110a171b010501050303030f13050a030905010306090c1e05130e0907 66
    0xd06000c040840c403440e0b8000c01007020b081c0d01d26407000c001d08003c00c03007803040380c0d000380c07a9a004c070b040b2019503540d1507103030742d111a0a101c40320324a03000f166410388450460300c801107001c029110301a03240740008803510b40708009010750058000044922921944282006002c098040341c10f10215480c2c015902c13104401d4900f194019608100710f14206810a502580d1207951004504200503042e8030460043c0d0360071242082e0110115003035001d5081c128201840d12311b01409055a403c60340c0c040202c1e10b0241084101606802d10748604030030a0a8140e42c204050010080c00700801d00b046801d404200d0300c010510f24125482c0f03d8400410340000380d00320b03042030084a9041d0410004540d5100b0521207264005910400c0e030003460b0046da90f010b2804c402c00c0700490106009d0803041040d5a0140b1401c0014030400740c1c18000c80c880c8180050450001d9034035815527180103160314003218450030a440d1480c00c0707480802211611662400c019500841d034012491040c0c5201160901c50f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 292177580 1250 292176330 292176349
    0x601020a0b161e1d061e0903070510020c041d030714070609050d110103020903030a022103130210030204180504020a120803011a1201060309020f0108070c06090501060f081b 76
    0x30984d500d00402c400320080d82c071340c150240d080307681c0b084040c001181118921075001050711041c06403660b641603100203044c10216144e008620070143e001f046210260045505a5000c0342110f000031140308101100c80301b1460200345145c2c034480407500408224030825464031034041b07841218040c581d100b03011251504d090150640201c0014062400561086c0030b40000c000141000f60500c000310000ca481c58000329950801a0b01c0b043c90b01403110000b82c6030040f8104070782620752461070f00100180100e411300000a00903c00d115840080c544694142d07005455503000b039055404180c0100c1002e00070981c0c0c1030348110482e80002948031001400b00404541c002100ca04682c644403205c12011401011f00030b007150104245220200d0110400f4060040c0d07880024504101d801401034298001041c2c505024400c802c1c0455250003d0310b000003184d0051000c01e00180529190340075242c194400040f500715160040751a03000130654140c0d4052901002e8400200f031810400b6002 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 292178830 1250 292177580 292177637
    0x2070b0a0b0a0510082509030605150618130f09030905090f01050111010b03010501060305010e0f0603100b01030612030f02060a0209090106030b03030909010f0810020c03030703050601020a0b16 85
    0xa120940c01145070f0041090755841040d142c0d803034440d142c0317240c0e141c0c3e1b114070f840a6032000104400400d004121680c0f00f0103810500448004109034562808960a40f00b608a8415050b01c11080320f81c0aa076030702e00040e0381128055003484040b10118005011705100072013140030506940c80400d1505043c0701051041c2d2502441c1254bd0746010015680311401283e410141e54940c0081c0c09151000d0140600820711564002215850410070711810b035406010240c48080d078405122865600003440048101a410300050210034040168001c03d01d62703104041c0350f611031040d5400c1c5a044002143c82c10055000e40361160760303805802040307108900711140c0c05100c01c0b00600c01706201b90301440b0b603d440581124541600080041c4400000740d00c04601031100c01c900b40310060090005241c0c00800703110a60a06520702442512400700070040b03810543e6500010344d181c0e100b0045d01c8034103a0455452141400c10312440700600c51450261008a00070f9040541010541343c00203e403070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 292180080 1250 292178830 292178839
    0x10110309030a030510232b030f0c0f080a08061807050f0408031204060b060f040509060a1805060a24081f080a050613020a090b060d02070b0a0b0a05 65
    0x881040d200f94010b003c040c00e803440c1100403020204541500c072a54114a800c0198000924840c0404004001d0035050744011b40c0308645030800f803c80d021b14030a0304600d6044c00c000b0050103002c00c1c1118501102c403405081089020714801c24030150000600780c90b030080e641c000c00c5030386175020700056016100070400d1810f0303007100103448148604060118101c13100046407074181d480392941d103107820101482e111442d6100500040058600c500d40d01a0010b940c1182004162400d400b0140034a104960040c1c1c1d040000403019551114802d01600720310000800c6840030340c03100300040c03008882c281d0048005000c0031400c1001d40414295801c0c0f83d0ba141c4030000740d0880100c4034803202500f1980071854000080408441032941100a0403121008083d0f819607410500d01d000d4028107101183c81c100c558440250315954046020703915010b40100e08040d8030350114840d0311400040f11104d5102041d41010403071000c5029000d001140824400d81e0f00d01c03410440e80702e600b4032650390320 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 292181330 1250 292180080 292180087
    0x509030d0203040204090b180601051002030d050c070203061009060504020414040c0e09090a030216050f28140909010b0f0d020a120b180f070e13060e1011030903 71
    0x181031640095501030310151001c0340e1121303103564001c1c00c0c0a0075510130707019403a91079102c1c110000030170020340104022030360364895211010303000e52284070f2517060780c5140d6100c00c0001c40043d10380c4115164250301030101cbe5814908009101c0401035a40034200742c03142042000a4240303028000d441c182c3c0c1e50421444c20607030f44401040b0040150410100034041c048060a0032650340c050b80c14842d04400c1c0142141c84010b190090801048070f4070100325510f0000184419100c400d046107820380b065806103280c01244884000e891512299184480c1d54500089440f050748099003d043da400c1e100c10384c8989607151141c0c03d855084841c2c580108058181f0003080c034100b13841d2404580003521040c252629050a030100d40300014081d660800003100b44100c040001ca882040b00d0420000b40c448850744c0b140c0c0a403540c02c1031181103c1c246031400411300c10341c1c02d000403940c815808641000a107002e0800a512418920003034000e061800c1096025140c0a0302124407e80c80000510f14 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 292182580 1250 292181330 292181347
    0x2060f0402013f141816181a10230403050105060a0e07080403261021030801090504050f0618060105010e1f1101060303050403020f04050903 62
    0x901000080050341004015203041d60340c11445007100502d420241141c2e1004201c0c41040402c400300341402d518064a01000c0c06000280c14030700c5500712040e144200400c0d0500c00e00c0c145030a03460b002c9502502c0242400040001c000307041c03064a4000c203401400090800b90130980c07818148a80b6580108200c0141c280c1103108504145c00c4044011158148002c420007030015504a60000c4440780e540e07606016082c40d04c1c0712454010f1607810f0f1040030a00d0080001001d040380035100805000200b01c0d2018000300004003009510360880509615190841243d40c0c040168820b40301ca0504d202c0120328540358160383c41180b42c1d05505c4104050340b0b4200c1c0480186001001030b1013030300825245d51030501e8180890790050140c41c80702c07070034418541e030030906000040e800503040c4800b0404071b80080e00c8186c000c0050b019400d032007600504404a080d9401c030a1920420010751801102100305a002400350043d28000e90b0040104e0780c8210520007210f201362018500c41d40103010490 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 292183830 1250 292182580 292182601
    0x30503060904081303030903062018040f1806150501020a0212010905030a1701090902090a0c170106110705060906160615090b09090a020913030207080307060212090a030206 76
    0x2070300107208014262601c3d03411441094145820f1704210006850120108180041409184085040801124a941900032040a040c0b04509420446548856803072915a445501070b250001d5050802d00c80e0740e011031100001812030030002ca40d00c5280a138500c050350300d00207424040e120103800415165129400b0003502201e00c44160303a2941d2610401000a803040c805040b041984c2c1e00e0b0700709041c1401c10f450900ca40705030001d103103052a004024016035a102d0b26150080035514000802c00322041040b6045127250001101d03005c0790000000d030b1603500640f08070840540500313403544261900204503a520a0740d0240d0b92280d400e100c04402c5001d1403840c400c80070300c00c00300002c03400d0000715100111401d540c055880d01c0e944042c84405400d08064003588011410060510007403240e0010f0840700010700b06400d9545401c42030010103008102c50030290000e80c0840351941c08603c1c00c0300181d03200c000c10300890040400422041d0200080c1000c1050741a000762100b66112030224 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 292185080 1250 292183830 292183849
    0x3030403110f0c1e0d1506051f080f0408090915130b0f04020c1f020a1e1e230a02070b030f010b0a030b130501090501120c0e06120d110c0103050403050306 68
    0x1310750140c0f01094103400580744041d20000655a03d0b80490710520341410024566000e50802d44c001200c20580d462150344088490b50181d4481c982981c5901c40f802c01c0e800c280034030010300340c2000f020418043c0c0c0645248640c070078000104c6982048030a0408242c060b503100c1418a900600c2d145d01d524454038268010b041c64560b580c007201c6616982140d04882c0144200c0008841d45d400070311280c586074000b240c030842e1800c0d040745114540c1420701c0140307111910b02940100c410249840e4440d00c0c07141480181d03807401c4008520f05807404030f4040017503600c2000400054419205c0c0040d403400640250b81c414100409002502e81c6440c180c10708a0344811444010965503081d160400c2c6c0e114040500c0301900000d00040e05e44c142070488040300c8040c2c110340c4007600900080d40c0000c840031600300980d800c5504182c0680c54200100b501d8042c1844800f000c0d003d07400d0001480b0381e001c1d00b101c500c2c0d80360300c040791488400351005400301c8000f031341c018000403020030000d040e038181501803 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 292186330 1250 292185080 292185139
    0xc031903150303050c1209010206060d060221090d0c24090212060901050105120d1103090a0b07030e010c0c090b0a08010f02040f0f050a060c08040803030403110f0c 72
    0x20031000c54010a05800c0071454108a0101d0000f040c100c1d04040200b2042810a100d039104034500350341280040e44e590002001940b05040100e05142001a00d070144d400f1345894010512044884030548100640120b0b400e00783d81c8034900e1060307003503407103140841d100f80c0e0061950f4000100300b007164480d010000e000b000407a502d440d20840140c5407844866031802c2d13210050300c4581030008989007580c4040c0d1140f4071a40b080300c1044003180003c51410340300092818140d1300070500d0b0000f40c0c294015000141c0d0b1003c680c0300300080b0300304207038010302e24240303c0d03600c2100b540c003c00010349019a601001502c003040007030051105582d282d002ca6818500141400b5031a95100d0310321f820745812141ca01d4010b500850100b10510300111284003620003850404c1c0c2090811010034407000c3c40780304440412011044403414403048404450241c500041580d580b80340500303003d0030a0b9526083c407142031082c01c004c0f120041c80881c030b40d45841d20040c03e02c4801da0300c4583d00408a00803007075 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 292187580 1250 292186330 292186337
    0x8060108130f080d0b1e220903020102120c0a0504030b060301090b18071a070809060409020a021617060a02030c090a09090b0c0406050f03100b0c0717030c0319 70
    0x1503a8046801c00381c0102c2d80300d11032109283d0700e4400c80d401c0720076580304410442c02950103801c642200e10f48103045107402d860a603101450f4405264048404080a600c0c0050071443c0c9040f000c281981034000344105204180102c006407a1100040f50910440d40d16900203001440184009278056000c0d0390805002000440c10320a0790f1105408800241c81801c0c1c103044002d0880c21042c0300307001d000010403080400c0c0712001d00d101c012566070f1141c0640200310000c0060452480d90343c04050b135015060140d821034807020080406940c840d0b04042d01c428440108100298040c2160050488401418050601500c1d611245006908040c000000503913050200099944456400c0b80052250b0000403403465910b007440d03441f041d405026110109410841400744540107000c49222090b00d02e42107549546e0f00555003aa48000e801c54000208009916110010001550f20688149072081d0003800501c1030310310791700e105d0040d2407030b5190404d100c85241090015a186480c040a04 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 292188830 1250 292187580 292187611
    0x3051b03010303200303070e0306010501031a09130c0915090c050a0e0a050d11040b06030c040e10090617010c020106060f03150906171606080c031305060712180308060108 75
    0x3140c10f0446e0412500c60b0000380314203000c0381003881d04200c1e0900500c401c0c01c2c1003082407c409207107040c0c10114070140340243e9100b0085802109110007500300d66800851410702151580380c040c01a01c0f42c1c0c4494520f007860050702041500140c81465a00d0015807103103403a00d038008800f502c075405009900f5501806101000400384c80f04104101214481d18224940c240c80b1070400040315560581907015030700c14020821001c580c4030849081c0c4454120900056984001c0e00c52a11038681140024500b0640001010281d010f07102c55102001e000038062440f0480f004ca0032915107210f05400560000c3c601c609403801782d8003100d280303041094030046150f00c0303c0421095030215071140300d020181c1104141e0307464060128540404814074948481460b001e0003c00c40000074116500031080000801c040300039610807080742a038048159801450b114070003420f0142c0315444200c9a074205582e481809240345031f030543d8035526445001d00780d1122401120780c0c2000401144c013011404 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 292190080 1250 292188830 292188887
    0x1e061c0c08030c10050a0507050708070f020411030405190312180f110a0f05090601050a0c0506070207140102030f0a0c050f03130501090905060d02150d060806040303051b03010303 79
    0x240001c04003c03403d68000c00701140c0e00000c14044500040480d8401c600d800288030035503500c0021101c582c0e42082455071121100c2c1480f41144518140c02035202c2d1038180074041d141e50603c007035032003203000b00150f8142c48a5031406030341311000b0a00040000d01c001000404944455000d62041504a0080220402503a4529480f010b8514042c4c4408004402c4c2003003a15003151031402402c4402d1030310440c10328042c082503505c1d00c00350804d4103004011a0b513100c0c0c1d0344288000076942c2c0d00403045850340e040c541c10103900c80d1007601a400764034625407000203455000000715407001c105250003924142c01c1040c203c41e0b00e10008000c41e01409003105e0004500010405400361107025001502550318080001d800e034000b5a01040240e800d1908000352540c4076041001656019213000c03c01d20110741c401c50f040d21030325041040e0586041408140080001812031045106c0c0d10b04128580319001c4452500742e5819440c60000801c10043c00041c0c030a2403202c02c0d05070035130415071541400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 292191330 1250 292190080 292190083
    0x1802101704060f09021c110604030f0b070c06090b0702010507020d020606041505030706120c03180605100b04030320070f14060f0f0a121802040b0f090705031e061c0c08 74
    0x56405151310b15031741b2032102e410300c1180c2240c00c0300d4010488195291616560b00c40d0240c48040101800400c41345001410250007a00c41c4081c041d40840d041090b14114601600b81640c00c0c2d03484030040d032801000072445800002c1004140e6107072f800601c201d9036035008100140c01d8400300720814000303c1000090a8800300300c100302400094030f8040f00781800322111030488040c600034101705400c00c00ca0a40080354400e00c0760f41e55030002004211075440010011903000c0301e80c8110710052000070008180360f400101d116291008010340385115005050307103507032001070b030007040188030000e10104030081c000104001c812101402c8141003e05418540400b60003880d01c880740e0b0840000c9403400b40d41e1100f05100f00e16403003c410008141040d003d41110106114024010741ea40c8003160b02d250345031034044441c480d008090f400a854540001000754109444015600b0600360441401c1d143d1246901d200c1d00014012204c49454150f01580208408400350361042d1011f20100304c20381e0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 292192580 1250 292191330 292191349
    0x20316020d151503060b03070302132016060609060815090c031911150a03022107021e010b01020c0607030c050a0c1508150d02010207091802101704060f0902 69
    0x504461050f07189240d03003003440c269003000e40d015210350010502440140d650180c541c070340e04035081e0009854010840c481e508510580240c2e10068000300706983d6000e01c020b0401c441c03501c41e074028040150780d100b000e0305552150107021410b0700100c0d90b0745048891003018990202c10743c0100d070180070210001c281001044c403410904d01644d642580f0920484e02d81c0c0040003030040c1c03180f90f165001d044200b0a0f50184440040425800084400003955402d08008940305010f181d804141410305003c0c1da11114488061b944c10b0b021480000c1c800010710401000303110603000f92100c04c0030301d01084034030740c00024110140070880c0004008a801005100460303072240d00c43c000501c7c101030504103101858031400c4c0c104240502008034000c00e080301108110025a201855015140700507401c3c1046038100c4085c06290031620705403441d114030958401c500030382c0c50b9400350034115411079070b140c0e408062400072049280802c0003d0140d0303121840c3c03c8500c010001d01c0d981c182c0d000520890 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 292193830 1250 292192580 292192601
    0xa031b08030c070209070c03080a0c0c06050109020a08090a080919030501020313020f0d03090b0d02040e07031a090402100c060209060a020303061306030f030c03030b13140106020316020d15 83
    0x302c0400d50904500340624040c1e004000303800d1103c501e484558006040360002010007621903110304100c08102c0c001c40c0140011640408248215a1a03100303810003508800c2d10b0000041c3ca4101140d0602c0e00401c00f003010076008001c0070300d44800c01c003e000c0c000b800c81d0010915410800740c00408113100303101450190420070f491904031003807070040040b41020000740380e01c0b800141d5561030000303030090010400c0302c09407401c640c0c40d4403a000b40f10000b80900e030703c072410304003620082002903503040e400701076194a40c030001007401805c1c41c14881210402c80c1c0003134011034580e50443c006401254540b10880c07150300c000d858914090003040c1c00360061858800540d0011061062600d002c1031408160450840c0400009145480e400b003d00910368025050003180c20440c018140300340c04c40120840d000d048800702d80c0c02140d81c08010a020800c00fa0b01c6685000003080a900c0070081710340541035500001e8660156400b00310300b51002d4402151480010140921006103601540c40d259 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 292195080 1250 292193830 292193851
    0x30201170903041a07121d040b0619211a0f03010609060605090108060306040c03080705070e0c0d051f090209180708010305100e1005131401020a090807080a031b0803 73
    0xe2541b494100c04c098140b00101050099000c030702c01c503030f40c851010055030703801c00c0783c0200f5080300c00d00208000b8841c001c00c5d0720720001010000b5034000d4003e131118a2a040c00e048521025aa01542400303d03841440c008034240303034100d03003043c192422104141f045100280001040760343c4180703141c1111f07055031003080899000300d500c2c6295a0000b900310b0384004243c018101529141d908da42e0404000c1c0001014110b0101d040300500c08200700e6000908550720003000342e400c020010100c9500705483c0402d01a0414000400e00b440300c0d003c001144100c0141900c1460800034a000607401404242c0d0f0071010990280700d0110b1042c42c0c40d4010301d480d4072000465411410703e80c0c00c00c04c0006041c001035082034109a4541c0002500c0100340142c00d00014a5446000300040c0d14443c018000d0709a08500c6400480d2181c107500900c900142c68888908142c0d5400c0d82c0c0e900c8101d03d00c12009190400440b101c0400e003e5420000c3c002003c54409040118a5840705501d40041d20381c070744079 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 292196330 1250 292195080 292195087
    0xa2301090501051314010302010f120606090e0a0c0c11040f2c1b0112090203010504140607090b070b0703140403030606091d060d0c080a080c070609030201170903041a 73
    0x1e41415903001980b41c4d040303182406010302c5440045040c5030107110007410002c110600030501881106007007035810100c5401d000050341c43c00004c1109145014080203840464049520b008a500c18021110100e844098140042d51100040036481a06198015071500550310746c4080070b22951034004606056840d140d564200c213a07000f00c0d00c1440454460b80078002c10324882940c00380c0d000c00701c034007480e1264141c40b941f14240007504001000a40540c2018240402c00181011080c0359040c0c520407540203607250041129200c00070322902103401e80800c28007020684040340c1c190721021504021a9a50340c28451582c1c11000301c1c1d040e000680c0e18074050000a038006902d10003082109010500228500b480c0188031304042c1c002c6200f010070b0702c0c518040105101142c4d00800071141560782042840c01d16030b183d5400080e0341c501c5801400b1020031524013500000c01a42d4041e551400b59441034144035902c41c2002cac14040f800c0c40144400150200c03083c807044034016000450544 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 292197580 1250 292196330 292196339
    0x70806040506100605030c0901030f050703141b07030c110a0816080d092c010b073c0606030503070f050d0306150c06111207020601090506090a2301090501 68
    0x1c00c070703001d450034043c0c0b480c204040104070f80c4081a6038000b0401d03224155281c52120040c3c1c000d1030700010503682036040104200d01c4981543c000c150030b288151004c50030750380d45c200c01c41000d600c868003100507030300510140000c20301c80c5504040d145d1191502c0e030810516440081d18a0b100c6610035840740c3e200800742d4400c0888256040c008107440e00041442000341c440182c1b038100980a1002035941d20380c424403a00310260b4501c880416442058821540c4420801c1c20a0740304071416200d117201d480d440c41c504401100380c184410800c0782840c6c00b4042c055100d280800600d01c00b41c40d4241c41d4000800031460920050140d988501d202c6100c440041c5080d50804031a020740c45c06040c50403000b04011803400102803045032242c5003240359190146402c2006052200d9000c42d0128085198080300d600c406120380070710305540031104943e81e40c1441c00d0a503001124480d400100040c00705c1c41000c0540c0200d00001c0d000c20854503010746142450081840903031045100c5601e5400402 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 292198830 1250 292197580 292197583
    0x120601020d0306030c0b0a031b0306050a060203130303031112010b130503010b0907140408011803090821090d120f11071a091c060905060a0623030f0708060405 70
    0x7182101c0341002c1c000c040c5161682445a001d5103d10003c0c2c56000540b01d04080c840d40c000301e1002e4007404608503032010030380010700400b154020140156046100450054000010341308010425040000d2403400c6580803000b4206262000420301414080d0b003154055000e811400384c0104001503485403c50300513061043c065a01240c0a40d00d8800301000a454540e1866440141410035454540301a8240d11071407249900000c4254030f840041da4450701c1001c192007001c9d00a80d42c92085a841d0291940c4816107105c0c12032800d0003120500c0144e04211000d0a0110130040c600124101a611340c03007020b030b034003407001c100080c1f52001801036903420005083d40c449615000380552410860311940200d142c01d00c0c04018000410f074039405070303200c00409a50a02c0310041e4a088a150718240000c1c2c511090116401d00030346000031812400c5d8422131040324034900c103910843c482100701c1904100d024005542502901c00b010141500401002c0d006006401c02450245800d05005 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 292200080 1250 292198830 292198843
    0x616110609030304021806030a020405090c1905040c0203032203122307080105010c031d120f120306060f1c0230100323160501030f0b0105030a0209010e0612060102 72
    0x80c11b144524000380b10198800103255200e9a81c10f40f00054507490b2450030341d29041030300848a6200c00c0c42864203001000050641003102c005503030501111018140c00e036140e003c205c0c0c1003240650070420400c0300320507041c0054456030081c00c02000c50722003c1017480a07a804900c4101040485a0611180c25443c00a10f07901c00321030300d04040d01e9410000000c21071000c140c0050308106080c203081ca46e010041040410f0b00000800c1d40d04141002038249890300f0360310b6010b070b41a00a40d540e00011080701000c41c0c0c850b4600500c3e1514104c0c81e40b008034025000980d000c40711000070302ea80a0251001c0c8018913110146807030140f642c2c4000c031030401e80c03890140400c9607603000350014054200710882d985030650f54042c1030010060100c1d551119a0fa201a920054920030110b030800302c0003100ca9000e083d02c07070a80e01171080015261040c4151103007449a980018810400900c900b01d581d4042e0190b8101498074800c642c1b11600042d040740c209030600c80703005200005102c0f0729a0100002c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 292201330 1250 292200080 292200109
    0x1c0603120c02150d110426070f03060903050d0c030204051507020f060a050c030a050301170c09040b060d080f0d0c090819080d0e010506130e061611060903030402 71
    0x4a611200182e01203084428080b454049201c000b040311100608150489403000200390400f50319146c0d034400f000c6005102d040c040d41c06540f411118052490040340304400c0d102d040c9580c8101c5485d60341c940d0003d003181d0b80d0550801005014900703810b043d0b405604010310792a83c000d41c0f218204800c009404c10204d20655060008111003001600e5981680001483c202c56240e01d074144840140c070244980083c49603940000030301064483d401c84c0c00f950680d14855035903c00d003081c2c5000d0a99030703d920004960301180c040c00140004800414550b44410302421060000300140e81c0c1605070340108241529940d03010441d07001c00c0c1c1a034816401d890fa4a49480f00d1090f103081a4541c40700c80c20303403412101580b0745e00048103204400040381c000428a081c200a0f600360907041500070081500d0705031140344031100c03103003107000d5500a21840030941c82c0034224070b807110980c41000d00007000c50f0105000d40900703280d001c2002407204620941403078016558902d8580b04105400020708030307 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 292202580 1250 292201330 292201337
    0x12040b06030d0f0206010b0a1803080d0605090105030a110f180a0b0105070c030605072105040317070f2007170105060604150818010507020d0e060304030e151c060312 73
    0x196100f0a50300245060444540500060781d45110300011100c092490108603428103100e480001041220402000d4041060707400b040b07401c0c0c03118100300b4480b4080c40381035810b0b0312225118000c02c0200c1c0c07012019800c0240802d803014011000308104241c010f40b01c00100381c50004000800840c0d000b040c0501d203003407802600d8a0380c0b0350307640b2012546501014017065690350001e00403600070349806413241004441d4003000c940012802000d000111401c5000407403101042072204528008240110305507241d01121074001c05c41102c4250341e40302001b649220240180440480500c04000074043c180e02c140c003e9040c0e001068299070000d40414050101080108101c5260a000700c004101500d825080c5441e0601508542031130840744032210352810051001194001072100401001d5032200c041c0d050b1400104021030104407030160125220303c0d02c2d25160314000788480e0704103201d01045414000720f21300c510340e446810a04841301c5669074200780284402e503000392070030030142d25 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 292203830 1250 292202580 292202597
    0x60f030b1206010e0403090803040b19092103050f03040524010b190234061d040c0c210801270b0f03010207061406030601270212040b06030d 62
    0x100480d902d0324144a944071068811004c034040602c03074101c1300000c021340000c07a0748464848030311400c260311000b140c540c021042e01032038a0a6002c2e259030070848031f5501d140010151807005480f0700301a0b0340001c6003040810011001000d1004001d5801a8041c0004060390318504510120644c0703c22803705980c0e1501c401017110064000483c0e680980c5192449100000e00c0400e80c90300b10164040c3d1112491021101200c038040c00c0c403240750400d45045c03890044e940e64025601c0e00050050200b40780c0c00e82200445608064000b54045e003050315102d0035443d86603ca8a0900b06d25041c0d480b40019119030040c1c040c0d61190116000d080410350b803204000010a141c20440f01c0c0c9078040a44949910300c920859680c0205104001006002036603205528074001004046401501050310a44000704107181030015a050503210f0301d0880c51610142ca080714202c0702b0200b800e01801d0b1340c00f0001440c1012007800b03018042c51003441442540c5c1005410507041111140c1c01c0403c11103a00e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 292205080 1250 292203830 292203859
    0x4140c06040e0a20120a110f04170a080408010c021005061f021f020306031b06030712090f150509190f0c0801020a0c1403030408041e03020406060f030b 67
    0x2c0c58a5007002c0f003000c00240c10800360304610100107105564840d03601c8042450030300c422494a4107031286c00079040c100441519a0b180ea20240910305000701212018071081c07115864000c0702d4518070f46403c04036400d21410303a4400c0b0156105800c51300e010394503680c81c40c070b001d038040141e4101503c4a800500c240d2030060041040011048142e02e103640c0d011407070300c410600070f0190100e240300c200a10600501e280d210f603c080e41c000d80e2914080d1041502c4010b540b540d01e80360000035000100500d24584900034100c8940c040c155550500c82e98070340800001078041213003107140c28480c68402c900d101c0892185411110b00038a2107402e50440660b12200041d01c410501c0c190740d00104a0303240c102141440801c0030f90503040441d5940c070019040d120690814034119201d0310842d128280204450115902c0b070005890040144406100a215010400c40b0200424245c042012406556900090140c42440c0c1c00a0081100c1260342d02903140e160141c140450015507541404094a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 292206330 1250 292205080 292205099
    0x50f01051911312408010b03040812070e0d151a1003091401090c1a0a020c040f0b040609050a0f0902060301090b012705092203030b0303090904140c0604 67
    0x424200d40316000608029583c01c0c4460581400303010f5140801540c503100c00b0840080c5882507650b8804180902e000180c0e6030300306000c4a100e0b59010070f040341011010f0808561000014141906014110100000540740c8a91184106000715004180031150703150302d4044603194030083c803002c1d42e81e0f0461551038a51901d61b4140c5820ba10700001d441c00c0c20f08141034100c8200800310050f5003405d0424050180f002940e8003501e03200e20350341d82100801c000203d581d100e00318110300560002c0503005100d180541c8a0410315120355400302e030020752800003408403850b94015415840ea90424050422050711800e950f0301d80504080004028940000741c990005120703d0603c03a480d007070351300100e9101d8840d0301d89040110b40141e0064020540c08090030801d03000d10381c040c1001d5400280c1c80d444d024000d251042c2404d1900041c0341064070114090251070f02115054482040082090f880d01044240b195004045030080005800756103820650040e048510a0406200500c08501c0c03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 292207580 1250 292206330 292206367
    0x3120601020303130b07030906050406231603091a180d0c080d0902010311040803070b06040612020d020102010e0d0809010b090105010f0e030a080a0c020301051f030f050f01051911 79
    0x1c000345c0ca03102030385c0c1d0b022045010b8840400010500e609007801d2104202e102c2e001706102c00c0541d031520604075404a03440c07600b184101c13407110000490201d0100301d18041e0b44456882d60090205008981d29001d45508041381941d40f8400300c120341000300c5604000780300c0e683c3c048a551a000015180a844181c80c602500b642420b801c1c0e612034081d002c584c000d81c82040034203200580305880d503035956046622078211130826102d81c070b003840004030742e131400748103000c2924180c06182d0041d8146400380400304068000c128199035a40040310f0303c81c282013100c69900301007552040903901e070040c01103094074072410606005103200700040c07099a0700846002201d00e40e500e080a8208440c0c03000030320303100c1203140191020800043d48901a40c0c0710501101c1d0b9802580203020984810034982980421020281c102c020040010b00010340c3c40510f10075018002d400f103400000312840c100e82142d2041d921002541b100e400c000c06640303030324010702c0c800b000d110418506000c003140154371f00700f1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 292208830 1250 292207580 292207583
    0x60b03070602100e0307050d110c0603060a230901090b0a17060609090a08120103260f0c010603021207180e03040b0a03020d1505040e011b08090a140312060102030313 73
    0x1d881e000c81301600b042c10801d03105265000030032112445004a00a0700044401c0f4485646006507100000503051910807a402154007410000c07440d8079020004091101003440c000c5191000d070100a4581d9415021601030014181c0010310100e1b0f030800c001302c14445902c21224070305904000c0c2c1403090040f50060740003200f600d07040303095601d03141d41d1401d01c2c0550900030203505000c120000003081c08844c2ca4140c901c5040420034640714040c3c450b0000456441d08540c4020130819181e901c600034000e004a0030a210000c1074107a26940050804540c040081000b6400302104018002068400803d540400a030070458844071035002503c911990003520492b500000b050944288241c3c1110702e494141102045545802c91000d01060401e10806100d141807205d80c0c2c949000600c5070300b1450030024200c944100030314000366880c190061079a507040c0100d50528002c9840e8146004001e00640d0240d541c42c1c000c01100c211883e0050710140c11980140100070702001811240507045 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 292210080 1250 292208830 292208863
    0x3120a0614030c0603061c06020706060905011409010b090409080d0506010e1e10052701120c090e061804030206040b01140d15021e040e01150512060f0d050307060b03070602 76
    0x1c00c0b11042c410b0304c7c46200302c0040200748000fa003501805801e0b8000d42c2981d083c8402840a40da86405c007416580420503041ea120a100d001005180c00040051003100343c0500045a099895100c4990303136080a802d1310840f5840c0d44c10000590303804800111101001c41d201c020044d51a01b034190740e0407000b024107014038820304004c4002402141030700c88041811a0701d0141c0f40392401c02c0e2040d000d900c1d9050380419504045180d03029418044c1c00c1450396296904811300d0300d44000001c1e024400303403146420920f040b20040c3d40708100c000d070340e110300d000303400070502420507150080022205902090707d090040307450307100c83e86d50b07100d0030111607410080d1400002c11800175080244240048103051100040021302108000ba014000700c03a60202d0b20985a81c1e075a110022202404800c00006441040809100b140080509400007005071a0142908417800030418a1140d4101612141d0000c200f0800f0402c1d81d00400140103001c1c1d02409071540b6164000c0d54802d450181d0a031701 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 292211330 1250 292210080 292210099
    0x120b0f04060e160512010b0309100f150b1e160614010303090b0403020609090421090501120209030606060a020c03190b07020703020631060503090712020102100c0203120a0614030c060306 82
    0x14100700400c1130b0400c0c002002f04403905001048100800f910010944c005000c1c0900250303a03260b0600782c038402c0345410701500440c0c00e415407691050b40b0400c40420460306106000012810740e10a00c80402403034081a0344c154103500b805402098690304c0460641010442800142c8440094400c00c07030b403e03074680140d51100e2030099040c084510340c2481608505082798110f0703501502d01c0084031000c0c1c13643c50018081441400a0344164074040e078050b8028400309815040c0240100b105400603c15100041c0414002038203040c22079040740313840240605940d013403107001200181c001143c0d0006110f81072031503000c074450b8002c08003480b41c000840310540300520030b1540c0607410f29810550070403100d5111350700500350340c009031020006032282100205100b414112140b19098050b00102030640301d628820024081050383c41045000a1080300c4180403601d0000b80200002c0314042012070070720450441810404d2210792003540b15641142454a88400310b03a040305003074a21208 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 292212580 1250 292211330 292211341
    0xb04030809063601081302010e06070c0b0415021914030904020301090f0506150904112701020c0307030201080a05040201110604030804060b10120b0f04060e160512010b03 75
    0x241c0f40241e0503c15280c03c041c002690b89070034000c125220111415841124010b240001120f02040854143c00c02c8900040203034007541c0104039a03e28940c4c0180020f180030016a070780312140000d54010011030001007014091540000102c804d40c2c001c40c80104050f80000c2d0308003900001c0300d907000e040544070101c0700074184024002c032480c003000904107542c0da580d02c5100030011f007014625900c080380b41101003030582c5002c0950440600140da01309007004c0f440010072005081c64004001d06980800c2507a001421640540318540c400c41c00010300d10807a103002908000740220002d11a4020142c01c3c0700507a00144807540003c0b0341d560008403030f078417880182d0740d00380102120101440f480c3e00304410150f120003294800c600c140c0080c03100d1001035050000304010740d1035942c04142103900322000d144d180d5000c0c1d000390310010242c840200c45030000ca011543d5a0300010440e101031020071507415040071103101104200d250041c0703004040c000e0411180d806024060810030001702041 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 292213830 1250 292212580 292212589
    0x180e0c0103150b070b0402240a030506010504030b040f030f02060106050d180519050d020a03170603070b030a0608210702120c060f0d051501092105030a0f020f070b04030809 76
    0x1c00350044251003580c44c40303142440190a8011a0100d100d00510072010641064100d1140700522084a64605150500c50249c001d0040100900e0420000380000004500701101d0107020302d009403020b40faa031215043c0148442403602c070480c2554030440042160a501004449103550b40103000548500c864405201c2e180186401400c107109150b640103024aa104540c0b02042c8107000701d9603010000031050707840300d40c0003002030085400460b07075041d454291001c5680c814001030540c0c0d038007505c0d10304182e03583d04195040040316a035a90140114081000042c6814069510703501151440301c0201c040361082e884c009016150015000d0607164082001940c07030480180070f2502c801100f0f401203000d421013079100583c00c2c206000f0558400b030b03880f0120301035001a0349004109080030174010000b008141c54400c5040f160800302c3c040b5000b44090148002c40e540d80c400d0020524800901d011351101340c60040750001142001030103802c1040b01c003107a80c015403042d19050b1030030005 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 292215080 1250 292213830 292213871
    0x3070611070e07020f07060f0503130f0c0e07031d0c150f1903180b010e190216051c05190e06070605011a090f0f1504060801180e0c0103 60
    0xa80c02c00841d5050145154003c80c031002c01102000c03c989140d9520881218441c02d2501e14001042c0104042074000700654091900c0038081c40c01080742005e256182c103070244690f80285041e035000c10910090300e505001c0d00b0060401520350311b07054074018080a480759140328400d48105124268480e01c80070316403d8425400925800c55150303207002448540340a00841400000791400461140207007251080a039070f10342060110b1216802c0183c84880403501421140404005c411448a051850b000901003c816062000b0340a580352031301910b8980407043c0c4c0107203001210039036113109070b120341a80c031035000041da181241c603901e1009542c442901341c52a6004280022034205000c21604a18100d0b040c980c49401c25000707204901320203018040801d42d0211007140c55081d81d1408109100170007074010841088541e00c079800d400c00358819840704002c2042c0d0001001141800c2c503100b1701200000e07005006000800f01e4103503e42c05c82c0302007981415a00c1924181d038000c0d42812 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 292216330 1250 292215080 292215089
    0x1021203091e0304060201110412030e060415030b03100204120605060a0e131104020c030901030b0f0a080616050f07061508010c02340303050d0e100204180b0307061107 74
    0xd14202d0184000243d16a030003805080e000d0760903d4044c0366901010002c80301140e00c4514010000180c6590403194040c0b480c014a5110905110100d03140c400d6100315541e0326082d40700000c154805805041c1814040c014201e40340740705000400a070303800385180603403880c0d10100014080da0307824002040d21180e41c104c1c8110204110400c840d0680e28841c00030010b00036503080d02d07000e19541c1000180c1c4075201d08550241c1041c84104100c0d4040d8111110344207005004000c502d58560120314110000c2d444020303950b0200c0180300c0343d1541100340b02446512807a11078508102040d5205083c4074031134005220075514000d042a40b902e40340c480c40503110460091000c4803410200039030320550b0b1420112a100540901c1c07040c4044038903e80c10400b04840b03070390400c604d1620300361085c7c1c120b450903061403503c45002d004100401d00007940c0710310f01c2d040012b84a904120114550441c844400e1501c0c80c540b03003010190b0f80e40010103004403011841c1c440c08904880302c3c01070074541c80b07a22 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 292217580 1250 292216330 292216363
    0x1202040e0117010b030a02011e090915031a0609040807060e0a060c03150f03170f13030b0c0c060f1e0f04050d080c04060e060f120a06140102120309 65
    0x21880c1c0400b6048070900982c680000c1c010390244204140e119420014001e010503c01c1c000d8108505c400b0308944401d00041c14105407480e80c4203c07001c252501c5803181112211207150500400161080c0c1130780400c02ca0803000c1c00b61420340c0100b501450b019001402c44000030910104002568015560912010b015502c40c0c0c501e500d0104085c1243d4604d00f40820304080c240103070f0520550a260441e003070300c24208101403a58885003903000c0c1c0301c064910640c108103e4a00140b00440045c00032640303000801a80525508003180c40420140a6a8400d8030800c0f500410a80000d15150440030b031041c07001c590b44a0b440c18075841b45500d41d05816000b010820411004d14400b401031080b4050750941d45442e20151007120114400c40d10281c0903541404240704082c45521302c0a482c2e02c02515503460b1030315050321000d00741c120b003a003000401c03850300402c918100680542c000a129030369503002e0404ea4003001079140d556010448a044070080000f94070018100174010740d0351000e48 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 292218830 1250 292217580 292217609
    0xc0f1c090b010f0b12040609030e0d0b1b0301030503120619120209010b090901120206090618040f02090a05040906090b18010c0507020906060703090b04290405030d120204 75
    0x9000c1d8030300c007401d2140c1d00c904a240600000c2e404003260440f584204079042c40c0b030312a0b8544e52042c2c01081440c1095040190485103407506441d01c5520741082070240c3c0c3c021030503250022208449080c3d047c001442c2d013405000420025100005030b84040812403544c03022640c1700740218010244811040070324554929001540d8115000ca00c10202d0090700d0300c0c0c03a0b41ea00c5507000e12851040c0356003540c001d1680c0d001000704001c0da01920315618030040a003490550a103000409540040781c800b0800d040340f0542290600d801d1140010100a02c0419802c1440302c0c40001c0d021901340c400c042c0507613200c21038032081002c40d07409140d915504c00702c01101da06100004441c1d64000442c0ca506941c640106641002e004400b510340072035000b081c50105544800910000c0e410009080b024401543c01c003007000020711020f00301070511941e0060004544502000043c01540c0f903010300b0040400c414081c644000c14050031100a41c1815014951185000b40c000e12850f8801c010700700161 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 292220080 1250 292218830 292218833
    0x7030c052707090807050607021f02011e06050111070f14120d030c0801060801030f11131406181005010305060a0b030a1406041b1206090603080912060c0f1c09 70
    0x4142042504c01100440d24071544410510006200d5040c010794070581d280a008a00f1114803407050405a00748000b10300041d9030000440204002c81704a030450391103034420310035568004003014a0090b880d0060400e0b524101701101604000e0003510510220941004850344038890740600346005c048c2101d90300e0713040c032400030010984080400001a405000040e107a4462540e160507603800c1170058001600f6544c880003049903044c80c85410080030b0124600c2040d40744942a540c806031030903500546400f100308035203103801da01b00210395020802480000c0d200714082da82030b2182805c0002d907586402c000503003e40f0301907101211180c0c00104100008265800050382204030341d890102c2ea807203010420065904402402140515007040602128810800d41161040424001035042d45a03052030083e10500e4000b40d4000400081600341070401040303040c1c5550a03040030700058140010b9208030782c8100c1850030101540810610050740d020300c0798545818407080200b0006105 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 292221330 1250 292220080 292220087
    0x301030b10050a06050f070218190f02071a34030609090503030604111309022205030a080c0304170a0606050907120207060f0c05070606050307030c052707 68
    0x4a07004020741025141c00510783c01c0054655007581c1c11603c40380d0611810805201080e04151000d0341d018000c621366609042d17626410f0350161480710040001000480b6142003600c0401182580d41841040310501040508400d06003190f100b807000ea03511b1312401071040d656000f070900303802c11613800c651505200318042003000c010101928107222032a81c80c0459012500301090140c40da13041000014860b10f415031050044080c9080c03c02c2c01d000180c44003082e001c60036088120810303070002c0c0410b0300461107003050000040d160412801c050500010984401c12000000c1c02d0300000b2404004100d014000e4501401030855001f00c65407005c030b0701680e40d00303071400241d43c20351400501107820b05120341c4061041113145c0b070ba60301250002624070001e6000c11015268542d980b9050615510180505001d030082c035502c480e100c1006050007001c40d68070f136022500c01d45c4065410030000d203600307a034141210b500301c503460311040541c6100e0260344080200380e0b0410f001c00c4108599980c2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 292222580 1250 292221330 292221353
    0x10020f07050615010c060506120102040803040503070b0c0705010c1109070f110d0806061b06010e0601080f13020d020402071406070329120709090308060907030c080601180803030103 80
    0x1182101c0c2c00341c89111450805400886000c3c1c0081c030100c91641c0402d54a4215940010014007109100707552400c02e40c2c00c9802680002100e604002001c2107145130410110300a4940340c1e03481441c04500b00c100d15901c02e400c3c4101030510040071204001c0c0150b81e000d80058000281c0321781a1845c0120009000415901507000450000c0000f600d042c40300240d5100f02510689694185844500402506402000014041881700c0040203070842050024500034002d1100b034500c0b0b41001d00c009061248024521000c4105980030410100d54100251412a1701690f002843d890b0700e001040191103007400c0074000f1201891410700c03100d00090f440780715031a5560100300c10000c00c41c0543c0043d0380210b810b144901c40b914001600d181110007210b411240310200c891655444041d00f0940307000d070209402154001c02001b65601b04000e03038030380c0500985001c121100b180300015103031039005030120b41003101c0700c0e2074020110700e410390003c06001810200c0b07807a50380d80d00d419612100c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 292223830 1250 292222580 292222583
    0xd0c090c030f02030601020d0e030c0607051e0a050a020409030c0204020c0607030b0a0f0314070312030c03060902040b16052a1003050609010e1504020c0309030c100e090910020f07 79
    0x240703400010030b819001403003901e0203000164064051003000400464110f58046a0160705000302c250340c05507551070300c000b000c5180c07042019007003807540ca0140e081108c030958041101a086a00c5403000201c0c04200318000c160304a500003541030960030121030071003120030001d40080c8002015201d15500141d451300c1a60155401d00000540d1010701a050255208180b2120608101400020001c802e694001c03000d0310100c3c1c606584c3e13a05c440824104d5800d0017000b00c2e585034900640142e250240c0d001404a888065180501d00600e0200e14410320b502e070b0141280343c0002004010090103103802c05070788500c80020001c802d011800102c1c0416034581e10071510070444121450003802518820207004014414980c6002c540b1550350ba0300500b06074411802181603c8660349034400351030902039240c011621100e454040c0345c644010321110611446007044124143c40d8024403050a0002c251000f014544901d500e5514269036a02d8180480c1d0020a0b40e10040020701c003e4481346 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 292225080 1250 292223830 292223837
    0x333040204030f021e1e0f0306010e070e0d0c050d110325120b190207020910061814040207020d081605060c1207110f060103030305010f051c0b060d0c090c 68
    0x1074204840f030b20542802c1445e00e410408584205402c505c40c244420b203403840181c84802d40b03c03203542c002800c207802600f020860b83c548000b840101e0394808608100c00300c080da48480d00100c107844080d00c8102c10b1058503c00c030004a140c4c01080090726541c0080240581202c0c440250703014481180045200c0702c02d0a030000c1e03031700041c02d0304d400c000320354006821140520594803020000d1244203103481e215404203070200001c20040e2980c2640700c1c4155403802041c01040d0808030001d250321031100e00703035001d90901e071070078851251207a0304084d00807030480300140d441c0c900c1c2c03020442719101c0c20380140c010344011513071001d081055950305816603c030314291140c40e91a0111319000b40550010001d0250340100010b0405000f65440d00c91014071108032544040c01845083c5401d41c26041100065202d0004200442c5041000c40c05802e00301c441ca0079001c504030040a01c1452040c003d440706640c01d0100ea03850b01d9110143c030880360801024032045880d174a060001d0030135083d400300017 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 292226330 1250 292225080 292225099
    0x319030606021009020f04021b060408091e010e0918120301210803060405040c0e1807060c0b0606130513140a020301060e100504090c020c030d050333040204030f02 72
    0x510781d080c400d00612581c02001a184906c0400c2400000d401085510001906202030400c1904080244510640c0700c0d401085e503035000706080c4007580c0d200101d00941a100d0a004e603010741e80014920000e08020303160304100350784888031924a12840407189a00303001705100000c605a80318000c50596103500854501540640d142e92048500d100c03000c4c020440c1440030424a00d45a04a581c000d405594000001c54440c01034a1002505407111305800180c4403004904c52000c4c0501c46c01441d135410006880c2c9219158400c81c1c10b402000c1601c202c1e00040c0045c10f600001500801400028000c0300240d0022180280140100f0304400c0001d4044400610000000d008880c1610030690724064211040d005000c0d9040d1f80045001c2409018400811400710510440c80c178015654010064228004103050801c2601d0b070003002044020003c1200600b00c5240440b404403078a01400701c4000c4131100440560000b02400386e10900005000050241d1150350700c01c55070007125032610 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 292227580 1250 292226330 292226353
    0xa08072105102c06030a08040621020a0c0803180114010303080f10141305070c0209060d080919080d080f07020a05100c020312100608070305040c1403031903060602 72
    0x7151000c140350a0b0410340411180c04150800c90f841503004030000d022142c1d503140079610403075103030800d400403400242c1d0b009502060304111101000c0d04081442e0440c034281d400500200800c200c884050b14400d0000082000850b826551a1489049000070007a05505210001c10014207210540008042c00046683c0c1c0d0002007406001d41d031118104a00c2c24504220840150840b10310103904c001105405140760801c0d00070701d80300c0d84c0b90359100076511a031803042114110000d000540941100780c05900010030744800c607164070764110707041c5145040a82140500c100c0700d400c0889035001e844600264160402d4a2034002c6a09141c0a800d81d61000802c03646e278425098043c01991003080d50204110a50340180c0f5240750f144196071400d01801c0684110030b0081d1000882c40c0c0d24a6401c121242d0312007a07150700f181c0340e07103028401420503441d0a0310036801405407800c1c0441c11540c406c190ba50030400c46003003c0039601c0e015041383d00710002070000c1007039200e001c000d4060300c1c2c1e90a4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 292228830 1250 292227580 292227599
    0x21302030f070f200610080f030a05030907170105100501081314030f03100e010501140306092707150912060b04110c070501020d140a0807210510 64
    0x244500901480346007180d03103200044030720801c0c0f50208428011907410203100c181141c0c02c2881818000d800400c00d6007041108401080d206034006010b98200d55041503024001204903041c0020501c0c00c543c9135100d03030101c503042980d190f00c000d22240180c0d80504c803005043d00601d202e40485070320713140155605c0006640c6103a0845084000315040b59200d0009210b0840754000504203c0449049c614500e00e00190ba920640c0c40a81c141c0d501c0c0c40800000c000f202103103015080030b10b002030083e207548150f142e0764040540250310800d40b080000300d4016071800e50290032050f5800c1c24000030b03200000306448881c00d010f81e595044901c40b2455003a0b0040400c18121604624418100d203450303103070f41006014000c883d85e801502c0b1101e14000300403d0002d80000c101d00c0700948079581c0303410300181c684801c0d6601c0d1304c18801a4140c0c1c1c2c000c1c480820a40306c40100d181040e15140e43c560794100c41c0c010400300e001e84030706050f0002c500d02c1a07030f070b81c000352054800e510b00d08200c40c2c5400004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 292230080 1250 292228830 292228837
    0xf231b0130050c09090604052d010314121c020706050103140c01020c0f060c07120b10060e010c030806040b0603160909020c0d1b020409060b0f1e041805010c03020403021302 76
    0xd41c1042c43e00006c0b500c1401c2030392190790702550656005034a041925019080105115480e0710311050b001c1c0107000f8443d039415400c160b5070700c0c90001c0018100001680c502401503030200c0300c40300010b80c201e15014103140c04452425074000800c010a40e12407401c014184800c4c0703c0e0842c1d9105401e1407005075400041d0f1030010280081541c10031661181c10001c15602c64608105170340030340200007858080050b02c12030058414551140d0514103110101d10b01035061f407001040051007228a0303202e90700701d003110400b541c1500c1d0030480c41d92248003007800b800200c10030b02e4010f100001000140061041107405075401d87e130300d440c11b40d9541c480010070303070141480040ca59001310301d080180d44c0c01203200700318900480c000d46050211980002d8100c80b02d030603003600c1d000d07101e500c00201880e011042849240c0121285071252980700011255203084200b014051607560b40850b9a6491150401c40015440350081c043c6801c00c01008019410512040f4000c0d000703540c041000c81418000d4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 292231330 1250 292230080 292230097
    0x408010b010206060307230d12020d0c0f0201050d14040804050f0a0506090904032303100e04150b0103021e0a08010506030c0f0a0e0d0f231b0130050c 66
    0x14601c40741000091000ca4080c1111a0921022601480704039202c000c48400c00b5802780044038044058844040e0500001c0c4044008014005600c8000120b444004c40d051540a1070481d0701e503003880d18108000c200b00c0960101c1500407104000800086800400c1610030507a20300d40111910343c10300030480158020541d11002c01e1142d001c0506041100c9a1703c5030003880e102c15000b003400c40ca441c14284030340d0209000403002040101006464120700d000342800f005000f0b03d464a5261120f10740c881c03610b101029501c40c0d0030031240e60b2003901501c4401e034920203100e41884081d82ca03480c1c81d5001480c035201107203c810001034649452810360744101002c4d2091840c2a18400a12105074801074284c014400d40c007042ca0415184c08000c40c0340c8a10a0911400d50301180c14200a40c0c107411f00c0300b800d0f2a030030940e00c040c8820045050203107886d00303038140c554080c81400181d0307590707401840560300070501d40040e02d0521501c2811010f5246080020007194542c0005104944500ca90 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 292232580 1250 292231330 292231333
    0x30f120e090f091002041a0a030b0a0603020d0b0d020334060908060a02070f030f02100e1e010e0c040e1002030702060712020412020907090b0c0a0302061312260c0408010b0102060603 80
    0x1810600e0312900007086d800342305140005004100c0e40006600d080140c02000000c0d078081400441d01c1507038481d80400c9001107814910b5000c007540000d699840817841030300f4001070300c441c10086524030402d01640e000641c2407840140d440707690041468043d4844c001091040d400070a401c40f40b81d1089641254010180c40fa581030b26440c00c0c2c50320300d02800072404600c01e90010014140c114807030b00e88144c0c01d0201038441c8403907200314404212070078403408425915000c0c0d107190710700c000103511b0078441c82a600480c001c504401d62038181200d00b8001c50070a0f00000820070000e6021a0651290301d16442d0301000c04200e2049070f04038051402140401c0d22a00c000b100989880c0c54050303403117040b900d025002d06489403c061000c4e0000e03c010703043c0364044d030782490415805001440d8002000a0081d03454146620390307400d041504003001042c0310140c02c0e062250448000c0340c0c00c2d224031ba100b03803540381c0c2490b01f00381599078001c2c070a0603890f501c0c04d201c21304136620100f40c050246030001c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 292233830 1250 292232580 292232609
    0x180303180503040b0a090509010b07021e010806120304030f08090a08070b03040321060608090c09040209010e1f03050c100c12120e010501030c051504030f120e090f09100204 76
    0xb030900d040780d4010b006038030a0101c6d05d034000a480d83c907044018060400e800483e515181c10f441884520f0089190840a15115000c0001c80340da10649290b40300504a915044190380c6043c002c0c114444c0d50030103080900b903900210284480ba500030801c1800c143c82130b105c070703603601d54105440d25002c0c0200c0c040541c0820100c1c010038420660903041c6030062258019110440e203050046400350303072002000c200584104034810900340000d01d9628070558041040f40361550004000b140140283c46140a4070808580316103400421011200100c0c01941c10b2144c03641000c1350b03541440344074103105205981003807003031910410450880e19448410a5803000c400042515030420091058003504d5850201c8240c00c90700740101402035008000700090241050107001801e51000c081f0004048100b000300001102010342d80c41d6280c01044000c0d45a60180d0b0848507030200c40703211503220041c001408101b20715805c2c0035029501d00000c40d00040881c44158041c0e0041d442405410605036 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 292235080 1250 292233830 292233839
    0x12050307060f0e0303070207061d0a0b1303080d0b100e0306131403070803100803040b070f0c12060b031b010e060903031207020a03030f0b0f06090a080118030318050304 74
    0x60300001d4044807003200204030f04030124a90383c41c6400859018005900c140340402815030440c1c1d003103100011102c1ca801150000740042500c0040b039200301500b10400045440309003405052400107950300c5652182d40368815134402001e1700404030028480c80071007010f01c0b18540201410341e61000050040d100c40e5070303640036807170381108200710a4030040d000000124000106100400c4220701c103144030303912400c141035140340007005500051100d80c010001803010b180c0e400c081c0c580c41c075030000e00034414500301c0c5880002c2010503488102103903400d9858204014a91f0441c181014054048624080d480c44804403000d0590b04206e0100e2052014400030b818808014101620040d0440c1d180c980d014069040314401202d4050041e080300b11070208241e81800303984103030b5103e0403041c48100c480c0400205910585000349104000025091129843c1c4049220081807803030001c01900f6002042e41c3d042e50008d03001100003d28280c014940d40f2480400c10004a030850001c600b01800e0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 292236330 1250 292235080 292235093
    0x9031403060103091202010c08060a030305120c090307120510060506190309140607020d1d10030f0e010f0b0604150f020a050d0906030609020922090215070b0112050307 74
    0x10748000d0400d0389606a0402084840568685010841e4000a101740342030000030103416000d400184103468450041010990020030b441c0c0d010000ea4820070140c1752070384003500500c5242c41c165014059640d0008107415002130035020355015506440c03da00100d811b10089034810b02800ba0f0014041c400d03c91203110060004420100314200010841000d0f1100700039103081a10302c62440d4410010400402e40c1800300144900c55070402054041c070007114500c402c29408002801518002c0c11090400d05c660485100030b4000d240c20443c040d21140500e0181450380c1440210303d0a1003070302d4115041901c200c0d011503c0080c1d80243e0070200c80c1048130b00c84e41007181c1604510071031608101092042c4151103445240d07031214519146000390240945045a000c02035052040c801134109840b114000a90000150341c011401c0e003038511341400a1046e9000a5009084c5422401c02092000010b0034000c0c02482c0341041a0b0b41c3d900f0079801004095001003d9401c10310210002806 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 292237580 1250 292236330 292236337
    0x70201140327100b090f01120807120f0f020f06010302040906091502090f0a060206040209090f100204031518060908040308030a0b0405100b09120f030a09090c0201090314 75
    0x248540710110300014140e985031814071410b00e09415084402c1c90710750302c5454481e183c25030a0a641107142c1e46411850700f0004041449020f0640c080c04900f0742c100702400d411190341540c4440c02d400300c0c01c5010001054a1100d15110003c60110f860810038a40001707655807141240d0030040403143c0c256402c4c00054180039504541c001d8454100e00e000490b070305004860f60030390140050f107035024001000940181d0400050094002a030184100d590106081754001c1e015120561280c6078401c0b0146483e180c190b4507070090140c10718840c0c0000e642d40003801124060303002c602c0c0e4588500c10390012103030701401d6035001c241c260016000155041d00508003043c00703a182c00f0308040d50b91700d80030320950086032040c0800b5980c04601b080362400707104d640e4209034880212000d0500f440d070640320a1042024441c030681c22406a9075031803c0c00c2041950088803002030341c1c0c540000000c007812103011402490459400d06040700c006501c14481c50b504950155580014204003020007400c40d030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 292238830 1250 292237580 292237591
    0xf1609081f020c0d021c031503020607020d12090e1e0f13080409050f0f070e04110409060b0a020607020303100501270b130b090d0803090f06040602030403030f020702011403 76
    0x2e400307200c07184810b03000740444600204207801805c0070801c03205d032000346160740c600d00809052502800303c5c0e800b8a01858582540c0d4141c803004d643d06401d0001641c40c100e905c0d80207090502400d01d24010340c1d0710101329401c5400300d24400703001c1c2e2070b40007840703a0700f60002883c01c60008030180040c2c614611001c2c3d072a000f04010100781481c00c83c1e9103c4548540c004c0d00306000e100d842d9010302c204000064000c07a400508020490207070b00b400b50004044403103040b0174a02c610b07100c4000c540069051000c5030020505003204100e4036640305203a28041c0c0040d07c115000d4054040001d030a18004022603100b940700030107030100c2c1d41c2000300549400c90312100800401c28011080c080c004075400005020b0411400c440340c503001c401d44800303414422a0420341001e6000c0c4120b0707000340c4131109005900340d44480765540340e5441e900140d10b090840000d0300400c2c81940709100500105034021800f442c001d0b42c0a12006000b81c40980581c03003100402070000301c03509011104401600050341d00729 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 292240080 1250 292238830 292238893
    0x60108060d050106081c02030a17060109050a030506220f0b0406110a021b0109060e040207050f1203040201030c0f020606010f020705060f120f0402150c010609050f160908 75
    0x4820340b00c01c0d003150300304d40181c1d00b10303030002c4102d03038600d9442c0c03044069210311032000307529025180100910360030410600d0020358000c2000b041d4668041c6d805100503080280c103a040c0a540da04000d5540e0000f80c0f402c1c4801020040041d00c002000d01400308166041a101100e80402d9030716150301c0300c00203100343c501c16507401094003640d40381d20041c41140d00325401000c140243d031000203443d041000040e8188180400c081001980240d181030032900c0858006840e078641d400e18504102040c803d56403140038420324a5500d4400c1c9004c2c0d40200e000380d03010806058410b20030b8441d018084030403409139011800061a540c4100390100c1c03101d009105640781c0c5075966000c0382c5241c201280d071044000b0f003c11b24102407294040c049a01140b240387d80c03005810a60085007815080c7d44040c8a8641c000581130b240709825000003000b091010400c20140c07509860001c50740030162050960624464076a0312003500c22240202591281d40181840c004428010500c401e40c0600d4008003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 292241330 1250 292240080 292240099
    0x30518040c020109050c04020310180f02070f06110301030b01050405090a05060114132f0f070804030209180c0609010c0803010906150f020a080a02160314120c0606010806 75
    0x8584540c001c1603890301d42500046181800c0d45069070030b0150340042c16018600c18020000581c40010a42044400424429003100d0744d540488000d003280f98204a100784c000543c003004c00c002880e4203020f01d4003130700003004451401d00c0070780328a2100307101c0a0f00c03001d4001d0041c422864984d10094014541c042100c0e2003084035079803242044026400b2104001c1120012622030804509000842211060070849560f100e044a010b0000131401000032000b0312000d8032904500b9404c80c0e04280020062a8076290f0a20344458142c0c80790000300c0c09161030306d002c5400c2440000c0d11f80005000c0001400828403044203000903a00000d0403507040241458510012031400c43c000e41c06088001d4010502c542003000311046404254020000c101d2801c03e03504225a02017020151107078040358944e60b482119004a00d4205444110344050704814800800c01507000c0c400b45251b041501510340c1080c00e160301220300d002e40c0380060030381d41040e000a0314a600c5046120791000c80100355050 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 292242580 1250 292241330 292241377
    0x402040216061b020f15010303080405031b0105040c05030a150b0a090204090b041d03030720060907050a08030a08041401060e0a020403020a1203021f06080d0e0f09060d0305 76
    0x16210790310340f402202d80c41056800e10203a8140170881c0003030030440c020301c1421540705901c903120105110140400040402041c10010280200c0c1d5011076405564006481e0815405000f00000d68088030f000015400c00240c5080209485200d2600121326500c400310f19069580a000100752050b44a8851000414042c48a20141003c1c1089640010304140d0b03d4043c841202d03200d0009140080c0e0740e22010034a258000102d81e4041c009241c00301840032401c4000c0300c0e81c40010440c4006019120800407001c1002820030304a80048820115541c0c1e1120b5542d102c1c031442a030750002440000000c0d01003944002c2e01904c2ca100070b40009101c5075584a080030081094a045801a400140070002d502e085c2c55070b0303009048160b2041da00190740d42e03001382d900c022258012140083c04c40d8a80d20450301503214100410b81003080e0754030408908001072200c90000d0240d0b100302e0f0441140b80c81030400320300312480b03200c0203015008812035a880954040d002040d02180d02d2905441c40c2d203 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 292243830 1250 292242580 292242593
    0x10b0a111204030b19140c09010302120711010614030a1b12030503040c0b04121e080c0d0314040228031e06380307053003070b0402040216 61
    0x300450244030600201d06004407401c0c4000c101c014020171041c10b0000014040c26400112900314508811081da2000206c0041e006405280c8180c0101c00b10241001549600b04078454002e4001c0c4000f040259120044186125104000d007901507016948038000180c410200c0420000e450806017540b0303544071203500c2040708142c0102c0010b41c020050108104e90340e03c3d1440600304050400d800e0038140105040c006403c200054003002801c02659110003602142d0041ca64108840b25903840380049466035842201800c8000070b4070b0311148000a42c1501d914502a6600504a01e1084062280020044074910178990b034541c0c1420004006045d104100b401c40300b121050841141627801c0160484aa0740b8500802100c60b510401c41a096000c0294100484c42c0d58900310601c24004280751105035007020b90001804c0c1391844003a00e9030811495801c0b20303078009581038200c5408082d103a0261583c0180f0010f85940031800514042e00504400e83c03240c1d0304d00c0081c01d49600c03001e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 292245080 1250 292243830 292243837
    0x11206090c0504030317010303020604020f0d0b040503031e191508100903112103070c0b09060f0717040303052503051006090f030210020f0d080915010b0a1112 70
    0x1440481d0000070300308100750f000b454000300c86d00111108582c540c9103071000b075103a1100900091148541115100c0706d596840100c0c01032541159110020746001d2a019a07207074016140f2503000400c05c00181d0100031301007180d034031400f900a00c4240340540e01480d01c3c058428107070001e91403002e080c1c000c1025031003040101104080450041150710382c030300307024003030401c201d8440845421000c00e06aa002c600f003800c81c40c03d200940c205950366603c0e04202e90400d04c644000b0034481080041c00b544020010304ac070302a400d41c0a1200d5036444400080daa155030b13142507040e51000075400070707000c01d0080e44043d41c05540c107000a480000211410140708440c02200300c0400da8580c00c1c030001050b884110006070500742021036500c0e090140240a140061100901c01c51103203100410a07442403201c003030700c000c100c42200d000304030000d00a440c0003012070300d403211071140c00c242101d00d106216155040318045400c503890f12a481e04229881017404030207058600c500502c0000741602ca0004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 292246330 1250 292245080 292245101
    0x40b12120a09031403090103050109050106020a0f1704060302041805070c0f02010e2110050c092b08040314010209010516110a06021b0303090609100c05010c0c15150501120609 77
    0x103180e1b50415480050111141a003003100f04500d060010700403244c00240c64010160442c85c0500c100e00c4a1804c07880c1e0740b41454000d050750310041000520b03140c164007d801542c078a581c002c00306052140221048038800c0320402d000680c1000f80d00c000c04c003c581340340c80c114018500b00c80b045124401180c1e16103003401c0c000b40e03148034050380744648440c140000500f00250b0b0303d0501140c10b20f0301c10318540c0e01410500310f101d40c10f10100075100780715594490b016802501481d586410305d5050220003608a07100598181011240c030003031001040c4203d401c0054140c560606060120f0002042000381c40d600700c4d001114440251980c4d0f035580410710082c0100d0740144006525140b40070038283d40e0204040c082e5109000c51f144981d1510240d42c62880142d03002d05040c4020502100d01d40895000649a07510342440c400145611144c0842150f006444415001d5000107000045490800c01c10764096600311045c07002d5840364007a040c2d101c00312000803d440d40c858104c28200c2d07048004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 292247580 1250 292246330 292246333
    0xc030d0212090d111e03040512030415030b15181207080d0c0b0c090a030f030c030801051801090c0c020a090606020c0303070c15050c0615040b12120a090314 69
    0x2c00401d940108501401020b5901e044201802c0291003150703200c4100c1c3c0780b4031282c0c8040100c240c0100c0108141c40003004d00400e0003030135040c420b00c030301d441c0d80c0103015500c031100040400203200c500a00030350031000800f0b0300c1c0f00c9684504134400c02c02600044003481e00c4005105130142107681d1a0181158901c0540103400704519100e0003078904558103030000c0c140300e0800c045402048156a241d80c0c000c0090314402c0d0b41d40c45080000705946c0462704000c225a440303c2c80b11061540c030170003440c4043d100741c8400c03815036252000c1041110038010000c91102100c001400342c9481d076004030074035001a080c072580124155000806418050b0000b2044c103684074010000182d04000481921809802852401c06a82c5602110410714014684681c4807602281511071088080751505240712081e600e82c0d04100d10311a8600401c0704120303100d035040507440c0001e8544203822a1200100d1001440c0305e00e20400820740f5504161900070a221480d000007000c182a000401c03502d03030300d000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 292248830 1250 292247580 292247617
    0x13230703020d02310b040e031204060e0601080304080106050604050310091514150405040b071d040c02030c0c190608040f020307240201021e0d1e0b0f031606050c030d02 74
    0x612000c80e0003222501d4406c0d030610000c4984050040704480540501c90550000b682c0c4500700100941000c80700c4204a00c00c0d50000101c07902c010000d00113645030b517802841955076840070010b0302c1c02540a003e506070440c481c071050607807140e441048a1845081c10406a00c80c0c04540f008036162003400d00c1c0303040e01c58005c00050b215a990b5080d050402107404006505040c3c4551031141c1009105806103c3c0342540c0f00085840841c501c107150308010003d00c07821511040013500c94100c62003510f030501c00d0750062025880c003c0c0c607089903400700740c03a0103803001d207808400c540403840548161014100c02c0342c803c003d602e0604c2440c0162128400b080002c50407103914684a041e441c0c611001c40e48188442d24070403112745411160150b0403904a6200d0034904c402c0c100601c003c50700e80d03158404004088060340c0341c40c0c1000d010860111150003904003a24181512548180380100d41f0300700041c410f01031f650084011b00050101042101c0c03e000281081a0032030b40006d80c4e02c2203900313509 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 292250080 1250 292248830 292248919
    0xb091905030607091d040305031b040801180b07020d021015090e030a0207060329011115150105030c040b03040c030f1b1d010603020f0c0613230703020d02 68
    0x6001d40c03c045c1c1954425940c103444c26403001023080c00040e24500d603d9610744403840f40c0c1a000002c0d940a021031100030444584800c0e40c10941100c40042200d03007803406000124000e0002c1b0b03103281e11b50410307005004c07140c00d1400781c48002e21128407080c60084000070081140822441501550644903005613981d421000c0041c0c503010150f0b00400c1010f0404d0701c600c10320340c411150700402d000c1000d60040300742441c4005880401c0e8044c4030580c030784a11246c0701c60500c51803c115020b60b41a0ba001d101072038209004540500c0116180e44038580204410010500440c0055510502409200c0c01c46034a950b01d03000302d00710400f4183c030701c205440e00181350b11450030010381c0140001c3d00b0204101c005503444040418051045c003080c10b50203d03a400e682000034003100e2159802805840d020b11b030a032030000000340e08034002c0c1d41c8202c05884038102c7d0140b41440340801b002d102d0060070110f28607030030015045410380c1f00700c2e08a5070780d0b00798444442c00c03081c2294075160000303841201c28480 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 292251330 1250 292250080 292250099
    0x30b1809061b0c07051009090e01050609220b0402011403090c040c0e01021506040b03070902030a050a02040317030901060902030c030405100507140717030103050d17010b09190503060709 82
    0x403482031003480800700305508010500107009005ca4001380c031200381c2a1005c0405a8044800354000c6178080e0a20000c0304204d00c06500843c0700e00c00455074010203484098420004010052440e61041d150781030300004100426003859100d48140b4050044580000400080741c200766110300103940500110a10791034640100b05090802d45056081c0c082d071200003c1d03407030f1445919000024080b9001c12220745640d04002500e2401030b0440781a1945d41c21000300a5000310760300d180803464000490041020703402210102d0790054880180b0b501070008a01981e0700241c440c0741690f43e038102c001050b40d1540042c6108110342a0b1468903840d02d0f04080342007020220513040d44034545404c02174490b800468004800b40507000b0640c0350209441c0014002242012142c2000384c00300000040101c0020441104009035a402444001000351418142020700603050700340304c01e01c41401c090030140e44600c0d42d400d403120302900c516a41d03030200b030508c2d80c08e0f6508030000c0d94101c0700f0700281c030f00c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 292252580 1250 292251330 292251361
    0x30305011a07060507020111270a050607020907051c05061207210f05010e011508010501060906110316030e01030c05040b09011107031502031b0a0807030b180906 71
    0x40e040311a400c541c0140c04464024440c148008100c10364840c08260b0b000d20035402070529020704198a079503994440214040c00340200350441038001c03040458102c500304040c100d0122171000c0d00340381c14581c0d40e074204078119000070903040401c00d041c080c80c0f240e448144030311440046c0f00301000480c4c1c2064418031881c4640b55070061a15840b09100b00041e503100300842e101c80c0e1802c1c0808450704940e01e422003010a030004043d06035070a2000c010307022803040d404184000c00c04511600d01c55a00c2e8070403403e84a09109000c0840c04108041083c1c901448160202c0010341081c2c902e0010890203a10009120010641c00206440ea451038030b940c0502c200c00c080740042c10080c0c2028a4003d1088203441140e030610304201500c0030a61f000e100030440000656031010480410051803092000207400407250480e4a000c00e00b446408014114100d801402a955070100a07603500b10f4268007510b00680d910707420002a11071000780007002d0341d6960060402501406180c24a050480e54510307 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 292253830 1250 292252580 292252589
    0x6180a021e090a060813140706020c0d0503030c031003200103050a0207020d021201020403231209010e0405040203030409090303090203010506030106080d0309031b030e101b14030702030d090303030501 88
    0x1040028903501d9503840d00f19002c44401d0301d40440103075100a2441c0082129a20040901030030b103203020209280454202c0940780d082c2c1c05c82d4000c0c6603100811100003a1600090a60340040001c00c81d081c0c1403500856011b4100d00f800020141d80b5915104071060802403d07810381c941c004032015541c4e050080030f401440c640015800c3c14155000036900d9400c0d032000900c6020360301c914046141c0e0a405407030045802aa4002c0c8101118203c000d2401500c80600c20502580c507150240400c800b0a4601500040c1c0d60990114141d40500c002007201420990b07141c801804001007880940c050500001e01c00d503400300d1480543e00c181800e5507405042944240d060540510040b070700015070510103001c0d8a008a418030041c182921880c00e00441041c07400e40c0ca1007101c0926801855890a10320242d03a10001c40400c4107080311140e8120440c0e030b540344040d140e031f0740100740210510900301c00c0f07100590746003048a0340003a1074a6901555000450341c0300d6001c02c280754040c0b0a2a0040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 292255080 1250 292253830 292253887
    0x91b0a0e12010f1d0d0c0f1e03090b18040c030f020d141003031407030c0b130b0f0105030304060f120207110901080105010501020a0f0302010b0a0605030901060503160306020306180a02 81
    0x162502c955042e10f940080b9020320800c1000d42d21103091060b13404010a569800c503a011080482400805008005560040c2e001c1024ac400000b0421840c0c4210307000c3c541d40004e00d50030722841d003003000f0260611200c90002c168a03031120640b4518071b0720003440359050342c800000c1d01c50144065805004d00040240004482013002080404c6d003000c4600300c14002d80d0000d1b641d48050f890140d40090080501400020b060002c104030303034036041c02c49032a02d405040003540981d140007030200b400e24240a140e8140d0800d0000b00011030141c0c0d0007950300c80050801c41414464504008201d8014140c01d540c120000700045825042a056290250000c00001d11456042c01c001179a00c0c801d07440000d084007071414049007498400e506c0382c40c540800410020040f079031000014099001511b0116255203803050010750f526001400d902d40c1d01d510f07051014814038507100c880007900010b0919411040c080c1e0003908245284055920684003014010703200d600d20340c007603aa4003640c02030306030f0007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 292256330 1250 292255080 292255121
    0x50711060a060f061e0309170301030303050417071a060111100504060606080c07260705010902030115030f0209150607140712201c0501020315091b0a0e12010f 70
    0x80e20070940c011750082d050120b85490a0324005400c200341d040005410b40e0044000300c01c15505801c914000d50083d0121800007551012401c014840c0d0700d0000c0028065596400b100c4d03908003a4140d001c20705050403140f2066047c8482c0c2812041e03481040065a900100000c020302d0f03206130320180005181032103140c030b00707000900c043d882a801d028010b01200320003112a554403030750320a20f010f00c24070621740322802460f04a0190105200491080d420a80700e600f0307510208141a040320340280c8030282c002116000c0c401d041c0e601400f520a045001c0c0603503822501c0d40d4008114081c8508205224400001c0460b4242056038110402c29003425032002e01140c904044404094040c10400915030729110004448854440940170030000b001021018002c065025500c501d501c01a80180307039400301d0030041d18034022a88003014141c0b109548075580210b9000e458105001c1c209600010844400214018280d50041220340e440c1d038503103500400c560144800c030444548c1d84100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 292257580 1250 292256330 292256357
    0x5010e0f010e12180a0605030a0b03010b0f04090c03060608070f0b091516020312040504050604020a0503070c06090203100c0e010305040804170a0f06020a020d051c050711060a060f06 80
    0x1207955545800f007a80500100b10381103100146111080c041d00000d255001850380ea21000d48950400c490342c6224a00d025002c491608060003039680f092402002c0c100310240c0603040100900c1c68140c1652a0890440e002c00080d0181c421040a0050300004200d81803a044100d10084510713000041c1003001440031032000e4950b42c454800e0005e04100241e100c00c2144118450808103540180d0b06102d010141c8000d04139007801001a141c00382c505024554030031061009a1003441c080c5030020354200001380c00c085c030942d21408000d205920118407034100760000b904d090307074504a45d4041513031150b04410b0140c0201d12042c03a01003c4c20b05225625003901e43c00550f028500c218500c0c42c0c04200040d2a0341c2d024041960115070044441114912500300383c8029000501050098440d0311803403c0c00e41d0107201940c800b1060758030b46c0a005100e1f0005003000d0300c000b90480301407026503c0402080e24080c0a1036109051013280003c469141003001e011000883d4410028043c80152646 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 292258830 1250 292257580 292257583
    0x50f030406140906131401020f0105090a0b060d06140f161211040902160b0919080a030608010f0e010b0d03020a11060405060406050409050703050903070b04060f020705010e0f010e 79
    0x14030348050b019601d41c580d09010b010039440e01c540a960041c40780c50704804180e601105a650000e440203900310703400801d01d900d9860803604161102c06483e4082805000007030307441d800da9030f813010f0301600803c01100260354540a5a5030b030080840d00c1941f200821608620701c100700d0b94050700918883d4400200200064032a010382d12002d101c55803a28000c00c0601e01c0c15044400400b05403c04641d2400d10103042d1421384c03040041101e040140c00c002c01d041402c001340c004111550b03400180b0b0003102940e90800c10360303c20300442062503151400019106000e209200c2c083d007051501241030003150352060f00f1070340c240e004940700d034030401e0624000c203a001a540e03041c10750040300c9011455810000a0702030203913601441c0e11072070014010840d554020301810403604461024003aa44074180150705840c01144e00030a90f60040c440c4002040141351840e41060149100042035004c04081d6010f0341c0c00380c4015620741c0c2d100d4610308210b8008000104807140c51400070083d14101402c070a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 292260080 1250 292258830 292258847
    0x180311090a02041205070f09020901140c0106030b040f050105070318022403042306160c03120203090a02010905060a09030201080405102d0c1e050708070f050f030406 73
    0x12402500c0c500006210030500c0d504a40240005910182d0014060300c1c0c00340e40d952043c00390225001d1100b2000522502500a49501102c16101c02c0d1213003580b49a054500c0c0c02100c5103004564a5117000800715141421450143d07005400344010540300307041140c2500d4000e4004010035181c412201001d4140344060900a1383c119001603a003c0480111103442040b910507a102c21030000901c0100108503020464500e44503c55080d241c00761441c440d12030030202e408403043e00c410310140130203a10644500d080540700b4103262915581000310300040303070011038012200d548590510300a41d0780200312000107010454030355290000501005101403414400241800038a1002c201001014851002401c46100c810407070388582c29071181424490301441412000c1a003207940314648940101e00b070b0002c09440d00781d100703074003500340480810701000c1840c1000020304c00c401c000340b802d100600c400750081c42902401c40c103504282d1b04101c1103565000490780100000c02c051034002416 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 292261330 1250 292260080 292260113
    0x140c0306010c060f0c1107150905090415050106020106090605041a100c0501021602011d0907080a020405130605040b01050301030b0c07020d02040c0c0308100303081807030f05010b011803 82
    0x20105000c05071070030f040540306807402c52070068140300e09600700c603030701103a1016500465001c659066036a040c4240400300300001020001e0900341c0103000c18100350818a410034410011150429143c0798540c04460007a04000d00603511007008014842041c044d0b003000c0c020881e4200010005818112805564420014000c0302d580c0d40c9154440c0c010543c0c07a0f20f2a801c0030007551f9500e4000b44100b240503003040c0403070110380c80c0c0c50b500180d128075403512207032141e01822495030f9490300c80060f42c101e00c0041c074400300035808000115954a82d4400125188036140c000320b0701074207200030801900c0c081108241048014401000840c182c00701d2039030007a000c40c0280390780e046940080751110510643c00382d0050300300104425000d90140e81030248030700a5903000e0f51a190320740d5481d400d0841d84401b50000e290880400d0561413083d11800440480701d01b2540d130542c0d25540c00a544c0c0b80b0100c141d0f103e9568219000300381d60000b0103014005c600900c281501c03811961240a45c00c00d1581 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 292262580 1250 292261330 292261337
    0x7081b0d02030705060a0905150c1b24030919030504271d25050918010501062d0c03050d0b060d1e1418010609050705030703140c030601 60
    0xc4140654600f4815000a0031000d00816681d004400e4040c000c201244101c50148416004502030280050b041e1024105520047d1495041003040d8203103c025031b15080341e00086d2203001c003800c42e419140e16055800b022106c66120b00d017002129081550401040c1482d88224240078002907200007150183c6046c0100e04080c4d44180c854040d840840d80300c000900e03032901600d50246251303400c2c0440902d04280031603c0e2511040007001140d00d84601c440c240c1d4210480c01d001924151000e17503803142070395185031848014107690f542540c02c281c2c00310340420242071002c01d079010b0350603d25500d0f01c0e101402001c219212400101081281d131030160070048007044005400c03130320350030002d0074400040143e07844445510342c910041c908010790509200340709805c403000c0030035406004000100c8803400d41003580c5000412000e045000c07900f404555844101041181d1280b081601420f41a80c89503103d282000e03002d800c80d82e80c4007441c3c24040700c440130802e00d811118100c0781e00403003e18 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 292263830 1250 292262580 292262599
    0x2150c0405030105040f0b0604140a0c0e100c050f0d02100b0f0d03031505041401050f12010203040c03020a33020717210c07212307081b 60
    0x901001805035401c80c036495401e0400f400140a00c0000740010b040c00360b400c45d000c0f51146001c00044036404070a0710513510710440007035204613107a804045101d440c1d0801140b0300d14504009540c45e18a01d00c0c500100c0c59640342e850520100700411100d5030142c2004103040840c00308043d5941d00d01c80d511030350341e80d01d901d1241803940f1004c084a0604601400542c582000384c58081c0240459401b40581e554001c0d0001a00e4074140c054642c90588400e42d54809909000c144414185200300181c3c00500113080c0d808410741c00d20003544030307038090758000500d281944100560b02c00300b07070311a41e00004018803034a14940003003480a00404880e0305403214040c422016405c18040e5409070400d01201d510b5056411030201c0d0700d00004403024442c0d0090204083c80c0d01c1c1d940a8041d421030345500143c2c05010134440f050709000d2502c4056a10644004565900c07461218011101c0d40401400c0c140b81c42184010000070300035060140103404d5001d42c07400d0011030b24840d044507a1240c540300 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 292265080 1250 292263830 292263841
    0x2040b06070c03260421060b060d0f050903070206040e0403020a08070b1501050309060a050403211a011112070f0b0702100507110c13090c0b0406110a03140705070510120506040504030215 82
    0x8e40c0b204112035000780045440e11131001d0098000c2c0040701054284030305180004402d60f40102c110303807205900034400c50409003400f0201e24000402030088065105240384080410b4544002e0b04c241031003036180950381e19001c241080c000d5101d030402410300105000348a010300e00421280d5000180703500c005087d540340d04045400c107411800c54680c440b40a80c00003101101900310000703c440c0c2c0c2c0c4000d50f10a82c09001121003c4144000928540003659441006500c0ca80100440c078003070902400e10003140d40315109a00000da501c040940c1c010461964a0b100501540740c1c4040c3c03c0c107000d482c04111012407919181d00310304186c42a621464200e0840d03403168001a00242c01c401900d0b140b50300e80c1841d9805034060301601006c10450b084003230b01600001903824105a0641e600004840e24110550664200100c21a4070340980100401c40f81c850b140c0a0100180c030b0354030b00017015203c1c850760080380d40160860340900e05003410000442e400080c510700024440d9030700c400550700c4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 292266187 1107 292265080 292265093
    0x3203331608010620030a210e030306010c140d020f0f0106030503120606091e040e0f070608091501060c151802040b06070c03260421 58
    0x1c00180a0780744540d060018103c414140c0c2c0c00000156207406055070004001040011aa4909040c00d15090542c000c0000100c1404000780718085561030340f0380c8802072500c0d0600041c0e464030004c100007501400100c202000584184032102d0070025100c8090784040e404610805044100c480c4040c450101100c0c0e1003001140b825180c0200d104101c0c80c001c1020f0b50200c0e00344030061580e00c1d990021494900b4a03001c0c041c1d008441c100300421075200b45900d42540c1c1c0262052000380d0070006448054400c02d040c55001581c61142c00362030300140804c80800d4000400000900b02d13002035010003100e03c00d044031158414180081c03000c840c0d034059804410505450a0005400c1c2070340a030118902c050003c0d8949802ca40302c2c1c20184005a1040b20070030721040e02946640b0209500002d00c003420902146814640004c984040c0b09446002400e010700504071750401c4207 = true := by decide +kernel

theorem cover : BRFrame.Cov 292086330 292266187 := by
  have h0 := BRFrame.cov_init 292086330
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292086330 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 292086330 ≤ n) (h2 : n < 292266187) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
