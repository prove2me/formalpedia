-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2211
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:00:12.949346+00:00
-- url     : https://prove2.me/submissions/c47d1e49-0200-4f40-b9a4-bd1cb93a6b8b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 397482014 ≤ n < 397661870 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 397483264 1250 397482014 397482053
    0xc0711091b031905041203240911071406090d0504140d051609051b0c0d0f09180c0e06090a061805100203031902090d080a0e040519060b0405010804 65
    0xd021408078149402268012130140c03403d038103207160071b0034050100c81903010b0704409034039034407a1500f114201c02c001130119a810100803580b0110100c05020501c14000020000e82031107070184204100003039103610501024003101d210f00c0003080140d501e4001e43c81020929810251a420542040e00401004600c54000c85064000104100c0314030300b000d81001c4401c50741d50b0104801c44bc1450004103809400c41c1b07045140017001c1450a40307401c65403031120140074115002c0351115100701c00a100900d5010f00e28002100202c803000c01070065101c2c0c0c80c0018400141c4c0e80083d103010400c9980d0090020039524603580303081c0080c0e49040c0349036600e003d01d58801d0380004039615038130700204006007150b001d9656031410b0f980070601c0a02d0b1001c0301c00c12904c10703c07810204e903c84149001140d42c00050058071042e4140c8220b42d1050010101038000f807d03c03090050709510029920144000c0b070405100f01c13a120750818009006034841c1d1400103441e0800700d808600ca101c0b00044807140c4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 397484514 1250 397483264 397483291
    0x1031101110a23060c1614120f0301240905040c090e1608181207050a1202030d060b0c060103230f030901030c02241e0c0711091b03 58
    0x181d8540c0c2500c0055402d440e180110f80980198003004240b003070a62000308180918100401c490356035900d40ea1141005000f0350358054502d40702d50040081c050b4400300d06a040d9035940d094881e0358029002842100011a07810a91541046000190b902c1d011104d03612a8686880c0004100c003504000889005102d40a000415190124031980780309007082000705940e004042c00007002c86100034840340e202b110040005241e04008a029101130790749000c0c854858801e0b040407801c080014000400c0c10003034199152085801001034070f071141003840c041103642c0d540c50b1207021500c90640204c4081e04800014400104408100781d4803425000361701c021440d0a8000915140c04803036025000d600c080f0b18002c3d6580e060095400090051001d0180c2010780c080f0042580b50025010040b0f1031410005041c0c5e4034140719890a03c081c1c0d031009640c6081003144100c903548042001c0d2000d0a108090700501d09040300c41c0d50160180c6542c8060102e0544510309172030b040502129580904e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 397485764 1250 397484514 397484533
    0x91803030b1815060417011b0519120b1e01020c04020a02101808030103060204031707020d110f0d1a0f010f0b0c150414010608010b0d060506030708190506010e0103110111 75
    0x5406d41e0025a462200000b6240d40e80c4004180140c000c845a030b082010400014001c00c00d052100c5415000c01c2c100840d4407981240040060200e04802a80004180c41001000302455150200662080e02511240301c070351401d02046c1d110300c2510300c0c05a4458040e0300d406050a500c00a111800200a518809890307500c8201c03a900a034000d40b01d541c0c0204042c001e200d0320081c0302443c800e55610051414a9a40c0130440700031468901038604060f400c0c2640094842c400e07080210030300180004500302c4903181003107803000000c0450a14004100c0000d01d11001d000c002c0c4e0507502c1c0d000c06051544d141c0624522a503100d0022408503004032580c807900003070010941405644141e032204c101c3c2c08111600344c210f69281d404121103a04140e00c1000c65260401221099500302002084964440010a10f0040e60342d1000880d171040d0348418100020302520500030520070810b5030102d0741c3e18914011400028007003c3c02460390918044034a40c01800c40c1e0030b40e1102030381614400c06 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 397487014 1250 397485764 397485779
    0xf0f02060a020313050d0312051003080f04170705150f0d0c110c10120e030c150402010801080604020a05061804050127050408090d0c091803030b18150604 68
    0x400601c000d8001d43e10201d50951881010090b01024001c15107242403d40c08a8500820000e1b0403000d2015040e607600c080750241160100c060041c540015400e07a8842d0381c00140407041c0c0c403a00c50039106400030079a000707000b1800701e203000031910020041015042c041003141e15642c40748184031501002000071101e001224000c3e4050300d85140c941c1144e2540c3c3c1540b460800c02056107040c030130841a60020f0000d0742000c5855903082002200041041504001914500c2400781d0303e8020320501c4402001c1005500005219500c00e03a42ca40032640c0e104c4050707a4410080d100203501c900030345800d22160030120081c0071409800f0300c00b0b0480b81da69201150446500784c000080492005010300c41038022100711804541c10a030081042e46072940fa8004c040c00b0700c0001600c91a40c601c2e00e00148900752107824058018030320200041040c3c00ca1200c2c0c400702c002421070109003003850780035170b5182c07034950010032049612040441c0d545150220040503019082c550b80510188030106507103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 397488264 1250 397487014 397487017
    0x50411090111100c08100501050c070611030c06040501091e0506070c020604050d0308010317120a0e010207120c050d030506060d0b0111150405010b0415060e06070f050c04050714070f0f0206 83
    0x2161329440d0030020b410101030b8883c01c0c103101d400241c1031050400c0030f0410a80009001c0381102c201e4604103020030708410001d4294401d542d80b0f40c0051080074117110034410190301050a09114010401c0c0c640103c9041045c01d0040d03040152494204800240025000c0c2244d499005d10040102c0d140c0754036800014850008440190001900d1000610400450290700510081448002814400380e50114035090200a01c440502a02c0f074020070115402501911181503020040d4048600c000b40028901210742005503124402d40102640460191280900419020b40355034544403083d640030000c1c0107071041090412482c7c3c1c40210183d6410f0200d01490150303021000e5507410181800ba0941c2d0b40c04030b8140c4224030b8040145406181c3c0c040600803542a4200b0300800c10301c0c5800190580644030024240519000226082110104a00d402c00d942110200003e07280d04108032810846c01400319039400d4204052801f040751901d420007010310610f5480c2c0c0813210390740810040d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 397489514 1250 397488264 397488281
    0xa0b0619030c171314010204030503190f0807120902120303090a0614060105120a0b06030403030e102c07150306081e10020a020a0f1b05041109011110 66
    0xa544400d00754149070f100702c2070f41c481c4141c4045030b802c07400c00b032000c6a082008044001c22807103035052200c5031044290107840003140c119050b2616440040a880010816501c40c04000703522030440010640c040c64203107004041940e5192420b104c2c401d8050002c00c3c8038502070343e0003085210104281003081000b548244c08541c003401d8001070702c0c6042c0b41a13406840702c0c400f6640c55601000201d99214043e03885903214003078098000d460380c0c0f802074000e09588960303a4018100008000615425400000101a11604407031000e041c00a04004856030586520141324888050100075130110750400402c3c0d540300f0903034a140b592010300080340c0301040a51000b0a07107070402001741d0031060100c910422503503041d8a400040b50740300da40c0c403803001c01d184926240d8046003021019208001c00b00000c0c1d40440d0403149440c00741000e4581a0401c0c00c800c04000d1030036400309903410640a1420f00c01002070029050000c01380c01528010485c0d03070403422601c5800c5603040c0b01416401503620 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 397490764 1250 397489514 397489517
    0x503071803110111030c0307030509210a03080c0a021b1306350624030607020a05010507052104060213030c060909020f0306120309041d010f0902090a0b0619 69
    0x1a1040c1002c0090300c1420b4a511207a0250028402914244008001c80340d500c3e44c1890100d5950982d80c0002e074058a802c400480c0345d00004541004801d000241d001940e07001c0e48070702c81641c4e101c85030809640301d205d407010010b030810030b0b0134461840202c50780c0d440414020704030040d4500342c10000d021620703698070010780c1c40030b0b0003002440345511146140601072054130140815121480131a903d54001c0c1401182d030130010501e0000c3d0150340f074103a00d01c94006054524504146400941c1c070344403c1010f58155107030001144205005504031084401c600030601040c200104040d0741c800401002a40c40340c1c1c0801603002c0c1e05901c0510307000070314850a0102c0c80c0744c2c10a100103005c810507400460840380704109a030200840c480a07070354044e00440320604296100341400d411405036540c12600607003031140c00320451010341a00c4030303a070390007400800c40303200b1000c074000641e89000f90294000440e00042004d2207515080740c0c4080001526083c40c11305280890001110030680280 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 397492014 1250 397490764 397490783
    0x50d020a02060a1401050a060503100b0c01020a02070509090a030503040c0510050403030f0e090a0e0c060c010207020f060f12100f0f060f0905130b1c030305190203090606010503071803 81
    0x100f2070150380706141600d040c0b40c092040641c10b15005c920b000041c1c1c020081400b1001c070005404013a40d02c02000500b100c00442d50301c41d040e01c02218040e400444609002d07014902002c0303024205043c41034840d4900e00002c0c0030300701107a201502c503544060000d031003a50704a02c02044648504290080c00d11003175a1b11b9955910754140104a049600c9446017040540c4030344180321350f91041c449030010484680001d5046203400c120f840e0000c140c41ca20381180c400b20301c2c040407440641c00b030007483c0e0090b6120460303664400c0400c8001d1080303d180035200c2c1e00074003600102072000c0b44025800340781710320896103460725007514801e5606540d01010b109003160344d0510070103a0255001c94100d40505040c0c60780703824640050b40c6540d013103004034211992007100c0c0c025991010b141c014110b0341c0700824a108035050500501820003240c000903000b6142105940d07850301ca00c200c0e803060404802070b1a16072212001120281c0c400741c594420043c000c04800e207940d4004002400441c07103800100b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 397493264 1250 397492014 397492021
    0x406030b040608061018050610140903100204140406050303071b0e0c0a1d03070b030a0b130603020103050702120d18080a0906080907060207030b061f021b0a150e01050d020a0206 78
    0x90120310392810701c01c806d14144414041c854484441a0020a8460801c0c3d10300940d0391144941c5400341c0e1080301c1d850320075140241071003190b86d802403090303804a0524044001c116820311094990a20031260150700c10007002e4003082d245554007110669150621940c2c60ba252002e03260700c60b0940d01003c891100044800c01c0a07007001c06801581e0a0341200b45580907c1c00c0001c2d15901c3c903100d007000784580000080c8000556500c440b10340304004080744500141030500c1c1c001050280012400b180c5850041003145000241d80201d81c000d03090214074111210340c0800c094418138070f241c030380300d810480c4940001e034448001d018800034a5568581040c6071038002003040c01e02804008031900004c100b0311081d580850307186c0c15a41c0040c080700700e9031503500105410390310418490a55aa46682201c81c280c3d01144186c800f290008a03c5041520300040107480d03000d43c894a034481841c0c0e0899000b45000e1001c4140c0b0200504003d8200702088008009981c844594400103030845404c1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 397494514 1250 397493264 397493279
    0xb0717042c010e150d060e010617060108030f07110109030807030203070b010605130b030c070c0b03013210030f0507170f010e1f0506040b04140d03050406030b0406080610 75
    0x100d00602045400c0109410301c101440360b402d11135110640580641001d99041c01180e80000b48803d84040c001c101c1c2580e1035245145590187d00d070424035001f428000200c0d00000400c0d03c401411041c000c5182c0f0342c00781c0d2583c210350b40d52001c1301d0601003003020000109000601030000d03140690091541d815040c607128501200503000f00c001d11000f0302004000c05210862203003130781e4590025a9585c0c441d0a040301c5a4064080b0050100c500d0860105406c4002c10256048035803501c0c04803c01c441c0a54510111028801c0c036031a525140e00c1450a1484d29441440400200e4200010400780c5202220f0550740f00b01c5600d0045980c0c510124950804001c0d240c1d40100b0101d002d513100d50404c84002141d40010340408078240c031103207450309540c2c0042185001820020f140c01d40d100d0b6240000c1006800c54451010780160340b20a02c6c5d402d04080180c00300b10f41e45035551070f141c03a040071000c0c0c0c0240805058203400c560f8a2a01142203001001000d01640d8003c0452118500d010f03032 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 397495764 1250 397494514 397494599
    0x50408010e070602190201110703030f120606050a0f0e1201061a0304110d05070e040309060e010e0a031b230306090f060c0f0d02120405160b071704 65
    0x5128100364810101003100603030115505520105d03101031041059418001241d05042d2910103011a0017218000020150400c4428080010a840e410000304040c50040211034082c4101c401080040200c0321500d44540e0758140d2040d602d090040c650400c60300402d2145007490f0f018181c50f0340d110001d000651040203620903464218444500e986043c2d50b070340c0031401104451500424500301c015081107021301510010701340000074184a85050b050003031040009100da10082210340c0410b940700d5208440206038800701801c1502c1d510310315507a0f0424802d408440520814640002080820306600d0322501c09020492580d0168982c030308150900d1800391107440c0d1030344610b25420a03400d000c248076500619503d42c1e142c071010f52400594591048030441c1c00140e100040c020021540000124011401501251404e008250380710703080e415039008007001c1d600140070303620001c0e446112004c0001007203580325052a03900d240c04860494010441803442c2460090950080c41201 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 397497014 1250 397495764 397495781
    0x507110f010c031116170c0d0305040b010b280e030f060108060f090a030f180602010e0f120f0705030c061014030a030c030807020a050d0f1205220615030305040801 72
    0x2481610340000e041c00c0116107407003000000c012041501c2014084030640041e1401c000c1a0808d94180300b01d80c4000800a240407207013111201c0c00e400000c0340c1d513079600e000e542e513540c00580ca52590125240500307074a0442843c2003c1001014806811140c13810300040c4a0040d41000800041d410f005039142003100003840700625080c01d00c100000080000b8803035000300d805081a030041c621512080b10781411104414140740c54005000500d00d0381580f18500408031501a60021520391315807035102c244c5d080c0290b403800014003600340303c909030800a28500f44a641103a1908003040d688070b040c54412200e40c01e15040040c01002413103814007114841c0c66044001e0000b494459901074024820b009028040188020014003d58000c00000c80c04580100c112540700444440050019120810140001d400103000301d003052401d0151501484103e040d102c0d5500c1070000d0f50511f00340104040d00d0702c60301d03040b02008584090300c104001d075000f80c0d40c841d0340d5403c02e0f507c0d41c256103604 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 397498264 1250 397497014 397497041
    0xf060a050402010915030b0d08070b0f04121404080f0c010f09030b240d12020d0201021201120215030a020301140d02280302030102190f0206070806040507110f010c03 73
    0x1c20005030703444020032007994030181040203102c403e203108400130070303d04490b543c00261001540040c804c00d000600400c901ca032890030300c15078911031070702101c0e40152401403043c21083c01c80d40d800c90144210205102d00d81203100e042540c5e91404501c4c1150180b41908542c1281400020079603101000c46950340075810202c2189240d07580700d5245c030074028010702c6d1352f0b40da482d00c0550f1000503800c18100600010404480d1784480d0800e03c0d4500b4251080754050312800258004460040c000d0b07030100e0307141000c416000d83c6862024481c0d010b43c0702049a015500c01c0c01008010700e440d0295005449001c1d00584070b60404175803207007003244180501c0c4a90382654880f0016940d640c040101821580c2da1a88035081ca4034080700c080000c0c2e08025419400400e2082240802105003100e4420a540e141d99041c148842a038445000307560040c000f40030080001c1c90390810b50421604842e561801c102c956800711010760402d4100030b0344800c1030751100c800204d5650325001d40000c40703110 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 397499514 1250 397498264 397498271
    0x1101030c0816050d060504020c0d08070e0a120515040b0402011b150e010f0e1005160807030b0a030c141f05071106040306230a1e020c011d0f060a 64
    0x160901c000821110114100311001960728440c2e40e41d50000401888054019519049c04000301a00c4800e05804c110002e2840c13400a403205228004105801001400c400211824071518a000c400d0050f0255074a10642d050480c034500b810401500c40d60085032400114100792000402101240b11005046000c9290001c00f054020b410400702400d1003000041c10b0074691312003400350104407182002c003450004e0540108a002c00c0380010300e890312904020959500410120001212060b10000f43d551000100000e002e0750068900d50001441e407100300d5540c0d510001d130080c064220b0303038000c0e01c0d03400641154140800000401c0d10010031030002440c401d800240903004010000d020048099026a0240c0b1140122009160001001c1c05012940b00940c40d900c5204c01442d086a5216400074030b40071481c1c803620907007403040074049a240c402556041d01942103a240311940d9542d41c001c0203020907400c80401500c0d98000054042c1d0700113400d040341000e000501072440d01b0309 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 397500764 1250 397499514 397499521
    0xb010902071a0403020c09010f050f120303040f060209090c07060e070e060126070806030709090c0e0c13061116050a15020712060f0b0303161401020c03071101030c08 73
    0x42c6041c03034204980d1100300c42d01d80c580e00c0303040491400040036202600105000300101d40d1070729072200351003911401c2d10b002820b10350728801d01c00317565003045c1a60382681051001ca4001407440c2d4910a40501584001d4103000070200041e40349002541d44070a180c3c0000385d0181003004900581d6160111807024155a03440c00400c0300884034000d111504008041e0200c0304164119800d44500310601031a4041c4c5140c0300c034018081c5042556014840e1064000005104181c0c1c001c810034141d00c6000044c41380d14101302c16800c007101405000c050281030000c2c51301134450a030b8001c01072119580380c0400050442400d82080d620003400301d00341081724004c0c0499155219200c04640c0c014510440a00c10b2100803410001c681d0001002d1001c500404802e12510350031052080c89229010442d135001c0c582016624400d15000241c490b01d07084001000c281c40f2041d50302c1c1141404000f51070070045e001076506603403110008640350900e2001d50282c6590500c55400d0b4040070b818007011604 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 397502014 1250 397500764 397500773
    0x60e0709270b06010c0b15010801080f10020304020f03010515040f02070206030c0a0219030e0a062f0709022a03031e340e06030106090e0a06030b010b070b01090207 72
    0x1d20620140c000c1c003018010400340d92084200c02c400381c0d006011061039040280642c210507810900030760014031a000080748000380811444a082c4c0500000c03e003490004803480d000c0d4100800699015010001e07806141c0c9003070007428851510004090340e0340c80c3c082c2c02c01c0103d070340400100040520510040c0010b883d00001c4942000c03c4040654a81148000882c681400d0030407840300d0701c0b1038243d810704050f080079105000d0042180c50300e003025207410080390070765950b0350841400441e09004040000040091550702c0924806483c0c5103511002c01005991040c40d1034280d405015140300340302031301100040310741c1804d94051842c5090906003202425031080d92221100c2d42c0401094072008040b203200b00c0756151407800741c110b030100303107a44401469100c406004603c81c500c0300583c91420500f164140c2c0e6083d110071000794180070542620703500c020100d03034082e5a1208080042a07000110a0003402c520b0019541e0b0f4a2030300e000c1c1d010348410b03801040c206005002d14070008 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 397503264 1250 397502014 397502081
    0x5060307061e0e04020d0617302d091c0b010501052d03040201110703120c140a0501020403022403040206090303120705030105010e0f10030b0d060e0709 67
    0xc0981e2400d007850366a03c0c800903009105030801e1300b42252520800007460650880c40f40d070010101410350b00203083c0d0003ea201201c4440603000000080e8684000c510300600000c0e103003440301280c00c40c07091104030169082e40441d0212250801d000401c0401079442c122500c0c0b041110020290045240740e6611048815418041c0b5418032030041003002c040706500d82801090280d144003403110120200380021a030744142e40981c0080d0010aa880d4200c00c002070550417a03911022650403141810300c12181241100c5013241c02d0030903404203c0e43d641040110301c100740d000e180010303959071a600c1001200162091110321130080d035003601205101d400103882c0c0c000d4050b0f034050380c1c61030003000283c114818a05038040280c451028406182e034048080d506940d0b00f070b00d8000f50046403408100400c14910f481c25803040101d00e004e10307002e1107904450104200540740b0242d5501c143d5400c0c050b140244a400816130044604124600301c80c000c00b04403051142d13440c0001c0c001003030030340b03a80e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 397504514 1250 397503264 397503317
    0xc06010806180f06070311070605100e16080c090d06092a060203040902090a080d080f07032a0c080307030c08010b0c1e0705040603080c0c0f0117070c080304060506030706 75
    0x3c6c1640e400d0a14803554036001102c14095200d0803c00c00d030700c0c14005000c40c0801c2c1e40580e0380810340f0000000d50501c105142e8182403500c985950102da034852030303200321036840f65228a801204001001000074000d0260003d4103114034031816189514005982c0e0403100840c0c50b011150040a00300070711500130044a0948010700d03000f581d1010407070b002c5000c080081c4d02c0349206128444003d411706a10807011405050304004441240c1c45402c0c1c00c806440c485a012906100a0507505a544a01560700c0690100d5030511042d0f4000f0781d15461715641049481b04042600d6401c2c2c40d0174607500030f103100d02418090318290300781590081119510344001140c0300d0f9260140e002821058020007154004090041060103000c0e02ca142c00c01c8030340c01a0042a21921030100d01803050301d4100b4100c526004103950b4125102134801c1111181c10000c1e100c002844402402940170074110002148100c6c002c010215050030140300349450940d4560200003040840d140c03d03010781c1c0c44904032808 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 397505764 1250 397504514 397504517
    0x60e010e04060603140a1403040f090203060310020406110f06010f0b0c0f072c040b04020918010504121d010f050d0b03031206010210020c030313080c06010806180f0607 74
    0x105541d9403621000030b02e1960400b820130500c10104034085100060040d0300305200e80b100b44580c051140c00707156079024600a0001c00c442d007100900c03401490b0f501941d0f2002004044401400290074204100d1b40b2a42200001030314202105250003001c10400f821a42040b005140562611045441d14101801911035540300010428800760b010051a040700c202d42080e1440c451b62204502c1d5921103254001c842481c880740da1000c45146120307198415070300302c0714040103699030380e00700a01004000e03c2003094821405004104050034800d0900c104e108101426003080c0c4a0006409001ca088008080000d2030740c03c542d05903480001c105843d5030038100750703880e404a0303e1140050103c0c840002d40504c80402e05207444e000c8410360a0041800382c00317888804503000c0290059201d440142d0b46c240c0c1c03040001c40c1c47c0302c0c1d101d1031464000d0b000c2c10301d55041c0f0b469410b000382803c03420f90001c1d845501040034020141c0b1070000d0300400b40740c0040200094840c0701401b0740c595500410000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 397507014 1250 397505764 397505789
    0xe090f09061b091f0908010213050418050303041104060b031e071b080a080c04210204020906030a0501050114160209070507020607121202070302060412110f0105010504050a060e01 79
    0xd20b400c0408080d5001d0000092020700c81003401d42440800c00c00710700859000071410400090b4040c818802c507240e05c45040340d200b56041c100300911011748294096804001807100b03009010030000d0003d540103d00c92581c4031500700e40c550402041da121a00603044040d400c0052144241c101d801602c60b8031400000154903030b46d6141c042e1641c240c00f4020314194101c054405003044071804c01040c2d02119030b203034010241c132a4120608280200e008030002c22510100078620581c221440380c08480c40100054907007840b00c008075001d604180e8641c85a5619100140110361b0440c0c039007040342800c3d42055041501084000524003ca4000a4020010031021400e41840b0b541150805500a0072f00c1d95516114030f446503001c80009002c50016207a11090f420080d02c9000b11504260140d004015907200c0d902c03408003c0c0340c448451014000341082080e440d404c01d1289849108905e800024598940f00520050b038400615600310320f450402c06200d5441110b4202c3d0654240c0013804 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 397508264 1250 397507014 397507051
    0x218130b060c0109020a1502120c0c120a0303050c1606111209030a080603060f01090b2404090b040209090f070c052b030e030d020f04150e090f0906 65
    0x1000106280c1080980040000503140d541260540201100364401d4030000d45081d03a031242102c2038031a114102005800c001c1800b20340012100141c2400d16108060350210a00b00000030816218040c04070901d4206032000f0040c1030700b600c80d0075440b180040280745031221900d01d48210000c21000185400d50b258044002d0111b401c080d2403d840200c50781000030300308001c0c595030f41e4100b01c10480010380184002800c500300844d42d03d0080c0711042000c0dc1503400c108100d8060000400450b40185407030440e003400b0400c1e0650808120320355141c050f61681068060016034410321049800b03140108070240d85900c403400e8190340520f028425181545038040122101c890200c000b4203244100c0b414624a441c4000440e0014010300c5c0142000014109080c0c2c242d5031403e00c90421900184880001e2952940080c8108101d6a2035185405d0300c80055012010580484800041003a081041d150508200e21900030700c00d110642654078143e0306007955014000d00510000c255072590 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 397509514 1250 397508264 397508299
    0x10c0c030809120f18090f01031403090f060c0c0a060338100203070f060501152d021608060f060114030c0d02090618031009031d01090b030702010516030218 69
    0x3c0405d10600070000c030541c2c104121107035082c420a00040c3d405006a040c4298948400803c440d8800c40241290400c4101d210401190341c00038a0845030502685443c030009070b0b1040b43e81000303001ca1361400156404000b03000c12203055000f4814030a114000d094410752511a01e5000b03013803c00b01c0f80c1903070080303103504102c2c214000c0c04001404a40e44540110422801390001381c1030320711406103140b01da41c510004981102c141c0c0c0780807000c0c0500c014008403d0801382c2580b511107105004a440c4e03240a910b107085150352913130100c03005402001c2480003402d4845000b5400400920300000240c2c8409040c124a00c000b800d00d8031103c0c800510b15950702055010b856681c10020110390316042c0742a04d00019002128004d031290007001280f2200440912801e05155010fa4905a10180e02182c85000c5031440260a06200c4560400100d4070003050065100318203990000c1840d0400b200a0608001035000e004d081c54010300001590101c440100718104808440c907407100860040c2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 397510764 1250 397509514 397509547
    0x8090613150207051504081810170c16030804110f0303030a0c1806110705060c100b13060f0f0602071a0a0e0a092004150c060b03010c0c030809120f 65
    0x848400c140b880208814408508080c04c8101c18440c1c101c1c2d819155441042811004005c0c04004190751480d581d0b4200300201e007280e40301032f131050300c186001c480f50b000c00a000403200c000c60000d040d080c1040200220445003a40c508015070b0032140702940b040000361a400000e1620b0b444590b50140c4a00e070303170302c540c130048451400201c88100ca540c40340c200503c0180d11502200703080c406c1200005032400c04000311920a225030020340b0b2141d40710741002000c1c100b03004c01d043c0e002d484040d11044519551240100501082c40e0b07140080d40303003000117184840039500000c10340d0001402001320000d24040001021001d8090b15035541d40301d0410754401d003000c0070389a0801d80e032541c04505090164010300c04003009034901d8500c00c4400f04a00c1c07941c0300e0340c01104400d1440c010116001c80c011443c00401510500d1701094448420002c2400c465407008c00100084400702c8a100741900500c48540242c440070141a6081c0c01e15850165441101c0035480c10f00740c0041c8900007019940b5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 397512014 1250 397510764 397510783
    0x2b06062007030803040303050702010c0e030309060702010507020a0b031b070218040302100501030305090111120702190b03040602030403200601140315010b071a040b0105090402130c0809061315020705 88
    0xd0f041d180d04160030020000c100850305403000d98602401c2e03440c82d6001c4c5400c0000100010021880c2c60803100510100b80c021540807418058184804401030752040f840f00040c0c070004003030315103d14003d035400340340c0e06040543c48130110781085090013507101d902c004243c4894041984080346c40b2450100d290070f004d116443e881c0b070f01d40301c00801016400b00c01030981c508241d951542c104030840300f180c0c03030b02420342000c4040c0784100801401400c101741c1141e200058103200c403034410380d01d40c0b00d21030950085800b100c40c02e500004020801d900b005986001c0c0c0308401e84510f10010780a2540e0b80e0300818029000140c07405901003410340c1d4200b02ca0049148007005140141d690b0700300724a84e9820101048a0b0880c5007141e0030401703000780244622445e00905180d501fa4607207028440c0f41c01c000340c01a600b0800701d01c400b00d0300030b40c41d004402d44166150340f020920f2818184003400e028000d030140030f426080309411004a0034403440040c07800b00c40400181c1c1c43c00c452a140b8a00304042 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 397513264 1250 397512014 397512023
    0xa2604030b0615070f0303060e0c0f0301030b1f030302060604050a090f26070501090b090f12030910050108030a0908010b130b0f040e030d0c05030f010b07020a0305032b0606200703 79
    0x41701d10030503505030043c02c11990841d4000609464603040030910f4001d0036402702d8030040074401040480c5907409080e4004156091501e40801000c4d00131a034088260000d9025a01240a00c990350410740300701ca41c0207100b8881005182170656855000c52a0000003030b002c228801c941d80c2d08168021a24104400e405401c281d50b9541c43c42e1071400303821083d4ac2030302d400300004002284d00601040c240808455840075200b0344880e0119490b03542c00150144600744200c55418603425880e102e1640a003040380c5c0216142c1a888600420b10721203074000c0d00044e41881c5c3e950030b040c3c6911181d18240070209602140201c10341000c541c0f401c03801c581e82580b050801d5400c0e100c8820101c010070030502d401c0e0701400500c850001c10b4480d031006a0b001c010541402d00100700ba0111040501a80c510081030404c005540391940e41c0f031500241c0313056140c1810a84050034640f1944040103540003078803014005e0038504a0068550b450021007501900701c0c44646030b0640405001050246512 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 397514514 1250 397513264 397513283
    0x712150512100f050f01170f160905091c05070f12030c0f0f2109150b011107030c090510082a03060609040204020d0b030a2604030b061507 61
    0x30200040d0344a1400001c490b040b460030140d1141d002d01c6010342841141481c0f0414266440c1903100000c1d1150b1002000d01130080c416a030b102c40e1002e112100c080750030343d56405040341c1088613110490344007400d0100140d1084804502c0380540b041c0480c1c84c0c0d840c41c14400d4a0710b460381441e01190a07100001000c1d516170071101d01c0030381c0c0c040c0d0102031040d00303955a1980c41d2404680c152007003807450201c0307000718045400c1120b02e8003001d80917800b00e80300c3c0800400c4106050303503500e10004141d429000710b42e0f00e600c681445c1d56440000e60121016548c0104440d6166407100c44034101d0600a80300020780342c20000d800001c406031000010035914040703c0c0d603030101901c460400d0701c912000d03040310000b019030400a03240009a039801030030b004201803081d403601e82c00c000003580012855103100791102c04080d09580e0a115960489000c0ca10028a12703201c41202000f40501c1039800d080600244001d1010468060100b42c1c010029a256016a52203407941500360007507040041c41c60b5034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 397515764 1250 397514514 397514539
    0xf090a0204091b1e0302090615030a090312410702010204030c051203031801200705070e01060c110103092906030d0e0609121912050307121505 63
    0x4040100000209619000443c9680304d00b504501900c8404005504d48403010003440545440c1010b140c1140c3c004101e450510840d45582209400884c0d0400482d80e4075541c80f8181030b000b4040c0300740140b040390f0800c501e07411003501c608113031141c80381584461004c0305040c401d4122007800c1c152003150303c44605a80d14140d0750081c0070390300c1030104886038401050001440d05069006906440000c0059070030f550364940d0404e19011a4240710344250b40b9018403d0100450300813071000e68400310350440e6100c00303508080b89850050303032189181828800040083c0303907000105120096000c02e0302c0c1c80d000c15020048015040040c005010200c0303c081085107401100c04840c2c400c0d11907020010f203562114100b40d100d030707420008003020682c060790100c01c41c82d2802c000c0481c03060007403000c02414801c0f0350342440c01c64031b0700c01c1d0302240f4480d070400d000b4042c1151070f070310901843c1e2510b00c0c9145450207006105000900c040c4d10003a40354404d81c0b8078a01c0c0701040f08058100074020020901 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 397517014 1250 397515764 397515773
    0xe030d061806051504291b010b030a050d080408071e02100305010509061302040909030f09090e0304030b0a020c01150f0f1d0c040803070515070c0201080f090a020409 73
    0x5080c051201c400d1070140c00040e94100b08454000481c50020150305142c07074040141d45c04064200c07610324200c1d40310030184000340c004003e840100400b1136440c502c0040c0030041400c5410310a071130b0384a80c2c800070300100098400500b82c108100c0c0b03858440c015446a20b03011a89000e0002d00400700d08850b1071180021140c0c218915480340200d0740418221648041070f0116002801059000350300040000c0300c5083c40c00722a40c04c110105801450140ea41c400b400803940d004030210001b44600034040401c2e980035580a001d03080411701017180e02d9254000503924405c034400141050206000220018419816512079295031030003440b40d4403544038400d07000f09040c0643c0b102a0031801d40416015541d2101d0380550351902070b030302100312106541038142c41c030040410000c540c0800010800c00c00034005041d840780b04d280103211981d19403466a1407844001c0407a0b08228003e005500541c1e4402a81a04101c80b065581c87c10b07100e441100c0d0801231000780103034005040500e05002c11 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 397518264 1250 397517014 397517039
    0x201140406031a01050a0206150a03150b04110c0303010e0c04081605030d11100e160608060a0e0f06040c09080a0b0417070201020a06020f16080705010608031c0e030d06 74
    0x43c10344800045100d00300394015219801800410781c010b80c8004002008030340e08015041c001d14000300b0071010309941c0e9961a0050480c04180064641c40300b0310020581003074001c00e1030000c0e60b03500702400c0c01d0b988020959280814840d070030a0300c0900010840cc06591002c980162414000b0345440e13085820904c1000c1005110b164080d105648072050590701c2003e40d443c0d05081200030b000044080f0300c80304040c01071884030354004d0060b07140c00a100d550501581c1c0081141c2d40ba102100c0c50410104100710149a01c5100b03840346140801420702d0400f001035501c800d0881c0c000405d503041150441d059545a0403145a0744104e50101e01448007541d5401e03c0b40c0d02c501031003c54440e10340f40c04c00c03450082e42e5000b405644010114000141d4907005009114218102d05040c0b42c0c1c18107040c60303290031620041d070307100c08002500c0052003000c0c01807034041d2400000451a05280c0310582109078050600c1422240d95101c0240c2c0701e8100f03004541541510500a02c80c50f1388603640d80154 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 397519514 1250 397518264 397518281
    0x50604051b010f08061519020d080709030b040609230705041503230703060605010f03050f130f0602030c0a09061106070f0203070f0b060109050604080304030609020114040603 77
    0x611400c00c1445001c50703041d181540101040c0d4070060f14142200d0169451100a8a50ba900070300012401c0b5800c80100050508506a030301c0284006a01a20180c2841000217145042000c0c1d80b04011010f500131071243c0840e54090b03606900c580e202d08181000380030251000f80040f00d010b0550040105101c440a140d005000aa561150b40e5000700f1013281c1c3c1100403865281001e65041000c1090040d140d42c0307140c4c224410381981312072280018200840c1b0742003160041e80e01c00040c0110350b8480082d081038134142c01c0400040c20500041800c12100402c041d8004144084000800080100f844101e59111a0954403800c1a40940c441504690f4484002800412000842511500f2020911400c08014050b01d0b119040c007140d601c0d2100380d10809604c800c00010001500e1041c0d1001014014900740c1d14609207100010451030140d8440745c803894003031105100c00c0703c0c040110b804880e2f0110001540500c03600c0140c40b014001958407100004c0800c0004505425410034510f = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 397520764 1250 397519514 397519523
    0xd0305180303100e060d0519031e08041419060b03150f04081b0d02100515030c06031b04081b101707051e12070207060f0f0504030609050604 62
    0x140010860945079280801c42e018000100320f203504110401c1c512050b150485c001500200e803d00454540714640204140c0030900804142904800c2c07651220503008403031403800115010b40c50b131170401415000702400150010180030700c48400d9240c10040b01d00c2c26042104201041e01190821000420248000c00e003c0c0c09000d8010310004943c480c00c91040118150a00c5261511303150204c0e03a402100c02d10413800705134819100d45ea01c040080c3c072201d01951b40185000701c602c80041080e91805000010305171005c0d0b43c14911550041201ca800caa07058403050b840b60b0350f000490a1680d81004039100c0e1100c0000c010a0882001c6042c100450b84074000141d140b9082c0c051080040d2101c1e10400044c81c24a000310700103100d0f13100e0b283c002d02603113003281c00e14140d8814220703d10311400b400c0c80035800000c0c1803452000c000c020268401114000780200c289020f40181102c03103491076070820886080c0303101000c5070150050320003841e0021810019556a2b203070031555124141c80556 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 397522014 1250 397520764 397520791
    0xf101d13060906051806030307062003090303041b06050a030e1509030c191707060b040e0a03110c03120313150608011811010f0212070b25090509090309030d0305 71
    0x3106941403005c031405801702400542c609405921544010481c000c800e0240c1140321101044482180010358001c40c1d03e040a0f603501d04003894504600d000d1030402061840d4020801c11440307801000b69002681c0754100492030051003900c09040043c0d411503008038441d00010b10a600300c0c00006030107000540011102203a2055414051141906074003d048a045c0c014148607815480c02804103148504004105005902e001409480d5403550180385940702003641414558007945201080d8070440241101c25000b1000c01c0c4c4403c2c3d00c4005624001e00080031500b091120201040915003203032024040c1c0c0e0100002d075025108a11400b20590b00b07000b00000c49003460042401d41c075900015000d916581c940c010349122610840020640c06004043d40041424400806e04548145010400c40c94035a10004180325140c0c0100450300060301801011900016250150f52080f03030300744d503255190407003d031840c82010300315a05401084451840c0f25003641040c0e028003503070650708 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 397523264 1250 397522014 397522039
    0xd0e0a0f1a090607050715061e14060f070201140703050d0c0e0f1c02091e0106080c0d1109060d06091107020609100e060f03060f101d1306090605 64
    0x2803620714003034a501c81d030364102802044c51075000320002c01d01b0034403c80304003504c40d801902000c1100e841758072465404580d264000b50305228210039001900e40002c4c00101180303040041442802500881021200001404d40a581c0941c9010180c0007005151940d902c2007490000d0050300031450001d00203090020550007940240ea4140300303100058158140c10f006541040105039141001d451001350440c96a009030b114060b6083c40355064002c801f0030401d00c1207928046410581c4541c007048203110a00184280f03050480d07007070082d16000410402074070b18140141c1d00c120303402c40e070340030070300003074100c2c08036055007042d000ca82c0d1284d410060721844c9103880d0030510428100a50160080010305583e2030f050001c2c0325801c00703900e032411500c1d00040220b809548650584140f1180100803c1824940b80a0b41204000d003a1007485146880b400d0180c00119900400f9803000004110542e0302e40f104460801100c450315070038006d0694815514002346440d014481c0240c1c1002c005 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 397524514 1250 397523264 397523303
    0x8190806100c0611090a090e0c010206012301140d0f060509101707080703050a050c0103060b0405060307020a06050117250e090309090103150e150a020d0e0a0f 70
    0x40c040444010b0b1140500750800c0e982e000c000b007101200b4600e02d8181849a85050344031090305001608518600080d46410100340d58035091400c0380c80f904541c81040140321000b554071440852004e41c01500d410701c0061401a509401d106040d50000c54001c01d10745040a03880d080700203401802030302008443d0310340050010352101141d001941c88500c010401c084a03040f8204680f120f80307042a5000d03c1c0e22030000a007002210303842aa000d9125246020500c02c0a00208101c0c0d44242410081c0520302450542c8a0046100d960301c10a408000500c016000380002c0745140e034494030800080da100d00a40000782c94055501040d4400c0f2450b0001d40144c95200c0d1a20070410342882d400a0b2a05142c03c0065400170840300071b0340401e010096958880c0425a03001c0d40c841c0404e011505a100c101d20100d0345011041906075004be8031000d40366200c502015004414010050303070701c40d07075540302c68058044019406424440d0f404940244210f55449103100341c42446100b13101c0070500c14 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 397525764 1250 397524514 397524529
    0x40510050f0a21030219050a0c0b030103110f040b0901082a03030301030f020303280806010e180c070203030d0615020f07061b050d02010b2407020d0f08190806 70
    0x903419000300e41540e41110f4500e952003d040ca0751091040f0b4072010f0410031612400c3d20100011503603079104446120400c0f0b110b64504000c1d0070103206079070844d851520b4041c50900f0404500d40501e0061444501e03a07240c076042070340420409442c1c2d07141c0d942d40392a0550ba40b40100020765a20f240b4111001003903500c00103e020701d580040042d4150b901f980c4410303402480c1c0c0f09003280c0c14403003000400c0815550780f00c01c2040109481c40e110f9540f50244024111400040005042041c904403290140d034540380034000c030340c050362607450165841e54040c103a18803030088042c0d41448042824a074104003030700b00704291980c0505c00c061010300d10a040e40c0d100f01e0203c002500c0e41000b40c091040d01c1c42480c8c0680704e4601c2140000c0c02d6500c5445041c1014400303481d51005035143c01101c2c40c541440386e0000c04803400411140602044081000c0c510b00034a60024401d05181c40c0e00004d00001c00c03580c0c440c0301d401284541d61040701038600f240d42e084260b0030740d020a000706c0000e4400c0c640540c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 397527014 1250 397525764 397525769
    0x3050c04050d0b0a02070f08120f0f040b07050d180501060506070f030809030702040e010b0909070609121a09060f011a16060e0f0a020103060b130612060302040510050f0a 75
    0x402d40b95040d0751541d18800003580080034150a10b0b42809802c020409a5213070505450040328202e80d580740700000c2d41c80c00800200b20f00340c2080c00d01c0034000202c19500000d42e105400c4003454849894110307007122a4072864004951030790610083e610340140041003001e8141c0320341c00811115a403101400b095004000e8060000d8200c49000c1c3c001c680154012139104004500b0380b446c001450340060704903007014603404030b680c0d50349a10200a091080c0c0c3c01d07070004010402804081d00d000401415540c46004008004000250340c00030040a083c00180f203420071500b603960751401c40d040347e9407140c040300c1160110018000000d00703051a0600925001c40440c00f00746010803000d48070243c400c172640c040352900d03540e0704018501c2e401400104d45600003c009000300d00403900005086d10640c1e0400c10807800c007007046080c0c0c4100000c0c4a011940181880c07072180c1550761501c00180301690010b034010307040400300f1003600e034400e0b135160a840b401c80e11400708c44100ca0a1111a284a0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 397528264 1250 397527014 397527019
    0x307020706080109110a08070309080d05010311030615100e060c010c0f0c021305070e040f050915430507120810062a05031206010f0c0224071203050c0405 68
    0x40080c1b14080703100304100c40d0b0049180c10f0125200e4039a40c1c508015901c40e01c84501c0b01a41c407401407003040413005034083c680f8021001001f0504000300140c59030052500c856110b42e0000d004502440c0c001d410814440e0801820151200d040b466624043d000281400e0001820210101015030251030094412600070b0552050150030007907020083c28090035250500c10707005050b2051303541e94015076540c00d400c1040401c02e81028108a8a48600002d0514960010004001d140781c8148912401c1380040302003003056564448410780d49880122142844441458402c0e248982002c0100440341c440c044680404025500807255400c007030700c04131511040700303400b0800076201c0d1621300306100e512540b1040904260340c944070b814038908400c8407550000318207141e80c06101c003203c55020302c080c03d01000d080304111000740b0001c41501d000f0701c1540960454a083c690446003080c602030325140c066515512810304960f413210f50007030400024144000265018001c2c800e440446201 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 397529514 1250 397528264 397528267
    0xe0109060f0810051f080a02040302030c060708091e15070302061602011d0601170c0d2d050a02040614031f15180f060e0a0506010c08030702070608010911 68
    0x101da41c00c482e51500545035074195200c03564042110b5840c040603581410208100c04181601190042e000b000001d00400500e4414042003016840c0418555844113046a03590341d10f618501d41030106014a00d6601d800040c111100700f8103400c540c1e06200200401c95014508031145499487c09126092000300142c0100003c0344801c8003800301d00014501c1c40c000824044187c0402685c5282600b43e002440d50100004010141c903000c5400c0004c101003000c0d0482e40e00e2a000700d600d211030310500804a8900001004a0203040c110488000444030080309420719282030065445071800410f0b48240e213050030002e1040d800079070b13502e890f14004d0042c201c11034880c0c1b818258081c0c00764540071226115100500220b16400d002d41c082c10301080c1000420000d51090001c42c1c00c0c1c003d011000038989502844004283c42d2400d40c080c030035000c00304480e03550340012500e0041c50340c401016003501000340440241c000c9001c00503102903035282c0e9101c1e030780d400341c0006640f0710350498000b0020 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 397530764 1250 397529514 397529537
    0x1b030a1101020a0c0204150b030c1c060302030d200d0305041b051c03030e070f03150b0102070509040809030616030c1407030c030207120615060f14030a090b0a020a0e010906 76
    0xa00b9000941f50709420184200e5039039464690b502c040c2d008481d4100824400500c000d01c54500d91081140700d142200b082041d60b0566002c1f0380d4600c0c009000d041400414681c0041c0b031019003401c0848612181c050754952900d0410103405014141c504890203441010300314604483c0c5002301048038002021641c0d000d011000b0220141d501f13450907400c043e111408002c05103400c201c83c070002c1200c6806494160b00d035003020040840c540f241d189031103040038860344203a0b0f4006550b20646004803410700d86a141d9103407a0341c0c0c3c0c0c0b040815280c3c040c01a030f01008060b101c603e020030b01d840a80c0d01d040c44505c003001c0c4100c4100164042e080e0210f02c09000c020082441600d00d100300034880d0045a102988645075082000d44403141101c003e41ca07035110b0500d285800e03c904000340307980d0a040700107444001001d0920310141c80e9510305580701000090400c80c041e040310900c16040718542002c0c1c181a52800060b61000c000700010030804038041b2025441840039800711103c940c0c50459644 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 397532014 1250 397530764 397530769
    0x1906030203060103090b09070608090d0e100c021003050a06171e0c0a080a06060b0a02061503010b15070215161412190f0503010609030f081b030a1101020a0c02 70
    0x40010300b0460400d039460309480b000651001d003003400351103904010a5a146840001004500024402001604807805c0b040c109500008590310904049036154119800008101c0b0b100d004124083d5100c14281d12010303000c0d4140d880640254070403041405004d0712041c500c101c40c5000b10000326590700521514141003210004044c14030b20344000d03a070450000d500000d5014107039801c007070349580000d1044000c210451040e08000c00101c21003d0800d9240f030b00c0652580d000414204811507003200c912600c0d0b5082d070001d210b40c130000384202840d4400075000295500f1026040b40a000302a00404803201d005054807248203020030394040c1015180d40d02400d2441c00c22044419200b0129030540248036803014001c013a070002d0b0707950000020303240700600c03c10b04400d02100f0300c20b00300700510520794000b52050030342e40c0044280c60705407121300e00702950384101d88001c1840340c5240c00200041101000414002c0410f41e5010109809020040c0c07c0b031092011040c00318003450503000060 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 397533264 1250 397532014 397532017
    0x11409060313060507020d02010b090610080406090519021203070807140102130909060b040b03210c0102041d1b030402040504030309020405040506070912080f0313050a0501060f0519060302 83
    0x2407030b94040104601c0860f911501510004c0d43c0302409a001010504026a824400c1c02c0a40900702c07480300d09420003101280f1000b501004820800c20047d001030180b25103a080b1000259102e0102c07031240700c01001a0b031807407407406812841803900701c0091200c400000242e0b0340d11500030400601d06080740d0350700c055000c4104400d40c0195020b010b10740c103503c01d07101101d005002c3c040d00400c2c00c824514091003250759101071588990701d400180119902c0c00294640f0038008080b804d05140585d4003045124065841400015800043c012440d50034001109032280b54a510052941c1c84030301d40524501c02282e4460303520481480020058a070a421050300705009090009003c80c203038000c201628001c44040d1140da209000b40f0130095446101319004141c0440701c10301c411540d6813021203600c600c040804040f800480416031410409543c003030b503294403c003100d0311b01e00e031031400340d010300713141d03c40d91200740d900e480000f8450400a10710070061603c56006009581800750030f5009 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 397534514 1250 397533264 397533271
    0x60c0216030510240f050916020607030b0a0509100e1b1c180f0c09090f08030414060a2c0309010c0507090e030c060a0b011d15040e150114090603 64
    0x800030000041c613072107168140c01c4081c04218400f2a041d900300003d1102102002e0880c15070080000e1801d041a5400704095411400c0c0e07140100d9421000300000302d80c0101508442d078000040401d00004014a00c0b80e08103c1e100d103015000c00340d888581c034490300019402a5041107004004907040032400c2e00d05055043c81d564000580c003582c846000c200030064107021121320005500d020700f4001b8030414680101100001400120640e569a426070103403800e009000320710110208041000c0c0c81c0b034171044a030400342200c04524081e41c51001816004944811603c07000b20b00f240e080000c00311424480350a54000d61504560100441d002e145074141950223026540000c5415400c1740201954800340800641d1030b00189a082d070305080025000d180908e04e48840303521640d800049504161071a4041416010400c00216580b80100390340000762100002e804134440401c400a18003d8440800071125115610010340310359010750304420030303100144243d448a02d0404001c551 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 397535764 1250 397534514 397534541
    0x302150c0319030f0e0c0102070b070609050607120b04050c0f0307111002040501020601050f0f060f0d0203040f110a052b05030a0e03370618060c0216030510 69
    0x18294000071600040300e038031200c2d4400262605480700480d05540a0f00c80d84070800310240c042942078100217507413517410f0306c100d14201c0801b06641c400e00456500c43c861080d0420181c40342c503e0580f40080070301c0d4102550307803203041c580304810141d800c180c400e280c401e2800854052410060080600e401c0d00024000801c0286002c4000e981090500980301404410007015840d5420700e4000380c181030051b0071203400340a06015495446e40c44031003c1100326010b03a402c2e540c82480449091040c800d03002604100e0380000b06110030450b9407564141401c7c001d24011244108034420800c1d1000c140c03040382d5005602000c0306002da4031211181a40842c01c1d503496000f80410f0395210706541190450708041801070140b0304442c241070082c4040c0d03102e80d140e88184101c0c15000d580000800020f0f05601c0310750303140c03403c04200c00c0350301590205016125505048005141c800c1c068403605070004014028443ca4074a500c5d0308220070025070798010050248001200300000c0185202c030003070f10 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 397537014 1250 397535764 397535767
    0x20d02030f0106080d140f0d021b03030415060e090c040c0215011806050a08031602060d02070b0403111b120312100e070e0121020d021b0f01060302150c03 68
    0x1d034091424070400009164802c0502400315298001400d800b041c81c103007442e1110b00700181108074242070200c40c2c03c3c0914840041e181d0300844441401003040d0b00b0840518071001003803005110b48001d548506e400007030300621801da110100c002c010700c0265007030100755001070340b455018035194106010600300d510440705202ca8112040701c40b44002e80c4404078400d00340c0200740070381c5454050308010300300a64844a03c2494148040d43d203220303d00e40c60600c04801147c40c01113540c1d04c1c00305ca800e001110350944d150115400d02c40010281a2000c60106103404501400c003c00851141c0044940318802000b441e10341c010300020a481081b40001d60004011819002040100c141e0061000ba100b60650074106010244e00c2c04000d484074080c0b00e00310a840d4556070b4000c10000f01c95100340f1420b10401848407144000e07010704200b04030791500101e4100c90254810940d100300310742c0c07142218889041d07030341d5180c00c9803080d020103900801414010282c00040301c008044104011003102d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 397538264 1250 397537014 397537033
    0x90f1404111f030209130c0206010303030903050d06080c0102060907051302070606031b060f050415030f06091a090a0b0d290103060b03160b031b040e0109060611010b01020a020d0203 80
    0x10555088503004890109501042800307480c2015204a82007843c0c0440c01c0041004c161f001940d0b401b0705100044c200754444807981e04043c440c2007030350a446403500050080e2130f210120107032100f61007003c260051103a00d00203440c02c0c00008100c421224058029052000c1e40304c8168040d50081e03c0545041d521341000100040c1c5005c1c45000003035036051141e031024180301004200e017500c00c0c080c0040240501c0140400d02d0030300942d0380058014180010340e04000842640a000741e039200d04481c904d004000d07016507407094000a02ca038803c0b91902841d40d249c0e83c604003101c6c0f40f01002604078003040c040c000005d9000d05040ea8800c0e001c00b12442240c200c52020b144027000341c00803280a07443c1c1413410314500741004a01210f50307a11007940d150320f0030014401e10500006002042e2a07804142e2046c0c1c50f01e280b000c035030103080c041c81c0e030035540d603180d8408101603e05803140f413001403450018880400c00600c43c480c84064143d014010050b11a000c1010180d01c192041e43d060180c00c502 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 397539514 1250 397538264 397538299
    0x6090d080906070308100905010e070e120d020f25120c0b160209010e070e041508150f0c070309030b040201050f13050102010c0f0212030c0c06070801090f140411 71
    0x9002054400e030340309805c03480c000b03100740541c201d240d00c002a12402d003c018084000210645a80501c0343e2030710640d02c54082c40021041e103030083c0b08850070300070821060720440c0d022500c001c00e580002e08840c04840949842c040f200380000c040200c9281100c414000380009451b004c85290180034081000c949460b607030b8519610540d1501821980344d019502181800a051801444c20311204616490580801f810354800c1c070780720300d1285076241e000c200807001403201c1c80040e0900304100c0c1c4051807088410070708138806460304000303600c05000141820880c1c2c422a00038590680c1e0364895145142d03101910078201810482c1442002d10000c5000c19903100640b280c0c540750b2290601140c948000a807c44003512510402c200c05201504065a0000341f01714030312003454005680c954a0182000050003145208042800342c1b00c01e012200742d0186d6075505a440e0004100400341c40c10384032808981d03542d08030842011800c1d000502140c0c2c0b291841801103005080c0c81040303c9010076 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 397540764 1250 397539514 397539517
    0xf03030a0e0d0507081c1e0f051b07060b01090b0a0c02100306080309010813020316030c0902210a0e06090106090f0603111302040503071214060606090d080906 70
    0x9220000554074a4040402803042000c210001e00380d0038410701d482c0c1c09844401503485501c06009041c12660400381d12036015522400090710380740185502e802c00007601c48040c00c0e100180058840c00c01c804160b18017006100000c00083d903507411440c189540c3d44902c0a810300103502410702c00740801c00901c0748206001026424100e0b581c03200440182c3c8100804a000e01258004052500c1000d01205a00000722580303180e090070000160307030300c0039481c0b80a16610380d00290180200b010742d1203c003007000100002d483c41a0803034040141c0b500e18043c1240200350760f44403d503a210455002e22024612450f80103600700300046012003545c3c6200380713030183c151109989695a184200310800842c07088001110107400c0c01d0000d40e295890f116038003050480100d218032100d001c1c6550ba040c0c0da074111001000b014003964006030340c403c0c402940102c540c00039294001c3c8800395074803c03207020400c2481090028500c904120518051002040e80302000b240c65140c1000b00700c100c0c2d500c040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 397542014 1250 397540764 397540771
    0x13032001020a0b0a1b08010e0a110a03090c1e0e13080a1407020406170c0303040b030c0f070605090c100203090306190603060f0905071d07030b0409120e0a1707050405090f0303 77
    0x2181e088055142230f2001c450710303900401180d02207191071403044240403141304540b0703074244c54a00424030890604100102081650045850170600240014419082c0749540c040721590080c0300d1040d9203510344201d103602011030007001403000700030744141d035070203082841905000e0590709801c05103294086000c681d00741e00201440340071080100d400e854100a282007100e400e0f8051410f25180c24034124083c08040d055619100f004140c0980c02c2c000c035400e84417050380242080c8054180041d003151580e0794003505a006460740003500d5141400002201c070f040801400415060751442200340d501c00d40080031201031900c904000010500a0092001d8810010070025214072103281c00f0b441c04023107a04c000c4800d00458105140c95503080343d0983d10001030309011544044680001d4018840703a9401490110080d104d900540d41c024246203540d481900e44100c100d49070303642481c600d14110098021070740000018041402c1903045107822024400c100d480495014840074150782046 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 397543264 1250 397542014 397542017
    0x30609060a0507110312131211070906120609050f0d0315050910060f0e0a03230303090307081b01140a050a060b0406030c120213032001020a0b0a1b 65
    0x61040c442007640d58850250041c41c0c500701001203c0440401d5916030042c1036406294145072000103624010030080e18882070350040c03c518400c0030f01c48000d4080b80c4807041e0007120380305550010a5080240c400c0c501501c01c216983d01c00001c060b5900b00207481811011501d50169100c9440031340801c0050207030742081074402044070102040301c0c0c0d201c2403d690095100d07490030303c00c0c03005003480d81884005803a16450800014002148140c0b22200d6011801750040c020b69000814060300c0c2d1114a08842d52114150042c2141b078a110365030301040d2510140c0740c0082040c200000c4020000b000240c007542c40318040b85910050646c01c4500742080340c0c8030710001e80d00300501c10380f2a100d410f03485048540c00b00452420300600400502480c00303140c0a040da04e0015580050040d01d4110039503198050940d0b50b0409009840104400d0344012104180c0c00b0903010b0112510300040700c454901a070007042c102d841c0d900e40386d0118034090880580103984103046400518840d0f1002c17250340c0036 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 397544514 1250 397543264 397543273
    0x40606090f2f070b0709050619030f0e070b09011205090105060310050106230c162112180b040e1509060904020603070201020f0c01060302040e15160e030609 69
    0x260700d2400402c44290203403400c8100141c00d030304500c0e5a0000d55811540111442035076658910058601250640200e50301090105403c200c00c003d0b03401c0d0940c4500a56030074401c06051600c0102a180701e42c0d1005130981142070103020240541c00544100782c01458401e04455643c1070a070115441a114850310381d4541d0300b0880f41d4103040102c0c1030100c5403d03400b00039a614240c0010046881c00801240d0201c5805442d00c1001c2d600b000c0d99101080e000075540c0d20111020603030024242d910580382c282c407100411100e0340d20000082402e55400043c200b42c0b0259002d021501d09107941d451100c07050402c103001c941d9691031001780010703208000300d101144c1480040d880c4205003403142a403083c1044400c0103220740f41c00102e42d410550540c1c5050702d03511881800c0e40640600034900302ea100f8040740c50700c02180150400400c4900a403001c2244514601c4081e80314100244e50310f030b0f40034200740490307007102c14203600d648418081e00c3c1c0154031500c000000fa050080669240005521 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 397545764 1250 397544514 397544531
    0x2070324020d0608010c050414011409030f0d08010909110405060103061203080f06120a0605060f0d03230a020a1401020712120e07120209092104030c120c030803040606090f 76
    0x1d1040c1c6c10844110305140d030500d0b00c0d00d04c51403401c258000540c0d0411114220781e00704183c1c4c401c140d5043c118002c041d240007030f0356402820303a218200c10a52000a201000004640c401d5106401d0140e03000080456410b04100501000d840c0181c1440d041696603040010300300c400007885030845101c0da441e4186414105d10b10207003208042c2c40381348582c014038003010092500150b4036418550141c000701d0607959201c0096200004150f0040d040400e00454a040641c400200001d05912424810b2500000c129280440c000c22100340d001d41c0c4078070442804a8a110a010641040340c0005843d009045e82ca02d004c54001c55281008540a24800303c600001402042c400881840003445c840d460000c00502c104045400a4010942c00780498440c200501202d00d8031100350015100303000103c1d1000e040781d4050310040e10784800c80702e13000c203c0c40d0f40c00c00c50b4028203402c00701c2a5512821522264007980c07000c3d1040356071540c6c07000c00291841c030794019440052100000010b4061 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 397547014 1250 397545764 397545779
    0x20a02010e1305042613050409061e060e0c0705060423030d1e1b0509030304050603070e011818110c07170d0305040c0308130306020313060612020102070324020d06 72
    0x16401524181e00d17100030b0219182d500e503100305c0c5104403a011500494112110300704240101110040924a100b1140b066040302d08507030041c00480d40c40712105051940c40d040b062045001e50301c40101950014000315011980d201d501c4401c40c4808501c1c2229641c002103450301d90343c820012140420b0b00c90340d00c519000501c500c0b0760101c0400d80f00c00c0c028803524070b0340c140c441d0450084410034480086031095103030b00c1c10001c0e2009020040d01c426540d080031a4040c104007d1501450700040d220403810f100030000c1e81404007203420702e0001442c0b10038502c0341900544098210006180c805111f00c540000040000700c004003410214078248040c20001242031541801c036100625041c0020303c07000807800040801243c0c0c0014035240c03180340e243d0094498465a50001e04100d001000f409813881041d10044400c0d40b141c4020444c0980c2c803a60040000802000640940c014541c100041180d942c080d40c10570841c8c1014103485d140035400001260040382d030301c9520b01c0d510700c814020394 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 397548264 1250 397547014 397547063
    0x300c18030f0b1312050f04030501020f07020f0d1703130b16080a06081b040e07061205010e090309090402010912050708070603050c190311070f02010f030c020a02010e130504 76
    0x5002401500c100c1e0710b03d83c031041101000000707101c1c03c0200000d0155008034004c000d6401942d03014001750358484100554550035041408264420610000011024030740540441862548100d0340060060426102c03800340e04020001c0e01b040c2200c1e010207000903e00900944184101c0c2044841000000c0004040410051058172101c1c50b000c0107000f9442d0001d01c4d039040341d29030300b0708140312001c00010501910244002451500c18020003191403604503e480c030307440b507403c01d0410080c1c1e60350300720004140c01500c01e2925500100590807180c20040050b0354424018100380c800345580340c4548014140082d030a55450300002c006205910080c40000004c100a1030b0910050600010030b0207030b44180c1c0355416400c01004211086c141c0680c001300080c14086100544490807030524a0340062a008100d000070700701ca028240090003482001c2400d44141c0c002d042400030369005681c1c0f400321000003036004000d8107408284040d14014240b289204030050303060b03030b00742821440c0c10 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 397549514 1250 397548264 397548271
    0x30b0406171015030b1b03010e15010c0c03030c020409050d02010b04240521030d0c030507030903050405040e0705150405030610032d140102030106300c18030f0b 71
    0xc182040943c020440304104054166504482c100d01d05880300c4211203c11400649059102000400001409004011601c0c401d4994000e21440d100c44c2100468420340584001804003d1804c414004070b8450b66800c07400c42d201500c0000d481c04242c131000d1901a0510703ca00041c3e446590107140f130704050250b2095202403004035081081807010120791080c4038003409010b9007840e144e00c2004c1c42d4524800001d0003c0c0015071341c0d901c000c110141d015068205110001c241003002203065144130b8807414144940680e00c442c00c0a080000b0040030b880322001181c000d1055200100301c4d540c0c3c80300b254900041210303101d581d6504d49402e05041110003428402c1c002e884500c10008900711007020040000011030041030526032105001041c88425000b41c541022507003240341e41c400540c01541a01d03019100c1707008880d611005100305c000034520703203038041da040211880481c009800500e00030b6218281250960480300e030b000003401140d4016a05030f1120181d55041c4501c07454003075003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 397550764 1250 397549514 397549543
    0x6030507140f03100203040309030f150c020c0a09180b0109060915030f110117090f0f0f120307031811041a010f110f070906080d02010905060c070201030b040617 71
    0x110200b4400007511803055900c2c5100441d000000101003500c64a0440c0246030310030035000007580182000640060041c820000080c5025613441d0524000a07041104200051030040c0441c10000c1c00d00c00fa00e01061441800082e0283c554000382c0080540d9018040c0400c3c000344852400941d0010354840a03940c0001410391802030001c176a01c01520300d121508100315880d4000e4a500484100c5000034110020403985010301084000102c0c00b280011100400c540364070010581c000d40710344c0c62100300c0009a009141404009a424019513403144444c100081c0304030702034152043c10006104100c4001032034800d241101d1a0511840552054290340014007400742e500107030a00940c002c00d50107001c1c12079400e0301003100800c030f1024880410401d071003d503079581e0b002c8405000301740610070075401181041003600d441480380010301c64001000303000d02c0c2c031103d680501560242105a0400d500c4131142507054442c0d02a0000070419032030301500b24801c00601328107090341110b100c1c2 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 397552014 1250 397550764 397550779
    0x902121b0c0a03210203040f0b0f07050714011b02070e0c0301060806040509120d0b0111060601050403080a02011b050316080c0d0209060c06090a0201110a082b0603050714 75
    0x8028030010300b104640340c3c1424070740b6900000b0300080d540b000c0c60800b08602603000108010400040130110b83c0c90314442c40742084c0c0c0c3e4498484841e0496811160300c80028024461500480c20142035046001002400042e10245c1964404081403032507803d88056400050104012200441025880545041c60310300710350400304000c001c02406003010344603540f05d0020440c0400c00384103841d03a4850b14030704580c1d10360140d840740c40035100b100e090344c0c04580b454252401000c1b000c25814400c40d4141d50b40752800d411542ca04a281d0031030400281199a6000d0108040f601420311020301410b644440e5100c1c581103460708940c04144000c0e1040012010503c801c81c81e000f030550700c00162400f409a02d41d01d22202149050203207039803e41592003000b0a0200401022550692241c000e0b0398048000102c0c460180d580c0001c108018492101003042181401001c0390a400141a01c6d8512040400c4500000159170f8581c01c01d40b034a40001d0000c00003142c1c2c0420b41282e8002c00d4601d80c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 397553264 1250 397552014 397552027
    0x60f0206130303020c15040c090605040203060616030212040618120f06020d11070c03060b0312031b0415031a220902061303060209102a0c0902121b 65
    0x10801c1500d00d00001d05040d00821450440e120511a01c1000058200305800c0b0b0b1803e400c120380c000540d8440c2025861810f14041850b0a050080301d05ca090058103091030400005c280000c610304107c416011802505054194810380d40e000b800101820354801710181c0180c003c91006910703d5010514500603002d038600050100050f5008107a0000c1300162900030101114024007840d40c4902d161010001e0f51008000e886e5200c03409480c0241d4041019440d108281580c580070f492014220b1503041c00000c0d04006e1644404130a8000d040d941070905644465103044510405108004a92200030123a03920000201441501c002100e900c035654801c08010304a0040c591001801982c843c5045019900e4031012280d286003d054580d10003035681c105140290402200c29200314045d01882300303c00d1152805941c4a442001d0345000138020320084000640b10002c2280d00d440328110000c3c200d14144003410b0030384810001e941c8540351120310514000c0d10040000c17010481441034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 397554514 1250 397553264 397553281
    0x40f0606020613080f040f0e0c091f02010618050604050f1b2a0607090f0e060d170c010b090604110405010507060e0a0f02010806032b0912030801060f0206 68
    0xe203802c80440c45a80003034103204e0602c14810311903000c3c4501c980c100040d00080e8601c13041f110004481d103455005215450309000303150b10b0f2090190181d404040700d80d9420640d071310002c04c00141c144c0c80c000003c61320b03590a20002941d0001425558040d034071400c002d2981481d010300341e480000d00c001c90109240803010582840050380740e07110100004900801107441004000c0071441d141e04508980c0c01448004680d40c1004481180004220b910001000c03408015104291041c1140042442e640c0009110003c0d05110056882a5600065500d030a42c01e00c0200006d108010004c1041d2103020b040c00340f40f80000c0d2003140980c3c079203486943c00004100555042d01c40920f4050303916219030804d44003a1140b00070008150003005240d000b00804c400813030301c21501c01e8aa0411503a14141050345030325000c080160100801c801d4040c10551110f0810580c0e8400d0038645001074031942202501088240114046195680144070300c54200300c032845030b05620b200038040307494214032 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 397555764 1250 397554514 397554523
    0x601030203192405010f14030c0105030903160503030702071d0117070305060c1206040b09040b0a02070501050108030c060c0a0c081608180a05010c050c06030c0403081602040f060602 80
    0x1614a40d0298003100404024490110440d041c0c0602020307541e80c589090f00fa80104002c0c0704048101c4c070fa004c070001e144a000380144214140060161102c407644000654040c0c1c0001d018202c0c0c0c1c0020056081c02640780e980c50703c6041d004100954880c589004041c2c40d00246400c4400780c0e403c044541c030382c1c001420b003100b030642e82c84040781140001d58001517450509180c0004042d4050001044164880100604030300103060640c5d400c02d07100c50080c131040380c404005207030300504a400001c002c212900342064100050010051401c0c4140d00c51a003183d40c00c0e004008160000540b4082d680700400c45c09030410011146c16251021034440607100701c0f0f050000400789000401c2042d141044030421890180e0800300c040d40e07694001280359032a400c414421031250a41d21000b144030b520031001194a80d9001000f414400813100810800b41c1009240c1c003100341d8100408030006402c280508180111030504041080091040106892001d0080d210b040c2c0342c0300040200c41da0019 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 397557014 1250 397555764 397555783
    0x11101101050106021f0c0309050a060f1802091602030c0d050301080c041811010302120a050f090d1b0807020d03091a1207081003120c230304150512071101050601020601030203 77
    0x1417001468120040050b130207445800e40c05402270061155070010300526400242e0055450007042000340c036804016000410070800194000400c00b0000c1c50342d1501a62000c0c0c5000d450048a0401080c80052031402e00782c5240500007900210040151180030812040b140400322014048552000c9a0444001141e20302a03c03101d0000382c00d04150f4025812542c040042d0590b540e40340c41c28040d044050941920200404a2000001541c8000108400703141441a47e604075020717070001c0381c40710020040082607485000030081000141c0c1d80b000d11000851081e19601e403c01d25140c011010001e11210041843c2002c0080114400c82400701c40e238008203d003020583e45c1c6403228540d0b164125900000c0882c079603140005030960700040d141c48114441c04186002504406004288444250a00095074000d2009000304111a200d0b01d039113a0340e0707141c01810a07810801d48440b00805980700000700c4c00f10300000e80e2003402805410340c813000070300007000b59514660100740d4420300103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 397558264 1250 397557014 397557073
    0x3031b06020d050f010810050903041e05123708030703020c07080309040e0f0727060e1005010c0b0601080c09030312060f030f0703030503041110110105010602 70
    0x810100100010355040c0d484070781405100f00a5440d010390b0711143c1c000c00380505240d9101b0042c030810b801c80113018851043c02c540f00a58200b9151841526076092041e10700c581d0250710b008041803075160541460318403050030005020503e45820a0302c100030501c1105284500f0070091145807516264030404483d03070101ca007594a617030f643c00c03c800078010050000c415000c6c0a0340016100130000c040d00801c84100c5082008401d8100320681d2841390490b0702195410001003004030020702144400000001008400d2015074808104100d800d16003180010f00e4022042c0110103c000259602618003800c019007814441c1c3c031109441800108418100040303040054070314541d200c162500c204020f0b003260b80341d004980c1d0002e4030440032075100d4081c2c3e040074142c40389072400140c4100042102e00c041c00f82c041c2542c03402c40301540010000e4034aa41c9000c250703910390b1035103610000c0b209038a9a903c580c20070b04d440c44900391030041c1c0c0840c0466004c00800c1e4000c0d2220302030341c0f8040180303 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 397559514 1250 397558264 397558307
    0x3f0a050109080a1403040b160c050a0b01050f0609030a1104090807050d0906031103150109150c0b1303200102040f031401060e070210021c0203010f1502122205131406030102040303 79
    0x1248c0003218000e8400200406074000c14014008115108131524161201100c03101e040f080c6030400d01c0030034081da01c0007661541c0040c440c8408188100340c98a03c00360080c101041c1c9012945a80316594400c0d1000c603195404800a4000e40d9030205100005d0700040c60203100021000320801c4060002600111004698000c0001141e02812460000303000052014480300c90115001d458009400020b40344100c500c000280340c40449065035603c0795164a4850a111403a603989110359081b92062005644c02c200c00f0411141c1c401d510802584103580c1d1554140400016074290349103940036000391100401840112600420300c201c4003801b203c40141c07201d140209042c03401100c502058100c5100000120f100000c0c014800c060781e1154034028014944500200d03950300038001250440002400461680c4038170f01c00380880c0405e0901c035010b17501d03124130000d40840110702076019111307610790440b080c47c44549500c6902240440c021800c052468038041c0481008441d0102007500 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 397560764 1250 397559514 397559551
    0x4022718060f013305130f050306010b03040c05130515040e0d0c03020a0c060305071b050703080708120a050a150f030206250c053f0a050109080a1403040b 68
    0x1542003c090000d403040c0100d01c800c44e000607000d0881d0b402404a010510000180403407005044258481240c0c400340040101d0f038038002d203000da540c001a1085032140e1018400003150f40c0c80d610102c0441c1c202000c001880e05284004010903007503c43c0b504e00445c10041d40d2503200d0400305511140c109281002c0ca194405440c0c12400d02d104404003d04804034030401282403541030344580d20410890b00d64a51022034204460301d01281903400412741c3e0b221800a00000320090054601c2c82d10034050396041c82445078050f101000200d40c1450b403140d440301089480701e550b001301d0541c45500f07820700d4445410801410301070f07100c07800081d009050000d402e0b0f003810740c3d0700307032000f041c00702c9070000310328000c585c9404008203045100701361048140d0780486207156000103c80c1d00c80303d80c1c44801d0b041d03a00030788440b03091310f038851031803000c03600034003803400c003c00c3e000e000e03907040c6912034210343d99103028644000d03181c12469641e840c40944240204400141000c0da469000501c03403811862094 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 397562014 1250 397560764 397560809
    0xc0306120c051e0a0e0601090602070b04050f0409080309010f11040506040902031e070e01091d040f021201180b0a0903020307300c0309090b0d060504022718060f01 72
    0x1204007070340c44d0000ca5880c400a010307240304a03110f0040400340d851002890761468226540c1c81030303000c0e201201b042004100114a001da1510051070000b0300042010811900c030b951a0741c004680d20422030b5121182d40d4100d0160b4440e190003840280c07a481e041509050120300c0f28003d40c0201d00d031141d40040842c02c0e50a00301d40b0059426551608889c051910703070710082108104030840d9011030440c660100b80080b13454204c84144000e8480071080ba0f80d5503c1c4c444c0709240e944c1041c0d13002956851103140014003809404922911017001070710502d054039202010210040c1000c2e2000e183c0760000c40042e42c04801c840c0459000b0280039000e00c0585182c2020602943c03415011809101141104a40020100c03400d0380c0280c484003c4a955500034a0645120b00583d5905c0814003800b00e0004640b6400320390082d0000e8041052074002e415900e00c140c5007413002645500340b440801920304000318400c00f07603c41c08006024141404600307a031800e074040c021141740e14045d410022029 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 397563264 1250 397562014 397562059
    0x3020310031202030a180303080609341101090c050d080412121206051012020408010c210908030408031503160f05060408030703050c0f0a03030c0306120c05 69
    0x3550800c0c0e407030036500b0390200042d40c0c0398072035500d00c40402c0708201c40a03080c20070784180800b10b0360076842d100c1d03c668403142004815040180b008001d03c8402100800110b100d43d03007058a850f0350001001156000003002d0700d105d450504102c034681c10403000c90000703005110900c08440f03050303402800b5400b0a20304100b01c0d0041d030b0441c0e907150031007030f0380d0106010305012480c081080135241c00100c50000c503590700179103200e4000d003508810841842d039417261094a0381446070040f018010b05190312441200c1c251041502503100042c100e41c04401c000e03104071305484999074170440410410f9525034501c40c29000080c8081d00c0007a011002581305403841c050280000c0005003540c0c0244404662070541011a018080b20402d45500118aa04140c01290180c030030a1004604014855070700312960740c05182410340742e001d03207011200e00a1081251042451190b1408200c0c0b054014005007210340380d50003143d40000303550700200810003858580042d958160f40c200b01a0040301c40780b4490 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 397564514 1250 397563264 397563269
    0xf0b1f0f0f171c0503010302090a05250504050910061701060c1b12030908071a0f090a0b120a050703051512010605060f0c060105091006300e0c0a140103020310 70
    0x3560750f140c0300c84040f0350344080118180d85c4202d82c01b06494903010008411603104560b100c00d40da40c1c40706403080f452401d03050024110b115142c01890181c50f200420240002941c191100b449500c8091001c82e80156401e183c034401031022220790761400b0801080c000003131102405110200000c0e4101e010700d0400c0704068030100040c50000d25243c0350040000d28140302d480c00328003405c40c01185403512100a03d004074402181d440c107010003c1c4254009912014040f0307401340e81741200050380c400040147c10103940b401c1d001041c500d807200007541a1200285040704151416081003507074003e004c4d210206100955070340301c0401082c0a85801030550760412588100040386112010300f00c0070041902880c000140c40440e669401440074202042d40c1c82c44000e0409c06c410f1240b58804e1503100c24010200d04100c51440a03500e0102045040c12000e684194440503807a001d80010040d400aa100980d590382d00b181c94940000c0e49810f6061105042507000404030f441808504080c102 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 397565764 1250 397564514 397564543
    0x1e03040f06110901120c0527030601030516080c0a0909060e01110913020a2307020415080c0904020306160e032b0503010b070f0f0b1f0f0f17 62
    0x82a9803085884460781281942e01c0c0041c645c0b901d80c50540c11103000b503a0f031300c0045466180c100100320314506d003403140d0035900090b503034001001c44200c0d075000c0280c24004c50203000680307500e480da11001094201035800c9124250f00245001060b5190009518111600c0240c0000d40142600c0c2c4500541001c81c20196150b00740703a00380c2d10b4070508a0041c00c450104440d101c000100c40300c46403060340200300305903021a00c1c81d00701c5080f0603c0880c0d41c101c0c1c816000d14261038070505500042c101c1d40341c1e02c521300d2048080345040c06883c008205840c0c01001c101c034031468504d011350001c0c1d5501001054540710607080420b41c0e4100c0d000307210540e01d140004081e03c4c14071550624101c070007086401480c4280440380035035041a4024003c0ba41643c4004001c41d1030003545032204600c212111400321020f40c41040304c1c07404a07401c0d01285020303103001c08100310064841d00910068100c80c1e040725101040710001005070852030500390040341d4022201841810036081c4680c208484641d035400c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 397567014 1250 397565764 397565771
    0x201030507230309150f0a0c140403030801090507020f0c1c15020a030c0903170906160606030506090d0507060b0a0806070806130911010e040e0a080309121e03040f06 73
    0x20301c80b0309034009188540d10100864061480684540c4070205041c0c480d074184249000104244418541180c1406261030400018140540554241a0740154015000224054010f00c195030541c041d10b81c0202c4503200034100048150285034030b80c4c881001740c900c205011030008070360502500b0b20201194004041342c02d0600e1600e4090040d50128a0810001b46841003020300940180c0742c4400b81c0ba0410024603568840406407039085e882010100d50000c000e029815103607001c1b030030010282e48030700f0000c1104d925500e01146440d00103030811007141c002004040d0840c1d4440152401c040d00204c0104400c0035003004103201101541100c069405140c04001c0c415401c82a814040d1500380c6020341d1541c50b0006c1c030800c65541c0100200038202c41c20b1005240d41c850204e0313001214004100140c02840442c8c2c091a04000c0c10044070070900200820011f07103028808609010044044d151805400c4080034030348844069035281800310210205003804402d624a04c580381e4058400c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 397568264 1250 397567014 397567067
    0x6090227030106030503030f04170a0c0209010803090607170d0507020a03022803080a0b12010e0111090d020d030507020913020321040611100203100e010e010806040201030507 77
    0x90101112055003091285010004005906052180104994100c8007035403c5440700d40b01c0c51090302c070182055a0700b014489c0d00820a8005e0f030004c0000c042d09495241c1610203900c180126140d050388107110307031b07041070192107e035850792800c40d40a01d91101d001d02160a01da9800e50813400b4204e61b5003206403418041080403500000c00c080901c1c02602103a000c0418403201d54840320b11030b442031000d00f100c484280d00107070096002a800070060003010541485800c007152603c0302c64035003200340380c0d103808030048207000a2003100b400c0c030a40300c80d6a00e40408031004c20a001203241000340111500c0d10b889040c50712903029605500d0307008048000f04e04000c40590304000c1030703800c142d00ca0701584c05404078901210180c0128008140e02031410145041816241403141e0540380c0d5140c080c0550b141010041c902c0114481c1c9640004c1e10300c540d00703103841607441d05816013103103503c000203c0060145c40e800040d05139009609180102da03c1e503c2007411982c402d0308011100722607042d203201 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 397569514 1250 397568264 397568287
    0x601090e2409120421060b0306101e031707150504051c083102131b02030708040504051005220f02071a0622020910080115030b0301060902 61
    0xa89008541640846002c51070860f40380016100d81c3c402d886070b58040d08840c01c0340003c150b8a41c0e0005003e210000745d0802580003007414003a0450707007103030041e002c071105009800b9144c000c0c200c680d082c00c56001c0c200d4199541e90885819600c0c0241141a011405004000a0305c0c5110a146000c01c4144882d040919101c0d40d5004600314100b2800d0f402c0501c410458824000070340f1461606041400c0c45001340e0800340c0c80000e40c00c840009984213109030300544c80d0140d00407110001c18000141c1c000c0c80d80b10803020901d400c1c651000310b410802c07000700862101001d80e0141c40d0200c400144a03103a10030b070004d40609aa110a802c1100b840c9650959108804145580710a1480600c03c81e0b0940071500102e00c24a2001004060340718149400500c010760441c0c2d0110b400342c101d5450040140602603c822209840706000b5000561680b075802c000d0701c0340c03a0b032480c9410118403075410144900d0003a110b603485c1c8410140d880298034515607003500300310018a0b10a404540e81e110040d00f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 397570764 1250 397569514 397569583
    0x40f110c0c15070f110f060703090e0c0f0307030c05070f0602030405160b0d0207080c01050f01060e0102010510270e010204091505010804020108100807120318080601090e 75
    0x11168402ca07000260340142d0700d03222046032695584030ba0200807507a00c82e5501c1508404100d081e1390400212048102c1b903444034401803001602130f482d4041500c1c0362101103208403400402c820240302c02405441c0d83c400008095a40210490402040302c001209040f13030750780a0b088015181c44050112075060103103070740c0110300544c0900c1c2034a400e40d0741c00310690160f205520035442000b1040040402d070700202c3d40a064841c1c4100a01d52070252a29401e900352102940c10001e00104940104855030300f0409091000d60280024400d07480c029410741c400c030a0601c507070101071913503070070402040c102000b115241554045041020600345070403039000b50024080c4d040401d01d400c584681d05000030b60070f24200d85050392151495510f075401103e2800e070240c900d486198402501040e98242803014101500019031000400400d034180100628590b100c0c4240d445c41181e8244076107040071030998107491064000ac17804a403000c06007403802d244031310f0b081d094040c021069a00920700c4035 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 397572014 1250 397570764 397570783
    0xb061309020a2607150e0402070812090d020a1127160905030c03061501110703030c200a060e010c080c01060305011b02030702041d03030f10090b0f040f110c 69
    0x15820340f20200030040030342c0c0e800d1603000e00b0558840540b40400c0051094000d040c05c00800f4201505106041d40c0b501c240340c108120341103100701c10f10b04100030108100a1507241c510f840c402012030b6501c903182c48079a0081e501500d4060041580c24034140340180c100fa085400c881e603100401e914010f504070140398800445400000d01000c000180c0d0700d00024580501c00004002e40440c1e00c40354008207481c07a100c18554180040014054110f407070501500d00154040d84600d50007110518104403070031684480c8500616615911f80c0d034075251691043c0984d40b0780e00380400515181c0c40140d4986a507120020074400c0000781c100b80e800410341041c4103c910800c003c2c003c014100140303425446507210740f04c00681c020f01195001d81360035080940d441c14080c9044030801a10900e0a045500480d01c8100c4c48560710309100402098111000091010040402902002d84005211010070701c014602c01d6448030b40011005800d0750040b0030400e019080c059483c11a800229103511015 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 397573264 1250 397572014 397572059
    0x10207060801140a0803030f070f090302010206180705061b010b0d050303040224041e081203130c0b030c030708060604080c06030a0605040c12061d07030905072106060803070b061309020a 82
    0x81001e402b105028100540a80364140c02402c41d0f60b031446040e100e2483c1110b0180e01c07d03c500d01000415888001c01800403107181d070f1500d8a5152003075500f500756045061a070f806010601c00342c2000c14400b00c10750350495811101c03440d4a5145008910701000b6102004a0032840010300050860740e08413003031100c0543c0310700c03001415034904074140c0315040750741c40b442d80c00001c000180030721210f40c2c004001d1a01c207030240c0e04442e884e41d5208406400403141464100800028001ca00750000070b030941c890811070740c040c0b81504048519031102c607150103e6003d02d41c0880400c100702d0840e00007501501000d881000f0244035000c000f00101b1030308202041540c9020800706030b200f0030b140021102c02c429800b4030100d4580784d400301c0c020420300300306545030b001c0c0c10004503400c0300c4c80880b90502078003501608000407042c2002800c5407959802004035910070850710001408840b0340c1940281e084810200101038a400600907001101000754002075103100428600f40645201303003001d001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 397574514 1250 397573264 397573277
    0x15060207080102030c070f150c03020901020f1605040f1404062313020925030b180112020105071b030609210207090e19050309030c010207060801140a0803030f07 71
    0x5408000c1c2c200d11003034660070150b001c2048030501150408810703002c224401c2c60900300340040340d06904100d841e190a0200081c0e000100c101940da8104402881d0311580d40140202d40c40340e21000405600e5440b41e50301a9440b6480002c442c0d40070343c000340b21200409100340140c40c2600e0210010070342080c48a00c003014401103640d24480c14008184280c01c00c24010b01c0026407502007003881d050041c00c04a5800d180e40c0400e02103076041100c440d01d0005514042000c5e01d4107010800c0c0905030341600d0b0a0311022070010010b14030300750401075460750282045617562284c0d08100c2001031102c900080480c000510000c02c00040e079100f1030401d8060440b040d0b40d40554202501d200c085030f800c080040c1c0c4075001c14007521041d50b0100c00d0001c204030803106917003016040c3d20040c9807170080544258202181c403060350300b01801580c0d0708074800d10141c0601810030501414660301070040b61a80c540f150302413201d586440c01040090080e9904407030b02da181611104101c01c800f00c80b04000200c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 397575764 1250 397574514 397574519
    0x7030201031104080d03050406020904240602030c0309060d0207080307091d01061e1b0c03170306030706050a030609060b07110402030903071b0312121103100e041515060207 76
    0xd06403c2c2c0e0140c400c02800751921164283c0102e01410002d481600c1042e401c0184528035a11480f035400f180d44c80b14126100d518000520b09070b0405554056404e40d0000c211030f000c105c1c00402151001001103d4954031036240c104510b00034024040300400076200081170082c1e10350020b0f43c080450b085030311941d00740012040c20400f6480e0a10480002c200410441c3c40405d1785c180d0700600d460720601d84001020004c1507401c503c5e50749a4001e1351119204030341032051201c544043c20002c41c0da91042482d50400780c0110b83d407009117110741c0080003000b2603c0040d0500c290020310003031481040a00500d902c8000760a80c40c3c0c0002021160114800100701031400c15000740d0348a00003110107107080c50200d4030380582d03d0000101740501420f040c0d00100001345a50b800144e44d24507980d44512500c03800b910102190744c4000b2900e94280d0620801c200d840301d00c005403041c0d940314540b40c4070f580c40764a815411031b68407042d10310129043c41c141002e18240380380c8420844205a00b103820259 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 397577014 1250 397575764 397575791
    0xe0319091503021206240d02070b0610080402011808070905011401080610030905010b0303030c030603062a071b170d0305040f020d02210303180f0706030e0a140703020103 75
    0x4a4004000014520540012914a400080e02d20340981b100750b6803940d450358104244c5540c0c41101350020709540450030300c05102c0d03100c00c0107070300140a0380c443c5403800c84000060000344000340000d04200a2074000c80702039486450080040505c6021246a152200140b81c080e000c03d000e01c070b40424928250713160540c070440c140380c0603180107081320b1000020141c049000c7c040314401902c55648540c12107205490400c001d5110b00401d28901c5d8981c10000f0070181003001c090f1050b034000c0c40e4400760b05010b003006a040042d440480050301d56a0646150036130f81407100e030701c01c80d9240841860003e1124a01862410080e03000002c1d221901202d00c07003681140d5090340d0140c9410007600130480142000140c1078187c40c0020540010303d04448007909900c1140c50407034407036403c040180410000d900e541c07042c0703048112000d042e2182212491a0345c85800348943c070100340d01c4190b86c8008007800d00045c101b15811001800c003200004403426138940451000300d0000303281115010601 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 397578264 1250 397577014 397577017
    0x6030501141008190204050303040b0706051b090405040606090e161e0b0c0a080403081e0403020f01180f03050a1e0c090b01051606090b060103020a02030406030e031909150302 77
    0xa00154560601c0c60b258200c204051100c14400410403c5e420400461103641c10030203480100900030089035120501e14081d0296003002d80805418100c0d034890780e600b0094402aa00942c03803e0702d00080981c0da83c00c001c3c0c041c01056100404081c6402600145000701058004001c041080c00c0d8105a50b54001c0c42503540c2118904070000301007130720501845540d42e00038481c50901c802225803c01c404c1e00c034040c8942c0070764401c840c034090014240e510010a85d60060200b612020081d0900d0714640200e100440740c40345032410803459025440480c0d000c180110064480c000e9500105030701d0345800e0f42e4035031519000760b4100401410480502c401704500c0c0020542c02500004410320780342c164000341010000c1d507818080c00b4014090642400801d9040f80d601541000c201d0000340d051800c00d03900064040d0b4101801004a0b5006c0342c0c0002c1181c088a03c9490006101280240158114050203148011001c03120307402d6201e4a03402a800010b4509880c0b108003105404001a8100d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 397579514 1250 397578264 397578289
    0x9090504080a0f0207050a0612140f040614070804080306150f091e03070b07080408010203072105060105090d02010306050402070614090609100f021315021014040f1b0603050114 78
    0x203091047c0030300069205041880c0300b24002e21001c40c041429144404440380c0c201c604205100306442007000748881c6004a10281c00281403800c66418007031401070082900070005030a107100000842c14540361243c2084d038100700c0c0015580ca501c1003080b000c07029880b03061010310800b40842d805010303107405504510640c000400600101d4a0200551166002003000780d40e00c135414000019216130038002944158001e07030700c1d285010344042504003080303d10180010850f1502040003100d0340c001040b118010001c0758070003004401c1e440103d020b444250001a0800e0000c070700c103c100b1489420104202d1401d540d09001ca41d0f801c41600e54030305080300e0301100c1c0e6015907a1400400550b0748524512691404058075041080c010500e0301c0500d64024907602c2d81e40046c1d024407980c18401248103d0303a0400511450007200711705c128641005e0070160155050f104030714104407050000d29640c4500300000c00030b150365507001a0040800744110310a80e02200410040392504000d910342c03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 397580764 1250 397579514 397579519
    0x5060303030429040b06011202121902040902161110020303060d020d0221010b0a06020715091715221407090f050a1a0109120309090504080a0f020705 66
    0x10342d075958540014040e44480030002c4003035103144490001d0000360100e88142d009070700c140c071103003030080004052601240d03181e00c2051050103002e1400e10f100039100d411010041c100004483d000740c0d15002031080b58010a6a240b001828494800c3d804100070301e50f0380540b510800d0307405113400740001001a60390900042e001000010381525065851084560026182001c40c1041d81d020484080054480c88900900380035820030580c3d09006156a01d0b009490f00112540f070a84040d6039003482c0d021b149894200801100d60403481090168014501e1450201e40511041d5199032100003800030b0b81c1a11140c0400183c110403108819140c190507038080211175805a250b906001c044583c80100c0350080e0341000415070203034055100d903a00c60080016460414100f040d08540b250745503451404003240284031603a801c00300c681c003180c0340c1458500d0083c1482c9411580c0850340d4010018440c80c040500c0141f00c0c2c0140541000041d40d00c515020521402045e0703034a03003083c410181d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 397582014 1250 397580764 397580767
    0x102150703270303090620070602033706050d3f030213050a06090b0f0f0f0901020606040501050a0b1c06090c121406011d03100c0e030105060303 64
    0x140454400e500c5081016820864900d10b829024500d0807502074a0b030040d00080d464008180c1408a10320030074035035245038003d0014a00c0140d8800515000d50b42000d0803050303010000601c0d65034504070030f010004840c103003500c0c411140e040c031114243e0301030780000703100340381060104941c200500c1d42d10741c0a810440f0303e100404444803544044d03425841c0783d004140c06e03102250200c80b40303110003000c1b800284c0b07015880b020a00803906145c0d0242c3d200c14800d000104081001c00d402004000a03510011101035031640b18810700e0406229095641c202d08800142c1c0300340304034200c0d003e404184030903800e896468546200308000d41e8000e000d0194051600e034410080340444a0040c074610b00d40341007000c089041c5080031801c4407550341c0042c81c41e0751501285100154810074455002001c01c0d400c2004405c501b030002e80100000384024140400c0076038462182e404080c0c2201c510300003e0403116124291543d0101514101424130f0200d030b080480b040385440d040c0103480c0716002c0a0000e6 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 397583264 1250 397582014 397582021
    0xd021f02092709010f0605090c1b0604050307061803021c020a0822240c030c1b080f0114040609030504080d0201020406120504120c0203030d0f0e0c010215 68
    0x10000354440582154000c1884054604402068900070301e02004982c4144103803400d01e05143c00d680d649001005203610b0b29400b403109554090000390010000070b204e80d11a102604160640c0e20320b000507503054464141080104074000004044052180c0c0c010301148082240e0529801e40541703008015070810301d560545406444000d0f20500d03c40e02c12103400d00d115032501c006d81c0d4481244920700c400315900000601e0364001c0d52700300510101c001002c00128580c20030103c40704031002d11040000c810b45000c241031003050480e6410381c218521100035070041c9946901c1c0141b0b4801c0820341c0c0280314407c014441c062240050510300039502e049142c0d156583c10300180307801c8000300c00b8040140000b02c1c40c014100052410f001951b00016921810454040e02d40170140c203074445c100d801e0a04010000707034180240c2c038080100d400c00241c00c501a20001e425030285400c0ca607541032074080662005011500048103a800b0380055444c08290480120b880b042c045404038042c4a068011 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 397584514 1250 397583264 397583323
    0x3060f030b07140405120a0210020c01050f1809070806010306080f031812031605060129090d02060a0e090f0403080f07090f0609230a050609030705040e030c0d02 71
    0x2416505800d208000d89011740343c2000880ca0590184200c0030b071740c040407442d0110f04250194800130000c80c00184103030400480003c2039880350700c0f85ca002c002c0d0040b810b54450640803102499144006180500515000c2001043d28600716103a50000e418000001000e00d40411001c80c03545044000d985819002c40003401283c2030f11840c6a00045500020011504140080c110300c1c0440003074011584d400d403c000e482c06404ac0c01c6544c10700c0840500a2540328500c034000403440c40c0ca90019120300d030850010340c004903c0350010b500490005000c94840b64018203400e454501101c4440081d2552071005009100464000340400e007440701140242441c403080c207502c0182d61810740e500c15114405009004040e5110301d003c100100b0046c030124a900742110038040f1109903145880c101c0c2400950900100c2c45410700031200011700388210344041c08440301910000c1c1c4140710a07184006081d0340c0390b0011300002081c1c000c070090140c1541c4080344550500820414401c84c1d40c403103010 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 397585764 1250 397584514 397584527
    0x40210092102030f030301030f0c090e07061101021c1d01051005150f04030c0e0c1c0518030309070602010e1b090c0c01051003060b030307020616060e15040303060f030b07 75
    0x581c3d00d0f1003801013100c0d00b03400030401503010398442d01c640d02c2c90440601e010803072560650080d040103403c0c1800384441d000d00003180740440344185048820701c0d10211040d0300a01c25030030140302c5491541450030f8840d94a8002d920f07118041d410450aa42c40014803600b2100144c60035591104d1141d81000b56141a0b20f601c0000031400c21020704e0503002e090003150a038040c1d4400c80312502c0c1e40c0b41c02c014520088003000d9000c003002109a01d4104100200941c0d007800c2c1200c1d0042560740c5010a08200308110901101c210300c10440baa2828441d104590310491403191030f00560801215020030320700411001207848400480c07003d074501641c100109840c00a003031080d42942840709010404090003200d0080034000041b8401c141141000c005407444480614042e900c20005c4000507240c55003290121080340b140000a02c156240040107010075003034000c0c1604c150360300040e004401390312182c083e44c0301c2e0710104186984d410042c1c10b98001d911020b00145c0b030410004e2420f0f8060f80 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 397587014 1250 397585764 397585829
    0x11040c030c142104020a0e13025b05030a06090e0d0309031e1d0907050d091b0e0a0506040902014e0501170a1205040b030f04021009 58
    0x2c06daa00c0303041d2908003c21442108490205461301000c0201044d42445420701d184003840c904484005003810141100003c044101c94000c501240000c3c64030b403820900300c3c10a1031841c600c0740201807174400d0003042900140d40c68a100c03403401c0d0001418003001c4c415a075280044401410b000e1700d0981090f001410103500560601900001d20007036000364030780300007590400e41c60381c8207440a1404803100d110b403040300c8075018511440c00d20804079003005c02d4812803002b051000c56020174a140130000c10011100c040d810054100380482c03040d2007200b9451003038601d004204016921030042005980135404081d012420701c10b07114520042c141f0201510601250811411111740710868110030703515050821903084103600000d20801e1809681d0041141200e810280c00c415100c00e0744a5000c0c0c1c0c40280413001003107420701c00754001d20940d80206104024140c0303d10344400003006c600c0040b1800c030300c0740ca100803060182e98001c280c1001914a031419000d20000d14102c109e082d02e2910 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 397588264 1250 397587014 397587019
    0x2010614010f05070f06060b19031a0f0a0905070503090f0706050a0522060206160908071707171b1906051b01050c09101d01050711040c030c14210402 66
    0x1021200082041402100008e2020581e03d6039641952800c130143c41c8042d81e941000c160524030900c441c2c03c882c0740c55000c8070304122004003441c0680f80020722013004542c003c1240c60708050803c105035030840095440b07156082c0c1079030b0b5550303e08840191100346a0046c071006c1741c4144103003900f0607ca0b84c00740047c20580399002c6118560400e0242181c0c00d20b500c1580168040010064034100d000d141424141e5507042695109003130030005c91700d840403030080c1040481031200c0084094020850074005011010196802c84280b52150f6101d41160020211007826607503400762604090710f550642d00002c4820074681814050b044610398071010903a2502c0c034180c185541000350a20072180a05640144203a655030010248508020030b20841d0043c8289180c00c841805810300802400304024608070b65540e94034a48003900c3c10030105a640c00902e0400c0c04d101c000d0701503206040c0c4d4446503d0780440e0840c28040c046030b40c494004482820680f8030700142c00b1082d1803804540140c0700 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 397589514 1250 397588264 397588283
    0x210050c07060f0e010b010c0f020f010e060a0309171908040804050a060207090e010b0303030103030f03020d05010b120f0c1608040803130f0e01150503040311190302010614010f0507 80
    0x251256010b40b41c0d140c520a01c0075030b035803d402c030120209200c6d004884c1d4003800c200c030058420707881d80c4d501501040d5020b03000b00461650354046a106da5020340407000001c290f40c3c4c4501d810540240181030505080718040300392058080030402203001d40e070440d501082880790040301c07520102c0e10703104042e1040359008002c1c0400f00340c65030741c4400403002c0c1000e0750080580c00c0c40c00d00140280c481000048600b43d00d000311000300c580300801100e06690705410000916040d2070b01c210000d110721155401214a0140085410491000200b90340341e00c0c40b04400064480445c00d101e1244103407803501e080c00041003840303c05440307501c404160501036106071341003d640b421081d046501414400880c4480303030b50140700307451a10080c4000380c506020003414a40c108504440b04030705111060040c08000700003e004c06100e004840128060340f0192041400100310070301681219840403000355007402401320f00d9a00800e05505072410580d00d461900c460a17605603141d0748224801c0c2d40c10403c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 397590764 1250 397589514 397589527
    0x20f0a06020c13060503071e03080301090203192f041805010f0f030809060c0f0a030807030f05040203060c0a05040906030507051806011d03010b030609030d0513030210050c 76
    0x128104484010001074014009a1429904000d1030034002c11480d24080d24100c02801140c90000d41d000664010303220310b4142c00b44401c80d449035031a441d80003d02643d030000c00860001140d40285004980c68000f80401500900e980029200c02c0e10b142d403c5000090351580e00c820080160010490414802038506a00e8441d010140d00e1424404001c0b030361104010012041c18042920040c81c48950807141746003503645155032842014401d52040a01140d08440d500080c0a03c0e880020342d1030480f10029281d10303010b454040220381c1c1602092910721300310300c010b80a0082c64450b588c014054082030f070359800340312800e0704245818410800e00344004101c407505840b5581c0614001c80027003100790310309002c1142480840080e41ca031444200240180c59030455000d0fa10140054009032000d240307100440e004012105c00107038036115100602c07074201d101000030400c0c00c0300b22501344103036611032243d45507640d4107203001070040e8030001084520f020b050b40850380004059914914050 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 397592014 1250 397590764 397590769
    0x120d08150306011d0906041511090301020703021b040c05040b0c0316030507051b01020a2a060e12070602060406020a1412090601061803060b06040905010314060604051909020f 77
    0x4804d8101c80d41c0c04099503c0300c955071074180441a030009003207004140d035141c1795840c560902340c80812160116151040642901c0b520380a81e08580f0307014000310740b6170410781402961900410180700203013800c80796000f841c2c10705005000e407040c22034807401d14162502c00320051551080380c41c50201d00083c003288240d0801039200c00b00d0343c0c4c0a41da03916220a840e0500a0034100400d9041320307241000491120300c3d9030041080e000040d04103101e0702e2101c00081d03816211800e4a840c248291000410110340ca40d0030200c9140928000d0340d0118078200c001d80b440d569091a40502405a4080400280058895001032818850901e082c204100500c0032a40481d04502013000e0364100c00e204102000d4000c01081d801130140b46082050007500a01715104000300c1c0c0806483d8070b4076071402c0c6205890325002c59005003807a1000b04170310b6a4a0800b916400c1c000c844400942c0185000b0600924007400b0b2940503071801c0380c00c076207540c0e0a504d0740c20081885140c100d8010302034400318841036 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 397593264 1250 397592014 397592023
    0x70203070b070b09010b0a0501120f020a0518030106030c0e04051603030e12010c0f031d0607020d0212030c090d03030e011506030b0904171c0603030309060b120d081503 74
    0x7005030240e4141c40e400c40c0c1c03405072011000149924a00d85c54180040d6803640d40e0079107001140d00a00706a00a012490302980141c402c0354031a1183e2030002500d030004a80c414000d10300342c140003440d0701884802004040c20394845100107400c00340708800901c07084274080d0416412500c95012140c0c11415509103200308091540207070013040141c40a20101e080c03d94440402c4a1940c0003004910104480601103a1221900408160f920800d00c000b2100101030007013100a0708003140c2440ca84a9130080da90207411045100501035140900e1f41e04060304160ba00441102d0101403c0440c018280005c0b4200200305404040e00c0d1041e5011180c03080c4918940c3c144c2d100c94100f00c160400c4006410344c2e0501c014103010300d12000c10000801ca051860502c940d42c4c1c1c1030004d58030400620720710882d500c46609507001d9880e10703100200301038042e032060044610510040c040d4040200800c54900032850702020650801cac0e42c00e218aa220b0341c6c1d001d80c0f1840d902018440380064201103880d1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 397594514 1250 397593264 397593269
    0x706140c060a0f1404050703080306030309040e070f080303090304140f04021204050f0d05030f100509010605040807060c080d050702160b03040c0b09030d0c020d0213140601031b0e040207020307 85
    0xb801d0740c9004501569415006200d4090700100001100c2e082541e100743d80c89101d8032018200400c080003140681d40e05104a50003207500070814040c01d1421082c030f40d00c1da40c0c5403042c001c1c6800c607060005590040481039070b101d00c0984000d1410700746406104441400e8070304170283e10455007020601555264405084c10781040003400c0041d18142c6012441d00e20707480d98464165114100031444964803004680e40102201074600440d261124090103c0c901c5070071840e4004003072000800c1081d4030201034412254800304442d51203680b42c40a551003110710710054807140007089400d15480701504425008503092046a02c40b4985e402d045807218566044446110000018041032290000c000d802604a80071083c0ca0003880b0f00002e40c1d60560340b40d40d0018491152070520641da101501003000c1034010300900c0d40400b8885e10300300142036801d610511140844007082595200340310740d101125005282c3c0700540c1c846581641e04000000c201135110740c080056500580b01409902c00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 397595764 1250 397594514 397594531
    0x90102162409080c011407060e0a0b011401090e090705030706030906061a090d030207120f05190804210f03080105280e0601020a060912110f0706140c06 67
    0x8244101c50a82001c4507401072001081010000b014004980089a895080c0009082c00d890300d81c1e0440e540c45c8140221000540319600d48a210700c0c5514010a510340e0091003542c6482c182d07038a80c0388111200203416946400110000c2c011b100603040382c64600d41000300c020860314031315500c500083c50007125810450000340c070b40000000b00300a900600e0701429082805080080f113407100041c40780201000706120700740d080d420b0b0081c940240130354409070516003a02210301c00d090030b06400c84c0d0200b0204807418810040345890256041401c00300d42e590000210340703441d2500c0d900811f4020440e85044024008103011000180c00d0412010454031a4485e044190303d031008001d442040c403111000460482c409041e074015a030900002542d1113400d5a0740d05451f4800101e161070080b0344003c080c0b616010361001400f100b44510343e40c41c152981d440440902960440e510307424a580402c505600c1054240241800b4110b060842c00300202d0080c1084955030714940b4000b0107840ba403c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 397597014 1250 397595764 397595789
    0x260a050f100c020c030c040903140f130909210e06030405010501060305010e010807060309151821021e16031103071a07022206090b120c0a0b09010216 66
    0x8045041d00c1c000c0c2e00d000c00841c0040c04401c44610003280d2070702900004d0611a0790740724111010140941c0c410b02c01000c2c00581c040e1180041c2001d0980c6900c41e01c10707001c0c82800c0d07840018240c54140a9440d0142e808200e110354a00d00701000070040c0c1c141d2042205100000c8052852600d076000034503c1940144000301e840d5140100140c200d07071060f040072485440b4000107003c01e09000900c102264594036001945900c0c41c14401c0c800d841d280181e848550806141c060404190914054410301070010180d0401d8802030b240c4002064401c2c002c05038010312184594844403644840044501c1003e950141400e038900300400c0802c2e0b002101d4800c40e4403042c180d107050401401011741400c007074004e800494941c00191030301a00702e0081c803c1034407000e40c080541000c2c0c210a141c049109090040b56107518610018192010119003d507c6000d4107038903102e00061002004400501007800850038884c001401d40c0c0461805415840340b4109101e4100d040b010080c002c0c401b050b90746 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 397598264 1250 397597014 397597033
    0x1b01022505061f0906030f020a050103021303260f030a05010b090d0b07030b030f0a15060f05210703030c1101030507091214191b260a050f 61
    0x4a45a6515114008440c4000100000c00c002642600f022444200c000384010790020740404501c0e54005030100ca0a000c00042040f161184641020788200c4010804586400c0114102d000f10806640e1640c1d040c0342c00c001050681180e000c010030710f40c2141c001d10411286540c02680001400001a100041007003a030141a10940380900382d45180c05141200d40b500086a2407070106000e007840d2202d00104044c640603901040c00304d4405400d4803254040741c0020360f00e410008030f00b40c481949040d01c80d440d1030128401d1a091f2445071041105803420141800b13000c44202e6000481c540d5100760046003d5400c1010b500194840e41d1340c14103111540c41c0072a900d06032051200d051500b041300b842444d6800c0b8224905a0742c02180d000307055041810183d950050314980100c0c2130044010390070080c1903a03581c0440944c058090b4003581c2c0303501c110500d104072141c07013424240035698030650500a1580b41c1c000b81403444104540c82c0414545407241000032111790a4881da2005260303 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 397599514 1250 397598264 397598287
    0x10081b030f0c06040b0c03090406030f05060c0403050a062a0306080d020309030a060c2c15030f0109051f032d0503030103170c0d081501050405090c0705011b030507020106050a060c0b06061b0102 85
    0x107163f000306c80a0001c0e080070300e541d8440d5541c2c000100b000f010303651640140b4540302240c0ca6040e8035080094a00c0c0720300900544081c1c02820f280c0101c0f281b0340218070000003041c0c00081204d5000074090020820136201e61540001440210603d40170801d141445903d58120903000034582001425011240d410300707010801b94584000c1ea151141009000700101c0340070a100c541e04407500c0c1c00c400302e220340d01c00c1000d40a0b00c08649010150325404180801802007841428400c0307801c0720310b00c2e0460303000060070004081c003102008204d0790081005000040380000303180c4005544040c0181085102006035042201f81419600058500382c00c003c0b175030801c0b09a0b614030f1300c400c2c24102e00d01340c18900840c0303000c00010300e01e1042000c0000d9180400c00700b50b115810300c025480c0320000e44050303000024040c0209641510056091400106680c60150103031005c8600f070340c441c0442038460b6600c00049031070043c06c0d80e41c03068050043c00030702c5c050243c00c0d89000c1140d4000690b40d00b005c90702d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 397600764 1250 397599514 397599523
    0x3010b040e130b0a151d0a0c020a0210030e0c1002030c0c0901050d02010c02030c06070f05070e0f0708090c03070b0403140303011d10081b030f0c06040b0c03090406030f05 75
    0x2e641508600340244008564a0401280c00042c1c060003c11000243c480a880d000425848142a07a0281440c101540000300d10b0030f0041070318441c207003c48100e0300741c00c83e580c42c1440400b07544980c141e0382051340c4500030b5000000700200d01c4252802420100d000881880154651001580002a00d0713240240300303002081c0074640c00c841c400290b5042c48045203102c1110300000f07040c0702c074500c0c004d02956002c1080c404108002032038035a41e8065440d010800400700c00342210300c1d00c1110404503078041c43d00e8400b84600e0481e84485030361750b1560710494801002400b0741e00280940360980d5041e4400f030001c0310203050010350b0356948910310702d404115040740003002d50b00c0790018001842509034440c20100c04504005200301303184c44d42200c42403080c2c016800041d0380d01c1094022104a80510065002e981c0700701c06492446036000f041d5612002c2e11082d03598040b40810007441605018405040c3d003c4441c41124201000c0c04007160850303000d5001a51001403020300c0c02c0c00c1000c00c12 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 397602014 1250 397600764 397600771
    0xf0307020607110c060913110405031c08060108150307030503131706061519030b010f05070f03050310031703100f0b030103020d0f06020307110d030b092a03010b040e 73
    0x50044454140103072415140c006207401107100e41400100091560f40d0356103000301f450341c03241c4100003500701d0200b880f80d9580903108181c060300941c09041d4011291240040400c000c039110081d580e03841500455042000500041d955484041c03143d001e602d00b048a200914441c000465031110740180c4003800303460b41ea01c88494404000108281814089036003500f0010991300b0702a1108003511911007801003620405c039060340c000040603220750580108484240c00e0300c1323101107400f003003504031010301c43c15001805901ca2210481f0001c0e10500040d44c0c0007032851010321035036880b99281030201424594400c6505400300a00a090401d00c10540c02080c81341c0d034080a0600c4c042581003079010522010b4030410082040c0e0092000c01c0b100000e400740d000400315a41e150400c00030b03240e40c101e8442020a0720a40503004801e90007489211002000144020f0382d9030341c0c429034181c542c0891071150038200640000885c02d06650b10141d4064441c07480000e4846007000d20710004000002c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 397603264 1250 397602014 397602017
    0x40606030c0b0a14031003050a060615030204050609010f270305160305210f1c060803210c160819020105160c0317010b0408011404030e190b0f0307020607 68
    0x20482001840d0b080703c1c0e410707004c1280000075038983c1d07942031030f0f00950103160340041c20380c0c05100b68680401203140d00c484c054a01501e403241e005100b03400110100e01403405819003003001000010f0b103542c091008240c889c225403034904042d00d44000200b510312100400715240f0000404180308201c03013070210900402940340f070f1071802d51a44e101c907559041d000304246040c80c1201942424001c2040c00c5490081301030904590710b4918580075040c40c1912141d01813a14036003c0c0110311180e001c812990420012001d80c2a0702442050160ba20400a042140b11f02c0c1c04101081074840100c1c03001c003500d070041c1e0b80b85450b096040010310380101174540200442e4908020440742e114061080c104c203135440d1a04500c205080d250544210310990810074400312400d00008120403008010801c1e6001d4800a10101050900000810100741c50060110380d0118102d8603900b006810480c07010b003880c3c8120301d000c0d643c0b0906e40c696401011320b81c0090b04000700b00400703e50100182d90300114107 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 397604514 1250 397603264 397603267
    0xd27060605090907060f140a08010e090a0b1603141003021009030302060117030d050c1b031903050c1b1c08100306021b03030a06090e03120c090d0b040606030c0b 71
    0x31114150304d40c100d038010070303041c8410001e03580d0f9803d202e11000101200070130071481c0c1e51b00ea480400f40c008402485240c199004030b40c000b8041c440b020030750b42c00c03680d4000854680c6441b0980d0305107040803083c43c018101a6100b5085e030105100c1c02c88107008e101d004440500f1181180103201c030803440da85845047c4038440b0001c00c0040d500240c0c4c1030442d051071002d0038072103000c410813600f584034012150642c541040b0071310000449160086c135010411859031000391111648040d103902907812008041c0d0000c4d441c001445000303401007603114500c1c0c428a403410b00e800194503402d82000c500038106500407862460054207500354044000404e09106406103004907003840034110501000b0007054000c0380000031410b20094212280c12050709481e143d142c42c1d1144130040030071380316120429041c880d80208400d80403080310244903d18045c0e070069a034251080382241d00031220725810002d21b04844021942d036079400e0340503030301c00c24001c64030030314500f04140c0c540701e6074008842d503500 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 397605764 1250 397604514 397604521
    0x10f0c140c03041809081b0d030c02060a020f040f090203060109050411340308040c09020301050607030e0f0d060b24160515070c12020c060706020d2706060509 70
    0x1900e04a40806460b1545400b0102030b00004d005c03206001400e0002c04600f03ea00d501c40070a0406514004d80201d448001d45a6001ca007510400b0381028050381001001c15400c3c0101d4005051607131200c80d150340740540e980d150500b03181c4258089083c895010040c4507081da03004030b8400042c00304076000d01c9085902042c003e6076101d0b0480316280000b998038858500880002044040e00440110440700850390401510005040b82c045800f1910000d0208900e8441e10980e8186c910140031142000002e68090303c0203550003c10681c0990307a001c914800b42e80d07940c858101d96103d4603000c00c805c5c0040c8180006602c040c2804462002ca015042e072440c00030105891296102214011181e6030900300381d4207180c141000b4949e41d0180d1400c11121701d800800c5220028424140041114081803080b6101d51810f40000e91003030082202c940460800e801034990205508800581501c02414008910400c10b052402032100e403d04d0001303101e698460b0b04c00801c1d042c0c420008516 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 397607014 1250 397605764 397605787
    0xc0d0302250c03141e0d14030a020d060f1403060411040b1c12020d09260c0904050c04241505040b0d02090f030307030c0b0612010f0c14 60
    0xc0c0403080014141d4041c0c84003040c40002c5000070000c2d074200030001d5100155506a54680b0b00341585042c90440e86219003100040024014050414540d0b41a0302d0a441c0441040c0c6580050941000d0799000c2c01140c2d0074400c284141070040c5441840580305070b03d81090103140c0500b0340e0352503210303420110400002c22125400442010021280003e0044142000450703032919242031145034891804038a081005459525858425075000c40d14030302d1340c2d144100c44c0364050380034101410784da2403015540c42c110f0b18203000c070000c0903500303448192240e440459505d40040b10b0a56a42d0b00c004107060302c604051050007482d0042c02412207080420005018003030b1071910600c83e0b40c04030740925a10852181d02901d010b070120350408c603540c26011000100be9080b10001030321442500002107090b25002040700d0540341d040d00c500c4000c42c0d094840780d121041c01811581c211210043e0f8041500007803007500c11042e000b40000820006500d801040011111602003061201b08600034541 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 397608264 1250 397607014 397607047
    0x220e1501022e0f0f2301080c01120b04092114071707020901120b0708060102060a150b0c0f070501020c0d0f030c06020c0a05100b10030509070e04080c0d0302 69
    0x10240c0820a1042094000c2d020008149507082025028034000d050030500c5010380201c907803001205414140015070034906455101d00303100c1c48038540d000e07038030243c2194010891403004011034400050307a248004c0115040d102c0c1001c040750559003800c09403042c41c0c2d000d0f85c4c00c003800001c1e03c0c0c9100064034041d002e580c18451618041e194900a844c9021001801703001c88045580c050106092569105501441c16282030000c5800b0314102d400100c003244204035441c441c03001680201026118585201c004080014241c00790401c02d05001c070300500c4140003488943e241c03600500f00000d550350080d0806146800c07240c11900003a02c8420142e440f00c0c2c441d56203603008441720140040302e1a00740c68540c44e20400502803030002c03c0c1d0380d44006000c94a904413500420585a45c5120000d1a100f286c0301fa10180e07921110010000050038800c1d0300191340151078000301e48856468200006c12a00100d9080702c0740d10001a00c030200200c24401c1c0003503084c003400d0541c102840d451940008 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 397609514 1250 397608264 397608313
    0x2010923041d1504020a0305011d0d051602060711040c050c10060506040b0c2803180f1403010902030a06050103170306010f110102130603020a03061202090c220e150102 74
    0x3d5a9a20002c2000e5543d00800c1600030756001008000300031710450074450340358ac2c140035801701e03000320010a11218054022220a03000107001040c100290f42d080054a80007010b080c1d50064801104001548036485440070110050b1242915100000070b110325040c103d00f5088003190a003a000c10554450340d050b07800b41c80403804901d486980d0007010a180c18411b504d80310400d4501c884510280e41400486034641c0e000703654402105040c12041940f20312148a2800b1a070150002004210029902c1d0440e044005001007456a0160006882c01074422f03c2903c01e60f503034000420412141562844031040302c2d55002c1d0541c98140c1c0044c01070640350b101c11091000c2411119803852084d4120b5071110105d03461865043d0300d0380760050007504000c240c1408079180901c040f40c911010300390540101c0d4000c09001413542c9281c07080400e07400c40c45c012140344190741070a00c00480002c000320f0140a46828400c40c916024407660303444413008480134159003021801544441070903210b40c41 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 397610764 1250 397609514 397609543
    0xf030312010b030705161101110c0306041407030b011707080619200304030c0302010501050607050c040c05040e010e09070605091c03051b030d0e070f1202010923041d 73
    0xf1250383c3d804064505202e000102e01e50510040455010000340f9009005031480a98441000ba085020400c1d551215002110b5042d032040000600080400c1d2100300b8805140c01503510b140d6803a07861420040b0203800c2441c00300c0319005001c17032581081081e4002001940010302c0c3c01d00344180d5640100400300d484525035900d07241024485400341801d1040d0034020340d1034565030700d454100241744204218003103005509040000442d49400000d031481650042d01038441107290804100042014201010600038180030000d02048031420040c001c000083e00c070000e07450070401180c1803016980003c01804818440d4030626203404054414050801f81c0e822841c0144d410286d03074a004503600089001000da0501000d070101201a0204d1007038000b0a1001b6040e4144c40f640b140b5003401542034000c0b405030104005076500c1803482403107006042400c1c0c0039440700c035420314080003555400188404080d0071101c5007414032451003481810301d04440b1a21041c4440381d1221000880f608 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 397612014 1250 397610764 397610767
    0x5070b0411041e0b0f09100902030a0f020c0703051903140d0b12100e0303070816030209040236030d030f0f0c0f08160207060f03020705060903090f030312010b 70
    0x355651241c0e40992030700a8002841c03c03004107400090005410416202e80c0140b1402e0034009440c205188044d010392101840b041c141c41c100f8803a540203400c02490810001e07240c0c104180303841c07000d10040400d10380c103a002c0c5c540c031400c5091182c54265044400120242036041e0400400d6118290040c0c580e2007500e01030384d074a030b20301210b0007401d04dc8850340e42c003200780d504031481e25200240c1c0501c115299070090081960400505480e07004c05c40341c40011411010002d50491032504003042043c1e042d00300181000220343c0481c080b0f03003100801511404040c1d1020300000721031040f680d4140b44855482071003003400c9011a4481562001030414580c41303000d0f6156070726581d00320000c004202e001c1080f03441d0308440014000d10080600a0100b1200070109041441d40c00000c2000d00e80d07500202205441c1c84800c81d40c0c0c088215440040603824041d81d0001503050160034050a1103000441e02c844128041014521800e10140d100750f200b04030320007500b5a0300210504480c075850380907 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 397613264 1250 397612014 397612043
    0x40c0e070e042406030b0307050418020906031501151413090e10050c04050a050303070c052e0806030f01060f05060904140a0905160602061b0409020a090503010c05070b04 75
    0x310700070003828181a83c5000420100d030b82036260340080241d4804804680c005543d5500744412070705000c1c0c0e207084010b0050140405801c1030b4084a410060140c12a03c9034160140c1c1c80e00111170a8100e40301800b030030254500b08640c004c011109414551080b1868403c0c0303030070301c807540d0100780c459001ca04d40c5403404501c070100306218004190b00025400d0185140c80c180301c904560041c02070f24416003010750007103414280001a07495a55010b07104101190800c01005405250312801c01e50039000d002c01c9082d0700c4007403094580326007800e03103528090f410610b080604140d03101070120700c1685400c10420456640f40032500032104296840c80c2c0e21070440c40807d02824880d4000001002c4460070300c403003280075900482ca498082d005031004c154000c07130030040400640c0301d0200142e0007800030840c42034010b00110b841000340e5803440e21b420740d208000020780e00168110f40100703140310350812541c2030a004011109105240951034000a65141e041e40640500068401020200c90 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 397614514 1250 397613264 397613291
    0xc02030405030102070c053307020f120114090d0c1b05060a17010b030c040302060318010c18090507050a0f1b0b150a03021302070f060501030506040c0e070e04 70
    0x129030142401400a6548031090304200810942d0741c4a40ca0050040341c044025500904000010100030002c001070541039461414540307030064501a42d03c031903200c0e005020341d40c44070709600009410000105101c45c83c645a0030383d60100400c40c003101d401031180845200d078400030320b80283c2d9104602d0920500900085c01c07501900e42c03c242d4110344c0002d148440c40f50425407060607180380088105040c0c1e00c2d0500e420240c00203803120034080109000500040c50404080c0d544031503042c1c2d041b01340d501501c0c01c040c02e503411066a00007040010800e540b0a8550445803c06003280e00018029818991030080041c480c4105080400c0341108846442034480c0780c1e80c0390500e10308942e9100c6d05000f42050000c000c41a110a900c82081c004d241025060035000d610480c0d400070b18140003030184480c80c0c4080e6002040886c3d080303011404000c0092218030541e40038500402c02403144d0700c0c003850b0584c400905600f08507060316402c800c0150003a40030780f544c06110410b480124515568011 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 397615764 1250 397614514 397614517
    0x509100c051608060703060302030309090703090c0e0912090f04090218040309180e0d0f1205102c070e01090e0f04031e020606061b1515120d030c0203 66
    0x100034420b009880c04482050380b880c040780c0950b04018181c0708145c031500030590440f00c15110003074254005005802e4203181c010841584268541008201c00c5400d0350f070300c600410709412080e10458801c080c4011b501040201480c00b03202c03101d02c4d501e000072540003c2c0d16890040001031046840365005411511180701030318000041412140040c00e091601805004807401500c42010740c84105041e41170a9015071662401002e000d4a0720041a010848403100c04880074810702468400480300040349100b5070b4441e401003113285081c14180000c1d1002c5d091801c1002162a20000e05030b102d094680228a4109219050184200705000c1c010b8950562951008000f8010341080140712540741d805644168482ea0ba98054200c214101400c034160b841c02c0c07680180d2110300020402c1c20250003c09503e804c03044011491440c2c640c12a10706802407101002c0b030601101400007090082060001804003207908064046140c51301c0d80c1d44201d4ac1403980201600c400700e51194600270310 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 397617014 1250 397615764 397615787
    0x209010323030a0f0311070f060b0f030f0606090c0c06010e090c0a030b07023018191e0303080f0604090b281a010f0519110c04050106050910 62
    0x100b520b0711074100c0c20303000e8032158503401c03c000801d080070030494807001100f04555559500034103820b10340c1070a0f00c07004000d0540c2442c0e180c00c0400b0002c01d00710b0382d030200440d400c0315800f80c00030300780d900d08030050002020020300100c100080600c2010380d0884046802415112050340c00362007a80e4552010b823418140d02c6c0800c0c4c002d6800b00c03010080c0010904050300c691000c4e0201c540240c5401b519040230b5400d5030707030072104134400c449480c1185541001000c0300400310b0b0a115900030450000745204840350000054108006420405081054102c0d42d6058190b0703548001945140c601070030700c0074018000384034610000c000a107103036601d0703108010a503040154901d083c03070480307007101c82d40c3c00103840808460410040b03402031400781d0103088040006895800c0c400d200410064882c00c00c108060410b12509004100c46080c000c00030107984c0710344e030340c0b00b0244200d04400d1904010301048814040c60416005200c0c940c1c00604851114100761203030300d601c10300100221058603110 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 397618264 1250 397617014 397617083
    0xf080f0d050c0703020a0b031512030a0c03120c0e131104050d020d060903200c1008070504080f01050712290a0f03060f1b1b0305120709080d05040302090103 69
    0x1c6d030103e161100b900c040c51103800e41d0190340e000010303220100a82213100c4410400c00364800c20511100c28410300031019014428200361500080c8400c10000b502c0300f0044241c0000c1e00039201814a150144948046490b040c0040050400840124820340714601505014541c020351110454030303240d05c0d283c031013a003042081210010342e01d001030050082d1401078054a50b03100c1c040d40002c20202c0c003000038400c020801141d640f0b0f08801a01c02c00c0d401000a07040c85014000042c1c1e8010a1140c02590315000c00005144d1915070005400501960f20300162180b50064850540d01c40c1c400e481c4184152841c0c144484003e400040c0708941a0f401100f010b154594001042000030340014081084548044c0034903044003aa894242c203c40b284076001420398001c42840e0002e408003c50504e0003460501d02c0d107a805a0a6440102e042d10240000341d5040c104000c50f103404e0100402a41e02440d10300d15017441c0d600002d02d6241c1c180006004411800514000e10304805c6010360407003040d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 397619514 1250 397618264 397618279
    0x50307110d141c050903102c010b01023705011d03070b0a05090307114b0a0b0f040302150309010513032001060b130f080f0d050c070302 60
    0xb002c0d915481d807400e0001c46078800350100100642c07502840a807080d540014001f03183c109074410304003010b01124103085400d110f034040314050010302d00b03610b910106e565a00128a040103d00024a40783c54100c14041c45000707001555081d00200c8032484a900c030f44a101103090030541415030040c6000311030030822041900785140d1208020014190300390003408605940d580b984000c4050b03a800704c485018503001000350b076001030042d070310409909002810381d5000081c26841c110420102240c20901441c1004a1180000c40071101c00715000c1000300e03d0482e00d4400c00411086582401004022a8040f0b210107070070001c03000356801142c008242540d9980c24500c45c201e00d40c81911070380443c0d400c1c840080c1251001c408400032150b41070750361600e2905800da54800307081c040c5500044654031030800140b5013911a000d89039000000003400812440d150108580d20040c0e032221034140c101c806c1100440c180496003d2527040103062540e0b44002c9000d4150034552a0f41000703501c0244c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 397620764 1250 397619514 397619543
    0x30305090f07150806030304060921020a030b04050c0328060912030519291306170d030908070803091203130b01050d0f060b150c061f03050307110d 65
    0x441d0300c9051101c001351550700040e02d401c020716880e0b10503405104c020540f2144204003049a0700c418103100c840c0d1038440d000350400ca600003101400250320039101c5050b44030a000c1840010b101c621405d000c110b000380080c00041c859014110f001309070301d80c0100300c101c851505101c0103030001c084040d0711101a01c05034001080203401040700703461950048641015203030040390240b20720158412072442c04030009500c40c000e2000d0034091031155400410705410301e140b180c41030041401030011101c2c0f8003542c0000d01c907801c5c901110701c0b1403002014145491500418071030b404a581064211012071703980c2e940d0000403450154032201074142540b00108000700c0e880f14001c0d40c1c035001d100fa0526a00c5e6640ea504100e040802644054000361000303940d4400110654480d02501754042e00302442541c103007030f403002c040c3c0100d02c000d0201d401403410002c1c40341001c104041d000315a2413100902a045032034070307a42d90240210040803100c010306c8a80c2683e0303c00410040c1300b0b1384001204a03045 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 397622014 1250 397620764 397620779
    0x18080c030d020408060708010602030c0c15040302031603140d0c0b0604021605100f02191d1e19061403060f0901170d030b030c090c040302190e010501020c010507030305090f07 77
    0x106c030f0800000703a4000c0040f503183d201108491440c640f090003481c17600c1070882040b02c064601c44032113413070746410007001005031024001100d614040400523641e0500c1e6040a56a1005c840c80c0da00c0b458010030032500315513070018a40050990882c00000c03055480c100803a000388181e21080c074451124103141810810300080107541c0c0b0740c1800d07050044480d050070110990150700c040e5140c1d14480a403c500d214031a20800d05c5c1c2c02003a0108040284182011802c503070701c000c1c0510b400f000075804020090600039903055070040e8505c54150b01c9407a000b4001d24540c48144c005502e0700b400004078440780d03605440c1010441b8000c11008071561f581a0101b41c1e19950318140d00c06028401d0540e2126000741f0601006460140c0a02a13108000040042052008011800d8544107100220160301d43c5101103d09030050100d044100b400c020b50014240710590105045501400954030145d9200c010740701c070107605080200d803580742c155081d405d1800342840d0741c005110328440001c3c0413 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 397623264 1250 397622014 397622023
    0x3010e070e030105010e07080a0906020a2c0a18020d021207110a0b06060703090f032d0c0b0d0e011121010503030f1605030a080f060418080c030d020408 67
    0x529003915070740798292040c801d250a0b6a024894140509070900000d14070354000c20b041a4048202040007030b02d854641d0b1910121b80140042da03000401c115403100c1d1040c40d00c1d0340ca40508096400c0b0b070802c801c44400045040c0018041c0840350211400c001b581d100b00c68041c0d54080d07031803003025134440780c0a010700341036154102d4003180080c04130308021015400100344449140c0d0001c9050500b99660824816194403524040341004884000000c2c4540030160440245209003001045a211010b808400e01d0113040c1c19001800e20b8100c59001510002841045480c2e880000c0e4a4010205a010040251785010b0517175500f043e03403c034101076910b4001c00c00f540d00109a01c80000c001c20f80c580b180e18007400748e0364042c1c0c410803100c0000b24251003d400c000340840307031117503060343c6660301c20741140c124071080000700e9440c0303040c4901024400b0400d0340c41117082c0c508019032585094100c0d60301c85007010191040200240492240400340111046203001c0e94080d03644503940c40d05207555 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 397624514 1250 397623264 397623271
    0xc19080d0f03180f021e150c1c0e0f180f040203120a0c080c0f070303031a010302280905190305010c1106041707060603061a0619051b010203010e 64
    0xe00d8400303c0d0340f5150200f001c0404482d00001000ba40a08580c2030018400140780803101c07006c02c859000005039a030340440912500d075085600c2c0c0f00c0c2c0300180044e01d0290a440e007134010040c40c2d07511821140e40140300542c8070074120781c00c803101030f0682c0210f4208074075940b070502002c8488041040300c13600704403402d001c0d42c400e1b0100d8804003c404444000d900544a01d0800280d06c103a01c1030101c1c0310781c801707400591100700c10383d010118100601454550a980308070080382c1c462095100c500380e40c01c0c4034082c402c002e080640c50705036000340e2070103801c03061518052211031803105c8500ba51310400740c0c10080c08000d440d84030115025641e1002d030100c6440103c0703880d800d2106070070344140705044c2c0c04030b00f250040042c512515a980c41c0340c049135401461411104c41807081a0210b222401600021405244c0000388107240c600d05410001d18007100c03901401d41003140105444003983c164803203034254545151a00e0400303507010440051341d046200309600200c00400d030700c215103404500 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 397625764 1250 397624514 397624517
    0x91902072001110309031e01060b040e040b01050102010902100f120501080102070506090102071e0809031207051605030303270304030804060f08010b0711040207150b13020c0c19080d0f 81
    0x40400342c40c4403e99a80c031490000540507041411076000d401d0048840e00000200c881c0042415612070b407248503941c010f54403110a51550406010502c01d8081c14140500001c0c030091007000d03180e80206400c5421081e540042214000b82c08660034450500004200301b520818480355035a0347d02c240c041e401c418070540700c40c0102000b14868010520031a002c2550041d05040006010780c9243e08400002c0015100280308100c55000340d5402e005180c0030a0500940381e442c1c1609041c010325242070030aa40081204452090150b542c001003079071b502507008418014400400710f0282d00c0740f01600c09000c0d00c1c0c030011902004200341000980140c40c1981c2e161038001613200b000f02e13036001080c880c641904800700010400b03e500082c2c0c0c5d802e041030192000d45006099a6012600781001c40941c40b110b0307a0701d0245d4100d10f8030403080b9080280da68015420504a03da05648546112480e41d202e4603500d2440341101d9540c030040c00050800000392620752440701405002d80091921540 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 397627014 1250 397625764 397625777
    0x4060b0d030f0f0504140f06070c1d07080621010e030c011a060a09050d03090302280801090201080f040c03050a030522080a0f08040f17120306091902072001 69
    0xf01d0b451085042c1e0301280c01001e84802c0d0ba078217900c00d000d07030f41c2c46030300c4116004071b020002d12000c20b41043e5084e00804565075040090540551035600c04007001c1e18035010000a42e05000240d5180222152003681c2c4040b00304485094034041c60040c84010310391081e42c0000b0580f000003a0341035004884403003400300e410f050305051404000140c4540c046400c042164084280080d00385000b071500c0080c4030b41000459241c031b82d0000f42408003040e22103000400079000f100c1500350b04000203002009404028840304d5096800607043c0d28004140fa24a00b500f90002010701c64001d030904011a0010140d5280c505103050081041c0e01c0040107450350702c58040d1415010045480f01e02c100e52048015000b000d0395943e50601c11401c048080c1c1d07201c0303801d00c0017150103c0a21480310040021004000c0100122001d007424030720a0201506600024410000740d0b0301c8800113680e000140c501165000e4030b404080000a008040300030740b035101c0f0000c03815070801d01d420520007280400d80b00c94 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 397628264 1250 397627014 397627037
    0xa0507050d02150a03020d020f09150a1d0604051008041a061e01020a051006031109100303140706020a171003030e01050a1b080912060c03040b04060b0d030f 69
    0x100d0410401d090003074102c0540360002080040c0300002d44600300040c50054604154400c041c401da0704000c0c0d41340d0944900140d803030b080d45000d61140c4000140c0c00600f0b41072000000e4040c00d04100004146181c0c05001640d5049075a01011980a440300a21601d6800d06001c0000d16865048408503000d14407981010500766100b88aa0f2144034028083c03c080b2103004241800d41d600e880c9100c0c1544030345044c0f0000030b80305014040c0040701306d001c0065000d01e181000034582c41156200c034000c00031401440781d80c040800408041d80d415040c969141c0e102158141c0c103601c21640d005d03110324808903101000590094880c009400c08400c1c80155459001c5011058011844010046400350302040001c1d40201e0280108581c10b05180010407032104401048c0e001c100801c585c85a00095580700c207103840700b01d004ca0440000010500c070328107070f5200003241c0300141025010747c000f00c00140400400d41c21040d001d29001d001d09074131080503d400380a000308403003030034042480c2d641c40 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 397629514 1250 397628264 397628269
    0x602030603070b071707140a082d0a0305040f0609110f01030203090601140607060e010608010e0a081c1e0c0f170105191a040f0509010b0304061104050a06020a050705 73
    0x140d03520f240e0072945c02000e02d461302c04120440e41c0100d40407120013456030b420303c148900501050130a0340c010070712a070303aa038041107074500310864000060030754000355442c00000d10040c03010394407580e0b02802c1c001680d484605110001445040c00107001e2802e0085080400c602402c484c2c404010643d02c05404000e1075005400fa80811114441ea9070301c100010060001d4503808481074481c040e00c0d007454031020340ca85e80255100001d024000f45e440e0345041000c0002445081d14046591000d0440c42c59960f540d4007482c4540700132504440c5015501c508412542c0d40015a4440c640064918142c0c44001610180440707041140100720301340798011666014110805c1068503900e1506150b03809d050403c14030302da100c03404207403001115002082c000007501c6042910004000b00c41d45076490405400c05401040d00500d000d070000000403c505140c1909494020b903004101081048002d105030270703d80110703485960310682d0100c000803003d07000316585030b455020340c041da01d10a44032003d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 397630764 1250 397629514 397629517
    0x3050309010e090f04060902040f0e28020306010e071404121505010f1208090a08151006090501030b0114030a0f0609090203030909130606031109100f0b0d02090d0602030603070b 78
    0x420004c40c042c410005030004400707a0011300546d100904c0050001c80003281c003002c55102004030701d582c0c1c1c0480c440e40c4030313070a8038258030811444098142e5068040c1d94040394a0301c206211703401001032044042054103000780209404001034405864469a640f52090082c0000034003d071080300d10420150007801660050078140c0340384584803266541740050900307450341c50080c103860041d02440b01c5213003503540060210081107100024811907103041a110301180001c2c0070501f42500b40e034810441c032a00800c11504494003400d0000b0a00400d50060380d60f0340c0704010703c0e081d8090000822038400d55580c040802110362840c20440d5613242c4a80d0b41c103c0d070034500701a5050703000744a04100c1d45417016060b42c0c405100e981c0c0984e604202daa0756402c0c2c5001c0d801c226003068040d0420080d6060419085920941071008480d4041c540f69888440c00094084c60340c120400160542e80e2160035011102d60180183c01819001c1c02820b000e0002d4000341d80b810300c00d010762040010780000110 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 397632014 1250 397630764 397630771
    0x904030f08160f0f0905090103050606030d02030a0e01030c020a02090f1803160b040312020a020601060807020a0b012108040e06190b041e050409050c03010b040c050d0e0f0703050309010e09 83
    0x12650042d608028000313941030b078180c54030f800412165960101c1c0984031038001c41c1c0210300c0388004185500740321007014200354413041c004045500c2800346400c00d0340e221450819011081c01c0006005207600da0490401d080070348081e401081a8080c001b000881a110500c212a80c400c0d0401d6a60f04408050b10f82c80341486204c0480380c04103c000c046442c248120f90003510a0030010b01c10304001d20031030b050b6084080d072480135800100c01000001e412402e8254030110701d20103000084c8007551407149002040c042e04881d00103c0c0755903500301d10641e0300303000c9064210550a0703d03690383d04039848011408503251401800521141c0800802000344c07403007034400d4140480d080908003400b003e00f641140d04150084c000381b01d40001c0e2a1503500c660400b1902400c0504508000c20382450301b03681071080c156000c1c0340b500588542d07050788031090f40c1d90031911040c04607032280f22030805490000c20750009515070282610010030024000f00600e11403c0a8803596aa40030fa5001c101100f5400c9 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 397633264 1250 397632014 397632017
    0x5010b030d09031e1403070309050103090b0f090c0a1e060903031e020111030405030d110307140d02090a06020a03031104050a090b04092003072c10050904030f0816 72
    0xa40e428000500e1040000300c000c40d010f90a5205944e403511161300b000c0c50411000c803d5040040c51509050b032000602c400340c002801d040c41006599034071004012001005150802c84a4011032104c807000d0010642d072902c000d0030303448020b88035689883d20b010f005003c03001c003804821000440c10302818441088070f805842d1140109962910207460046010140007103541e95170000000091341d0f0003460041e0301640066460310034007101c1a080301d08034162403103004c800340100700200340e200e42c0c181c01c004000326415072112241054180a03000305100240d12010039500410320503070009035000458081d9809000549135124007003d148500c0c010350360005800e802c1444000d40e9a0440300b81081c0180000503011229240c0010043c1228100c2c0402591b42103000c0491a081140304050f0580f24540000650a40c03020703c00c0d5061075001c2c0c0d04e10000100041e0240b6060b501a03070040801500c42d00c05881e140ca40200250680d40d05103001c01c800002081c0c03501c00760300318060040c269 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 397634514 1250 397633264 397633277
    0x30601050414010312110a240e0706141306020a03080a1b260a020901022103060405130b0103030c0c1d0c0c0c06041d071409131d0a05010b030d 63
    0xe58440c09810340280c0700c005d0900400601002d0720703d02c104020031000e8014010003a00c03609080500c40d41c04002d000c0109140d0810404010b0946c011031400f048910380c0c14510f802c6042c480b40490280034003401d4184080f95000000b80e003940115135030b00308511a6a500240e0340c0d40142d1141100d1012000e03074078840d10540e000c0203c0e80030304a01644c6a03450441d40304c55466030411110145001c598980c0d07440d40116000d402d81d41c0401c018141344410120340000e40007088240642e178000201031a12494680020a0100c045510700a15003500807000643d5981c4a0a0280600800d48001ca523200d40c60f080c00541c074040f08002111061042d611230f4820307240c0c0401000307140c00201d02d100759801240002c00c00c81d590080244010110151042444008191000e0598000500b02d1040c021440c040c0303203481c0100c0d0304a0700107880843c0e40d1802c0102070f064240c020040086e0080200d4a00c1001c0f0400760000156000c03201d20880080c08140510001d05031202200282c150103da034 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 397635764 1250 397634514 397634519
    0x10030201030b0402090904240e1018020a060914150d38130e10020705010b0402120402041b0f05160807080d1103041a0a090c0801060503060105041401 66
    0x2180d00310010b00c19009001600780010b030000505840b006850403a6001380820507207080044030a140c441a5240c0b01041280b46225040c49440307072251812003420307507540e1600c0071120a06141107010190042c0c003942c14a074a51901402d81d400c1c40c000c170f8003507681c1281a401107281540b8041100c001d8584a130b07003403121500914005d89910000d643e1448040c1e5041042e44441c00300000960700c400f0134030b02340c00c8244c030240003481c442c501c290640c260070202c842403141d00010b80851410085400142c3c2c44106080076030042c045c400003668420700015000e8004001986000d015074000c440800c0070701c00000508441041c042c400720007244011880c007400b1800b50000d8085043c00c5940c210303031608580d58600d0258000c14003244c082038003090f034100201c07241c0300304161160313420706142c0307181080d1700d860103002c502c00f4403500003192410000c0c0c007810300b58012a1107a0381c040c0b1101440c644a0303010b240606018003c4a0080c842ea0b00001042d180500a0a140c5406c91064080c542d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 397637014 1250 397635764 397635767
    0x1061407031b26180405090703120c0c120210020a15090c0305030406170a200a02010e06012303060105060304060209030307081306170f220204090b0412050310030201 73
    0x1a00000151032185048400210950b02465444901a628a04a5941c00f01140d81300b541c04c0c8003c40450040f441c01d000c00c00780080024280041ea90003203130303405916030000011181d0480c00d01008000c0602407000041000c105900c250145100700c0d100000001511f82c01c03642c03417801c0e00d000380017440c49007800312080c0c140c1e43c80f0f0b088150248088000d115200c2d05c80c0c0340396a000703a01c56400a02d0030350310000039034a40341c070403034102070004004c0c49401000203460504068003445101c5842002541c403204a000b5401038000f500d04800f0b8485541c3c2d904041012002e592808000d8501c2e5152100c0b02494003040c0b40c0d06842c0e005041b1400d5441e1034807504002d41103580c105800d80b204020303440100301900d0143c904040020762070510542414002003c4074003044942c1c00303001300a82803040c01c690441541d544104041c0100020140f1070160a58040b030a94010303404c10b180000b210144290480558802c9018100400740c0d00a100310485180c88225041c00105200c2e042c14070056 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 397638264 1250 397637014 397637057
    0x71b051807030c05040b0c030a170405030306060f0c0d0206010305060a0c0203030c1e030a09020418120f210501080f0d0914040213080321070e04150f0305060106140703 74
    0x11180c44c94500d040589985109035654002041140194804a40d141f111588080c0003030203000823a6082031113081503500c56036a40000f07000da43c404d49006c41c030502018464000c1e1034111070170100300c6920f40d0718010080c6d01c8038020302054804d0b005010000d500da0940d0b025041d4940c4040e4003c0d4916611a0107107525a084003881c15214004041080440503401001d903018030f20b4201d0008614109104000450f2840c0c0b0103110003041004e51800841e860500818035008203091200c07111201c4001100c0c00b038079a0a5030001054154032102c10403003d42d00c0617060307500b4001241c1000041030240344c0d903041b210086000050b52070405001000c190000444c0d20140a4000f60a20145052480c2880c881d034000c1c01c19a03001217100341a40d003030200810242c6440400000c5581171441c002050070000440c0300b80130b1525803e0a103a551658402140105a070028288a031502c0e031a14035142d0b0000c0c461034002818001900ca001c8040e403003107982681e410b0304c40c001c00e0051035803101001d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 397639514 1250 397638264 397638281
    0xc0d0f0203030f19030b01020703021302090d080c0d032714010b090a0b01020615011b03050712050909010b0c03071220010b1e09010b0c0f03071b05180703 68
    0x2501040c000720000490f0038010300f040755024550b640c0c41c5080c001e0018211105458110304541c032205080001d40c58a040d0450140d00b8080050380e104403c0e030101d241d000a80308010a10a000a041c03402c21001080c3d0961444059800b03109004071109408400f0303a04210000c0300f5482c1040520001e01c0800b18008900d40040010405851042c000f41c00c00504032999426991a500d06080a46c0c8c1881201e520484241001ca0300b640d0750b200003403e0413a142d03003080b904c030034503c4a141818020000d880300f00b03a1210b0103540d1080700705001480d54000c03660450003a80c111002103000e11358541522840c02800c0000d6043c100140c641c014241c005121078024407102c181c1340704110342030f161207100c1000c0700400403481b074401c4024840004401c0d14524001021850400f0507a910b0010881c11a40c44030305041c1c444220301070082c01d058020f101c00302c41d48400101c4c9400c005002025510301c401404040701410390360814411394521542c0800703527400c50800040e89a6000e44e210325003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 397640764 1250 397639514 397639519
    0xa050a052205010303020706030507020613031b050a060e0706051809060a05090709060e030c1c08041d060102060f091e1e0c0f22021c0f050a0b030c0d0f02 68
    0x1806601c060041d0845000380c00580058109100a0050f17a03003500076690803007014401440d480c50700320b00d0000340507102c1c040181003002104ca80c00c2d41385048510f42d43d1007a0054240c6d12001401d00d82440140102d021140d40380c00352110000d101800f800030b8801c03885000301a9511405208108200310070020300142d440032540d000403403140c03101c1703900300d110309415280d03003146a040ca18081c00d90440160030714469888100300d4415a01d07841e05001e28400b1007280482c607804180781c210b02500603038000d40a001c0c030200c00182d040d41010b40e40c0380070321f400307800359403098613070780b521007202f01045503001c1b120f46c07000381c01c5481a80c207171031407000d043c0c00841500c0340024980e617a64040114601207040075405110001d480d85000d0006c41546501102c2c8420013600302d1082142070390441148a64443d170129000e04044000e4403250002170b010441000004100c0000c1c40041000341c0750744040da454814408011704001405881c90705008040c05000c80095541c21000030380a0f0301280c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 397642014 1250 397640764 397640809
    0xb2701140418051e011506050f0409020c0313290c0c040510091a0120030403020d0807030e011722080a09030b0702011521020d050c0f0a050a05 63
    0x140d860100314103020300d920503000b400b508101d0110301e84c04070b90300280c5448940d1510ba81c0c003031143d0f01c0b02c0b20481125940d09001e5200c4400040001a07802a9400311503000d000096644107030b00003000402d030358102d10020002e602d854840c259110f8480312030400d1140c1680203c40c1c40340c02c410010b049101c0c60401242c10401c0355078081070584105440c03403003958040700070900088005014680d025440070021024503040300c3d000810040c10700b68200c000c0014902c200f01701480a01c101c80148d034010300321a240203c41c1c40c05100750343c4040c20940026100d010200c009602c00c90340740003c0071041c02c8841003a1600b80042d010700c18603040000e102501d903010300d4000f800f03120180115411689501600610b141000d14039018010006030869150070441034641d10707201114016911042c1054000100c0e40040010503035002c0c101075405040c1c03017241010001d0001e09030200704816074804910030414400e0000341c450324003400d5031004558105014506040202c610140c0c2e0340b01494 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 397643264 1250 397642014 397642031
    0x10b0703030b121501080f0f0d080402010207080d020a0b070c020a051216030804080705060f030a050601090302030f010b15120604090804030218040209070f0c0308190c030b27011404 80
    0x2d41c900051080300518100c01c0740010481c4203807d00c00303051502c80c1200540003140105041c1d58441210303403009400d000032500481c0540e44200241c0c1c0113080c4c1182114071141d00103070041d50310510b0034800c8038012043c000196400b0310035042070321019805000340c80c010742800f0400c8a1544092008509803050721800288060544401402140035803216543d0303909208a040c10003070076400032030240700304010040340307410020100c960101488500169035252040121040a02580b000e0341c0b52151540340c070806941903110001800b01100e5a04c610070040a4080d25030180c14119101c401e0414000b480c00d00b002e8101020080c07180240360719140e1258001501d1041c0c0b2141100341203103403010402181018648950001d0640c2450310550303d110000800110907070b44001d0401c182000450042c03207400c25103500c1c04012402c248003240d00b40340c0045c010110650298440c400700c0301c1c00041070350360b213002d070512900607640e0700d031a40e0800e96030b04088022071099a42007507549854 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 397644514 1250 397643264 397643299
    0x5010b0307060c0203010f090b0a050c070b090f061b0703080a0b0a15020c0a1a0a0c0602180f0409210c0b1608060901051c0204200301030b0c03010b0703030b 69
    0x10026160030f40381d40210401c140189401c4624080300103002d00e00e442c45c01c80104045003403c41e0700200e1854041400ea1329015070001e40c6c0181e04c402040008d82030140802d0200c042840b0600e40700180850760a07a4808800d0b07014075007c9217074101506010420003010911411701c1642c08900300c8008a44c69031041d01050a0703983d5507100240c20240072007801d050a605201091542c0003c88130401401e007846140f0400030840748034500c0c0c4207400240c04070340900501c0803814103030f0445e030215100c8282d1082000c060042ca00014440d50500c8918502c9103400d101746001c054010900082c440384507108088907030400380e4100c05001c44138a002c400240600c2d241c902c2941c841c10620228115002c01400c094405480180b00e010148010305c0162100d08031245011380c188c03082c100036a003a00205000b041e0503001c0c0d00100038542000301190004400940c12240701c0c481c14422550b901c550002680005e00410302d0401c02040040c011a119800a04003000b00174180c002240e0700d210f4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 397645764 1250 397644514 397644523
    0x602030103060c1d06390f0c100e1908010e10141305031c0f0501090234021305150607122105090d030b060c0a17120403030b19030f02090405010b03 65
    0x301641401d002060180d02c400500040309100029401048e50344141d8001481e48070a40b0946000c1000c0c13180c503039040f80c0e2a4171150007400e50684078101103d4845035280d0180c800b03200c1e100d100340308260300c11500303000c140b00d450a140103003d141000364550041c1c3e1172118040701404c0e07a0034481071003842c050403c1003420341241c2c9541c1e100012010800d143d80360940742c05130300c00c03140c540c4107114007414010080554015004034040041148801d000311040810282c0006074002000c4079a0103940c400b207600c617a00940704907100001a6281c6810441c05206c0d00c00d00805c0d024100002c5098030b4006d07900c0244440c07961002d200804c0b044695001100c004031044040f40d4014034041803510b41610500b44881c50075960785140054040801d55510b081d141c005085200c1d0840d100b40a46450302643c545410031b1001070309500381410000c000c0c1000d2a406486405184428405440500d013014200e99001ba8900e04026041e0200086003a00400aa03015522480c407040165010311 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 397647014 1250 397645764 397645837
    0x11030a020706111603210608060901061208040909050a020d03021507021b06070c0306061806080303060907030e0a231209150a090b03040602030103060c1d06 69
    0x24801078480a141c00c1107001e84240140c2038039545002c012080592a01860840c001901420318031202c0ea02da201c40c0140801c1004805103551501a01040c400d0010445074041c4100700000c2c0101c9841307990000644151150040140008200c2040f080c281d03a00132241d440c1c094000c0e00c0c041c0d00d80d90045640101d48440c224016000880440508100594204c3d0020300910003032905180042d00d0300082d0481c1c100c0d881c8154400305000c010005d910401002841c2c1c041800e02940769100500d848804004581050a5003008404a5005000015284a17a01c01010508030303880c1c4e11400d5000385075920000b89580034010380301001c41d07030001400b43c603c40a04209407001c01c1c031454060a014a18034116a04d000402c241c2410b40e80c1c1400c1046091741d00200256145040d03501510040031030361101242c6400030041000340080ca50103541200d01a580600402c040088200d4012415070100d00e07444160582000381410400003034000f4003580b0303810116103071541416200050240 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 397648264 1250 397647014 397647031
    0x12030a02091e090a0e0c0a0801151505090f06070c0810141e0601110607210c09030b0a1e091101020f0c040f0204170708010c021203060607061103 64
    0x1110300c442e0802e6142e22071540141c100c00052a400c140014109141c054442c0c80764580320701101c0c01301c203401d100c10146500002c12245840b41e1f2095003a000c1e045207054600c45404048000807152103403501100c4440c080c0e65102d14203890f0328108003080e0b00c40c103515504100140300d420009050104001d020f07007001402440b514003403178050701c11b4503090140244200040030900c103035080c94084850055840036005c040669071100120b40c3c034800200241000c1c0318403018400c02e5600500d48450700c0308011b54400403100c0718800390055649807608dc00008503402010404506002e0b01e01d5003204020f1000306161002d200101c507124040031840c84800d81d200000380c100651240300d416240340c02e001a01500e0314104003075444040c64403102d03024913251441c00b441e1110a60446003c2e0811480c5141300302d07003160303400d540d44049020b0fa40b015840c107d076500d4003074000603244910401c1200e00c03510b150769500901030250441001120f6003078032150f001d0f18020100000c0c4d071041079003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 397649514 1250 397648264 397648267
    0x31116060f0507090b1207050c06040308070f0f0e01081b0a170a09021e03010f0905030d0c090b070303090f02030604030c06140106050a031a12010c081b1b12030a02 72
    0x20540184200e44024010500380113102c84100720105c0820192644001c80301079221055892480a9590344114000700b482c070300507501000101038210306c000d401498280d40d40b1f41841012401990800030301c411003000305a50341c0401540d90b02c205812980541d10003040401c0c5061071090f030b0385d540c020007102004294804061102c180da40007415911406060f41481403600d950041040e1400d01021240c001407199146541c42c0c8003504408404059000200f1850003182015a00c070380102a142c242241020307036076600280328290746c4080d1462980380b42c0c54144540d400307030000c2110800c220780004410181c280540d80c248540f84c030550107604d40c190020100d1038802e04035540048003071010f000c600014441d01e40c0c84401d41d00001d03003a0a00040f034282c1c0e4207410058564070740506606c221400d200c07020501064110114100f0641c039900b41d55100d12814042c1c495000c580c60407006000e0050050b9241d446440005031614042500d514150b884502c00c22584215004074030700d43c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 397650764 1250 397649514 397649531
    0xf080a020d0815180a0e070f060f0e03070b070c09050705070312020a0c2405090c0f040b0609010c03050c030301031b0e100e07030209030f0703020901061e03111606 72
    0x42042a0543c8144074001072204a40c902c400189007030704910040b11456140b03c0080c644200f079611280b048080307a000c40b80d030141d0f50240854400303564019903002492520b003005241d0300900045044200090207404524104144a10300c5d07000003d003a1064030812100049000b010b1290303038051001c680d07981d59501d8031414040c000988032115490740343c0c4104010130b41503521407444040c60340e00000190f15042207900060030491200c42550b00180741c0340038041d0310000010680e1a941c001c5d0703070341e05000c0609000c01084421154241d504041b00b048560003d61003107136410102482400c002c1d082c00e40100503246503402c01d030030884010203150181400306500740703140c45c01403083c1d000c501803a140140303c07581c0d042d5a0b845180d4407074007d08080b4280b6402501560107440d406030458260810007054540c0e1210207200a80c003c052450005c07811504c181300c04030f1090300d015414540c140c15010114014840308001c01e40303080040c0b04607a03490340001c0e103043d0000e0290401299080 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 397652014 1250 397650764 397650767
    0x30b040b0907080309061308010f140a1e050619030b06090f2818030801091b0c08070203010617010504030f030606024204031e1b0f080a020d 62
    0x20800340452801d0340c000c002c10003020000004891200c1c4040d02d55644540c98218888400051508000c04d69400c0210410722122554071a011060003500522000c1d11400901c00455511580c2140481050005241c1055a98019981140010b000b40350b19200d105603d24401c8880d4004640911a940a000d0240381c1054515000350f48402d0140c0380d41805603d0601800c1c5d00400021164840440c0081c080a107600c421501c040320b4803400500c100900c0c1c010464803090041d51041850300070f10142044299108000e005440e0325091009440f54480600070741114008076070543d00c990000c20f001103a030440c455401000d0700045160300b000e14000d08817101201c0f074402010310707040040041c9540022040881c020301507030440c3d5207464140640303c08174400c0d002d090700e07211000100364500301800c01c0780c4541d0103507031021035248448201c0350001041c03103004e00001b00ca82e1240c56130740c0107a2164030143c40c0301e044400b08284059550f140305030460890070026070056110340510781d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 397653264 1250 397652014 397652033
    0xd1112090f01050606160f0203120d0b01021506030d0c050106050a0b2802060a110c010203010b27010e120a02030a0804050307060215040b0603101109131a040f0f06030b04 75
    0x1100d4250030110503450f00046c54414540c041c1c00d05038807150b8001036480511407000c0d802203406040c1ea07035030303a40360040014004813816a80144984101034041c01c901c050031500071000100035004481058104842c02c10400d041642d455603a281300091568603580c410000b000d0942c059603d413044015003505151080010b07e41d41824819414100d80d03001c58260ba12120804002818100298011440303014001c0404134647c4000004640e5130a0200607014001d0301d0032a13450450b1007600b00389a00c11415030306c0390104200800c2c0041501c0c113010044c40b1b40140004407100b00140c1d8000a144c803640480a6641c4c000c0000c06021500301401100041c0210740010130351a84401d01c044a120b000400241141070a00042859680d051100c0c8040b003007650303401e20044841c00009045a0720042c500c2d44a00e581c81100c100010081c0240b0902116a03e250503040c0e80380c005000c0034200c11a0416030455696a11080f03010180c4106805036004844104151400703207010180d4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 397654514 1250 397653264 397653271
    0x60b030a021b2505040507020606090a020c0601031401110c060c07030c020306150a080a0f080702010905120106060801090c17040201030f0908041502060402130b03031c0b0a05060a050d1112090f0105 87
    0x3a81486c080142e015000544643c20910585407070105548506004000b07000e030550b190344901039100000300748110700013020545030a40c0c00030010918241002125031040b0821090560400d0740054550b4501001502065000c0c0c02c080c040c00c15627074000382c01c3c404101c1c4c440d60300a561104040b682c0c2080d801400191010300000d04144030103845003000310f0759a01e002049008002030340400c40e4815110f07072000700340c09041d074401406031441c464084e003540e004540000358400000a92000140101c403d29040ca0311401810301c40e07540c109200346001401030341415100d0b0306103164840076100d41780c2e02602622007152203031305004aa080d010081400b07e01103612120502001d40da401c041100c0130410080006034400c0c2c4080464254003e050b140c001254201c00c445404004940214004400031a1003510090701d6000304903043c010b02c031800c1d0000c1c000344a01001940740b41e0160320801c14106e003260034030035104406207a48200300c0340f10090303404c40c11407102021024010140c1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 397655764 1250 397654514 397654519
    0x141c050f4b07020a050d03200d0b040207050604060509011107060e1606020703030e030a030806060703020f0307030801090b01111b010e0d0503300610120903180603060b030a021b2505 80
    0x1c00138080300440c1012510711601350b60346c2c0000b6064407009c81c5030301444003030002400030742d111304a505000d501d03040c0071502a244141088001003a020041c030440d4002da6000401030b09146d0a5203802d40109510360101880e48203422030300424840c3c40080c2e10013440c2c282d00030440141145801032680b100010010300039800070441c100000d800114559201405442c0c00740c4a01841c1001c91604000c1056107140b800000f45401c2416400725803071b416600e0a1509100b8120034800440307030942580030147c0a83c1080f161580da21584c07118000040c0b0b0145840134a112000300010f400784250f500c00c035480c1c0c0c40014440d1109500da0b01c094240d80c8507030b1206981c08a11010b1100000b00106014440c40e201e05903052164000d140c090060310301a14200f1a01030385140207840e89004003002c12081d400d138400041ca5900ca40265070a440c1c50540960850301e4464404010b5000703031100c1c1040c800801c031364005065082080c0700018584205440c418003112210007040d09050708040d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 397657014 1250 397655764 397655771
    0x307060806030307030c020a03080a12180209040b18070e100609080a060c14070b04051207050705041a09070504051c0201050307141c050f4b07020a050d03 68
    0x906a4002c404d43c1c001c69050b08020000e5a442c1c4005104482607030001070000341d02103040241c8503400080b250412481c00410000424140340e50303194141c1c0360354020362006204000034002121100215001040100621019040100c4241c2080c007907411054074000c544081102426082010000604071400c22070000c906020b02580c40300001c10004d000f8545844466101a1051080b00d5950050714201a22050b10780340080c18900c060364291604d1054000101000d50814205d8114551280c002c00c412482e107010b02c4007400243c03820041c5040610a00c012640766804030900c2090b03180d0380c165480c1c0c244803c010b42e4080300e071008481e48181d5200040141d030000304681d004509820000c442d001203100c0e001181c4030b903071035015005500210048607070b505038101d240605012040d94905a84500d43c2c02c4607440d081803038160542c40c082006600186c1e001d525114544110450f480f0f00b81059008407131b0307881c15104c00005a20043c800f000380034040c4504100300069180a1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 397658264 1250 397657014 397657021
    0x50c0115030b010902070c0f080a020f04151e05060304050a0605090604030c08130801150303080a050919050321041401450302060601180e070813020409080903070608 73
    0x8162842c0501598429a600083d88000c0c420740e140301100a040319003442400c5030300e032503920741c44a01d9103004038020b25078003a200c610703407505002d41c68010703c006c00c00b80c001525082040185070b015038201c2e54481d0f0107210200d80b0b03440f454021803181e4090001461540070304d18004041301e0004004803101d400010a22002a62007080c106880d40c00029051304c50242e0300c2d900034200d00b15802986258079000c90049082c2c0c04002c11030440c3d0194442181c50ba40d4201352200342e5a0031101c1000c50742105050506000314481c40c02c460314040c0b01200d040150310800c06004140e1554000c0d0344c481114100000c0101c882c04071401000c5000081c0002c0d2a8507541009010070716902c07a40544610603c001d034100110341410501c0d0980041d881e0404580c1000780d1102c0050b96200c0c00121301d00010184100c0744000d504c00c40d44c000c1c03245d81c560ba0b9000011a100280900705c80300036142040c1c2c80000d41e65074001c0c0380070a80251102035845100204061600c1310300d9020b242480032401c00c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 397659514 1250 397658264 397658273
    0x212040218130308043e060301050a1703120a0b0a050402091f020a0524060a120605040c12030e1905030a02090406060305070b0c01060f050f0d021302040303050c011503 74
    0x1c41c40c19543c5420103020544491600c0b241030103019000c40c80c1c008818000c030100c442c0d40317804002449a030000c241400340e1040c09100b01444240542908040b402d40100201c0c030a404c0c6400346d502444041e40e00701103803003024420a08064583c10462a20389000000034a8054841001000c0899007145000d9004020a051031041b00080c0140540f40380700c1e141103402030149511203035014054607039059500020324090390244240ba00140c405100054140c1010003c102c01e171081d0401d121802c0e40c0136510000903200c0200110303a04041c11400140c0064001100c0b903080b40319888204150340c1c2c00042c45180151540082100c05d64030104001a0f00c0c00701d110300c821901500d101010341d0b0361b03043c400050078241d8401800d0f4460750b1030002d60a104400980204904c42009001c856030351821031108650b64010f039a17114490340c030680280d1502030b140d00c407081e202400780512030369100200012038100340d00c1500403410001d403a00b002ea10a206082d15200c80181c0d10f88a40c4c259200c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 397660764 1250 397659514 397659541
    0xb07060906111c0902030309031f050106050405010207090f1d011b140909040203011b090303020d020703080d0203103503030f04031115070e0405090106061e0504030203010212040218 80
    0x80c042c03207140e13a03081c0840941d1014401c6480750721000d4125107044511142c901514421680714889203464880081001840b41c000c4800300c030016402042c1e07040c10b00540000401e01440894511603484840c1100043c0e1154140c8040c03044800000b04d42c0f6030440701c68a1021254640e40070082a11100d00500b1100025200c00310402d07941143d0703580c0c6078400310303004200b80160781c150844140c14140060794000c041c9401d882c401c0d401c0d24142d41000340c040e80e0f0740c142800001d2521406000d8a51840038039800b46901110200982c0422a0b0301c902c2240e4100710000c030f400900940604546030034810482410390705908800451030b5240036001ca030040c42e00500f0007002c119070000c0a1960a8040004006444450240310401d084c11107010700705a1802c1503250003a8180000640c0e84803061141c002100e405407101901c140760201c0361080302c043c0d4000031040c0701c424407000c805600d003403024042d080ba03c3e034080e003c9400c040c0100607100941720031400390100c1460411480414024 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 397661870 1106 397660764 397660807
    0x1911190e310209090109110d050103050d140f03010909230c090601020307030206070e0a0f0b0d060b03040804120f081216110304050d0501060b0706090611 68
    0x6001c031050380a051600c0380d000f15a10010040d2102580180c5900070400c1029450450340c2c412850444800382c0081e10168410000c8841041c3c001450303a0504090b004860306210b00c424040d1910300c070500072039610702d444050707641c20040c0c40300030307150140d0b91881500c140c4180900d00c1a961000501d04920441c40e1402041c81e550021080300e1403150582d000e0481581c83d0141503c08494500b901d40d00010085400500018200c0048000d801510350079966011a016142c050f50300a820034040c1e59420411303c00000c081c8411034040320400300c03500c0780810990505a051003101400906882000504042c04803020241140707e180c3d00c108110070346006010444186107080d1000d035681d4801c10040c00355142008403529038070b00c510300105036552907160314034154100c0903040f202c07151944034080420071140212150030300252405410138038000401c520409052 = true := by decide +kernel

theorem cover : BRFrame.Cov 397482014 397661870 := by
  have h0 := BRFrame.cov_init 397482014
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397482014 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 397482014 ≤ n) (h2 : n < 397661870) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
