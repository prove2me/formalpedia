-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4680
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:23:39.483523+00:00
-- url     : https://prove2.me/submissions/74f5fc06-920d-45de-8383-20f7621bc359

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 841546762 ≤ n < 841726618 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 841548012 1250 841546762 841546787
    0x20d0e01090605090d14190204050108011503080702010e2e020d0c032f0307030314130201050714060711070b0c071e030b070806120616030c0c021504170c060406 71
    0x4481814906d9011128280310222240d81c042002504580f000e51405004960144c50010001c00800400411018000070f281c400107000722030220b00071095a02038609003001c030f1400f4141c0e103485d69589207079000ca1401600038960101d194010710000d1440060040c080c0b0707485484026041611f9201680c0b44203004080d8500c4114440c0700940311604107c1054010302c1e08001191a4210f510b005400c3d07442440100c0a0180da80042150418036034805420070f0b40c0a080281e80c91105060000001c20142d036008a94400d00702400402c640c0b18910f0300c2d4103040001503c0307a076070f200c55074000b45101c1d0710369900301684188400d000c2000640024203003195144d1945009a036256240064000211501c0000c96480b0b000c005550501221001e00750702404050703d802e10340001d0300d00486680c040301208055031850324040c0c4600401580c1569a00140004008041ea07504403c03a0b0f881070250792420100c2d02c9002c000e031240010009444000280241e05103403d080342251140010f06 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 841549262 1250 841548012 841548023
    0x40320012a1202030406080906130f050a02040501080f1e0c040c0207031202010b090903120115140313020111070f0b07080d0e0c011e090909060b030d020d0e01090605090d 75
    0x40000041c2051003442c42c0c159079600519111403030b0030310242410400a0440c030242e0448410400c152095001c1e000d0803035485005032030362401764244203160040600e00290058074000c000714030245d00241d070244002101c0304035410503020000441c0140d1481e0860000c1e51f1100c2c0340c030201860720b508254103c10491044a0010307076682c030303481c00311060460001d0150750f407512858081e0a114020fa980481500011842e1000c2c854600202040c14410048030300744046400384201d201e02d0840c00c0d202900408592a4141040480320718295550103d010a03103d01311043c0d01c640100d54501101c203211100540a4508000701100c0d41c0311a07011103c0c3e010400030b0f040c110261b4800d90000c08085c0e4014050400c15200161070042c01c11035040e00c8800c103000c0c0ca034038258032125800c01c0d10390850300030421407a0351800a01401c075440820b41c0c11f000d123016400003241d0004041c1c1080d49a0f90711901e860301100019503030a010703801a480020001c000d1311501d81001c3e80c140410a1144 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 841550512 1250 841549262 841549337
    0x61801030b090a1b050306030d140f040b0310060c02030a080c100c210615030e070801110a17010b04031b051c061a0f0d05070b030a0204032001 63
    0x48000303011442c1c00c40c2c8060000d0380e6892405112018070301e4503003c00325141400c1d813079030800d140041d681e600314220000401c101c020450542c010501d05451510419551080c1c507075403242d90b031007043c0d0000c403410911035019140000c0c0c0c070b0307126641c41c0c082181c028020b88400c001d1516120705ca94040120195244074880742c40310b0280103840f440d10065407a55480342582049000c20704040d25640b140740d88541000414010340c20240c4a08110390a81d080c00a50f020004041d541080c00d00e85c8a10340d10751a014507550a0500c45d0010b19000305c650303072a0484882c140d030310301a4142c400e005403d03500c6001d02007480060840c003444001c1804408410300d40594440000d00a980e014074102c021444100482080004900030a03100d54500300074036010340c61070070101746000841c610407481041050309500600101303010540207081c18140320359580c0b40900c0e480b80a940948000c42d1202ca0810f41c0d0b04030350f402880740100c80c89050b5515110001c080410b20340d24602600a0705100004 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 841551762 1250 841550512 841550531
    0x1050717040e040302010c08150f181509011205071a0910110c01020106080d3504030e010e0a05011809021603020d0819020f04170715050906180103 65
    0x80e800a00700030201001c86074020302d090f01c0c0090a441580c81d800c014412200d0038042ca400040907500080c04054031040b0010075901300242ea042c00860b6101070141d0f020040c4203c8840c1c04c034100744a52001d0b03038440c2e41640da99010103000c1e045480054400d40001c00180481540664071003400d030341181c0a24100090240084d211010721408440820211046480c0301c3e00107220003d203501007400200045850202e465895080070040d450403c43d620842400c410010400c0040c00c540b280e03450040c52107480346002c42040d00741d41c00e8020400b00b101d11070107588948103094420401505425800d45004010740b4021404888040340d110444000301d00d021461000e024801030308005508417241c90301f0702905000340045660100180303541086030314045030038044c03030b01d4110b00401a56002e5a005000e42d500864028085005840207202c00c020310000e40101510480c064105206444a07020707a07091080524640d00f2540038010030b452000034561001c070240707044c180030485072030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 841553012 1250 841551762 841551803
    0x306060d050a0b03010e15071d12010504050729030a14010815061f03090303060b16110f0319050304030f0305090405070f09141804080d06140904080d090b10030311010b0609010507 79
    0x14580e480c00c2290b9500d33807c1009200c0300700150720003818800c0c0c03030543e52600c04070002c182101901c11140e020703d001022440d910050740c411003600c02095400d49032542c507140d219444044141c40000c00c0a05030020600c1c1e0b141c081940440c03403035000c41d2a8220266003038141d020345030042099040c1a43d68400040d59161207009000d41c510070000006581114a04104030340c10301d003803660161907500700000341c5803800202c01c4011400c0c9002c02c030303007100c1518009240d4820780c0c00041156009514200c201900040500349407202128203101c80c0d50703240000c90300301d500b240004001400303990f010010264810600503101402820a1003042c400301491110f01c10161800c8421190002d0000b4500c07100e4031803480070300304000702d500444c0c0700070b40007410301e010140c0301a08074500062018443d280315405030080b02d42c4040d8940f803d00d045948000e010241d880181c021440c08807007228203540621078229034050003440a4103081d400d0004560507040100e00300c9800f02c1d8803540c40300001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 841554262 1250 841553012 841553029
    0x2101112041a191d0c0d080705010606080702190228150e03120301060c0303271203140103120311131e0803070c03080306060d050a0b03010e15071d 65
    0x140d101c002440f41c064080c040c402c4070000d500e0002c051408520201c5003400c00b02d0450316180301143c00300b1001501d07042c400304030f00c245130b4020000e41ca04100090140d4001c00018425070a58081d0b9500c10301e9a08458462051180020340c030600302c01107900705003a500301400300f29210340d900c040025251460000f58628a940140114488484400c41c070315082060012031b0b00b0006607242594901f103406004030800d40b400805040d03e92190001d5941e10550980b0031072400f03141085c4034036150810201500c8032610304400a07050000c041042c0442c0c141c2c00341200c0d070140100400c1140301c10114000c10548080041400c01002460804600401d8020140110000900b8054403802c450a5640780d0303580038006903002406421f0124403044d0740d86040729040b490b0a41d403a07680c17800042a51285580b801e074050301d003405124109016501c080c6512800341c0081000c00c01e03407007032160741e0020014060031000300305001803019449050343d400304610b00e00d41c600175100802d00056200 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 841555512 1250 841554262 841554271
    0x60221010e090f03120606071106130317042303010e0a0507090c0e010813020a0914090f0622050c12031e090d1e0206070c0602101112041a 61
    0x50328080602265020901107400c05a003e000114a004907a0300c26008200b001031003a441024041070110620582c000500c000800080a4a95a818036070020f8500182400207035248208500904105e43c48041100c0594113410140e0700075016140801852252640c0c826425548641c101c00c0f080c54204a18207000c0e1052000c0c00c041800c00840004444032403012002b0004441c90182c0580d03000014160003003a800c8003c2c80000c540c0c00130880a104c01c2c1d001c07003603c5140141648042120402c0c1c10f02030f00300041551030811070320070f00c0342e5a0481568402540c0049918112502009240720040e0601c00c0703050301c03841c400040008994011811400741c00da00b00050700701c0105a4040e20714225841c20b140e076030905c20080c2c0440d10070100314074018982401c070340207045c102150001c0765420303a40c014091952541a40740c52050700384d2901c64031000d44035039148171030341c042e0600615004030380e03189240707090100000c40694403000181082d40c50300801103466071406082c0034854400e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 841556762 1250 841555512 841555529
    0xa0e120c0913050f1f18082b021309060b031f0f060f0e0306010b0901210204030303060f0902030601120507030b0904060209010f14030c13090216030909050f0406022101 74
    0xb91841034802400044955200030b2856140c02100708800309140040c3e00c0080d00200155101c023241184114104c100d4a01105040390200c507402c14284690001d100e0300220b040d00711b010503601c07154842562818086c0c4c0c01c140c4824000030790b2030307081c85d2540c1d02c0046000501000300b90b5070326441018840960070440004a000b034040c6038580c3c00c018900711000c8250010800d0303615195100860740610342c086410415115002500c0601e004c00000c444043e04400b15521a40c0780b40c040c0060503903120701c4103407851034100021528020700c00c2e2441007006845100c001c480d100442c0c40101001440c4d20103040e6900080b508544502c200540b0551103150016914014240058054000034042d142003000c490040181f000d03100d0152500440f1444180c4e4944e0040720000e80c132160250400b1000910102e0005191103003c03003844030680c0291913000c5010340352288102507500880d440e40c070045400c808500010a6030303004101d0410840150a072020021880f030f403100b002a40301d00c51 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 841558012 1250 841556762 841556773
    0xa0b1317100207080417030a12020c03130f03140f03040605070c030b130b061507060b120a03050d0c050703020d121e0212220f020a17030a0e120c0913050f 68
    0x2c6c00081c0034100c0603000800000d600780381c8040401402c80503d034010280c0a85c01003081c1003001010025154400d500641d502e00345929860f241650b0001b81c07100341c0380c2e100380f010700b40c1c800700e000b150184524044a010314502400d000c0b0a560591000b24100c0305107012001c00000718040201c41c0e4001c107450014001c10240d1350401107020310b006401148a1064ac24030305ca030f0b0150f228102c4113556404280440c000500d0b070000345a041c1e11b03251032107050080203125000c15600400030a40c088201d4070400411400042c1118a4002c001d802000360303010381081e40009004113079030140f02545c00700115041a00400000c14201c2600c6c13000d005540114202040051000078a0381c040b0310751090080004c951000e64105000b54907004e040c0f007e031140e000d010f54850241d00400b800e184500e40b48210703d6550610360b282d1103084d0301400101c101094841ca4602210701c2604502c210700182481c0c80e40d4020070481181c040d1131ba118580012840100142c0248440030314460841c0c054607 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 841559262 1250 841558012 841558019
    0x80c090d0b01140414090a1502070210020f0d080c12040501060504020a020a061a0913080705150106030b010f081f081501061b0203070315180b060a0b13171002070804 73
    0x81d0f44185d07070300103210000348040100540001980c1c078074064100b588a2030f006c5d440c880510080c811804007a42100c19003011000c455000507440c0101c0d1800e40441d40b1700c3c80d10440c00c81d42c83e81c00340c840742900c0c0810019918550791011a01c0c1d04540924000201b01d81d4410018041340c1c440031038280960006400b40301800410b00c21424040040740040c040594a0b20000c0d80300e09000386403980032003d040201013070007955400d80d5003050b840b800b2643c8005c00e517180020114024030440000900b0501c0c2807e495200d501c0c2090703d110f450f02da40b40d640e10340000116807522024500888102032070000559281c08001c4410310b404846004034103941418001003000103001500030254400000820060710005514002c80350000f01d1040b82420000900e8040c1c55020b10f10035060300e50281c9c810902200c0e03a00e45000346801c0781e43c40c00107a55030203140840c1c050141410001509141701708141041c03014000380d1507042c81d05660104000900700e4089070850801911201008074013030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 841560512 1250 841559262 841559269
    0x405191101181206090c091a0427020f0f09042d1a2e050a06030b03030409050702120a020601080714030616050f040303030506040c03020a080c090d0b0114 68
    0x1072035444800b841c0c4034480e5042c030004a03803034200c03107000601c1d00b50381d10000c0090155942d43d0401400c8940e5003400742a047c502103030390100350318111600c11850041c888016219040c2020030902404040c1e241001c0c1079001c114807511440181600701c180705440542d10799071000324504c2103128000758a403140140351595812544903d034681b071154201d4015002c03c0e1003201d405400b5001c020695400e9440c00b03c80c04100440c2c45001c001003120041020491040894600540307500750707000074030a580c5142c07c50036100007c80c80394154004100602002c941ea41056034082010300403903980c107603000035a40300c2d40d01030220031005800150050103110800d0040030014101548140c060f8001d26000903161840a00035007000b01100b05c0718540c4078011010b03500a401001007641c1c55540e2070070060040c120888409104034a058043d00c03001e4081d2080c2c402c84030003039544009650300c2004507202e40c1e0040119503444201202c60707200040040c0c103603901074490903c401414140b2442403 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 841561762 1250 841560512 841560527
    0x14090601060212030a0c050f160203010e03042105070b0c06090105010e0c0406050d06030206040603020406031808090d031101090609050606010f1d01200d110a0308040201080405191101 81
    0xe41c003150007094829251844201c2a66000382900800013901c1d40420300546d0903101c0c2034110140f00c5000314140142032007407001086101d0080d0001c1c04143c0024481c140c99104501812200d400481401c8070310360044400010443d12030000c40d800e50361a4403400030681c01c032049528056000740304003e584c2d0028000c2d240103090100b242c0c442e6051083c10840c02e4040d0780031b032000308070001c10000b51050342070f04040b0040d5005030800f540c607919080024041c1d40503005140100c2d00b0210114420550f020320034104035088011681004012820016041c12052007501045024071120360b0b920001c1c03149645c028840c58002035039a009152050a1040003048039043c0003100c0b01c0c83c01c01c69086000b042108000d41591a00c681c10381d00166440b40103003000c0c001c4c020790300d24200120000012103c138003000d43c0c1c03a0240c00784040c4800c15514001c84000034000782d070290218006500403115650081c3c403c6084d02c81d00620030600031a00300307100200b030321400b00341d0f0100405560031040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 841563012 1250 841561762 841561769
    0x3011a10020a030804030822080a03060f03050703020f010c080c010f0614030c1014130503070b040602030901080a0609020316030509010207031d220e0705090105010806090402120114090601 83
    0x82c00510001d0344029010810040024060051080000340060340580040304401e540840e10329008202d801d00c0708040d01310301200d102180c034040c80864160f001c0071049080725481401030400600b1a03007800742e81c44045070381e141440441e408580000b807a07200074080014902000003030000b9010b14a0003030356800c2c1e01650800000c4411000326860108420bd0400000d88070303c5064854010f0032185890031a902800c616008606e180f52480206054001c0310021003c03915080d441d60112a0340340318900c07170f1f0800b683c0204000c924550143d4039040c0d104a952100082c80b035661f401c00010b0713a104980c070400341c0301407610b85009603800d0310550b6000030004000310705101d210395000d0007480003094613821201200504401c3d55540300f44d0600e180900c40b04100c80c50490704001000f03401d03007401464040c00707208000700309406c0003500241280c90503540e90081d174031400c042c44402c1e003014100743d07001001c0360188c2011070424040c0281011740c0b031154146034500007038503506000d4181c1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 841564262 1250 841563012 841563017
    0x4051b04050601080a090203031c050a2007120c120509010221090f06210712110f031e01080309090a060f0608090a05150f181b0f03011a10 61
    0x400380203050360310107511380d80322690220015505402e4000039140d03000f0300060f4140d40d01944c40e086801e21007a000a40a0f1400801c1440340b1103070340ba041c1c00b1800314003946180711001807286501084500d16800c007585000d007020134810125450b04110b81c3c0b001c09610011031800109c6c45465613040240015800310b041d140d20321119032582c1070b0b02c18407a01602038410146144020110740d00c5401319540740e0181011103180001c4800c09602080044540c01c1c081682442c01101c4c0551038043c0e8400c0014120080c0d03d040b0b05001c02d0b2805410143c040600c08800000750720324501501040d41c0a0071007003000f1900e5403560002c0042004004104020003403e00404000d0f29074484805c00c2910054200384e801d42c3d65480080c2c1c90074040100c050850302c02c1002c0d03500301c030802400d100d006020ba03a99a02c2240d4402014054aa071141c070101c1050340006180f49080048040541c008900105648400005a0f0000b8203451000700c521121101a42140708240b4264402010080d011b0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 841565512 1250 841564262 841564271
    0x1706100506040510020309120601060f05090d02010f0e090106050c2806110f030a1b020a020901060509010203040807180c0801180203060a0e0403031415030606120f0604051b04 77
    0xc40850010300882c0301e1680070304c0200003415441c2e80244169420004091b100c030480740320030440503944031000c3c4a0741011410346403032164410300c550211070503000c010b00303100c0c141c40865004481d0503202214200401141101c61a000d9a07441c5c1124000c0c140ca566454aa420a0340110700704902c118000d04800006507099900c2804004824142a00721000141f5580c0102c8036012504c5404103041a00c4400070411490352019400303904141a8025104050010020141d9880e81e90f81c4000e94404551001040f446100e0ba000b407458110610590b4240f6a403003031014940080c54105542003010305400c1c20045a951042e0141c8d08040e00e01610554582240c0d9500c002103444020312040d000000240580c5400e0b400e000105030b11500c0b10250301e41824001c00034030500d88440780d400a09404503405001141100d9003802c0c004010300303a10f4841200300030060780c0c0c1c070701d222181d8021904010480101846118410750154010307006000c0c1d05040c4814a0312039413030b480d200d646070 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 841566762 1250 841565512 841565519
    0x2041701060f052e0c050304291206090402030f010e0a0b060405010f0b0706110304030509043210080d02030a0207270b12011104170106050114071704170610 69
    0x301c43c1031218a1000003c103000c01901048800c44501c44011b030441c40000f07070000b100900340b420028108480d05500911034098140c2404500c561140586203042100120f00c1030b140c0f400549410603c0101110850345039030310107034251500400c0c982d0503604a2400d5605000041d002941d0000c8c00b19000c00c41d42d0304001e001c0444104d40c1c02000885040402c40000b0003000d0303404040082344a01c10300b40c803490705150051541e400000e00502660400c0c0340e0803149540542000030810b4184420740d090500780c900c20049200041c41c601c1e400407981d10015080d0350911800070f150806501442d590505100080e25000701035102503202e1001c032400b001d083e40c1c410072180c0341c0c03c0070a902003181007100c0006070642842c1a1103020551800304242c11509103130f0010012034199055081030800703078110302402c13144a1303c5101d000c90421045248003400d00c5005260061140c07901c6d4111811003c00b4104a404c50741010002d4031600c1149200c044003001456480315090075041c209504 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 841568012 1250 841566762 841566799
    0x501110c0d0b0705090a0f050112140601050d020405040204080102220602060c03070507140f0d02070305070608040f08030705251113020f2a19020603070302041701060f05 75
    0x1160200034002c0301c80840414515489501111240710740205154000340e00c800f56411034aa40b8032603180418204c1d10b801d0072410a0740540105d105280c00b1005a0380d071b0b02c90042d941d60b401030340d010030308503802c01006c503040c0d03510b1000d04050300c42c2400058461744403070b4600b1118500c0558065000c5080a410400d00f9800594140c0c41010b4011460712500e40440659107402044070082c000100e50940c1c510341c20740000d03071500e0b02010710100c90900220140607a12030320380c1d00001c1d14036000385070203000701806012100c0d0010301c02c80083c007401581d40c9a050843c0c10540b5091b001660000d01040c800702c4260070211140d440c0072081c00b000381e0f15680c0d40f02c19842010003501419558841d42e030280300f00d506803801c0386d015451203551100501d2082a454460b03d48429403002c4400f800e2a80a01c0005d01401121081840e50302a40301c640070405203810080c251010903400304030214400c510b0341f6190300c107071242c400046035081c180f034050542210181c110700d01906c1d035240f0701902c515 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 841569262 1250 841568012 841568029
    0x50406090f140c0a03020a0e03010c0804050709060602060604050907120c1e242f010e060f0a1808070303050f07030b01020a29130c05010503010303050729100501110c 73
    0x8042c14010380d10505001f043d90000100b501050f40f552915000d08112604580d15911540c824025100b80e00e45529003142107440a0068500580c40703000081c103a0305042e0701c16034000c046182102c0f007060340c400b2085d00000100e40308440c42c040c100d808010b02044240310251046001445851340c90a0071200d110076903402c00d9040348200c2c411400b81c0460300518441c480c4181c2000c00d000c12114184580d1030108600b00a10119840c101c1c8280d400500070942902800300c00d142058507440ba0344052001c1c00044c028058101800100c00d00010190070041800912949001ca01880c20200c40f144a2400030080000d05080000ca030800e40c0e40420703040009503000d0750b07a43c0711499003c480c1010030051101514a03100c02e0707040c4805240061001581d03540318034410f4a8103600d800c0112143d01081c4001004070380103004882c002401108282030208a8a096409040300b502000c002058161380a00e0100d022107401c2c002540d02007020566450141b00078051220000007003102d11 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 841570512 1250 841569262 841569277
    0x7080a090f05060910140a030605031605030c120114014e14100e100b090f1503060c04060e090c040b030405100c050a170402100e0a050406090f140c 65
    0x102c8600c00012045d5000d5403010070418191809281c643c020703804d01400034070a6004061003813190b540000d4038044108000015120041c002e8407008030000140b04424224400a050135500d03000d03810151000d006e0700134000c000c450041070109039102070507120030700022002d02c404500d00d040d513401720b0544840c00d5164805000100000d142c90f0601d48010900252058458054140310690281c240c2d00b14891a101007010b403052031701999802c004590b8980b01c05074100d00401c00003080b50300444065a444500b034880c1c544c2c0d816165001905001048861001d03034800400c060021981c0904600326200c0190b80400326420864441c51203030146101e00c0c4181000000007408201e400c0c02404101081c40c80b0a010407040114080c02c079400454201e03000072040d104039071601e26424800303406547c004d0b00303040010900e02402c1329900e031250741168100c0707000680052a52141d104000003484c5060000640d0b82e000072040046d207032208814603480410b0028403000100180854204 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 841571762 1250 841570512 841570519
    0x5060f240c0c04051918111003020702040e060910060b040302060c0a05100504060b060a0f0825021507091d10090e030a020c120d0e0303040b07080a090f050609 70
    0x103079038241c80910b24001c0407201050f00700342000c040c00b10000c0c0000440080e01030760034081c000c04001e02044680441d1010300030340070034200c4400ea0600d041039004207080394600d01c1c015190460540206050b00d00105031b01009a10400800001120074440c160704c1840031340040c00914a40200744407240230328000640324110019401c90822010400d4420180d404001d03542c072030440d01c0302c640c02404d040b6001d580d86030030318044280c2460303c0f40c21207880b40c401340c43e490800c12801ea4100c415680082010b06860841c5442040742d0654181036064400d06074001c2c600e00c02d19504004107902c010740b440007404403009042c86952a510001c1c1d2211225401600381c81d034503880036038030405460b0301c094600d51400c4880c0361040000b1000306503e95282d021290840401424499200044684903a05401042507101c009106d81104240ca034401800c980c14540c80b110385880c43e03440b4200885a446001500d801c002d80c1103810f040080000400c0301204d0361410700410b14070300c140412140f0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 841573012 1250 841571762 841571767
    0x1050a020c0c1c0b010b07030e01050a090b18090a0c110c09041202030919174b0115140303030103030806210706031109060406030e0f1005060f24 64
    0x108642032942400410750030071485401c1e5655108041c0031a841f01c078068000070105200312a5035406407048034200080c0c0e94500603000d180c640702d560070350003010a40752001e40112180d0226503508401e0b40c01403030304040001d51410100e50141003d40d101282d210241c00c03580782c05648d541c0e540b9059a202e50810ba102681444414080b0305510620340041e0b0300a403001503520000910302100c4003900c816000f800f6100c1816503159507140f00b03681d040d241240640c0d0340c031100d214a01c0120401d1035408054004403040b900c00748580c000307414160955130313036607a2281c00207000350b540c1d010014860b14142c1100017400c000400d0722844140000b5050107004804120301d51161100c04422101030b844440c4d00d03040000c10340361501010310900b400a07041040e1a80d460160500321851880c005013110310341441c0c8030054002d0080c15132210000d00480085003113140090010440105811400007500e1422408000608510081c501e02540a000c8040b000c0c030a040c2c00310100d814141d80c900d4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 841574262 1250 841573012 841573039
    0xe1504030611130608241e0d0203030f12011d0c03040309120317010b2502010c020a03050105090618060a270b010f1401091e090603110301050a020c0c 66
    0x101030f0b2284141d00d55498018900c005440da81c40391189000e600c00c0c100d0a0314542c4254000f51440070b1881c1021340c0034180110f01d001190320107a00c400b250a000e09002e54068841d00020701310b03082150400c6030703408000303000d40c1c035490211a118003405007401805500c41e031714004541d44941c01084444007071000400300341858001d0010700000e00603184c0b92404503405140080c0310720000c10403450040c4804c0008905c4070a02d1098884038400942040b1340200e5a115101c1c685044c1e039010703414401c8500c120b0001d42c0741d84034108003460107540040b070181002d0540d64540b91005007029158000400c1c0000207a034045074164104120543c081048080d1fa00400c4407400a060f07070484295409213010f003040380380b00c4264102c41c280400500e0043d0f60780198140400a2072121340081e994000901513500c0380e60842d030110b0681d005103440795444440032000c46801c0c0c2c10a80d03003460003596103200f9284c01d000740b5500049640f0103505010320121416540c3c4120a08184550559410300 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 841575512 1250 841574262 841574291
    0x19020d0603060f02090427032303010f0f08030a201216052808030910090309080c0d0c0501030b030a0b0403080103050f0102030106020d03022a0c010e15040306 70
    0x10140d03801120403c00d0101d240070180096114040840c082c0f030402e0b107410703d00a4500e04a186c444428213400756001e41940c5d00303d80085c4810320040070702c6c4d440c104860314103004c1805580603122039007031089034606089030310280c11603507804410747e80d20400141e00c5071607000c020000000140b0445c204090030300c4c800e2a0604582c0c0b002140c0343c0c0f002140e4a154104905c00d00c03102140548107994020051405a9801403c80300d000c10703800c00008064000136181d90015075128100c802a0b44c0c0d2200e280c0c2200c4252400c001c400c0e000039000c0d5105005029007030003030060010048600c90321500f1503540d0814004d1151042c1410302d1f0740c458180c61182c9040c0a00d24040350700114055003031a19180140c40b103039081c04140c826108000c1948048081482224141c1c0c03240d4005001103002040c0440181d4001c1c0b02814900c14030003210000d03c3d14a5601d00d1028414401401200c2c0c6e4010004140c00030011103d40b02c0c0c40b822540e400d904580c141250248d0390001004281000c800084 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 841576762 1250 841575512 841575521
    0x50409031b0305190203070b0c070302161508010504020306030705040f09080310080c0607032f0a0b0f091504020d17040803041401170f061908010603020a080619020d 73
    0x1ca516812903002403820143d12400030300d000048040e020402e40480c8504176940d010342c0c00d0041460302c3c0c400200d10720695180140015511034412104801041440c0d98607550003540103070480ca0750321a5100015070070070f403001d000d4181a1000c41c00c61421400281d928806c903c14180103035562900c0b105914540e42014034450781040c606070f540c2c02d00c405541e00720361881c4514291401090740c6030409240031002c90f0f003465056601c06018408031051412100d4803501089140c0c0110008044050750600900000a0086039160034070f10b401803030300d01e01b240001d150710000d4204054070943c030070320740304103581260f0161001300e02c0c16403d00d80b4440a100d41110f070410020081000102a10000001d0044d40d0020280c03000007c8581c005490072640c0c041a07458444010000030880c410942d081d131b41c0580e00503c4214074083d001031080342c84d00150069501c69440d04014425820b0110484004004a1005003220300e07000c44100d010034180441c6406654002072108010400e07901b1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 841578012 1250 841576762 841576787
    0x2a020303090d0c0b07140f01060e0103060c0203270a140a060819090c1e03120f0e0604080c0a0b07030206010605070c050414190b090109150f03081b120405040903 71
    0x3020341d0f417a1001e0074542d01c0c14069485181151041822145032614107008140849690440d21541e42c0d09650302d442c044c000070340c03015045220600842d502d01b0151104010082ca641030018001c540f40410f1040d007201942110350360b04e00803407080500d5242e407100c0008075052840c1c005240e8507045111403002641181211501d424100854103010b0060754070000c45558200c82c0c489005100d002a082844610000d03103c85110244a00391500484844100811600c0c080c00ba581c900000606c031500950004841648646100714050601c00c01038009806c800d07400300d00380412694001d58800f014003c00d400c100020440a00704910000f071500540001030041c01b00407004a081e0603c00011103c02e0301238161030802000c01101e40c03043d29154500602000d1443e820090b505014050b940000812051500d000191800ca1105480080d600c14011969100007090081108108401414019800040010303030304105400884003100c2090b02e0100300740c44103040c1501c0c405c00c0700c003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 841579262 1250 841578012 841578029
    0x61e030b090f22030e040e16180f05040807110303130803120105010c050a0201270807170d0c0f020d1505060114040b0706090519032a020303090d0c 65
    0x7440360b61000d0351001e074456010040c1e858030b612040c6818000c02ea10464001d03011810ba008000c40c40c0c200754201801d480c0038242210200c045080e51075001c1e41b5103601c0150f040a12440140d00c5070600e0081d03c0c0c074201c40802c140054102a15040030398415228020b101c0303032000c000444d4586051060301ea02500341c5090420301c607615581a0745035840301c610310060900d07401c0041070359070140010440254101c0e008100201c41640151000c180c0b070500c181c5421032a51020b806030781d031103070204c01902da00d1000e042a18079105044410a074840c00b00c030480e0b0880421075240079445010003000c0d6801c440b21070700000b5a03002241c0303c50070841b40540540781c00760070b09003581e0032600314902a030402c0c0c0c0d54002103a8680352165030340c0518090082411010442000844e4968000702c0f801e50042e41520021411819140024440003108401168034020554111000e581e251007140003841c1103004132445d43d0f0700280d1607115811100e80f00b158948400000d1200000c50300c806000c081 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 841580512 1250 841579262 841579279
    0x10030b030d0e150c030a03110c01090302150604090f12051204052103220c0b0301060207030606080a0b010501031d01180b0a060b0306010c050a15140f01061e030b 71
    0x100301c001d041070900c480d814001d5941e03840401501d41803508550f4580c44010145081440c3e000086002d00304100d030000e2416024041c1049846d801c0c480c120003584650010900d10002c4126030190340c50040015214600d0201c200001c10000a1b85ea43d06540c0700980c021039107402c440548142c090003901d4556510b1820400081003800200400d00c43c0000d41c20010740800f13140d6242a23840101c0300102001d086101122515000ca45440314092060038800042c070b440c0c000429a5410907441400145c1c0315030310070402e201071441900c0c040c160318406081130704103030b4a0340b1079001410b02c01d070381c1016a2142408100d0100700c0009910038841c00c000d00078030003041a071050140e1105410350391211a0000314244400310f1244604680e07803d03001d9401c41d80c50034015501c003480c20205440d58042c074480341c00018412031310400000010080090b9880c2c00e58080040040020510302ca131219102c010b02882e0f070400a00e180540401d40f0301900c0c0c0d003034040c00328090b0006906598102810 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 841581762 1250 841580512 841580533
    0x3071a130f0f1d042a0302041b080a0b030a23060a0b0f0102010506030c01051309050c130e040209010302130b04140f100f230d030e010e0f01080610030b03 68
    0x42c072007001101e25864030602100ca44441c986501030043c2c038001c100303201c80c80c0a035503e004641116070002c1d00c5010400031080d526008142510620070f035030342c60b0550303942010f41c109030000c003e2500710080a07000c20500d07101c0c0001c25518000281e010300003110700311805000c2202c800748155418640400d40350a8180108000e01400103900001d00c00d00c1e14072180300e601d510500c103030b0b8850140140189407075440c190054440ba071181d00c1c070042c80884a0008a140d200740d000d2103000f103452400e0300d0307605d243c440c00c09249000c558101c0c4116121841c05c0c40301507940c08a0031410340307404861040581d000100e404004240580e000d5400505002003600c164031100070f018030400441c4041c2107181d0741c01c0d4444030008014090221149150384042c00089079010042107141104041000c5804026002540540840034110005840c2c106000ca965034000440101c2403400c0d140101480a4000060480d440007444103026100d80040d00b0100d030320a03002000b150a026003991504a030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 841583012 1250 841581762 841581779
    0x405031905010b011716021501060c050c01261909030503040204060b0f18010e12030304030f091a09130c0804141216140d0210060503071a130f 63
    0x10650240c806500c0c02102543c07550086491588a0702c29a03045103055850030080b14800c5500038901e0304521403d8185d00c141340741498200d010f081a9201c0e18451401480e2003407a00d103100c10404e0400554180e6407200c10740001c1107501d01c440c480e80a651558403d042081464840d90328001c60314108110f0505264000380194001c2d8025030f0700b030001c2521404030014520078060903d4620004009003c03031b1800c804140c0c0c0d01142d051400c044200098000210010020f8001c1d0400d90000010f0104041d00800c0b089600340140c1080080c051828560f0780c10304d80310080c4a500c80d540040c0d1003420f9618a04071960b03100003400100075070305001c031005082c20005c07102110b1031589071001482c0020002604981d10540b40102841c0c0f109904c0d0015000c154040b0403500300f8000440d40b58401070a1040c0900d010059000b000304080024188096030700c42c0d407140340640c10200083c170801a4000c1c40a2f000152410210303aa00000310603413980395600da000140320301d41a4808561041d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 841584262 1250 841583012 841583053
    0x152012041404050a0b0901030b07030e0102131410080c07050a1b06140301080c0111010b121c03050c0d091a0c040f0e0f041101020a050a140f0712030e06040503 70
    0x92055404101075620589181d00301d6100e40c000c61b5008000000400c00502503070210f41e402070962801280d069080800c841c2642c1044843e51114502c542c01404200191008801d6042c0110b0b40d981050740640000741034801c0241c4031005561000481d2070501004200c080c00c5143d100c80180d44816003002541c400010b50f006034000030b8842402c0c0c0400610500030b0701e068640000140031004031680040d18016174918072105103540350001940703580c1e20f80d14014081d507519405044c08111580d402d440c222050385850040c07614010034003069240c01015501088200c0d039001814141c103041007042482c201b0401c0924102100410141905c001e000d40226540b04084d4003407140c807030604070100c903800c98684001d41c80a20029001c074040c45005e244040060042d502c80400c640c480a00b801d09000040d9441038205070741103020182003250030021407240003d01405810407880f20b4044445220140800c516003940c03980c41e503541c0781114010f11004084540800b09040313511a010b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 841585512 1250 841584262 841584299
    0x40306050f0c0f0f0a1b0b060f030307081204020604030c120507170a260d020408061003170306041d011e06060c03031116050f0715201204 61
    0x4a01c02002ca50100c03003840c1594801000340d03516a052881129110380d050308517141031010010020564040400e510307081006c801d005008004c82864070105010585551065030b6000358001c01c0408003240920055132143c4400b0041c0a0360f5441e00d000140b0980900d800c0544071100c0d5000c0011351403641e408801d806482403042d610240d07a544417104100050344068403203030300200501000265040710000380b44068008490a4007c1c022507204035410001014584550004041c02602e00421100381d06c01072201c0c2d107001c19411607441d035080c00756907000c2940d0000f001c0701043c0d982d50749402c10907017510354010400c0c16130f1582d10114003034001c10360000800b619224a0342c3c1c5000d2107014802c290365650311903001c0030119613012030040140c8559298034074818411569003607101e000004801e4050030042803d42d5805035240d0405445900103807040c02c00544030a4103c0d0042501e01c001401e10f1500685150403482a5040500c0c180c59808813020005021030782507800300021125 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 841586762 1250 841585512 841585531
    0x60709030308091b01050a03060f080a030207050603010501270b280f050301120614340c0209040203010b12010c0e01080103051b030a0c0e0103020f0f0904080a020a050304030605 78
    0x340c83e1080d11030f03100c03401020350722526038640f450a10254080c10050125448500d4001000750303444a00c41440340081c0c002440942002615205060741004010003400701124114590351514002800d01038030352130000c110001400b00d48003c140f81c6d00144008001c2d44075904e503107000c0c0000d40b04070400816440ca8078002c021302080d010300c1c0324010300720810072161101c07442c0d6403c02c24401401601a9030480e41e07e40c4410b4821654402c644484e03000c0d9980c01d2007200a484051201014690701e420346058280069500c10121a0302c10f00c901c404035010740d0401c60741c1d00c0354008a400743c400074150076048066020715580c1000c0540c03001501405075030721800801c058100454182100307200103030450b0710a810607540c014081c0070380c04965400030100c81c400c0b2500ea646241c8070503160f1000d001420a140100306506102c0144000020115036425469025400003800103002410103404207c0110f180a031860080110b81d0f06a504001140c2e11540d40345041b101400086070f66050 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 841588012 1250 841586762 841586777
    0x1050f04030809180f06120f0a08070501061e1a07020301050711192301061502030a030c050406200102090409050a11060f1902150f070206060a0b07020103050a0209030607090303 78
    0x4e50005036030540d8014000c000d0900b5554a0704810040c1c01e4581d45016403260217001801b440103001007001c1c0d201d442c03240748441c0c1c903070100b81003a030f00312140c99001c41003540c50000c5030041c00c00c03d42001015030707205104c80f402c0d0030888540400c5a004030718009406600e48001d000d089600402c090014440d030b401211100310916000d485500c1001d10001c0102440d40e448030304480d460250b10701040100f000000321035594071030744071241c2004151400503800024444640c280d15000e4821551050f00744a823601d483c00100a042c000f03100181c2803001c0d002c0345005240031b0203404880351481d005206004200281c1011911800485c03000c440880342661205681d041801c00d5489100702001407904103804070030146505249040340504501401d0700e01140c0e428107102d507038040c00440554201e60710b840d80c2c02178902000503000503c81c0c400214100041c07000141105c28180c1c0c20700e000f1503951680344106010340900351a10b42d1600904003000315086e8801000c9084a0090f9500d01 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 841589262 1250 841588012 841588039
    0x18030f050f13080a0231020d020c0102160b0901090804050d030210150603050a090b01120602190e01230a03150f1d15060403110303090405150a0e1509040201050f04030809 75
    0x6d1514500c164200c4914504d18181d2500d00002d80c0074040d0390b0115003001d481c24a10280035030881c2c0c41804005198050340310300d4024099203400301c0b0340c0417003810000c000104181d200c00059004920410b0311408986041c0c1080501c20b1011181240b40e402050201d8070f540d48012070030358454043d60b00000c1c0f0300f03000a07c0350f2105003e680c0c0030b284c100c0610a40e503400c11030f850403520b04000d07040e10301c5034081141c1040645000c00c0100c000d103980c1d82e455103000284000500c403503005212002100c0d28103a2a8103403c21403030884001014900b000901c0114000181c1c023600320960011507100545100002d140410b00407090403144502011040c1d41d40d401d1440c1c034080c403040c5540360070000a102c00c0c000101c1c4010316884c4014010101c1e810039082e02c000030252001140c41030700403509400c4d1104503040c06500d42010b0700480074040da41d460495405190502c0c0c1c60096031146401501040c15a4040c030216030b4101d60980407650717902d40364217252600364840d00c1850300030b681007e00380 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 841590512 1250 841589262 841589299
    0x501062706261f0605040f0b15031b07050d02070b03091b2d01030506060c0a021c15022508070f110d0b04020418030f050f13080a02 58
    0x1281540c808840c2c0300040225907607403180700711414400780c20510405081c004030400350007030b07031800e845a090b0214000b8100800d101c180c1d401d450302a01707124103104000d6042d555280307296042c5402d044095480e42d45001c0c00d4036240100f4a400c07842400001001802d0240c081000c00b1400d440745c080301c441555030780c001003c0c1d110403a00500c480e00101124080c2880000c2c04440018000340500c150780c45280c0150038951600002c2107007691031989200295030580101a401a4110350316030801890b4194561500341c5103030001e106803d0740143d000d920b090304c002420b1f525082902c00c51102003000000c0002c1d840040400030302c003104850010520b4903580002c07255a403120056050007081d030340c0d81e000c2c42e00c0b8450864015001c2c0500e940b16444403949001c0890060091020303c3c03d0a0040c0310031506089484004880c80e0416940800c0c2c1085141c042c000d1946803181e619648500d03000500d00030341144441182c2d0b043c800046d01d0340c000520001c414000c45424120351580140d4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 841591762 1250 841590512 841590521
    0x9050111280e0a03031115070e01030c0f2001090f03020f0115061e0c05011a13020405031e03070b011211030105091011040302030a08030f01080313030807080705010627 74
    0x81075112003001c40070704c0007921903068046c2d400101d004490710546519009103203e02c0441e0303c0800600c03514541882507034103004139002c10007941802c80d140c00c1403c5009010881c4007640040004611501003207402095101048054202a10301c1c607042c81e51600a489021052001c58903600b086091402c40605410400845e0116140d6400000c5090201248403036104400c0c0180030380c0d030b25040d010a5080c028010b640c41625020700010800d4810050810000d4640d1507500d403040c03005100e5514000f4211011a5225640101020000300c00a25502c0f03030070343c005e00301c1300c4c09000002c203003000304010000a8443c3e58031002d2aa00c2006050807540120b0b0384030b64503440503110041241712a071140c0402c00780c0c006010300d010348035008685441465102214107040c00020420141e401c81e00641c00b410400028524000e07200100b6880105076000180c001c0000181e4681000900f104480100ba800702c000e0003603996540e040003102509a03854500104041458513407600144136 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 841593012 1250 841591762 841591787
    0xf060108060a0b030f120318070b1213060e10050a1803110c0d12020c1905010e040207020418021e010c0b0a14011203090e01180905011128 61
    0x8041e15962005484068010000c0140c0c040c0203000400c030082000784070700403042c110b001d0a16924206011754050000702d03003940700070a4014110501041540600300d580040041c0c224005540302e0070408043d9139040782008220701d207400c080c000844c601040c07500041218860402c460307a10b060302e000031742d071048442c0b1481e043ca90000f031001902601d010400c0d0155082260200002c5402013641e0008040b0b099440c3c84144480203103150b03040000704d48a01040e542c07500d000034a140403045906060040c42d050003200e01d07075110261610b90594158a0b0010014044202d20000d8192501c03405a4242c0c00340c1007103410243c450082c02d12024442c00c060752446030752602611841200d440240c010b01c001c4c0d0300c818840e00041c00c1006480c0c0a4020321561100280321031038098100ca00f59400034205c1803140d801040000e860700d0300005049140c5078003017100a500d24100340141386c0032806d07980c01c80c00031800d81001405880a01c0d100741d80c0e41c242d40c4042d40703450000d58000d2a04207 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 841594262 1250 841593012 841593029
    0x303090d0927090606080f06040b13034a101e0804060f0c0f081f0623030109090303110306030d05070501180f120e100507171b0f0601 59
    0x42c5210070700400380d00c186000303401048002003154a0715a800c1c01c021100d80641c1c101c0c1d011109000520682106450300f04520001462070100c1c0303030390040e10050107265003191080e50100b0400380404a00b00004e50341c4c104400807103a2201140500e14090051010303180244001424100c18a005280000c5010210700241d0b2840804003000c5a581000a204a401a48a1400c41900c0e204c50150b0b030360850264403100050111307084010605140101155914000603600e4145d052001d0000020740b2031038504580d411842c13111700c4529064103113440d2030b144030010000803d010154011050248251750034840343c0f010204807081c0740016070340150b242c0c01485007202c5079409030008100c954032950000c0360102c564420040c024a140c141a104080613005580030403038041c050806608543c20000541e1030000041511b0800e111000e074140304000610130240018444e803d49800d00040083d640d80c2c98461721041109001c4a040e02c00344210004102c0e15400424003074180d440e101c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 841595512 1250 841594262 841594319
    0x8060112020c07120807021311030601140913020306100207140603100810050618090a0b0a15090f0b1e150f190f02010c0c12110303090d09 61
    0x1000080300a6002008038001407140c06400503103549480709030320826004090a41c0ca80915006110172a20412420802140b903c1e101ea00c190910100382c9402445c20f2800700715050304903807a0044c603c12900d20540c80441c5070b4a40498200c2600214031845094910b00446090801d040c0d0f5550400d0246a010b0001140d49241c0c40c1003010296506c164201005480b040d0f4824100d403e1014030400d28288030340b0b0708204405410001313030324007100001402044e0b81d850000c09003920792018460060007981c5140c041030102c00140c000b03054460740c1d50b200b08017042d991400e56001b42048019021000e051601100c01c0d031a0281c0072070354600d002503030003900c00d1603907003000021000440c0d408840c10042c0070b643c0c0c141c0c000201401c4c02d03081001c000c40170041e0301c0401a1030601503e040600f10380c100403010540580c8400b2200d00582d0003031815a0640c1008000d03910600108900a5948804401c00c004d0305800540d040c50b58231262603025185407a4100d4804014800c200521041940e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 841596762 1250 841595512 841595537
    0x1503011a06121012050a0605150907200106060305060a0803030106170402060d09080a090b0c0a02010309080702040c0804060c05120612010b150403020a050f03280b070302070b07080601 81
    0x4a00006900001007034100d103c00740c0310301a000039842c401c2030648241d402103802c03900f041460b209603030b084540582445a100c0d403040000d2ba0514000300800e0802602c038020f106909078003116218400f00b003a000740502525407400a000784000c487c4148102c1a2a0740001c0d882c5000c411a2305030795180e518800380340b042006200d00e40304090000c9030041801c11a407440b144540c403460f05802c2c030650b0000d91710900404020328100300f0f5001030160314002c221100380b650b00054841841e40c0c3c2030801003440b165a0034008224020302d44080e4000d410807020280103a070241c0158816885841e0401054886840495660083c81280d11942c01c211000c291103140018000f80d1000c0c9480022400c803000f24003286800040341c034081076448010a081c01146045482c10014102c00d69100507000b180c000020b41d034080340000742c40b840d81904292141401d940600000c4150070130644e50290510010081c025440003105035008041d40f80401d1007140325500c85406144143c0d55481800603 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 841598012 1250 841596762 841596787
    0x1050105091e150d08090907210b04110406051e0405100c081b0c0307051c020d080f0307021006051f0f170a090c1512090206121503011a06 61
    0x300607001c2c0149043d80382c2000102d41d03505203c01d16003803090081ea6240c01110052114111000d0400014080074480c0f094454540b50040ca010785200180881c2d0613580c0c0002c140141090705c01c06026003030018021403141d80020091a50100c00782c2c0c104002d411040c20310045000b0350150540c801c4020a54101062084002d08241c82c05094107524051801411803c440700c0c07611000307002d8001c000d250006207401d10107031005003002e40303900382c10403130a900c04420421011002445504041c10160508c16000240d0ba01075032170051150f642d003030100c80a07550f0211900034442c5241086004501070400348505002c40ca60188201c0001d03a0980d41910b9890108a011042141044550304240b14035603000e0b0180f4045c607400101c03001d13107041c103201044860b005000700c03504000309412030300d0340702c5002c1420610034030000071492a07510010760584a4408000c201191200034480c045a02e501401540b80b0304800030400b42d030717006c47c00b8042440b0103210b15510a1007800310046001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 841599262 1250 841598012 841598071
    0xb04080a111203070f1b06050405040c0e060406030b090a090201020d120e120c011523040b090a020c2a0d1109041217101203031118030105010509 64
    0x2000401464100b0304414080c0d2440c1c0140d034064803d00e034801641d40034011002500c10091991121800c40b160900d00003030b00ca0f20035440b40b280110354403520213510381c2c491640186ea4800092002d907a9540e81c0b0790040c050103880c5020b0303100b200044082000d914140c4a2641d04560680107030164030704110080d0380c022201d8244106032030320703001c51561580092040d0389040c685c0c083c01e0790300c8013040f1200b1804c603040c3c8200050801d44030081032084c03901182c01800e02c09201d129404404800d980450f021304a40c0c3c84040e08904031030207110008856401170300000c0345100c100c9611019410041058130301c4640300700b03c0c048400c00c012040303092050006542c6400385102034100690f510210700303200390072103054442c2c0c030231005141e0941d5800050300440d26000c01d201011030070015510340358407509103d8404454040c8801c241003500a80001f0b0a183c18215001d440d02d0101034015210380c07070103540e03512039480c2070300100e101c1c0707000c00b0000e0003500c04910080e1141002401700c0e0005 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 841600512 1250 841599262 841599293
    0x12020607050616140a21112109070f0e04061506030603020423150d0206030406022701120c021e16050103020f0f09010c050f0109060b0d0b1515040e01050a0b04080a 72
    0x4c7e110340000b4070712805600200f5030103440c00441d0808180d102c207034001d1444040c00b003400d00d80001c10108402c0301d02200d40c9080d505000e01803219601c2d6440c22400618400c21819401c5441110025026800d644810112402903c040c0310041141c40403c03c010407500d2140120f4441e080418041110009141c146510142c131140e0745c000550001101500115412100e05800248070410114021501e00b003060000c0030360313001c03501c910740043c00200e8001c0341c8500c10780d5601e64a031401842003100600c003030000c2c110070b040403035030072a01070303e0340c4083d0000f856a2043c9080080c5652083c030840b4441042102030303a04003480c1c1c6d0280c2c0c8040d44081501810041c0217440080422000d00010802e6a00c110000488150a1401c601581c6504071100d01c60028603c8000c007040e03141c40c142d5405145101c007164004c810000180310340c0d4503a52160205800450089048109545d0840c180c07403040b682c0300c3c14660b464034800d80314130442c0038044061b04902202c400280d00306030b0403040b2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 841601762 1250 841600512 841600577
    0x10e060a1112011e080708190218090d03060812040302150418050108010614010806040c1b0b04050708160e13140c0a05030f030412020607050616140a 66
    0x8140b40c03442c0c0002d4480007038200c84020300400c411042d1951042a00c240108082009440100d20381845540c845664800c888489034080c0300c900110756810780c212012403c0e058141010f801d0450000f540c4d4280800740401003854000c0c042558840002c1403105e022a51309070700e00e0705041d9401e003c0224004289580441c1d4144404900e003001219030307406039001e400001545601d8188102d081d681654032090100d05020508002c990340300c00034550000d41a01c0c0401d42900906048504103500300d00d6641c08d40a0403a107504101224041c180510301440840380c0c3d040d1140d0360030f034403140640020314054034010300c103b00c5226010140e070741c02064038140401b8041d00d616a0242047c02c06911034107900400201501c5142095640d006064154010b1465488210580ba96403159015504600c003290306244115076030881106c0081d41d10030266076030b0341007500703c5603224591001110302103000804141496420242030302d040505580cae50854044642000d802c140c201c0c0b145100c1c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 841603012 1250 841601762 841601767
    0x6010203090f120313151404060807081e0a090317070906080711060a0e0d0e0906040209030a021504081e06041101121a01030b010c0b04082b05010f0602010e060a11 72
    0x300c060031702d0120001e00d00d4000410304441c00d18002003612810394840148610288801d00900758018640c41c1d10076000c1c10820110340b1000c40841c441140d160a4815094400c0104044a29a50062225a442502c03602011082c040032800c01481c1119104d0001e468070004010040c82034400f550000040e040140d03010302d02d00040d90410724100d8a03004919150130b8545046442049503020005943c9800c20b000d0054500141030642e02807e5280f01d25004110b00d9966a82400a61007095000344040c00e055005003001c3c466811a109851050046080b001d041096060301d107440c4200040c00740c5069a5103070f60302090b00c401282c0c850704220700345910940c0c410b400d01c2004025403c42c0750400701707010300c0c00c0018169011480341504024078208000009840301400f16081540b014216403100340c9000d220911722a002450056100d40e55410241c020250307000c503045c2c0d02105503210525813140713000d0f82a01c004030280d846070351010001540e8270704568170001034100c00b40b11291 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 841604262 1250 841603012 841603027
    0xc031012030e0a06020c090a0f110d0501090612030e04090303060e041b0501050c070b0d02121f120b04020d02010203090a09020309010c020f070608060112050903070b06010203090f1203 81
    0x10045403200004502158040e0a8a460b40c0380140b05a8001d110500c000c04402e542d600c003003499900064a00d141c1183c03616008003150f24160041c3c4441064507408540b90800b10311854003401027072061a00316840c0040c0469122504045c110041c0e8140e10b48541104d89807080c44014114050107a003007559410012860019404c220760166021ba10348510401c0035200c3e004e103115a640c06181130102c108240300e08504045407200813038031031940a545465004070140060f104285410030041882d400300042e2074a41e441c0d41c000840c490029424950b16a00c001a5480c48040c015221508803000240140b8000d56600d21252040c4190b80c00c0500610106640c40e8154101c551410b4000c0304010290109100c2c08000300c00c1440140786128121182d281c031440c0e00d0143c10200403000d030028100c5c0c2d00800c4003207a0f44401d01810007403454031400392070304c940013800e04552142e12000410080e6100109403130b0b0711400103004103d08080c4200b040030080000f49001141d020912114 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 841605512 1250 841604262 841604279
    0xf09010e19021819050f0111010f050108070807050301050c030a0b04061a07020103051e04420c0e0a090902030a150504020a08070f050603060102010e0f1e03120c0310 73
    0xd2035298520b0140c80e2608501c0310401c295414011300c040c1e400c02c040031042020f584d50b1680c00c440c0240a00700100b410b1241c0050380d000d0404c103d08051a1401c0c4000010128000100340303044030701100541d142da60b12101092700783e46043d5519418a4014404104543c40581c0304076038502008200180da0fa40c0c440340503048506640d103850814202280c032406558150003683d501021565020149031406094118094000b40001d4034140503170a12106c4080e888110b01e00c87c4081c851116449125880740c0d55001185e06040900380303041511484646014898030030001500801102c082820200444010144460140e07414440c0243c0700c004980820b80004107008490030104840c41d040c0144206280c069100c0e607003d6200c06006c200a4a5480003403081d00e400b1030b8529a29110840100e0140039000d0300642180501c2c817032042082c01c0012102c0001c07220020b003c81c1c410a48107055205d002d403c4c0e408900c000848000f850121000d0021a031064402c2c03405001641c130740401 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 841606762 1250 841605512 841605517
    0x1203060f12100e0d090b18210115080c030a0305091503040c0501080115021b060409020318010c0320030a0908040b03061804050a030e01110111090f0f09010e1902 71
    0x9441440e55034554100800d0052100580402c12424103c04176807030010307484440d1007560440c43c001c88920040d440e0590f218464140d0424100c0d00b940740c10445084400e00a040910440c1c000d641c0500e80040c04210105080d403c40d18010050004040076403825949a4882080030b580a651820102441818170000d18003440c02082142c4445040c8000503040d040117800c0940004120043d0070f01c159400603042003410180b800d80c1c210503588001080ca0f40c0101e4005140d854000300130403e034001c4c0c03242d40340e24003060800240402c81f01c0100581c12a01703c410211251f240e40f02104005030001801035030014000400001c10788581d0301d80401642154004119614000041c82030500d010103a40004041681d0300302201c0c202607403810380d15004140010240b1803030160300f58a0760300800000c40b00c40350341e100901a081d8010941d035042d0303000c2c0d11568811110813074056410f05107a0398180d901c07000039003c3c000726400c00700e20b22141d20000f0820455161500c2c0000d40d5948540003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 841608012 1250 841606762 841606783
    0x12011e06030204060b160609030207051c05060c03060604090218100815040605060702130f0507030b0306160e15070602130302090a110910020f010903020c10021203060f12 75
    0x3408606610411056901582c082c640c10882440000c1140c141498010b8015500c01800280322403035140c103a040030302c80e52120340d000b10f8a141c006485a00c081d01c51894a2080080d00c206607128003e00010f4041610040e4000c0c50502c010301000704a6030042c20640145100c0f201d041007007100050940c01c4580440700020413002c24003080c001c140e615118049411101800030300d080c4030200750749014040003e072045c0c1038095075a82ca074025510500418400900038416442c15080203405840403036102c6010388500800500542303403008968a111a0075134500ea0000703405401c0018202d0b18044820b401082001078a0004056200800b0a24540742082c400c20b480c40c010000013020040401c20010705119001840c2c080c490221a000b41c0b00301d401d0b00101841e400102d1402c0200300f0b0079011036207402c2d105000d041d000242250042c0048035a1190001c00c0e070340407a190015a041d41d04800030030b10110300c043c03070315030001018400080c1403e0b0400610004061504030b9504 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 841609262 1250 841608012 841608071
    0x516020318120f030a080a090f08091c11150306030309040c1814090108012d0f051e06100903020f22050702070501140301091802060705010b0118080c1201 68
    0x2481403541c0c0c0c0c00c01a02d50384011011f0040001404688521039000450900244940d800191020050780d035000c90130301c2040e200d26032110f01c0000c8e1410201840302650014818000344c41c00c10390b503001d80c0023100d2050b03001034003440c00e000d010010720000c2d00c050110305d000e000202c03920503004811010103100621600030442c801410702814024a010103801000d001e90500c22020303581003100081c14412400c44015410011201c17004100500b604104000301c242400203005401911080340c01803500044001d903000d4483e042004014048541d004000c150b60420400c054a0a080c0700740711100085c124400044201c403020741c001d25254082110240d6440501c8685981042030b0409440282041d400c040410074540806010512440050036116040c07591a4602010020700d0a0760141000361182c84900e0202e001e80804400503000902d142680780c1c1c0391445070500e0040b10818000341c1800f81170001803040c00320250904006564845048015428080c0000c039110107640 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 841610512 1250 841609262 841609267
    0x5150c07120807031403012409080f07090f090b0c03040203030d020a020d0f0302040b0f090d050f2b080106030902010e090c120f0c030c1e040b030a0516020318120f03 73
    0xd2130068451203030300390400245403080c80140103401d00d40306100803012118000c01101c1d410704400b103424040a0308203105500a80550b250103150000350013040d02c1c01c00d01d0502c1f03445070302d14418084800b40080070300002840004200d54000d03590045810600103020b40b8036000350459010103992045a1010041c0c1c0060b00c1a400e03954484400b045070795042c82c3c15803515160848908050188039503040c02100001404081552980c450741d011940c400160340ca1101c1d0444070f143c4400003841c0401d02c1e42c00038041c071604180710086060743d1200c6034480160503420640100c2c010f008222089060206454070b881582e910860a548540c00302d4440d143d8036a05c0035401082481c1c00b9140c028550012824410054540f40c15a5806125002403544461500c5185e042c00d00c01c0c00b085a050040000700070800040040056105009022040c805a00c4403005010208882c17402e800050f0000e01140c2c1010003001800c2a03280d00003031035007100070119010030303060002e40a0180040e6000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 841611762 1250 841610512 841610527
    0x12090209040f0302010b0906100f020705031c0206070e09041104021225080f0708071e0815030c15030a0e071202010809070303170712020d060e010f05150c071208 71
    0x24002d0740906c0000b96410f03415070912802080200f5012000031081c401188101a0002c1c0300308880801050020100c85c55580407040050100c0910901c1d40f0060182c100000e10702400340c5103181d030402c3d02912002056039207445109491906166080d842a0200030300c80f815400e810030580140712071611208581220320300c0301c0d20708085c030340c01713209100c2440c080101300f1a854207201d40c410b00600f0010110750319440b04468a0b1030b0803110000301d00708011402807031640004001e108141150300c104180b004030b030815070303143c05000189901142410070318214524080245070440c03015000498511440c021060821300710717820081c0700b00824507440f000d41da807008485802040c070320013a0000070b0550b1002003200034801640c3c03401a80b00d00100380114810451740440d0f01c40c160045440d83d20321160800079000e1440340c0180740c80c44c100003003041c1040c900d040c4101c0320014207580d9603008510500f8100d41100340b401100d8020700360000394901c844c2000302002480b40700c4103a9101031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 841613012 1250 841611762 841611767
    0x19031b03050f010b1e0901050f030a050a050a020913260c0f03090f090408040e0c131409180d0c170403210e06090439110a0507030312090209040f03 65
    0x1010951281d860f240040100307106e0300d0701100f281c1541c0b801c0d5000300501c920030b0040703880c04d40040d50040c414850440d419051003804108000340600c22151000140c603004010584500c4c030200203008140150b2540c405c45c03182d01d000d9061103040c8251213040002d404581d03800c0ca02e040c1240344954000040d000076500c0c006d600c00481401c100e60340304850403c0c5c0c4468415000351701400c021524403001040b91441c1001c2543ca9000d011a085ca02d02078032020109503124100c84194001c00484000c0390009180000c2000d100f44444014581304181d000210b8100245400603202003003a5030b0004880e4020500070405140603a10114014500946110a0035144c0c240d44041001c802151010b5507140c90803070304062030848002c02da012082d8030030380d810322298808181c0f80700b510940e181c07842d0401c25080003141181e241d03500c0c001c0b100307001d150712a004211f008040e50000f02040c80001c1c09904a105400100d000000320704520b603021654940060b601581d00c0e20310328005404165 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 841614262 1250 841613012 841613029
    0xc0206060409080909070309380103050c210f011e05150d081c050a06120c0303050309161d1e01170f10050a050619031b03050f010b 58
    0x100c00e6908010303114142c0c40e1000d940c050040060710035912070000c01e01241c4290040c100c03203070300507050740080c2c00c18203000d68a6403600c00102d000304a0009940106c06c20303040420b41240d0f0001c0140c42660129000c0009000000f0103135200e85080c40c0003090300c000c04201030207100d00d42c0000001e185a0070314080c07000200c02910008014100b10402040741d8140904130b07000981541c40c01407400240c80c00d0342803405800a07c2203c1c5110b04003075190743c0030036085540106d0001c0f108205540d1148a65030b102d103075101c00504002e0581c04204006442040295405442c2e40e055441040d4149010710200301e0690100954032401511030343d00d500a1448550800721154011100490300d0a0025000405100344501c190304c200718140004400e1041e9901c1a18600982d040c80c6e40107030b10b1000030441500e044001034030700f00009089081144540e122901130803c00002607286030795408500d0004029041103000d02c10380040000c8040002401031b070180c40000c100204844c0501c051702 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 841615512 1250 841614262 841614271
    0x2609060f01080309010305070c02040c0c030306090e07030f0507080609030d0c0801180c14070f060b0f130b030703021305070e01140d02070221060106030c020313360c0206 75
    0xc04400c0010840e07114000122400c50a0a0901140907500d510741601c2a061520f80650000c0c10840454a280c2e0311200a01c80148a600c007000000d49400034001114401500c40c0c2c2c441d40300035800c0c40400c18103000e03410032512446c1110a01a01c1e0030b030709400d10000f901d80b400154004031301801c190703401d401420f210071302c030f4501082c040d0303d461002d680c1c03640401180c2e01810340e10889070164900c1100c1030710301240d58500099950101e4074002880e40720703501c4251089464901003010515003c2d001d18240880181141400220020031000501c4104400d5500d4801c0c0d03500040140c540c02003641014540b80b10010b071b14a80544081d10341144d07884540d0400050380c8a091220981000307582048100a00041c0c44039141c0c4045141028840c0c1d0311000d00d0103403e4601811000096024141c4032296810321800f0440c01046e0ba580c00750040001c0800d124001c20300050071908114000a195803000c902c1a81808000c0c8651a84a16100c4070590b2500350400d1126010084541c01 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 841616762 1250 841615512 841615531
    0xc1b030c03051c0c11090711120d0e010207020a030201050309071d0702100507140d0204080109060603031407110d03020a061e181502031008160e0f16030b01260906 72
    0x403444d80e44180041c5104030304e0724071030304150020541c00c51040c1801c1c407e92032028119018000820565a41d9401150a2071040f604004802e0500745060003902c030380603400303031a10b01d195085500640750f03608000e10300083c500c100c040001d101c01c20001c842c45013840700114240741b4140010b009003400712006005158604000a0101440e0300c1801d018420900d820302c262204800758084000c1d02c80c0e68000c0c40150708101218003886110f61200301100e120352240e0b48101e1419400040343c0c05036a40213400104880040111810003c034052011442481a600c19110507039030742c0d003141c07646071000d041d01d54003290340480044075101d103c44402d416080710706410f50980d10328124454800c004442143c001c00810300d800c2c0c1800d83c00d80074141c01c5003a81c0c03028405031944200c004452084040044503a0007040e0343d40080380c006809462a10304103a6042c011002c19400741c440171000504024084540160800d810304ca040c00401240c401c01c001400d01d0740c1901c4ca0038501030081040c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 841618012 1250 841616762 841616777
    0x3061a0d080c01090204090c05041b0e0f06041d010306050a140a091b0305010507120603030e01320d0e0102090907080c04090e03190f0c1b030c03051c 66
    0x46565244050028960056209944070b000c507600e14054020454006e4003d410109801d042069141e101d00948400340d4040040c85081c5041101c0304500003c1280030a5400181c918a0304100100740c09640d0041e086900c0c1c16a511402d24501c4138201c4c1064089a01d10f0060007000564095150024031000d01404001c1d9000c003c4500c2040c00f403e910a119a1a02010204980312103410100b040b03190740c3c0241e0a40e40e00f01240600780c02c42c0c0c41c800103510142e405805541c2c3e0f2044400356a096611011814581001503505140840071806610003002007444000e420085034150255180c4245031100401840c0200f62841455210003990050081c0072554403000d00703090707100d07000f0702d0045150b8441020074512840b83e0780080c040700b400c12650080794040000145820203032a034402601b040101800c88922201070320650005503201c40d800003050040940f2040d00b5034042c4040296070b07070b070380d903142c9030300f07a107510858498100f401ca04865000c04c600c00c6010f040d440c1458031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 841619262 1250 841618012 841618061
    0x90501020115140d05030a0215010519030201111507021e030412240c091e05010203041502031909033c1e030305092a0120030a090306 59
    0x100c04094050741d40c180c240c41612503401d6440c0b12071307150031940003003e40c0d0b51000d00e8031000307444140051040aa1454001c00005d10b400c00b000ca601483d0f22007000605903e0455004554040c1c2c01003040c84284140e41d18500241508200f0a028941a80080828418a4000814540c060109038115030000e0108110304101c1c0c40000885540c01401c451310440c0030003240095110300e90043c200646041c9240c0c139595001001c8505032034810824454001c017020f06d00b000c80760039004e040c1c0141c000f07103c10032403000e0405148070440814019a410007126000660842e0030143c1403800040c0301c1541041031000c881c02c3c02c6686201c0003004121208074868411100c0c03450682d20038014034941310340c0140204101c0d42e40750f0809420074501080c40c20305004010b01030076244503040f4018207528440415803030750000c1c004581c0700c285a68400c103a100640c5c59580520b1003a0050384103201c0c1d00d10310b14003800101016486a150b038040c040c25800e243c0c003161106041d4841003803c0c00e8252 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 841620512 1250 841619262 841619291
    0x20609160e0606070c0e01031a01051e0118050d0c1716060819021614010e0705041109100305090d05120f0a060504110403060b030606240f03010b0a0905010201 70
    0x55a22000559410382d9450b1301c0e02c2c040c410786880f64401c1c0c010014071800070041001401311441c011101c03030110f801c2a41c98800700b1080c101d10110340040c8136160854001994010404401c02103c42c1c41c01068071507440000c9000000c0101e42120350540160081c0502101030502681400c5c206004215941501502c1c0c1a0712907030f400340400780280e6900186045481c1e00c51551085003280066460300008070340c15080100c01401101c139218001112903044005200300043c102d03901b4000c019844c03418003800003d192920348150407402c1001030404a4940c1035208400600341d55002915191080101e0305040344d0104101c200310041044240031039008a00301d07045001028100010745458215200600441d4407164029040c840c00032008d031044000b41044074000d90040c8040b400c6182015100d04044403081d90040501e400122401a503800d2a0701e030358134041c2100d1511003411030b0038829410907403114010302800203500c11400d512005910080500303000038010090400003e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 841621762 1250 841620512 841620539
    0x50907030f06050405210c2824020307090609080706052205030706020a030e0402070b0c210406091505010f1202030102070813231809030d050702060916 67
    0x1e40981d443d0404501031180078400640e45000e44101078907403005540711009150051301c40600f0301e0244031905003003025020520012502ca14031245420300b001e555030401031070759252170403440500c1d1820b9403521348203100640c094040c0b41c84024516180c40e0b00100312669641095140342c000b82c4080050300c1e00034080d90102c1c24042040401f0f1018400401802c558a030300840c2e25108200001034036030b4012481c1b00301315010759203000d03600e41132005000981c0310b0345000034110301000e00081d040085c0d4801410701112003543c030701c98040c0c0c413081c00d02c0510310684007614900c1e551141d1008000c2c1483d001d18040c510030b80140015858002c1089100f100c51142000756980c00e00340c41c00710f640c00e50468050a50040200d5218403a0900d840100101405000700101420045003191400c01207070b102214002442e40603c45007030718840d41420400342501c801032000b40720440c04040f450150920400e420740c007c00c254500b0044244c07600d61071501e04c80c540e0031002c1c002c4c050b0304248040d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 841623012 1250 841621762 841621793
    0x9030c0112090b0f0711030910030b030a06060b03071b1109071b060204050a051c0204020a0c050d1205070302040806010e070c050d020610050909150603100c0305060405090703 77
    0x208040c102190a030024060140b519000b44005075100c01c2000c41d005216506015210503a118845c019250064540c2c1e40b04071440150720058003600001d08034070941102c03000c0400503003541d0100f201070355100262f0b03a0b15044648002004010001d00c02e0744134401405a032402402042c4043c40f54850024450f109444140100301c2c550015460500504079401c00e0113504502d0030900c0042c1c1894030080d0043c1c05080c0c82810070407000100c078500000e4000b00c045480d0013261300d0f0001542000006e40c00100450b0a105a02c0e00d2003011910a200e80701c3d89041c1d80c4ca4000c600c0380c21071003030012a540181034109061052000380502400007582a0541d0413003024182036031148032094401c40001c51004040d80300d5142030ba0200c660109010740108c5800b041c0c43d80107900d070800c101035400121401032456100b281c2d016041d42050000c690002409019101e024661010300420f4403c00c54420001c0381d11003051000b24205441895031294110029000075415903584105841c80d041 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 841624262 1250 841623012 841623017
    0x203041a070320011d011a0306040203100b01140703020a110406080c120a020d0302071d04210e03010f021b01050103032c100903150606020606060d02040e1509010b09030c01 76
    0xb01e8640c0e144000d5001d04558002081701030000302c1900d60140c060301c032420080321010441c55200c3e0310303420700241c6e280c091503000b005003461080009070707a801170512520650401420301c9040030384210140040c8203482c000d6019100790074440c145000141886010203004e6450514208840c3c203011460162018080320710310101041c41c901c9502d00340c4200c001942c0101c0c01c05e07601d01015000120801211100800000500b40a00002410810466010340403075846038150640102c80380510b031500415041009004132014086421542e1045003400950ba0000f60b41e0308001080080c5404810214000d1100f50b045580092482d84444001841c10040b0001880c202c8103a100e50200c801019043c961902c02104c3d0040c494200c0b4407050342c40780c1700e100c51102604541e0040d9400c1d110143c0050000d900c4442c01e00400d6400023aa90460170360911010512600302c848090007920718914003c1d40c0700c03a010030440b0b14407069228281c003050400012710261008143c0340d480310000d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 841625512 1250 841624262 841624307
    0x6071e0509030a0b0c03011a0306030a230d021b0609030d0818030c07030317070903171b060108190308010603020921010f050a180f080f0301060203041a0703 69
    0x5501280c904407240c04001c10100543e410002ca85101002541c100c4400408e0040054000360050742d0510043d03c482d905500030601c480b0101d04040d044a01a42214101252010383d00168a0408142440e41c0e001608035858120f8000a2003014074000d08044a2652402c1000d10020303035a00006241101131048150020b042c00d8901d0904540011b8030700b0503a56100d50300040661100d0b0640021000f02d0300200d400c401a0448040300340c8502519100e610301c8500355214508a100ca061510110f000304004040d075030007600130103c0f50740c0030220092525505080502c0d0034012415181c1c0c07000c607c610b5203040070a44c04480c00d4115801405c0043ea035103a40d502045408950842da554030041c00c03881944540415401449041e52141c4104295240e01170368005692440c2e806107110803800f045100421000c4241b50155845465030034540300c00460642e0060300268800c0000d0b81011030200201342c504207030004101c030442d692034070f03044155078050702030707103507030040309041e01d500e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 841626762 1250 841625512 841625527
    0x30b0315180f0a0b09010c0908030304020f06090d0b01050a08010c0f0507060933020c150a0207140d1d0a140a09110912010b0904150605060a0306030506071e05 70
    0xe0103242d40100070001607446900c0300e070511150100054640c1840356190010a6042520449025007625423074000346185850b20340812a02d8628080c0040e4000c40c100f015150559404804411891103010390310955803400381003100303030101544610700b075905000030600b10079409040d840340000076040040d228901410711600130447d80c0d40080103040c02e002d503e0121130080360141c0c001480e00450b000da0944507410700d4183c1c02414003210b102d034007a01e01400440d180656040c0d10080f0b440005080207070646520742c1144441c0c43d205102c1c0c200042c0f074084107078040c824609152a59070551124403103c0e0206081d1111403080d180c14110340031090206944622024004002144007401103180504c2175404951218510601c250100b040300c10203020f040c00b611640c00740040c031241207580d0707a0729980800398040c079184101075030701c0c2804105503881402170215080700343e50010f80d05046281243c90542d0241c14a01401482d04100790198400b004051121440b460010b03202c490703 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 841628012 1250 841626762 841626811
    0xd03230702060f18041b0f0314010e041e051908130f0f0509160c02030a1203050708090a0f022206120b010b0a090b03070c080d0c030b0315 61
    0x103503400c001d40c003000004000c2d04030b0700d0b0a40074010700c00901408160300c043d01400c00c030490b0808401c4800314403d040724525414098200d00004d001e16003000314400c140d05a080208080c241c00c080310080c86601404140071201002d441c2d4118001d00da041c020f0b1a945035160360707510034048184c4002036020140d00f0092a6019a020313240b8034115101015251100c1c5688068513000702c0c103030040c140c0c1d0005018078003482260300070b00d41d007511005044200b03d811102000d07010300980c2c02d0b1140a1025001170310003030518201600d50b42d0b0006160a080c08002c20001c00500b181a09034809000d070b0001c5104950603c600e11350403103920729a0b51a0102007030303405607a2100813a02c1480c0010000c3c14440b000580b01d000c900c1050074050b036030788854003a44a0f0040a15160004180c1705c014454900c0c0c000c0103540244142c01e018a54040030354030040d41c0d600400e018901150cd55803010103aa40600a55100300c03011400b80c00b0900c0d00c000f500c0c4101310001c00e8883c01d01c040002d1903c00e145c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 841629262 1250 841628012 841628017
    0x70906030b0f251407030f0e042304020103090203060a200307052208070b040302120d2003090907030905010f110a0507020409051501031b03032c0a090c0e0d0323 71
    0x21000c083c4c0c26120129400e0240c07240307071070154000c08695480301c07803c00c51506110f03041103000003080107039002e1301185079040300c0c410041c4200d040c1581c0b01c003040056a0300700071441c03141d0208200803c0545070300100d80c1005100d021700c004103903014001c0c00384144d00042682c6940e41d034107a0100488008109200801c046a030140d8a240204036003c521113803070b0f0006005480c02500d4125001c281020303047d94908251249600054800078007004850780d10080c0310180e07180008607424901001b000070414081503840e1700200c0d550310109010031000380204810304040e44020802d0040d0b01e5292a114495541000f0801400088110840d6203680c00524003a40240c01c4a8100e50031155070646c002c000c0c00140c1d4034280311400d41d4a040902c5603080241e0742e255580050f00c041020301241c0b0344030004407840030440414426245a220079000314001c0501074004030307651341c0c80200a402400b20b0846180140ca09803807140209420164048010040f10b85020380481138400502d007a0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 841630512 1250 841629262 841629287
    0x105070204050402150f042606070c050114070e03010c0c03051b010213030b1014011b0320030406030609290604090504060207030e120615030f070906030b0f25 70
    0xa0800325981b040200540042d0054400c12111141045500b0600d0550461201c4c00d4140f01e620040000d02d016204020050105100f2000030591080c44020b055070100100c1c1c0f40d80c0043d128400d00002e80c502401406081030903401c00300404031a5840c010914414403030120201c0202c00e0489403560000d504a03805103200a404a659a03200d103010412440103075005000c550288402290340d25000d446641c94260503141e041139130072086816207a4540105058040c401c0c040d181010440c81c508061055205990155690740d080100c09800c0b11687c2d04201c160910301085600b00002c000d54181e85004001c8d02c2c07400c5414104006000d504c00d1740c02180c41c19040c0014081080341d02e4018140c1d0522a498800748200140180070b410341500200d020543d210002281c1c0c0404038100152181c00c0c0034054551141090044a07d030503074590002d18401d5958800b002441606990b42d80c101c4c04040744004642020300031421044902c0d01034105440850314000789490183e0a004040d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 841631762 1250 841630512 841630549
    0x60402180d050717060921270301151206022206050408070e07021c020115030305070b0a0903020304150504050904060518010e03041412060103150b0f0105070204050402 74
    0x1c44030380707191464035102c00f441803c2e0349a0134200059441c07640841c000344900d40e600010520000c00440310b11908900d1081c0020416040255182d0b4140c1540460309100140c00707540003403048d0000381402c45440311207150000802550600280a0807007200050075000322000d600c41a81d89100703014400355040c000400c0e00d52141c001659908040584115030000f01a141c015a82d80c1071030061b803004440d90001600150340d05145850002d8110390304030810703c00043c4411034001d4040621060390401ea010a80c040791440400100c41c1080d030f800320300c050040c0300d806160355001e550303400343d40903105a807811400c050a80c0c505c50000d03a00202001407048040b400c090030f0a400a02081da505d84c2c0307500c44c41d241c407030040e02c0c140204034007640694015032505280c484d0843c115125042c000707901c805842c0809030042c80400c8003502a5004800e076000c01801da0b07000c0000c80700000311840c02549000c40005290382c10000340d44a00360142c40110f015951840011000d02600e92910b89 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 841633012 1250 841631762 841631779
    0x30a08031f06120606030c0f03020c07080613020a090e07120515150f1e0f0f040203041a010602060603060103140f0d180b04050f0f0d050102180901051806040218 71
    0x180c00d5844207000150f118121010094552584421015168104d032100081028031940c00f28161080c1d00503c008071402007660841d54940703001909100c0260741030360400c180b2000360019880c0480000c8020000076030708000c1070001104150f25282c0724441c1501c8401030164001c1800014850a4821070007006001c44524110243c0a00c00d03540490050103201d440c141852a401c243d04a84c07540c000d0407007804c8241d440b4108106d208014810b0035a00a0030780072105010343c0355030010b580654801d200c14009207490b1400300d4a580c0c2c0581c001404c65000a042c00080c1c0c801141c003c1c15642c0000f00b4036068488250750b0761510840c400b500401c0d11402402c0d4034001e13400300008424544040000082569814003454140598003400b41d10407a110068500d81c81d00b10485800e07040f01401108840d2940d407120341c220707000742001c4251018944030403100c0b8a400c01c100c5000d010101c1342003040f251081454903019a0091141e401144e002403401c2030002600d1041240f050020071418 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 841634262 1250 841633012 841633019
    0x6032805120703031103090c0f150708070501141e072d030f09020f100c0804120b070507031b02030c12012a0507060f0b040203280209030a08031f 64
    0x740150b00c80181900040c3c036014850001941d020b04030b03402603039110001e080081c8540e00f000f02c0c0c01030441d000c90b4403142003080340d425554210b003d440c030340740100e2420b601c030105401c0c16403c2d5600340095090096594081124404004200c2e546041107a940b10b0016a074109042d0742c04203c5c00303041072a1000e03075820044220803014400b0b8a0180f982c3d418010401511103050580d21b1340b800c000d50240401e4000901d6003821010242211124509180703503001c44e071501100742d401a0401d88802d5209000761041c40300201201d81c001d095440c1c428030380905a04d00410841801e02d0940d803244001a0708004e40d54204080240302c180108540c451402485840b8020b20102942d40c5101e940c440e610041000c0b04210030040c04010b449480c03802206588040003040c5d446050340b03001740e883c0300251094039940301940c49007500f014034014210001c403500c482d44034954480344482d401007050765034645001c2481803906071f00450440c1c0b42c0c0c0364040c4800c801c160140200720780004100000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 841635512 1250 841634262 841634293
    0x90602040e0711071503020f04210b0705071a0901060b0c010b12120a0807052106180402031b01050c01020d1b09030b06010c0f0c03030201021b010506032805 69
    0x350140c401c40d01c5024150040d0359034180c64644c2031240c030301600c00c002541e00a40b4003136002001041801841c0d60b141a8440e580001c03841c0340408a0313030f0048101d40008040110714054a0f800c8071942c1440c40c21704025940d81120022266a00d14000c140c600202d56010001d401c20009000c65506241e214130813001c845008007007212050b80f01d68842080880d00460200300002e640710b032980140e00d4480000340130b0303e48070000b40520b002c0040401c0000441e08403450300a0241404181013601c0782894070030400061490038929180b1545e0a0a1200503a1b0020301d0324240c44081340741042600d40000140c0380d03400f42c032010642c0d40d40001003829036400c00c0e501504200b68408100c004413500c0c60707811a20542c450100501b10f0306283c010980c590f0203006019040c5100c0c000400d05081c90307940700c1d0850400c0360700c1240076039000704d00148940080f0b036003103d540011070020000ba1500f80700283c0d40d2600450000340000c18540c1e01480d80840e1a1888502900300d02160703030a040c040c070301 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 841636762 1250 841635512 841635539
    0xe0a02090f1006050c030f13030506091501090209011709030403081812030a1d0f0d1103070b0a090e04060e030403051b0618013e210307030e0109060204 67
    0x80c2d48880c085220003094035402401500c8150800d45d0080d4107110400801d008654010415156160600708000000038020098070740300d40d0303101e800f41480d5408594401d0241006800c000900341c01404101c100c0d03644450812078843c00358404508a803908141c0904510543c1c201a01c80c410000f440752034059176a20000551000b0307101c1581d1010404002a00c038000e6041c100c00042100d081c6c9550491000680c5000490003883c101d40742c8441000902d4951624008840342072000c0c0c0620024036050111200420f040c0030140d2400c00380c0c92000702442918010401030300b1089010030b044c131150b030380070101c80c42e0848112660b498032070414541d0740c10a1006a401da4101103d400034909181e01910320040615010300c0e10700c7c1030300c0c0056800281004840b02c1031648145104201035407541c00000303c00020b60b1a141c0410a40d909500780040e00c1c4001480013819082d41b201c40d9120f10403203600c2482403900103084c800c0810030074050b2111010241a00380007150201e42d03030459002 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 841638012 1250 841636762 841636771
    0x121b140f070609150e060a030b1026180114041b0b0d051b0a0e0a05040c200316060c1d010e130209210618030d0e0a02090f 54
    0x100c0d100c4000e00504503541d0840e40c05041c00155942104201c2da80c1e54448129560b045801c040101580d0302000c908903821004044c80040d441d440383d00a0f82c2084544601d0f076007203924003a0320403500c10420025004690300032030688801c480019801e4140c03c40345d007004202e803100a000007a601c280790318542030259002c0d18040c1051a07034280388016401084100c0b2615408a0b0901d40564aa1030080c05d0050a108168406c0e107400100b55a00c01c005080051098503061001c5941d04140b2034900d107250032040c0110300c0c082039200150707080892548105400c40300162440c04052110b410b502500b0300a003c201a120702c0e00080001c00d07008842071000a80d03885046c6c0c0740c0d1090200d200c5000c06132580c007045070450400c6c414242480d5062002c81d030b5250140c070303041d860408504070035218250841d1044000007a280122020711509401c40209a1000d1910040c40103080e164428003402c02c3e0f0841d81e80481c11041b10702800741c103a44540007410403041d03203400c2818001b400412034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 841639262 1250 841638012 841638053
    0x2280305060f011a0c0102071a01140d050a0b06030a060e1b040c0c03030f0b0d050a050d170c161e14120d020d06030f03180603050c07121b 61
    0x1800550b02e02c80200b0b0042c120303001c2c51100b0440081e003141e514500d61001d4035140341035400304124030202c0c0001907808041c1501300c415980c990316249213120207204041590307128100817001c110102d540020b185807030716004444041c6075200c40c00000d14000c0b000b24002d002351b003448500c00c0c0045003c540998488400c8181c000d2040c1510104801c0726004411000801e44041035a0040b0b4440d5000004c3d0900f0348000080701d045020020700ba0901c1358400701c0720350b8002068502001000d0240340003500d47c03810000f11203d00903100b11015000185019002d64000c51303441d000c00349101c0c070407160380c5c1c00c022070b81c0d001c070070407a0314494507010b403a4207031020410b041c100105101c00080412040c0a25a0380500b05000450090301a501100d40c0c207251607141c2d13101202084045801650003032107a240c000b03a440c80c0c103e805401c400540d00500500d850141000059145c110444010b103600214000020301201003e91344559a641c1000c80034580c0c80e203960800c00140d080c0000c0310b0400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 841640512 1250 841639262 841639273
    0x6100519080717060d0303052701020c0c0904020604030809040b120a0b09031309180503160b06040510030f0302150c040501030e0304080d05070305091c02100801031e02280305 77
    0x3d20307038000e5a0707000d607902e81c2c00c0300c4c12111010101e80720342c0c05039811042241c0d004c501081240e44949030039403410440300c0d10740d600282075000060100040d40e1002019901c0420516041c0c000030700b21700640c40064050500050b2260080d5078030350250804540091403401616042482d050340c88411000441d8800842c60105018010000c00c0e624922290400d91111a00f000002c6026107042e074284210b4018608213080042c07814005070801c6443d1036500740546106003011112100c010305898011480e01051003d000e840f0340f804c2c02520f8001c819049041103904d0f080303240c20070070300c5510035002c0484148007084204c10700030300440301d090b60140031410103600491303100e02c10791045614640c001800e0600039405a40a00b8496000c0d06225040500d52808101c60305c0d400d8424a0790210301d04000030452500c0010400e25140e01c0c9444a80b40d81580d07640e006c40c0d41c42c488002e444d595000d10303d20031962015010b10030300300c00790029205000d030309001103000c43c80f0303000448590058 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 841641762 1250 841640512 841640537
    0x306050901050f2502070f06030c090605070302030708091906030203060102010f181b090c18060221031504110322050a0206071a1003030f02010c08061005190807 71
    0x4454250b4041c04044504e00c02e040250b0703004420801e0500103807000c0d0f005501000840b94012400719000f801d00e502c0c0801e0105031420000c00c0c20217160048802d011044c0320b64030100c1c0e400010f0f106041e90180102da6100c1d516800140c40441031a12803104038000c03280400e9195054004e54040d45080c1c009000e11038601d2809001d498110b0b8a03400d4801011039110041441c01c0745074a43d0300300d00c06022045c9038070b070310154003603802001d03400700411480d21201c44042040107030b840052030b4910142c03032420a9072401c134044110906100440780d0300440840c00c5007404004081c146039000340100710f41c4400f10301030901a0000c40302005001400c101200c140503020f4040086603a1000180c481c1020507400c12150745c21000059610103c0c0054035146c01c948081d010740114400010040000d00c0c5242c02051a02040c08400c1164100000740b1589600200074640108040761030b00308480402101315190301500c0c109803c1c0d500c801e4060400030340c00c031002c140241d1681e80e480540490 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 841643012 1250 841641762 841641781
    0x913061401260601051201080601140a0620030408010f0f050108121204080d050103050a02130b0604270207080301030501060b09100305060312030705250309051002070f030605090105 80
    0x900d0030a01000b000030120700180d0514515881e07004805060060030940d00c8850460010b0090300f00780003503030040c4018441f4285c0020040001c80003200e6464140c1c1c10030100925401805458840003440120681c02034402030080d6805889002d008101c8a4062207048000d000c10018800d145e03861300002266100c8042501c00d4450307011005280ba2020400089481c8280141706443e0902c00b0300c80c81103400d400340141c1d8020b40c0202e0050049882c18010008840342449007030803068a42000480e0f41e0b2941c8041c1c03000ca810000940d007010b90b413007000c40318118140155006071840052040704200c2c800c80914141c0c0d0159000300212030301c0d0f441c5000d241c862100c0c1c2540c032029614882c0b10080c032035004117a0002028055a6000343e52101c078685a40050b11148081680031866907840e0000c00c544000c0d03c0b005940b03030780789402c0588018000180c2402114014814117451032081802000000d008000100c0030001155581c00c18000419060311509140d500f480f020400011 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 841644262 1250 841643012 841643027
    0x6090902090109180b06040611011802013c02061603050907050d080c060403120e0105010e0412020327090a050f150d0611030105010806061603080c0913061401 70
    0xa8043c1c407603100803428a16a10220011024000d003800d403a9001003000380c5940d40900300500c42ca880e22902641038503880c5007968030154074803180d103000a0006026030fa11080b23a400d4040313020f9600318801030b05014140c0b014054043c140d40c00800b410301030326450740003030041e108500144283d441100340c1e00b0308405480003560100074507032001d02c0501c46841c0c04403070244401d108108041c50081c0c0460b0081c10085e0442c2c003940443c040c85004400b40e20140900f003a05c981a0000300070130344c1020012141a1340140024104400141400c810030340200210f03201ca046038010101d40401d20068045034044121800b4022000c101c00300c0c50408542c051540140007105010800f03a482d1b44048075040035686899a000e601c01c070004002c00e0083c03082151010a2980c2c2c0c555941c100000580040000350826002c1e010400c10b0011031a001e0302c22981c1158103143ca14081d80f030b10382c442c1106001c2c02c03281541c0050458070f000103090127a48084110380111000d0101d2280d03400066581c41d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 841645512 1250 841644262 841644277
    0x1a1809130c2417220b0a0b040f0c0507060b0402041e06030c05030f0402360a0e06042d020913062a1107091d0f030f1213020301050c0406090902 63
    0x10011901044c1c0c65801024009106074480c800d502415903151030340186a5402e44200c1d007110341d5190545028103080c01354016a000300e50080c000d50044102c014514801d0345000341c01c05682d0070150b10141c0d1203804807001170448840082c2c0a00030701443d20503d0629200306d10100307140010b0b00d10181c3c01070f02903030310600c0c1d03d002c0406540d0f12038091040c1d0341c00000031001c000e6102010701c600c2200008510700328410300ca542c55001e1a01070242021600c860209603215400903040100040000040300308513010540c03a0120140c40c0c0020840e00d4000b42c200941c8004e51500304151480079141d0381c010f46004400074010103401005c2c590098000700c1c1401041c251f0100310080d00790080c04660191030041007180c030800c0c1d4404201045540b00c1482a0162036502c070443c1030a03408101410309041c0c003901075454042c6a031490034041c45031040c00c1c10301820000001c5d15150b074455a0381d1895402600038061454003d00c02411644280603040100c1c100a50105150110b0f10070b80c3c1e5003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 841646762 1250 841645512 841645547
    0x4050409031710050d03052b0603030e0f0d020d05120703080a140c0409090c08030c0307021504060504090b060d050c0a1803170906130902041a1809130c24 68
    0x1031707180e480484a5900c52101503a254030b20840400380349603104802d403d149500c0b6400203080c2d0840c80c00a00000d007800101c1d200fa0300d204102d2a032985c441649210056049a454050111030b01d070890801c90f04506e124100b840205c0c0c920706142d0000349903841200080e20421131071b509440c5c91415060151103450301004240414803400510b42c0c4028a06405090504540daa0711182c0602e540e00509031400c1503000030403d4421414030181140c000000e071002c15003450708103800240180102e22490304c04981b00d40d00c00084c0d0b00c0c1c0c10100c0d05003d00c009400d2005181140311602a980400d4001000400703640301519083c48210b560000d50354440c6820411410007208040103402502c08140d00c00010080325030f41c007203a800114000c000c040409a251483c00e1b600c80440c1e4034880e2030f50a004010000400f010800e01000c418003c0222403000880c0c0310341910b580303402d0170340038018124a01034202091100154000300d43d62064210704a0382ca92984504807540040280075500303 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 841648012 1250 841646762 841646779
    0x705100b010203090910090501080d140d1b031a0a0b180a050603071e1d221802100212030f07020c0d06140705130302090604020405040903171005 64
    0x104510a50011540c240051044034100b804e82c0b00056150201502c00c0018a003810400300002031760350003914014107121000d841002c42c1d144010b0003002800d0704070b20110400241030b140030600b03a804040315544100d840751005040d1f841c003030000e00d0840d4080d1111a280b0024641502e0890705c2034003541e40515031903051600889031345454200c0d468009602c142e98040228264407184099807041006a076060200000c2c400c41000980184400004200f01d2002c078410344240f0281003040454150b42c20000314400146640440347d07010300d00c004e05070a00c07804036818503079403214041c03460085480002810030305070243d84d600035100151050000920004010200d0224260380c444214010f48005242207000281c01d00c00741d1208591803540c1ea040d00d82040d01c042540755205940c0d042c4580741005041c5822a10201031100038880c0968500103065074885070107540003050040d0041c0072300c40301844c1c0030b84062540d101840c0301c0c489050014030b00c0072007688030f03500f259404bd03c540e2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 841649262 1250 841648012 841648033
    0x10e151903260f0315010f05120a1d160f0f0506070c271503050717010f0c0804120509090402040f14010305070512030c0705040519020f0904050c0705 66
    0x5180380b039003119820400e860300707422010004401040c0408036030005035502d14001e80e43c50603c4841420003810850603207100a143c9070000c0c226885030701e80d03401c1c4441035990360504a02070150071400d910049980d8114101c5908002180c12400300e40002c1404d01c26120710078100e030140b081c400c61030001c00d480001c00070707802e18200810020380100200c010f030340d07180c4091249070400c40036611000030440702820100002445082c84000b20442008911490f54960303903502c0d6414040c44406d000041c19410842800358080705143c07a0b01c0c007041c00000404079014100d0041182c0c00d070340b00c64200303401c01c294a1240089807691342c0010034600540c1c64907000c0c04010852000d44a40c03a0756145091980200c8210b0210b00940c4660000d248403400c250500034151741c54540340320f50781d1050000b07182000002c50880280c0e441500d0004032030342c485c645030620f101089401c0d01001d1000598299030810a4001c080580d170680b828840c03503c50203004041803280c000050200e800105011 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 841650512 1250 841649262 841649273
    0x306061002281101030c020a020918100911120a060207030c140706020c0609061204021f17010f21030908070e01050301050702030307080c03130b010e151903 69
    0x8105948603441282e41c01c40c42035608a42003035500c001c0c000d1054014482d0010002c0320007003600312400a2800f44120280300c04060341e500c2581100a1241042d02c0010303480b03200384c4003802d403604600001c5840e00e200682000300144513251058444038800e800745016420b1000602e0603001e900402405d004030b82e500c4400003500701641c01c50401807400e8500c00440c0c000c2c2c0d9030748011014003000c1c26540d440c04002a150400d195051401680705000c080d841d42c1e161802c0d1461007840b20f2000401da03803141f0004880c5000c0650700f50f400381c800e844044140768820591406a091500010034503600d0b11080200c1123510b20480c04d10310000056008250401c92503481c20302d1180c104044441d4035501441d0425001d90483c40409141c000108840e142c00d010340b03a0050a1030019500e50704104600401c2808024032402d00304ca400800304907110700003080c007000c0c150040d03048011961212845038070b90205a800240d00c50010000a40c2840c05030030151600541c10341400780a4550f9450 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 841651762 1250 841650512 841650529
    0x90212280303060e150102010509012313060212040614060907030c0903080c160b1216170403030501081e1e03070609050a0b0a0605010801060503250216060509030606 73
    0x8030100740d1a401c0008441340d4540c04680201c03034551020031402d410000082c212000104a110180c1c1810455000d42c50f00740c41c01c0064815182203069580d5031424851103071150880c005109a2000613107030384100380e03446284c1c001d41c030441040c00780c230b00d10b112000c440c07141c00d070b40e110390011803400810710981c000d40c0310200f29451030412324005c51750b9480c0d04100360072040181805801c82c00c04000540c100c03815007405020a41a42c90600c103d07010101e802c1c5c540149201d80c0150400107200d121b42c092040503140c2040c4211419040c5082e25005010301820301ca98102d900c1001d41100694040c070b07201e055460049001400d130000110030b07096203043d080c910814280001c020702008541680120031001e400b0b1002451250182c1c070f030002c4006002000218020302c3d025062100e030ba400300d0b855044404078500103451b40c846442ca000240003000080030410000009446443c1e00403600e50044001015101d148903540d102c140c425105403101241e243d04030310001803a6150400a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 841653012 1250 841651762 841651843
    0x9030d11152703041701020f0901230c0106030c05030109020f090718080303100b130603050a110307020106050907050a35010b0d11040806060d0809040609090212 71
    0x9142c5103200b0005606841144a901507100b00e400014040c000051803c3c600003061310403400031071400100c580c20100324082e1114503410040315030151341028200c00e80000f40c44103001c620350380c0c0b200014092030081100d448100c80e1800d501d24001920328042c8201d842064026144d40b446c001423174104001d64800800110900c40688003030419080801070b00b0029211080c01103580707051564440280d10115030203d459440200a41c0f8a98001c18640d0f200f11001c50401243d1500d440c400800a0144420b4110541d070003c800c1107485070b41500503c1c125901655401c120ba01c511004503035a100c0c3d204803401180d4055071064120b83c203100e1070301602c007640310b40c992203000403c41c1c90358860007030340810100075021400c5500c540c17051180145242100480900c0c26261003200b980710040240218440c03c1e9101c0d0942c103200c008000c070380d00300000400811900351140d1103c40107005060003a8090030780d4034041d14404500040800e18059480035000800703400801a00e04035413980e1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 841654262 1250 841653012 841653031
    0x9060501053c0a0c170307140306030709110307030b0405010521010b060721080411010c02041506091403010b1c050f0d08010303021c120c0207051509030d1115 70
    0x140502c20940c2101812102c1c1032961031400e9180f40382020055144001800750600303800700188181c05030003080e40644d00300110580703a140d5030741c0c90011b070400d40b81740c0c48900418101940700e01c604400c4801140f0990b51500c0070090001a0018001241e81c00d0085580020020b01c04044c2640c0c11420042109203074800412114000b0b00071480c5500945000c5074040708003449040d403c021010300c03003003200031403a01811500c0c16449003000c00020504007410b001050b4100025501c0702d030410b20740b64104032001d00380d4540d2104002c0c200f144511801c2d1031008564000c90803843c042c083d00006a4008116480d041c0b41040394546d140b014840403102c40c031071034a1801e110b0f50706110000f00012540c840084561450801908144910f81e103809856000340d55004055044901c0740e8066403030340340019403a00401b43c10303032914509400c0264001c081f00460440100801c0080c810400103400380c41074041022002e8884100040340c104040d042071201e1001e00206c60a240c2e4003a2140 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 841655512 1250 841654262 841654357
    0x3180714040222121203090201050a0f0c0b0108060a0e0703050a020603180703080306100507051209190f0915030305040e0c07020d050105070e030f03030a02070303020903030c070906050105 83
    0x2014034241c0b41002d984444c0c00c05015400d490184440074000800b070b401d050070203001c10822a40000c20034402d889800d000d0041550200101a206211a0220f60352108204086503100d5000950350301c01141c0360303502141000b060392118080490b010046070341c000300400450f0f849a0800a86400040c02c0601c0c4c2c15038450b0004270b0410401000009500034038520b6a0707800d100b4144065003604c170041c0414810b0400c82000081d07000283c400c040642c0c1c00c8900c1d00c5200345030005003e07107004130300002804a24013011400f214600501c1d4121a20510b00304465007100400c41c510355028400a00030440a0100700208008000c50590020791040300c3c902e0040350341d00003040203503000802c0d64280c1d075401c2088042c3d90400c45d0300d40410400c0f0b0003001c880c2d11208000383e980c80f008000100303090300411f14504050180d010f40d01a00401006e4079110420118195501c4000c1d1040d000c0703503810120002055401482105c4000c090035590b018201c900001c0071501d190070300c0d08ca02c42002c1c0d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 841656762 1250 841655512 841655557
    0x50f12090a15050a0507110c090405010219021f1401060503061f0305101406070204020705010e060405030712090b070f020121140f090604120c0b0c031807140402 71
    0x40e009840c02c49950100001660300780714800c181150f41c010030300400e02007040c298020010300001e00b18409001100c04c000c0301c0d6654500719001e0300a0400600488204030b00c0918102d03004940c0b99400480f00f1228190030011540350001e441c03424940440341c03800100180115445100215401300703010300103030b60500c1301401054140d06056a0100065560360901c45410314002e54000100b507a104a2032407800b13a940003a0491241c0100280b00c0d59000a003441000001e40207161500a024150b580c0e501d45410a5034681d0710040c02250050a0741451200242c000c00c4c204058600004032103041410701d40d41c50782011803041050b07050111600500c0f0a5541c400096000a2604400810700c3c414080d003840c4540000b0f05040c0300f85041c0c104020507080d0010f08943d205811880403181c52094003400c4d1514411040080d110080000030061401c50442c0110301802080501c2f001074105e07105032944508041c0100031140b14000501801880e0680151400240071041c94940501c0c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 841658012 1250 841656762 841656773
    0x70c05070b1b0708030313031124090a05060411010314010906140307030203031206130218011e02070314120d3206040f0e030a020705040507050f12090a 67
    0x540c0041460032002404521400c9041c4030400b0402000c8020503209060503803041d00d034040240a51a04034680c6000001d0603ca03004065103c044441919860440038542007000704441140c04040443c1ca030100742c60500020b00c1c1030003650402c010340903d4440b47e0310031401e403d420b601d035410592900c0c2d420b0240d00789403202c5402001c0d40c09001844602e0140340d80790403103040050354800d401030501000076072801b00c200c402c284070040f42446075584810001c0c841d040a100c40d0010035101040c03802c13403200e158000c94540b04d4262a8151070b88213a80d02d080f21288441019001600a800200300044200c0b5500020074092825686a0b500543d00508190041000801c0954494210b040300e0034030429103424031034401c45548441403401240c0017102c01c02500c00c0b801203940300754a4030300700903640c42000d1045000c01642da9500708103400a41c6c0d40524059a44039500c0d02020841c198003070411940c4481ca4203045d54280b00f400941544d402c14002c042c000503000e102003110000b030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 841659262 1250 841658012 841658023
    0x60801232209050706090305190204020c030301031506090504051e07090c0930030c06060e0c130605041214070308030c4306060306150303020132070c05 67
    0x480080000a5214203800d009182840e5544104103006c1d04000034404600042110710519000380041881c1e2070051021600078410405007644500021001000700110200c0c00721014a2001041c40041d890f482800c0440da4223880c010503d511000c1400f040c607074400304000380303032407400281e910740742c0d42d603801406841b032243c0d04600107a181c603018000d04580007200c00300320f1000301011002a4013070040000c1072039443c802406201c10040940100011034002c0310192034600040c0780075043c03050705002e450300004003040c518080002c01142c540d1003002540e0440e1f105049035a0b42c5151907c600c803c41d11030301c5511810b4015001c002c03010078a4500103501855441d5542c0d55208140d03500c500400700780c40c0744030024074200c1ea6203061000e07680013080e0051501803130450030240c040c074203000100500d5100425543c24030202d6044206028040350469020b80c0082c0080341c0e0020010810b2107003490b51070b00c1c20b2401c0460a80d07500700314500302c0e8414100d00300795100c01115140d061821 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 841660512 1250 841659262 841659319
    0xc0309031709010318030806120f0106141e061602030c04051314010b0306010e07050c060a06211a04030207180203060f01260709050604080d020706080123 68
    0x1a5400101d030b001559162003402100700c08034800c0e0440c0e03030a0fa64000e20884015101780e106132100b01e00441103440074400c400541d49000300070800180d59010320b20200c0c121032001e610848650100c0708468110040411401c80300410031860320490311051044503000e5241a40c02d442400040a0180c03582d20801d40180d00301e40c0c2d0502d00342d04074901240303454002c4441e0710a0343d05010f40842152000113201d4150340520b10008269519108102c4140c094212a10340301d200c1c800c2408400c2d99541c1c00001a280c1ca60300e130060f194921094546003c3ca0400004d01072105013008001191ba1403031840c0d0403074840e106403035069641d4401040703030f60502e40d4040003942d80001845010720380b03007804c02844030081c01c0000d5a4204c0d4030395441e202410508801103070400380b0000d410144120650300242070001c00050b141c80d00c55035026901c01c810b15050002d0302c502080450f04500803850103048503460746030f035031000782c281c0c07000300608896001c8035030032104950120303480c2c4d542c480440068 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 841661762 1250 841660512 841660553
    0xf070909050a200d05011d010302010c03050c0d09061d1315030c03200d08090d060612150c03090807060b040b060c010203091b0102100b060708040b030a0e1c0c030903 73
    0x1949003d031504c000b11841a40138510b00c0900480d0713100b40c29000010141129024200100b000070035041c1940c062040d00301003400c60188408591505420512190690300682d0f10b1200c0301c0c0806072040c11b000c0c251440580c2c0301d0860b090314503000480d0340080d588011486503403070300280e83c6d0350b9070588141e20307400031100100449003d50100d103042041c200006030844800b0100243e58454940c1d92080168460041c0c8071101701d5000d100e01c5402c1000100310311300132030308582e42030308080139080030307114010340b400d07090990142880d4440e01482240340e8210b00c03128980b0441307964081c0105001681982c2040e125001110641d50ba01c0c00303442007600078400542e80b4a45004c1035800e04000c881003d40d04403200b00d0740e01c8181d0780050f1a80c1820488240004d84440f03110010742a40100500106210000100401c072111410081c50041402c4c080a0040d566901d00c030503200e1a00705040c1a44482c21104c40308054411031014000c0c2e802400c0c01011981c40e6242c00060300c205020079001c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 841663012 1250 841661762 841661767
    0x1180e041b08060108011103010f03150902100f080f04051207110415080c010801060509100c022808150a0209010c0f0c060f0e1e03030c160e0f070909050a20 69
    0x96540030b015481412041f12069803456041010701e0b140c00c441d901000d00045090958a003118543c0d5004803580798000b000600030b01100d4600510000e10ba92a0800080c10100451300f00c10340c00c1420344c052035100e8064005d41c841c2032001500c1d500400000d8802103424006600b482d102c911600c40c06501b0038440389103076810903050070301d49641c408001c0e0401c0b0b01c04004000550f804010b036036070b05108682d2446102c0b5400411501c10351110320281d405034902d0744503890000c8074403003e02d0382079440319400240d643e1800595154000c180800ca402011b5800150100b50755a0003420305c09414103003814669130b00d440d07035411228200011900d441c4515000d0203c1e0390807103c1044400000e2400300f84d50400900802d00e64608402c49540610f602e54803100a581c00748251070f00021000304844a07641d8400c230500c403040491060703000149150012604007040a1702c01031103030715a0b8549000e100e2500b0781303c40050070300070095103a06a59981c0c0c81c4203942d80446440045407411903803038 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 841664262 1250 841663012 841663019
    0x90f0b010f030c0b1c0b2b020901080a03050d18120210200702040f0b09040c030c12200a0807080c09070e03150703020415031a01180e041b080601 64
    0xf0122003854000e0100c042050010b209008000f011401540401d03003008070b50f02090034045014843c4140300403070800810b4600c51030590030000c4070510039000b240c01c07818590380c0b80703c22038465488000203000030300100882d4129018070b400291109288207080c0c5210506a01d81081008070b1460080050b04102c0003404070503100d008142e5a0000000a00026643c980100d42544a8040002c0c060303030b26000b28010100703040e4025200e03010083c0c0109414546490201c0c585001800105c5201018035400f0484401c0c0f2000340c00102d500c0b2141c6018510b459040c071042203a1000c1140e40001c0800340441d221005014840003440068014900903070711104000000000405000811200d541042c03580c0da4000743e01c580489804261541c42d03100c20808801900c03803078110002d1015025180c001440d07040d0310007004850322404085005641400440361040701c1c114580041c0d160404c10311030034104659843d00644200703802c484441255101d01c59264295214051940040c030040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 841665512 1250 841664262 841664273
    0x1204030801060801060c1419081e03060609240c0703210215070e06130503010518030406030e0c09101a04060504090509010e0109050309180f0406090f0b010f03 70
    0x49002d07011a0902d014150304000c1300a101c610501005840b2007010180c6d06e55240c4140240b00c1061081850040405120f05003c4103940c0708022810360400d080307142d0294441c040b03055a0103000028002c1e458981d8640410222880c1c00780c801c1d04500b000402412803803108c01c010184500310002914241e8034608003041d047e040000c45184040400b1208848154007298085c001d0045800389203d80d10340100803103007406040304050304640001a400006801005481c01301c0d02e04900903c25903580724024058a240050b6080496200740418040035000e40c212040030b824403012646560460070001c1e50110042c6c82d071151000c1e1104052003a0f100032001c14424088402003d031400f03181030b400500c48d21480c0b14051b10155201c2c0480c00c42034003034020f0100b610645009104440310b500744241c990384031702e9500e403007865507004c190101407040b09014812140700c6003410159940c0e4481c00d025206541045a0f0702003010150000030703100e01e50060103080811020144c003800c40c40d0a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 841666762 1250 841665512 841665527
    0x180d0605010e06090a05060f21100f0b01030e1002071704030302060a05010b16200915012019021507050601061b170307030e1b01021207050615010306081f0b0d05060426120403 77
    0xcd41c0c10142410b40605203c400040c005046034500c03500107948142d24108107040c4440141c00d40030b460000100002030541c002000d46c007410140300704210b0ba9a0b156031030185407082d550114141c030345056030100410f243c000580d07800c964190000340c044514400080f42e00c0e10403156500b59290a010101065920021a81f910b4a00c9442c20701080c682401e00c6648081c070184046000250850080441d1503400c00c80b404941d580280c50388680f0f0f50f1a019403214000d000d91400101600305011050b010348502840694102c0f0024000c02e41c007283e515030700e9000525003003d040d100c003544410000108404501580480076140014188800090414a007003428030841ca80902200003c608086031341904a5850305410741c4103e46040140d0180c00540d0240180d805072000380021403448080e000110066500c0c204000050141005100d02d000d1001811a0b8000740010340041c1e012580520082242c207082c0c00b5903043d4101040140d44080f01c450015001e00c0248010590000304 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 841668012 1250 841666762 841666781
    0x10c020304030c0911070f06050f370b0a0b030405010510030c121416060e030a0302030a120b0604060c0308060301060b180d0605010e06090a05060f21100f 68
    0x1552400385140c40780c841c110040d01842c04440e1740c5180c1c00000044000480d10305940c0f1040e414000c40c40c90130060000c00040b03408110b481d1f01c000005000d5042d10a0610300492040c40c0265004034055516120411001c89049255503070f4200713507020354441c02c20500903e40008050f5403482d081c03411a00f5240080d044042d9190070700d6050001600306140001079a8580711076200d0351880c0d04241c6240c0c5500010520107006101c0d8441907141d945501000760b81194a0b0101c0300b0103071205040d40c46090400150060704140704504626126400402d50781d074640c0b10103c2e07011b03180c8d80040d105600030390007000440c0741035200c81c0c2010707001442e135640010200c008110341d61401c3c10f000024443c84500350b40300c111691011800740c2d03c046a8580154110904001c0c668680b4400e1006030000d4980c544109076440021703c8103012801810710540c0083c2080110329004828000004007214810302d88507000c0c0040ca4210390100400303020040b10704004114480b12010120403135a0400c0c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 841669262 1250 841668012 841668017
    0x2b02030402030d0309060f0f0608070503150615040b0307020601050405180a060c0309060e030d0b0a06021b0d050f0604030e0618060309030403120f0206070305011527030c08010c 78
    0x4010141c1d8021442d0b80890003e41000700c0c2c10040341c40d00c84000c140030501c038140b041c5000e00300b840341c101c0c0c0d0b48034400341c502d420102e1b00d49030740720000c0556a840c401824640000c0b0607000074414100301c450810042000818141800c0d02d8a010600ca90801c03030708a80182c0c003000040080c0d1429004460700250703413000403203220308503d502c507440b1500707440050200d5440d1001c400c03545100e036010f01129078000c40104a0500c0c072611440e10395000c2a411407446041000b101117500c2e00c41410720407945070b41c00900181c8000300c500c80080f21007182041d44046100c00c1c1c00c0100f101403161100039800c1c00040c18181c81d1500c0e0150070701c07000c07000190107442c050110300c40c03c0740281140d1181410894100707441c1e650f00b0844074503511554000a0803540c4215005907180c2d0800c02a85600e03c82da0240c5905a5801c0c40c100c0071605c00341301e1050343e0040c0d08404c0e044a03000d00a0340c2c0c0d1143d0500386070012019140b1a441c449540d0343e0040311003c3c0c0d955030801c451442071095128110780c92 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 841670512 1250 841669262 841669267
    0x3070b0f04031e120e1b04061212020a0f030e15210405160e04060b10050f090d05010c1101060b0306101b02180a0b090108060703202b02 60
    0x291401050301e68803071503450310031100343c0203000d140d070090900c80c0324803a20180a20001248001042d102e01032001c0c051b04982c1c4d072400d940e00d1441c25002d00003e03590040ca502c1041000b58842ea8031440d04101850b0550180301c9903000828180780070704400c0ba010ba100c0a251404000038881d4503105400040d17030281d001c0c007100b00c1006c0000040b1044c618140d118a401c0e403a1420000e082140d8201030a00b804002d81c00081d80050400c52584113601849003005890041400c2c4800300d01a50240c10000d101044144038141810010344003040016180380600c600503603c960071900c031704450b240410a8054891090942400703001e0113840e00c80446415410310b07901280320401c0e03240124082c840242c480070710b03440381d100d2a500480d40080038507002e46c1c0003460343d0208810a17150190300030700b03242207186030341400d042032412507940304000c0215640b03441013207000703181d00d035050811700e0740f0351200c150702c0300d403c1c03001c0c11120707044c01e0405140050007401012403900182c041c24a09005 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 841671762 1250 841670512 841670521
    0x304020915032d0a120801060203070b0c0724021b1b1002030d18030905030313052101110c0c09040302030409022a0705030c0303040e0a0b010207030503030903070b0f 73
    0x100380c89004001c0c080020b001074070201d05a080194030616192040d2213440340050034064940000b0307443c080c060321020a2a40c0b9603904a8a81c810032001403c001c00d05008900b41c41c102400074450503028040c0150b0807400a1070a60504d40300031311850605801090103d1080044840c03a4446c0c1e0a0400504070911351131510808100b40c241294440d6a0741c5c90072840e818000d000316401d402110030200101c80900880d4202c01100c1e0400b600001c1c12184c003c00c6c02d0031f001089450744848130b40c0494400b0b18000030800400700c5004140250f20b4251190130000c90309000d224104881050030a860b0041070100760f151030300140807a4807580c03a460a01000c250003008036410358260400159981d090300c203420000000c400d8140d10100002200700380413801c046030351415a0401c40549281281c0307a010076980b40654004c800c0360a00a01c046135200b251540304c565000e506005440300103541c0e40f1002c0c219003040708c1c003418036000002c100c010415549031071a4409903080002446041 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 841673012 1250 841671762 841671769
    0x120c1106060d08120a060f171e070b2704020a0815030a02100804030305013006061a0424050f090a0f080f0c030102070f0b04080d050a020304020915 65
    0x1024008078056801481001c05200d220001c9407135158000c2512020342c01c11440860041072244101018040300e21008510104038060038100040d41a00604861894004640802070120a5202240b20340d2078002a006800d8020b1b00117088140d408400304030041c0300614201d041c2d240f805100ba0f01c100002d41000b900f00a105401036000b010640c100140c0d10080b03850030310700a1000e0b40c080101420031585aa201d011680705d60b100360b50a102c00c1e6a9200740760034000c80380c500c5250108038076140503210880e540d20061240d0003102d0214a09a0f611580b81c5180304018040c03c011740002414000034009094142c0142c013040007104d41805044030092007400f031085101d40d4214005040c2600355200c000003009483d080d60003414031542c07020f8481c1d0316504c000c482490703402401c1c240c682c1d0f460b061080c1c5800340e41140403035440c003c10f680e0308801d0010003041150b011400b40b0150711000307070a00c0344520810a0481c0180e49091a0041040c00301e4011f14201c00b50040200701d48a548 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 841674262 1250 841673012 841673023
    0x8010b0406060203220801090f02190e060607020d0b010e040203070f050d0f050a061a10020105060a0b1e0a0f08061c060c11060f010f12050607050f0408010c120c11 72
    0x910b4400000c603e0340180c9501c20081e51640c0c4082d00c0c6d5030038019007806101c00382c0c0e003800e4210300c200d840441501034000801c80c002918420f03680220106400210b541c2061b40050075450310003484424182016510148160300c05c8e000b004000901c00200400c5003000c201d642c000e020140d6209814510305400140d8910070b02d000100080c080c60308420420104100203041d4940c400c03005e002c4070000d030180f01035903000d41000c3c0d40706850003100ca060150040c880d59005400180403000740341d08001d80e60a40741e210050b98503070000500008003400300603802805010b9442d41c1c0b4001000180d0034010070740c02010309641d1150742d515448030320081c0c800005100b16903006601080a06800e10181c800c0720308071421039184c2c051079041241070f010303c42049060350b0f80c1c510401011a110281c00201c008031b24030081c41607220801140d4540d00420140408554442d001c529142c1c0f580720a03404d48041380660000300c2c03c0ba8040c00000051406407841c2243c1501e0300f44031628040e0203282e078a4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 841675512 1250 841674262 841674277
    0x60607120f0507081206010306050a03031b0219060c171602010e03120a0c0b0a050412050d060314010f141009050402030705090117120909072609030408010b0406060203 74
    0x20010070300310208180220261025590003107101c648881ca008209074491008442150009180c0302021643d07140456240007a1794043d550f800161100c9030340c105d042c1000503000c0c0e074402d02204400c4100c00303030110803001502d441c2c0c0e2003403a48080d5190003024801920010710307400c0428000c4c00205807911449104542c1c0920709100640c3c03000011900780421042d001e010001c00241f40c8210710340104c001f1240301e00c14107030306441e03540310000070048440617500140841400340040300054810806002c400c50750a000140342c580d40d6450340395000c500740c140d5070746946524449000701c001b40704060b0035031240340940d511841d00c80c80d0854010528029078680720ba0b901c000c10155101002202c01429024001708125611100c409500b00c40c0c90079003180034401c80c4001802c0d01842d00a071030a200010b840144607032203a0106075201106480e40005c07014002da00402207801c90400302e801080c458001d169a81d042c02640317420344a0100345103000784d040c1402000150307400011038442 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 841676762 1250 841675512 841675517
    0x30c0206010e0f073623061b1b180606040b0a030213061106010609120b090309031606110a0206030103062a0201020a030b1207030b070507050703060e0606060712 71
    0x40d0381d04c0c108240d0f00d4030b900e000066103000000381e40701281c01e5030503c403040d46600300d0041c000350380d5244200b02c3c211401030050038181c6001307a10390300941400782c05004e08040303401540c1b0008207090147c525141c060151403000b1040b002c00d000044c20400c1c5180301c0407004440e40d80d403a00e04035002c9200b5224030320900402039030002e2601d10103403203070b415658008030010b44c50b001266203003401020382030b002d0001c2540d03000704000003441c3d5015407061001c0b200603d44038410407003141c840b2a05410010920840c0d070008002034003c0750747c2400000c02165060000c010181c0c00c0903402000441d07858414030141e84615424000340e035445041d24110b941c031007008100c00c00384019410745965490b03d01044c0300060b18001c18841d8040d0083d100386d900310703038040112142d48ca0401c02000e0110b28240c074543c124000500208454400c990790080d001d0a103103241440c96980c9501e011002d0f8411b40300c00703a0307a4a02071070740d01d01400000d42210f4111100b50900b01540c07030703000c191011b185180c0d09 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 841678012 1250 841676762 841676791
    0x1d0f0601050c030421050106080313150309060c11060a06140d0507120f0506070f050712090b071401050c032e0b07050d0e10020a02061e030103030f030c0206010e 71
    0x6940100b00100c40203812503010075030448031700c1e100d08650401e0120040304c055080c0500411501000010740d0403012409440d494014644122518080400c2d0482c8003050340300c01e44603000c112035001d84005000181d64041c0001d80c5801c505041803000b801d204e41541c1001800c004180c5440c0300e100d102901100c64280070130161804c24605642c81d880341e0f0304440c600304440140880d4a6820b0085801041540c071583d5940d0001c56400f0281001d03000494000d110700004190312102c1c0281481d0681420a46d458a070014000a43c10002003241d071001e8048400c446043c080c050207400c5160009139a045d8201088080e510440c44a00c2c1110001aa02c595000c000c1c2c142c0000020b184840c0026915883c0e414500d0b140c660075108803001c06c6034000c90242c03604002d00e000801c25441d1b07002c1c0403607003002e81c01c02c0210351010030080000d03079039200c620511100400c011402107109413903175621f441100034080c0550b02441100b00554005000401900c900d807030501d540710030300798102c11 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 841679262 1250 841678012 841678027
    0x406050a1d01200712030c1a0c03010612060509010b04030c08010903050405120c1e0405060d031d030124061b080306060724051902040b2506050f011d0f060105 70
    0x103240050b26405000d0114561540800385600440d0b03201c803c60040c1450001020723032a03100200540140d80c00f1003200744c2080100005803083c20035444004c0a10404603045070b5170b0002901003002038000303a0030410000b9040040010f04c12a541c01404060000d00c41c180040e02c001d02240103034410607010300d0510010740d0211009100013241000010010900d0702e2030401c405d100112000f82c018000c61920002c100d0f07030b01d0100c0c2c80880c000d0341507036002d044030b030a56080c6000900401d0815010340d20307803000000781d00c08041124440a15880820301c05850074000905402c40c09030ba422090310a22072180202d64a1001c0301e07407010003511081c4e51481180303069900c680c80140e58510f100020300f01041c00c5c3c90f16400480c00b80c0440c41d100c02048014003101400c078800c85c802e0020002040001c500c0601284002741031540e0302414008445e043c1d40c4901c1d09a600480314581150003074001444106128207210303131000045c100744110391904035035864001c0d00190481f41030050116540 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 841680512 1250 841679262 841679327
    0x91b1a161505011212032a020a1a150a0b0f1c0203090109060b0111100c11100f0c030e0c01121b0302040302031506030703030e0301020f0406050a1d01 66
    0x5074004411640200110740c0d6900780711540380a1030f0b0044400f90139503255003070014800c0c02001000c883c42004030000c0340042c003294040c036030850815002c0d27001d01c811080101d19a0741100c1303d051188a11842103280c902a90904088110600c0d4800c0401c00b40a2060500b603c05855100b0f5900055594400c1c00050610000458400800304c1c1c81c000002c12004000c1900301c0106141314400034030130b4803c030703800545100196180441c02035010203013400b40c404050700314128110950030044100e41d16000e40b14142014000702403c441e40f9031101c44000c840b10301c2a40b08600707840c5820482c407617850b0000c40d12070b00c03031481d51030400c03080041280100041d43e00141340c034101d00c92415410228100c0160103500544420391084c0600100107c200d10603041703081c442d03035005000d40f80203811a6420f0303c2d841c1e41d000d0402d80665080c000e071402d4001100080025103140c1d2112a240c200e028001804080703241c04601c0c40201d810010701040c0d800004d41c811508071200c1ca80888040300000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 841681762 1250 841680512 841680533
    0x8041b0303231303080a030c0509010e06030a02040509040b0403020d05090604140a36060b04060c062c19050606060a0509130501051302040602030909061201091b1a16 73
    0x704001540300f0500200f00314403400101003102d01038909205c860b40c5140c0541d100d000b104c40e40b501080500038030009501e0910000c41c2e010030b0384200141466210310108a00440c100c2d01118021113003010300082c550100140d40c41200c5901e441e92a2803840700106081d0700030740c80391941c41e8881c8203007511260703104040703080a00300041c00e9410321050f2400c0b08004940001252421039040e14254802000d5800b425050303a000141c0f01c1d1405160400480d001401007030140c5e1100d41c0c8a0049604004e00c40030410a2440303009a18000b0310000e42190a0100001c0c400d8003507104941404002070000c145603a100380211065a100d481d01d4100303844900c101d04030075620a0380b42401d0300800a0f540d00140c141da034142e0b90388000c921100005c1e000c0784107900508016034818010780c40140f60036641e81c0d81c4880007a02c0d4a83d411000da80c098291515520200c0706504640c048651550150305c4c80b00003440041c100c558140ba4118120501d81314212507030755a40c58180c0c1240c10300c18001c6a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 841683012 1250 841681762 841681777
    0x4080a11030a0510150b0915030912070f060b01020307030c021c020310020d050705130905040201112b02070f03080c010e060f07030b041b0305180d08041b030323 71
    0x2554400101000b0000003080300001c801d41c1d42101c801701280c03d1110409441400c000a0500a50300c403030b02d100c1c4485608000c00036007440c49080c9070f04052050712806003821610428a40a0300d03060381c07910300c0642d15104c0310703581194414025000440d42c00b118208200d50155842680609243d0115042005c15400a5010300c66803203040c00249096000380f0428446520401498585403000c80e0303c5d115082c00402081480c0f00305002c114165030003076030000e105040000030b040c945d0b02043d013001d84508030143c0184540d034950020840b0107081810300707003503407010305912810000d020505101d80d0001414980c80414000d500314030075400221441c01d8a02207454a20304402c00108a02d02240d0502c00241402054242d504083c0601301c4101544050200340a10300340c0c0c00c80080c040248035145c0c0e0558001c0304ca181290a0112842e102c5403561501c0305898a4140508502c502e40c1010461542ca40001c1020961100c5000d0800c80c0380b0011400b0300c440d4204864440c012401c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 841684262 1250 841683012 841683023
    0x7062640140601050102060108060f060a0906080102090a050103150e040809041401061b1a1b19030e0606060405010f02010e060f0106022b21020f030105130204080a11030a 75
    0x54010148141406207200c1c008040049404503a241c4c4012a00c80380e080c40343d00010383c014008500c80030050501d1550000c2c02504c0350300c249940f807010105035807640e0b116403401d035030028402c0c4050621446610261074207080600c00701e035214140480d050700611590500b02040c9010400b045a0b007001c90b08002c4009009002e01d006c0c071100d060781e00b082845108042103149604005490241031028003058100c01c040040112444d824401e1860003021100c5e01d82c11f2140d40c05640765040e01606c0c41c42d214802c1c442402a012001500700c4071103403000382c40f55004071700f001112781e01c034400c4409480d000e1030701030980380d12001c013a40584503903041d85506011303450030441c10000c8105e22a040f00c07e00c0c0d0840306e007070700b44031190542c440c15030301c071070020f40f40c03054403000440d02034044040c0c1504c43d0161416032052841e0501c049030465145031035010400401000780c3e24004228403402084128110b103010324080c0050340c0c8811142009104582200314056155002c0c010a4010794020 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 841685512 1250 841684262 841684381
    0x1909030309020a090203072316140a03030501080f03131217030103112106010506160c08010c17010815060d0f050604120903150f0b03070626 62
    0x3c0451300d0180d00100c524200058881000e803100503610249015480302d9014502d1a08604c081001c0d401c0d079100009582c5006000090328681200300301c030703860250080c0c1e8000356550500d00b802d4100342860084800c103500c24440b05611803103000890707007150105080755501c5c40852404145038180b441208180c84404000082800b62110180794040012140d905a04000c4150745410003e07a0325410420b40c0a1401071001c0d00b0300c440205107158000312600d0002d036050341e80640c084501c2c0c02c07078021651510511442d480d000b8188012101420441581c6981000141c50b641d48849120484910311100440d40a4903801c0154007540d4200d600e00c0519030b903078142075a03120402c0c4c40031111340500001c4240f015104100d82010f40c0d0380301c42c2618074464800f102401802420425240d031030340d03d11888555541c00c00c0000c0017810b454031498a50402d0f6040b0107009266900b540320400c51203001c0002120703818940c480313035a0b0100800741c43d850320f40009951030089403000404041c6007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 841686762 1250 841685512 841685519
    0x40302061c0e100b03010c0c0816081606151a03070507021c060506241b0118030f080c0901090612060b1b010e0d170403020c06070303050118051909030309020a 70
    0x950030800c4c0482041d0000d0207a0003290400b102d045e42c00030005031412009001700b51110b405002400c0c0d0b4940a004080d0520041240090100050407002c4504a5903040404985880c41139041d0040a0780030b141d980740d01c1006030003a03951100030021000c12800150321402c560329102c0807817465007103020449400d040b038034008008150030f07540765100707101141d0000c3c940f40f960f009031040d01d210340540c0740c2030a6919805241034103019285a18a5480d290040b040c5043c0081c3c04d41210700a40d614494450040800341c0781800c00381036903201c400c1c10004060349907008030240c422512030340740c03044030000300011202c02130009400034a07a07010002146a2402d4000465a041c9100307400200100d11401101c6030352145108015008035a00340e031205064180202d1841c3c1c01802401901c1040c841800082e81d141c0c00918100c0c0030903680c400521444204284c0051030300030120041090b8141001c1d485030a04142a281c1d11558480307000310304152007904284121940600503044403071703c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 841688012 1250 841686762 841686793
    0x14060919020d022a280b071e1115070302120709090617070603020c330a0b010e06030a0b0603130210090e060d08040302100903050c010203040302061c0e 67
    0x4440c0100040e1809503c000c001350780b4000355000c0d414070001030506109400d038490710040d01c244a2aa8400c031004a40003107402d00c50841d01c2410903a07074060000c01600e4040d414850308101003400c0004070399400380401c0d0001a40b209082075510210541d582e0401d04801a01c16554540c8083c45444240072806412458079010755a040c0c10074800e140e20348082840c9800c0c980e1854100c0d601c5400e003042070314042e0313005110540b0b1040686150305440c011101482e06160b10424480c1d07501603911400b0205a80b48941114115038140711071078901e8002003d0350f00400c509807280a00102140c00040b00d03611050f00b80b6400380c11152680b0f0600c0f00c40c0705464004105034080c01c500385c40560205e214500b1b0038262140ca11010b50b10740c45400c00c2c07100070201d46c94104c840c01010000400540e0360f00000e48031903aa00d03500c502b00345013507107030031030900010625240c1598010b00003400180c0d5880f05403080e030840201c0d07802169030302aa604c809440019034000ca640a8805c0c19008450b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 841689262 1250 841688012 841688017
    0x615081e0c0f0d14130c05040c091203050702091e040320070f080609010606082409013809010809160303050c070f03020a03031b06060b09030c0414060919020d02 71
    0x40411361855031300c2d940544000c0c9080070000740f800360f0800040c08145070a40c001d00c000c1b4058034205c000360f034482040e00200c0b0203020741940440c1c4042200b208500c0c085444a43c00b0354001059805480d402d0365040000802400040c00e200015800507a55413070f40c1220030325044607a040b500b001d5503030f400c860244001c6008a0105005020004000b1076050040404450070366540341f00715a900100d00100100364021342c100c5108950340c0c0d0381d80e0355461401a01921382d140c0011f500c1c0400d64050301141c44400d856000040780710060070102c200d41c0301900d08500f02030a14100d160f6440b0f0790641800764201c4900a10540122f02100341584900034199040d00304040b62100c1d6281c1c801a8091003041c84002c0d0302c00726a003414000a44646602c114829004100345c0303c10890f0b984003005d407002500401a040004598006a4a800c110401c1050b00544d01004030010851803c0400ea800410300741c010405c010200d0710030441e1004000642800701d40854485500c840114040e6 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 841690512 1250 841689262 841689281
    0xc082212051206030a030801060f0302070803070e121513111509031b03030a0c1e030e030d140405060f0705010f0506100809070905070504180615081e0c0f0d 69
    0x410b650002401800c001602083e0180c068640000b1a8a007003001c8580e260b000b0080740400d60240300d100006500000694010b41223170311034807078030b00901c4140b090444111800b014207a012132422000412824821508950000c0d11248200c8242c2404030030081c80c560041d0f0400c04a0f03480713030100700200018103e03140c0300301d00781c40707000940750804203c108074036010f0780d803540041102900300ca01034140550018424848400000d407102048100d1900c10724084d804503154070421034046c5401e0180d03004440d42401c0a00000801e15141d07521805180200d50241000003010032504017000705582e0284c1c1d200d002800f2a10318500c245c0042c0c0020b8030381074060807004900c28a49806881d4440c45400341e0030007820b40c039141c40204400b03441c02821810501604020104402c04540500703006100305000100340603203400810010410340d141510b00304607110040c00380ca00040d20000b64140d1002088004948942c401c80041c1d100e681008080103100144086000e0120380100d4107030f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 841691762 1250 841690512 841690537
    0x12030a0501031109070806060307200d080c040e0c0c280b060f030c0d110d080c07050d05031b15150406050916140d02040806190c08221205 61
    0x903c070190051240c4003009035400d0380032411007000903495003800c00165620105514055842210203040c0c1400516407441c5900c86401c800550402c50303030008003440d002030f050036000d8039180c901400d89031080c202502a44248000203116180008200040b41d11180c8601502e0707440507900004c0d040d90f4070b01307001c11601a02e00ca800280e072032514503016110058050091311311510080c2c208504410340560032a00004242c003000c0d01c90304c912008040b040d100320082c035580c02140c1c44040c41c18845900c03180c400e030074071070754540011004015030341101040c01c044885074151810796402c0c83c1c0042484484101008100000300d407521010782e5640c0c170140c800b001003503228801e00c000c0c0003080b00d420030003486111030044024800c9030180749000004c5040c0b410200c0c030710f400e02c0690340160b02c168032551100c01440304264010b04044104a0202c0f020013081807400405818024010860b950b03154034008465410046454100c62480c1e0001544070a80205000500141c002e80c154410 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 841693012 1250 841691762 841691783
    0x303100807050108060d08030a140108010b040612020f0108040804091b03051e060d080706050403053127090303020a020d210e12040807061106072012030a050103 71
    0xb019401078120034050b8601400705410948551501e003541e87c005440003918a81c0d8546001080d20403036101c601030001c1c0000072801d00600b034201300580d0b80c0d54011000d55007070340d42403000607660081e401044200c2803c20403560b80d25418501928003990f4403505201c1c3c1003400d425966400c42e40c03655078800842d1000c002d0ba48896064007910085d00f070b41c3c001112020700115489182000e00f2440d61440340c16040d240405030364444043d40c000b55002c03404142c02080d1200603190340c1403100440c2403d60300c0ca400605284002043d00035685c45042c505804600002d851040c4148a4140500741208280404489464010000d510220350000107018640091006034400c0200102103040d000c0007402291030340889800802d85e4141081c1c04d0704c541080d1070b00300300d0301d0710160004080c0a8040c0cd509072401c1740160080789208035200003600b04408200d1600d07000030b44003003007022420301c101d02003525504091070042d8007031a00c19401c07408010000c0002c05034104a0680e44514596603 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 841694262 1250 841693012 841693019
    0x11404060e06060d080d0b04140a060e09280f140d03020f0708030601020316060209010e010e0102060f060109081e0c06070c03080a05120a09050c0913030c140303100807 74
    0x15112801500c8042c1d0104d142c20801000c03941c401d000d400d1160965400003031400c03000700001c0445100e184c611880c0e085050130000710080900c44e1500800160241e2800c0d4500400e8441c2c07285010510040910313110380480c903000c3c4003a081102c500e9402884092000307640e0505403200d64900314010024810a00d120000610a009990024000001039410712170196a0035020350030081082d411444140416000c5a003408010100c481c02401300681e50104100010300c111004400c00f0f040c843d040d19042c40c280d82c00a001580511142c078110010b450792801200c00c40c1d0340740e020403030601c80c40c00d0203c3c0d400b182c40c00314101940c0340300403520f44c0141c9406000d464091501e0191a00091035010008030b80540001c000107681480e242d440c00302d80191b44001740e001603820100d0181c0e5424182c2c10044200690445a9400c456940c6e0902e00842580b10b010484000101001025100e22041100640300000b00032030301c10a5a4072858031011003400760703241d0700c0740417590700ca91039000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 841695512 1250 841694262 841694291
    0x150503091e030910020721050c030106181505090a050403030605120706020f070806180115120203150124030b030f06071209030503130f020904120e0a0b160f0501140406 74
    0x1d41c11210064043c007c08040c25002c4041010103200c03e80d068002d6001150041d0790a01c52400136240e01c04101198010014485040350b4030124545003502480000344056980c03510102c3e8000050034010400d44c2d51341c0b4044000e4403156219a4006200c4401ca850780403010648005958007542294081c006070070000f40e0f2180e251090f0b0f00107400c0100803610060b143c50001c01361064802c000300d90744088540eaa682d40c4840d40c040000a2805618481103180c00c2c007600c5010702d469010500700b5410001d00364255030211020082402c516a0581400c501030707000703000034000080070380c3e00301c0c40c1d80b00c4110703100c0700300712520800214a18a60104008144140c0d1220b03509a900d00b401c40c0e03a5624a0880f503080741106880c1000164128001a600e00c01014452403080e130b2000c1c0036070030591010b01001d078000c03d828801c1004140a02c00201d851080d6120314020032424401d400403424850f003024544500500fa55081244000284682100150280b48a2002080328441c244580c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 841696762 1250 841695512 841695523
    0x7030c05040f02041809031815080c090f040b04090c0b070201020106080a0308071b12030c09080106080a0f080712030605090f0f0f044404150503091e03091002 70
    0x85c603501e0346807049405000e10f45607110916161190a280d05500e80c101c0d10a03d501d0302a910904160b00d1003030b58110703100c0e03001c000d00c1d41000355021403500f0030741041c0c0081e0180c401030a90300d018070340d9411401c003155580d802891a4075000241900d000340c070760036032016a0380b10030026070241d800d084001440c0c04001501c01c9500360140c1c7c1c2e81403651185802212084840b0365800e0464030405d5004001c6002c4d1140c1000c0d01000c0d40700040c2415604001400303030300803584200900c2e45818002c00040a0101c0c0700c518459102c0701d0444112038a140c201410700a06202801034220002401c01d415015400907041c1c810442d4110010f80d5150404c25120360200c0e144040001d0810100c4c819100120f103087e005803040e15164605600c0091b6400344e081402102e407403c1c401c0050112546151f85024100540b00110360752801e4209501003046600b0790b42c4003002c0040000001d0182c0d002032210322182562868088290341c0406134465076a004900c000e40b06407a800703100c140c141c0c00000c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 841698012 1250 841696762 841696769
    0xc0109030f08070c0e240a06020a08090a080f0d08010504150e1302040507030c08090a0506010b03150a0b0403020414190c26010812030f0103081b07030c05040f0204 72
    0x10844002400340d894281c41d0700210700441c0c040c020110040f03100304d02821498800e502242c086c0200e41414407180e0710a201c065201c2c0d000b12a2001c051000b240e0105c0d40c00c94054102458544c0c031203d5002007485820983d1103000c550081021143d8128004502c00c081d51115541d200d20b6030340c80341e00300f008455400b40010a00c400c810000c204000b1441410b0f035220a00c00b40141104107a50041400c1d950215a8800003a0ba01c80514020380c0c2c001c64000d80051030007004004024030303599056600c1c04180151010f1450100001b41c210507020030003404200080c1800f43c240c1d0f03072400456440e402c51301007240316504100d5880304203a81000c00320f2003071403100414100300401c05405e10080820308901d60401110300b900c01c04108144034041481252034400480941c580b501080c00d00e00c254000a40031403040080c8440300900340718890540307800c480e940d5070303805c4503e6010860011900c8890086c2c002d115001050000601444044030b0003a50280500003010048504a102e03600 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 841699262 1250 841698012 841698023
    0x160b01080d020f120714030706060b0309151314031306050324130513080403050c010206180d0f0903120c051b01050d110c0316120306051f09090c050c0c010903 70
    0x1703101088159501030a1005801300b030340d00e01191078445200ba1448c07500207482006c030000078024200d0342001103070080401209017000c10700b0314000d00001d110440138050045410030000e0b00c144c50f424001c84140e06480c180c1d01d0502c0e40d940e140a0410b80040354580c00254031009103c1428284201801c01200014088030600c102c00b82d000000300409480d94654412201c9202d00160700d020041c005103006200800811b409213000915081d002061a0390780d00b4503170300a80ea10000000c850070300b440c1303a0400754050061710500b00e038245d00c994406000c64084282c060301050300601c0c10010913029400350b605080d00142010810074688080d21f00164040284075030190169104003004440e0a50543c81c0c03503800d80b00a85542c110213100c000040604001400b0010032a01c2c0c3c0800c141c0390b05050001074640000654181448485404001c3d0012484a921449000798a0142c00005810002c4240c0104000c002e5001041c000f031091040d801000f040d5070141e004002120b0380304 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 841700512 1250 841699262 841699267
    0xc050702012102040906090b090a02160809060906120702150106021b0303121e0906040213050601120c261501110a020901030b0603010518030906160b01080d020f12 72
    0x74400320a034148992520b180140d030a10000c54021110b00801c0000e060090000c00c0075000c070820850f00003006041c41121510420000b022400f00b0542c1000940c0c011100c9510341002001056291080702c050703542c000b20000d4030700c52400d1301c940c410f40036203202d0b400c1300c51605071070072118104c86c420b0245102580c4030f1501e0795a0802c00d6442d0703880101c006400d413420303c040d004006000300c0d402e480e030310714903026120300c0040100c50300c407800d5029654500600b203c3c10990003050002d03d450103d894419100d030006521640110140d0b10401010b003070410424007a40001030105608a00031003c506c1106e03000303024070300c3c150009800b402c4515001070301d100c0990b0066404000b40d194442c1d8600640e115080503940b180c01c0b1034001c6005010400340c1d0310344803082600311200101041038004a0702085560b6840000566580400580c0d1080e52088410402240410401c000420060300d0100110348000c1c08104950304082c15000c90303400070180c0d5442500c0d44201d480149680406 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 841701762 1250 841700512 841700537
    0xc080d031505150c0f061602071203082a0406140403050601060f0c06020d2a020a03030e030c0a05031323060d021c06080d020c130506030c0904060c030c05070201 71
    0x1010301c8200d0714000308620351a0045400040741442100c0c2e0170004240c009904020003241103008101200e0b2a23403020300303001e80c180501d1a0406103505805030403c58503400203441150400c2060301d10750070f489041501c5684482000b80070343c0c010302420002404000c1540d0044010206481c01c0d84d034080042c095603030a00d80211204c80c8102d0000c07003008031401020000c200d41e0b01c0100607110301c2c1c1e0f101251440c07420703038190303114807891400612080d10420f10748141039002c1001c09aa03a414074000c00d8504c1d2081d401491070240010141850090744030039401c0000002c0240040c140d42491080800d80d1420703d400d050400c844403034120b1550007000c10035480c22200610303100a00000043c01c000488803004640120505821481035803460184a44081040784a280403c02e10003040480b002501042000955001c080c0007540c5450104009030703018440300c164100060090705040c90301d0f0a00001070401642c1510104c1d2a0100c1030344418400d404803903482d6010b844000040c0b41 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 841703012 1250 841701762 841701769
    0x160b01060f092315030430170a150626090303010306111204032712060e010e160f0f050d030f0903120201140f01062a0b040c080d031505 60
    0x83c03003951140a411000c00380c442c0010140d03025502904030a4014012401c0c0d044010001415903440084250310040076a07602c0003421005011006541000e6152011990090a0b2118560310403d0444030085031442d40039880000040d41c0b01c56100b8900e40184c40c80c4140202550144040d800420050021031745a8021080050201081c42d18000500007621070102040e14218006019140201d810014601c000c0030711644800380a1040c51410081e40c04404000350001d052540700c02c41e01d07071005402c0d40305060159104c1d0a070741d895010307041080d1190210740903844079a68804c80101c0c000b00841c405000b5070384050200c484086041e1001d1310641c9504030a04c0130803032805000b10020300c85481803800199140c002080c0d07451148540010b6003c0246000c80070b4041100404c43d19900c4600e040e035000d581e80000d00c107043e000b01e01c505a0780d0700b01800307802e03050302038140001c00c00203000c11002c440200003a140003d4a0b010220f040d01e05078030701070754044c929041c148690b29 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 841704262 1250 841703012 841703069
    0x506040e1611150103030e01111905070305100e0708010b01020a0b0402030c0d080d060608040b0402010c1e05100f0902090105091003021203070302010b0d0807060c05160b01060f09 79
    0xc2609284090b054030300180c518000103480d0b21a40c064030741004108140d0000501c000441d0b090030300c000d0f042140345200c1d036112404a044d4191201c041154400d00034244004005550004203460341709070000e0240c030140c032070798042c014544900d2400040296061180d000f0f842d105034041c203000142d070380b1060700d09407001d0410390303041c001d1a404114990315102c001e020244540d10311a11001006104402c45085500c0b2205220000040000181204d0000f540c400d034242040e08180d6041c0c109031082c000c100080e84104035903404150280301d800902c2e00340c011420b0005120385485c00020f0001d448aa120094000130369030014440751409400965101d2208108a9882556500020242c90255071101e485410024404052503420300401c0d160307103001d541c8803100501c25551011b05208002028103401ea58454040b0041e12036011607003a102d0350030071425a2121070900c084642001c0c4038030801b0502c03003404015820b0044000f403040790484050b240341414900215101c84 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 841705512 1250 841704262 841704301
    0x2e03061a0306071d0a150905120703020622031e0b1008030a0e19140907110d0c06092907110c0405040c0b19030b01030207150e0f10020a090506040e 65
    0x10f0740c5e0b80c3c0003003440982d600d082c1055100d6950ba80c2c001e5840c100034004495400000c000300c5812000090000d80c4506044480700d0540d00c4001034040320400c0104920705054100034011800b00701e034410030f0034180340d0014484c0d0044603071118075103c486c00f405a034007041c418108540c00a002815900d405008894a0400050b11040743d07041042180881120250000c0b40245038034408420241042406217034040340c0d0b81001d001031003820040a03950369100c0d0032079080017440701e4490204a4039070042d0082585c40303a0382000049030103813a0f0318001458800111010312440c005aa924441e080e4107800f5200360f4098072450b080e0809100107060010010348800b07806130000030701a20300b0801882c41c40e540c180f40406848201030000c0541308a004030504150040c030a880102d0f007200500a910500c640b00007407a8207404201c01c0c10301d80841000c15441c0907524003210045070a400030440942d01e56968206552903070100001c42c0030301c1c0261b016a14103d000598048412109507088 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 841706762 1250 841705512 841705519
    0xf02041a09030f010f450606030b0a020c010c0c08191707020c12011e020702030c0904080d060e090a17040801020c160b122e03061a0306071d 62
    0x1032034900e0f8400d094540c0038009802d0541d807081d00018180c0000558010170f0112800b4407060b943e0070f075018519846010600350241d603051980d0003044011791100e001103500c020481c81ca1b141c1501340c00c2c000d400c9940302e20429424007002011452054025046050b40000c4050400710400d480c0c88404082c01c0800048c061540500c00d421401c02c01c00c1881445968000c080040d2101d003070004800c254294024140e041400c81040300d2000d07103017010300c03c1c1d00e842d0042e00e0f4105800000c1c60014800f4010350880c00300e0f020b010600c40300d80c00600748140c92040c11b110031036407090a10070101d401c0380e0303601581d000b1991400020745400016110f10904210003070034140c0341c01d00700d422a0720151440003540d01c128001601c3c0c101d00c0d0b811500030008892120300f869118010410604401041070508600d1546010241c05030076500309100307100d1424601550b52246891001080340610000301c440d000c80c003482292900081c0d180c03090b1071540d5030200c204a4004016580341c49104003c0d030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 841708012 1250 841706762 841706773
    0x1e0b070813140f1e0601090f140403080f0114010804020d0c0b0d051e04080912070b1204060b030604021e01021c12060503120901050d0905150a0f02041a0903 69
    0x22840b102c40070050995110040c1c03490703000031003140e40340001010300c00c41d0280c800454075801c40d40100b0750750b0464a4a00c00410340100410302da000a151f0044115041c4100c3c0c001e000926912407c000c0c49820540c02119183e40c07581044500700b11810082030000b14410000340060810050b4180700e24421001c42c6e80f00c60300c07807a044400d600300500f0252810740e2001041200b0703041e2407000e2580e050a18001c001800d164903145598880d42d83c14038060b65440000040b2801300700000da00810585051503201c00354980b810142020a0300c0a0314400e0604000702c4440c580403451901a0b50300400080010013000c0b40245900842002c2506500604a0150070403580852000d102c4c801075640c005050030703012051003100e8a0340c03c018029032020344005503140a003000c981c80d02409080040c1c65000c40404136014081400c0d004101d401aa0302c01405a0b4078521140c1c010280c184051140c10b100c07120050890045100b4010f4106e0b41d0070500780607021000007001c09110141c03c2d80e0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 841709262 1250 841708012 841708051
    0x516060903020607031401030f06020a18080a020f0f090105100e03011803030507020a02030318030f0f010c0f05090906010e040912080702071d06150c060906041e0b0708 74
    0x844031100c40950168002d2820412603039070500c20303500c8034141da40c0708000030350440c1c43d05000d41e200020b0041100781c0c00a01120620b00070002e10000b50020b1001003216a21070400c0b540341c10b42104120b000b40041e201c1a076045ca05410886403d41380035000300402da103080100020669460101d50a10000da000b80d40b2a0700c0138000c07090507a05000002c519881c040c54024200d03200240310300115000b07610100010398000c41103540646551060210341409903000900f0481a2001852030380f06015080120101c10740040420041c585c5070114003001c2c030481698940301c0d842e0750310b80c00b01026001460341c0d802840c0107070740414090000500e4440c1c3c2e0b5260200100f1340d6019401103000c020400610030703810043c46021740f580040c2500c80c0c3d41e0711020055140806003043c1d01c120b1584881d600032510120a9440d4525800c2c02c03200c081c20038400d80d42d19103a003238800b5a0030348400c20885000c0c08a5085200c030095000324000c08590b24a0000c03600e0400283c01c1c82c4840d5044500308 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 841710512 1250 841709262 841709273
    0x40209150f070c080319180806090f0c03060c0412061e0b28030b070516210906080a1a03010c020606040b091b0a030219030209031b03030a0516 63
    0x4090341c0c0112680c10755070741c81c503082200803561140d002ca030740c60f84108040b00480c1041074030714030000c0150a00c0a04504a00100b46a840880e00701c00c3c2107204040410190007000155042e00c1e0b0584815034a00d0b40417081030680380d0404643c802c843c42e008000411180200714400c124540c01900c000441c0341045200280794080302c1040078041c6d4407040151118500040b02d2004a9680c3c9407010308403446150300010360200d480058002ca0025000644503805181154559044d02c4000899804189010f4a502e15900c1040d09414015460700280b18080c016890a58030b403030f1030b65000c5603203d0780d24802505104c0540310700382d2a1502c0603002514240910f05032904076801409462030158180720440e04400081442003400c4010702c88042c00c3c403045400700b4011008615950b000c220000d5001e481070100340028904180501c2901a0781030b03014200700308080b010750350710148a041c2c20400c1e03903a05130500e5158008015042c4410301890061180700d000c400c5d0440402c02c0d40d00d40 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 841711762 1250 841710512 841710517
    0x150904050c09061c020904061103070207060206010f0e0a1805030c10050604090b0402060304051504030c12090308180a05040203010306051f1a031509070f021005060d0204020915 78
    0x11202a4826011281540b4216500581c0401d0039522075101d40c141d01481200d4040d280d0029001d1350003100481d0900c071403904001c409a030301000c01941c0f8200940300954075545880b035a40140600000030030f504100b404a081102d080c2d0101c01c1d0191100f044000040446a45a40201e03440601c0b04000910600250805802103805030a920020310043d50a650004000500c03403842c1642400000300c8035918260800d8041d2070143c3c60b562985003041c07404020840050503200701d4030402c020194810900c1d00c10f90700c1802c4428006c110701038159500d0f83c003800001d0090000384143d00e25140460714071070b603440c0e006200a00c05c69545020808076403086e0410340c1c1c0315407580204000513401c0c0c001c0d030104041c1410703c25841403030026408030141e0b07009261031135643e000002c9508035080b240c00e00b000400040001d05035040411000d403250500041c800c0141c054425075004c444880d1046510941001c1c0c6640c2c040c0195601f0007001b03612410f8100d41c4822030071803e10099007074101 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 841713012 1250 841711762 841711771
    0x1401060305070207061107060c02011808030a170717191a03010c020a031b03050702030d110f030403020d0f0c0e0c03100b160f0c08010c0507140a1a1509 67
    0xd0008440c1003801c1c0003420081c0d1900b0440910042d0b8480307a414000008086048500900d0140c180001c9480100d481d540945e003030380a0383d55010341c04100320101200410b460320310703501d03089032050a05035521130b50300c0200d0b22140464403190340d10f807041e0315540600d40d01503e0400203c00d403840940d404c001f100c0000b40a2003485683d103a140270380342424441c0b40d0f4210300a00007001c0c81c120300e0350000d240194140d1120a0003002100e2201014002c8096600c4968002d090383c0000303d031324000401003200c2c4050310955201d48002e0742c010394ac02004840949802500d42d1007005d102e51110a41c8101c000811200610162000142ca01034000142c0c01280005001c50740e0781000f46c1880d0080f400b90300407125010f020401010313062035a090f0724036150381c4110040e013070034698140104c407100c46a00c40d403865400c012038460700c280e01100400d1418400c2c2d030480301d0311409846c00c583e211440c08004008100e03802006044180145245a21140b41c920103071230b034403281001c0f41101da0145d6 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 841714262 1250 841713012 841713017
    0x402160302030c0c0a05090703200c0d02060106050c10020702130606020607080703020f030105040f062312163305040e070e03061503070b0f030f01151d0301140106 72
    0x1241d94030200140241c138402001110005211800c0030000340c110f5802900080c01e050780d031802010850564060744814000380c0c2039640d20b402140c0e1816032198aa1441080140610300011540c10f0184041c2e0740e41101c04402801100102110100298002202a07034045014007502d03540f4980c500615003d05040d40c00b4041b90b06140c8809002a113018083c00142350040c04201d60340c5140c3d405036811504125000f00e00e800b11403242500030074040c0c1103112151070043c4204210220f604400f028207800341c5001c4140c800304140070341ca40c2c0540c4610098140580b204102c202d45001c401c00500c0303102140304070384d81100c24010b00103624507100b00340880d10100d020031220203048401c6500c11600d0401402c0709001d0310000c2c1c4c130b400004000c0038103281c9110100900f41c41c1000030501030032640301d200f0707a1491f0010382009180c0003144d0514042c2d401c04000302d0b40d50941038600d007094200ba2521900c0005803440c42c465414036001054040d940c41480c2110080076015060090a0310b4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 841715512 1250 841714262 841714267
    0x30906031e010e091b0f03160810060311192c1f060f090815090705030a030f0819021803190f020d06060f0801020a0306050a031a06040216030203 64
    0x1501c40340e44541e01640100c1000c01e60740c0030002000f8012906141285185848155040a640015826422000c081c98142c4190074000560110160120b0285c0f0000411a00d801310a035500700103444c802d001c0145040c400c1c0407010140d042200f0b004140c2035480721254001515490a5144200503540c0303882c60364104420b004500b606498456001012702c681061302c0100c41000640104080c491001006041c6007100c99444c4034002c00405480c000342a590405003000c41803142c6881554058014050041c00091500c0d00045000c850748d0f25440707054509007241c0055940c4000282a04603e50306400d540410300c00710310040401c1c5850031b155240742615501850700c0c000c00d2201891407011b0002d511404101d680c51001e01c00d503811940ba002009407032800602130056503128500c10f00d40050080b6100c030040d005088800b1450b582081b645030341c1c6040104104292102410041000b4001150500d00c4481140d0001000c0c201524201100188901e2402115003e80058201 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 841716762 1250 841715512 841715551
    0x31e0c170f0715320703150e010509010b0c1209010e040929100302040902040b04060602060403020d0e0112020d090c0609050901090204030809011b1a011701050c04120503090603 78
    0x10b2042524682c510f600500e29280d455030100071070030240318411001580c4c10f0002d80380074420340212181c50007a1684a2a86544140c0e1255400080c06101e00c24403c2d1000407803000004d0341900c0e1000a14001850485180881c0d0341165009440c0e640c1081022500ba1170305803200d0080c0d401081c4500c69902102520358660f4115018036103980481d1036100c014131a415520341c038460241da8041390f0000e4a150684005802072403c6c2440540142c1040340c0000d074107401003580c601c03c03070098003507501e030322803640c0e04075003a0748050941804600c15010340da20300021680507010100b016172000484c0c01645d1288021041d26901210014020400510850900000440c0100b070b00c81e105506103400c50780c900c2001c5c0078050243e410003510450b1100f102041c0403203551020740080c41c4500c5400c0a914600c00c0c042c0074004c814400480d85081ca0138841d0510071903106c4c101c03601802e42010b0610030140e41100e072a00054a40d4031090150342c801e903964400450003204c0c060070305011160b0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 841718012 1250 841716762 841716803
    0x10110604210c110103020a03020d050405071d06011b05030d06080304080c030708071707030b01090c030c0804261209030909010b04060905060a090e070903031e0c170f07 74
    0x4104048004011140350b07240001160030101154000e001d00b00583c0b240304068003100240140841c181d1803e08241c00c0c482441000715440f01a20314204141ca8511141e6007502c125160944805001070f04a054030004421107400d1a5001ca10a8083e2031801c10303a000c0e004161541d58100082e10b030000030303040141100822205e10024015405000c3d95407070701105ca81c94030864030800c40c40e0065158a055000d10910503070b006154891180d45580d611010090003c00b030b1610302002092600d0005901c203406a07074400e2096038414103003038075401c0d5040c032044100d055032000d1101500501c191400c41c00c44400311481003180c40c00440d04e451125040201702901a03101c5c03420444208014446268030174081c1d8140c5000b42c80d8203666000100341101d441d10142c0c081c400000b014400e000403d41d20402041c101c1e4000da0312058550941c504c0c1c01c615485100c0401c021440103001c1800040c42c0d09000e1026410b02050340303040c49004030755003005502100c1c3c116050852740820081030507 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 841719262 1250 841718012 841718063
    0xe0603150a0f06080c070812010603050a20090d1110110d03020c101104210605070306060c1b0806010303080f090303041a130c090209180702030910110604 68
    0x602e040c1000505403a05030060400d400107480d8500070000028040c1c03c0c000c2e04000c64200040712551030a146da5945030050040c20241d03200c048081c2010100c2114141416017103440b24500300f40c5a107444203440c10001180000d036000c49142166079040300150365030b10f030701c2800e51307659032100815290710814981c00c3c000c041008c03200349407040c081106240700009503c00b404000220010710345900c0e8010300b0302406943d002c10482811481c070b10040308028070400404500c252000c5c0029210f40310281c00b50b414a000f01e0001a0040605501060180103400540c44249440251894681c0700d414141300098106030045a0840b040c0f03d0115030b2079112070362000307484019600351f041c2641c564180c01e20b0302140c008440800000b1920001c11901101000307039004041b1080c0c20350710401507004e074005000d901c2c807840181464000205080405500c503510a6015500e03140b580c800b004000f41c038400c0083c0412030800c10705c4965200c100040340c059406000304000d10780001100e0f800d8031 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 841720512 1250 841719262 841719269
    0x61e031b03050c0d0f120c260f09060c071d01060e030a0803190608100f02070b060409081603080a060b12010b030703230405060105010c05031206010e0603150a 70
    0x144030007040800c0c400300e0045504a001c5403070440700c3d220340c2000300d40c1a0b91010301500d0030020310102c1805541002c1191120b03072041d101000c0d18041d03501c0e00486c0c0c148001c1c0d50045244200281c80042d060030b40184a0800e000700050300302400c40e01518602302450b008091200802000c0c01544e444400f010360042156242c080360303054a6001003a205c4400040c0200101300c00f00200c0d401e6103110109290002d6400d00030009550340305441d0303030340702155240841044d10f4601401d40340074144c000c60f5055500300c805404182c4440050000500c2911003d40300800c042c0f00404801c41c00444007401280030380d490060a040282c0000c0c210f68003603102c500194030821240c2c2140c0000d04032541110702d8103030015100d643d003807420340140194140303501d00c030961606030003002c5005054182c0554065400c0300d059a8035100103696030072079004042c066520500c1141c00024040086643c4454189001401c4000d80707800b0807415081a20702e10304070780140c2e5a100c40d9080402d10039004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 841721762 1250 841720512 841720553
    0x1050f060c1f14070207120606052709030c1207060213030305180406120308041103030f030f010b0705030414031f090b070e13050606070210050a0305090c0f13061e03 73
    0xf541028000a556509039101d42e104403510700e42da000502c000c0e5403046000703000181c00340260a118480803680d401194102c602a0344030300f0085246404000b060f1820241100000d01040e28414120355141d002084210b681d580c00300701c0114006100c00131134000b103209850b030a480748001c210041628444901c6140500e14011042200038101f60291a5064160901c0c1039142c4582c04c20b0814082c501c000c0607018400081d40b01d800c01c01e000021071141ea41160140c4070f9980b81c40864010b40306a0202400507030080c03200b03100c0c54003c000c2100038450002d089410742c401403070305050541d803d060001c0c03141d03944800721010b105c030900210794800041d1501e500481a0314000592156808590404c071565400000703002d41c686408603801c3c550002c00c2003000e20000c1c40700408a40c40030b608903001a0a01000c00c0c03c5010005005d10101c50040c040c401c8070506c01b042c44240c000d2244022040d50b01c03890001480c509100c0f05051080510038200c64480c1941010002d001083d40311205 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 841723012 1250 841721762 841721801
    0x6080f0c03010504030c1112190b06030d0504260601121416090905030c06040b0106140f040902090102190c06021509151305030c1605010c0b01050f060c1f 68
    0x86d8041c443c2d802c01a4031083d000100400000440c1d04483e4142001c10148a0156400700b0340c41c0400d0170305802840b40c1e44400701640c5c1e00c018141c40ba880e146180300881c10030301092000b10441101101244000100b1b0240d117a0080034491408200b84c0c80b80d1a00250f01070440148a1807401002d8100d00c018000c001c40484d00008034aa42914441d910001c1d5440c0c5401040040910880b1110340c0d2540072100c0d44d040c2418800d034003c0b028842c0b500032424152144044010410a41d4110348039686244d081030300d45840b550196014802e42411401601d0300401c0306003482044851060064440040203800c00d80064642282c070f11602c1001c88012040041c411030010381200f00700326102c06640c5030b45502d560b0010211455000030407600000c100f003c4484030001300d038a11952140c40c140c030f00031b40e1000155801c101010303019119000e80b030010310590810403a00b0040c0e501c0500100d152000450101d0f0804041c1e000c005035140e40205150603c10f445e0144d1024100511b09008 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 841724262 1250 841723012 841723021
    0x24060a060302130302060a03060e0406050114100206040602071a18010c050405031e03070f1a1b0a0c0311100e0705062d070b010602010203040302011a030c0105030c0d06080f0c030105 80
    0xf940c24194031000b807190300000380313096820f8400d800c054010320600340d4035400c9040c2440c050b000741501b4001c154445510f00490102c51400b000500c2030040c02c0e402811294465489050196001c9002513943c45d031421170821000b0507900c4000c4c46201c241c03410008503c0001203840c2501c0d580c1886604000007031000b8003032940c0105e41880d02c0c1c01302141d2002d4100c0c000300003606600802c3d1015280480e811101000d0003603900039182c050b298012594081d40d5020b5500390301580300c0c01100d58820043c0600b02200b4050f48124900381d0090805c1038603014001645031501d803000c088050741d03e80310115040074050420000e009081c044484600300409002501010140e8500c498214540700e004e895a2400480803550fa164011840a003950303164603000c5d0107540240d0f0114019031030211220500c10904404442c020001801303464030300b4000c2d00440d002e07000640320f10225801000844040b048600c03c0c0030040901d0b20280040032400c00a540c184480c5940140c0aa41801c0810 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 841725512 1250 841724262 841724287
    0xa0b071e2406150f110c03010c1e020102031909050708030a090e09030405010c03050f1905180f09070c020112060602010501050909030711010c0f0204062d0f0b070524060a060302 78
    0x1c0424490b00c0c1c03100c40d16004269441c0350451b081c00346501546083e8806622030b07032023584003801d8020b829200307400032640e8108038201d2200f10341c6020898550501081c030205142c120942d20390040d0111200c00da100c0c0794482c110b62000c440c1c0400b06107000307400c000c0300746c00d880760304d41c071060500185080c1860000007a02d04e001100000b82000303c0010410540c5a680f0241d0b01d001d40e850407402001c00d101d00c80030741103070301829020445030007142d10000c15180c0341551048070f1a020308a0403403900e68020070b50b400903550324200d05200c2e0810b821b0222000c10b104030b00c01810203600200c0d00794508401d0107803a40010b02900060b410400c480380c0800d1407903001000307000c2c082c83e28143c0145541030800b20080070a5000398001d007400c44c00543e401910800c1c0c0000c02840d036420300445140d245480c0800024801c40e001c0c00c1c45c507242001910030581c0074004190090080d41c5894402c810074184442006092074070180e011030501103d800c0142020000d0406c81c10708516202103200031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 841726618 1106 841725512 841725527
    0x1410090f09122334030c03030b04021204081206030336092a043203100e0118050a0f02210c0f0a0b071e240615 49
    0x150f204900c00311101e0280540e151b191040514a247e4003940038115911019512950a201c011034410b5104002c40c8102d1007140015610b800c2414105801e0030013508242c0254000d1241c040c0141c0800010341c0d00300079240300d01980c0c02003d442000800303d810070050300070000c4014400000c000d00c00c0a00c01007c44485043c0d0641100d50300051809280f18210f0350075030322001d0b01c001c203514009030b20464a90745602007416a103000031074549111003000c40042d6949510f82d5182507001e12920094030440c0a0910281680d9118140c0e10540400042c00c14003680800400319030342d0070300c44620250984104019052001c401035281c0340c464445d64041c09400b540001c8034548196158241c07580f04400d6070900341542c0f5110300150b0348044032501000204601400b1556004488101600031040c420701803005070b900e00c09462407607001120011020180b080501e802020 = true := by decide +kernel

theorem cover : BRFrame.Cov 841546762 841726618 := by
  have h0 := BRFrame.cov_init 841546762
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841546762 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 841546762 ≤ n) (h2 : n < 841726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
