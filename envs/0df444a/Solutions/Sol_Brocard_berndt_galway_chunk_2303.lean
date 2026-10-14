-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2303
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:18:04.851501+00:00
-- url     : https://prove2.me/submissions/381bd1a0-1b26-4e49-9181-f8d6a7e7749e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 414028776 ≤ n < 414208633 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 414030026 1250 414028776 414028789
    0x10203070314071205100801050c0703031107031d0a0816050405010506040602060a1d030a1e0c02030a020d05030d090605040506070201060b040e04020102032704050a1e091a070f020d1d 81
    0x4080403c1c00d0504546d80ca110241c00d650042b500c543c80400c00082100426800d03220320b2030022101d40e0300a00b801055a0301400d00c84000004030400115990307400400c0e9501c0000e00d000d02034620644c0d0b10480002c0c0450101c40c2d05000d403520484c2060004107607800d1280555084480b10350041c0a991a03000102c402000b4541c480b41070313602102c020380d4580c1d40070001030001c03004a54415614111120003e0304980d090b03005001000707270104e804405030740d00081c006081da40482d581b404281d82840c02c1491131140c012800c1116040207035150500401d030380f1240c030072400751080e1205507640040413402c8030201d001d0f403007960a09001c2030000454040c0302c0d0303611a1041c0101d9180850150b81004aa6410042c1c91200c07280c01c00f00f0f0300e42d03007028041c1d02c2c0c00025001d014040c0c1102d920b0320759810b11014020405a07540c03a26440d09010400b00d111040c002c0742e017082030f13482c01c20300c4005165200c4c48024001621415071074048491065140e90107510300401d000480001c0c004c01c03c01c5c03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 414031276 1250 414030026 414030031
    0x1603030c170f121005181918060f1e0b180709031b0e0c031906060504050f040b0405010807150c0c1203020a0b0a0e0f0601050d06022a010203070314071205 68
    0x11010120301c4c0c045003944409056003c400b20311100c058007480e1410b101480c2039071890000044905103000d02c04282d101d5800741401035401039011545a038200e08407001003006035880035230590450500c98240d5a60360051440c14810b856504000310104401090001c1c2540d80c0300c0042c41c000402c0012681503645071460b01495100000a51754441d01e81b00006010f4440b08107400340081030140c070380c003859125640c0340e4009030f06000303503803816002500368013991003154012410030080410769521544080e40c0c140300248100b0855841e14000780d65a90140181d580440c0c4600d42c454245000304403c54505078408408103850b41042c03e01118448482130440c2940b040008180000304c400200074850105020005130f056040b580452510815000066154000d81c0060202d030700e500201080c0d80360041c00c050380e00d0030340754652600410403090a0307100304840c0c0300c040d800c148103400a40c015001e50764103000c0c0e050464180102c482098403944040f4050030b40f2a100300071240c21855 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 414032526 1250 414031276 414031291
    0x1b061902190b01171c080c0d06030f0507050105040b0d3204050601050a030302100506060c06010306060509150105090904050f0a0503032a07141603030c170f12 70
    0xe008a0100d241001070030365803a021142440d1000c01840320419401168507410100001082c004044008961001045050b16001c0103c00c0000450b40ca00360303012100e10844050040003416a2402c0001450324030303108c1110305008440300040d45602c142c2c00d46050311000e0011a03d07044410300da942c004e0030300d0b0141c0c600c6000490260fa80c01c5c4007204203c800d00104440c0c29a69140511b849400c0c150160040e130703c10200030b80d040c400300758001540d15030b00c00c00c00701c00501d6840700c0300011000d008440c41040584150b00001c400c00c0719076082141111816220f1401c00d4851070031000071103601044950009000740b016803041c4c600030050030742043c0074100307071510300d405090200c0c1804210041aa0298400010720401030400701c6007001c00640c4d8441400601080c4100c458a4421300700d0151101703c540c1540899014140720020740c5184e842d503000b142c240e50345405401025442c009440c0840c0c4a07100c00b20040641c412150700b142c04601080c58050044803082b406503000e003021 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 414033776 1250 414032526 414032533
    0xd020d0f0203010b1902010507270b0a02030a11070627030507150e031615051c0603030e040908030a0911040e1c031a0108190614031b061902 62
    0xe1015540c4010741c0a00780d01c139042940d41d42400380b07113004100300da03041204582c9068100003446c1e07032040d01851003183c034510a82d00807105402451480040360842d804689002400c000746640020041180d10100d40750b040c000d2030075680c0c1030380342c0c401c921500000c14109202405441c07800400300b4151801088411000c41d1030b03481c0c1500d05601e43d0000001030019076580e845050b040b08581810203000c41c01810000c0141104a01c0d800041c810340c007100c101003402c000081d00480903079481c3c422095100c10850b11136203010f0b01a00c924030040e00400c100d02884803540c1001e0188040560304800c80d00e10303548801a9003002000829400c3e12174003070101917010300e03594a0180040001510740105411204040c2100013901041c0241b0145450710080130600142c0d40b02000600e80c0c242003080c102d65901158084154007000030702841860400301013011400030f0154002c600c003c1e0101c442c03080c5200301d9400810100c400d2194458004c2c48249000200641144001032851068 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 414035026 1250 414033776 414033791
    0x30b28050c0d0c090515070f0b091c0c0c06031515030e0304120b090f0712080405040c0926070b0a0507050304030620030f1602010b060c060a0b090405030d020d 70
    0x81c02c100e641821a00001403ca00c20410151600c1c403040200081c4440011340307018007950740d09090740b0301243c0c01040711b4203220014805910030b0141c4880004040f001090314054448014940e002c4410102c500340140000820a203103c0d1158003540301400e000481c0e6507080a12410030b4140b2003420100300358946900c11501070081c4040c000903c040400d81022030110702d0200c500017402403102c032259003d00e5040d906010006810005c4502011981e0401d1080341841c003028869a04896005801d0038080c0310a154030500c41e008031001b2108a003c103004da00384441a142014220719142d0b8010001440700c0c061b058000c203500c0881d420014070b0300c2c0555840ca405c40d042903000f601d00c15940c055a600b00150b0180320500e210722035802c14a1032410640c659042c00c0080c0800008141d010740003942d080c000d40c841e4054080081c4101d403150f050795000d070794803a400c81c0c00c00000da042420413002400c2100c855400b559002010b58180501500d80074003c2d00045492010b05031240b04 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 414036276 1250 414035026 414035047
    0xa0e0609040c030e011109010c08130302121b030f070303080c04031220030a0c030e370503060402150a03020f16110d02060417070b0a09030b28050c 65
    0x6110103100c02d910003180fa00b03003109219084803015200c4800d290741c2080401000c0c0c2c1d018000c030146680c0081c8042c0c07907c0e03a20758403003280344240e00000c1d000740c0c64034040300c0b0b081c1c80000c0c0c00254041001100404418100502da100c0400c0c01800086500100b42803001a010b01000303070340481c0e000e400904083d920703283c580c04405903075040c001051030340c100c4031848807210598610a40ca064004e42c5448401ca0008180c11005030b400340401c02546e500d80d9683c0e49420310b46d0318404081106805042e418007192411522050140180240c0c5800004490070003040c0188210780003001c0030303408201c1c81c59404103a88030b005000200f660130880742d801d03486014003401083c3c100001100812101e450648070619074184124407a019600c4060010381d0b4000446040c2c80d001c003110420b0304014001c0e40d01d0664071790084041c1810104d006041d00d64054900000c49005003401c804548a41d803021074401041d600c144a00704902034488421038958001d00d801c005002030641c0b41031040300 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 414037526 1250 414036276 414036281
    0xf24181502010e07060f080a021c090201031b18081501090c11010c17010806060915030f03070b040c1203020a02040207020a08060f040309081207020d0203031e090102120f0a0e060904 80
    0x40024000c06c4842c800128050380c0700c40d220790f200820950031131508080803001090602800c482415581d120030045045901c40d030046954511482c1e048400c401074000090110000125007401114450400080c3c2e003100160b008080d05031030320145e0f40d036403d00802c200540918200001800041010041026000d11420b1600c2030a0369803090700c590b01644030100d450060340700304044d5114900380501c9035a580e10031500003d40c00400c8004500000219062540e0112414081d000c041000014050808540c83c8190f03c12000b1059103504d881078208000c2041e070011b8010381c0002154001820141d0003420030324001404024616561280585000d908132000700c00d000440702030008243d0080c0203000502910400340c1601c00c0b51142454042c011b60070007a110b1441421071000b5034a05100701c40c1070b2140b0561a0064000040700c4071415071044140c0341c018400c008aa407103140000f019602c110306040005860b000d80d404048500304800509594005410044c050a580e20361 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 414038776 1250 414037526 414037529
    0x330709120f05010b040e25150305011404060324090b04060207060501050f0d06050c040b040807061101060b0301030f2f03160e0f0705040f24181502010e07 68
    0x1c001207010080716203846401d603041004540e00580c14412140c031283c5000c1041d1349002c1420900c00c1e062400800c40d00d941500c5a0300c10481105081c405401c0240d264010070705a0b15480600c1d840c207981c0d00240000c4900d240300c041c11286094a204412420684c0500201d1180c00008100c0b102d4985404071a00e01c00d0b1030032a24a5400542102001098040c2c18010b12046407107050b0406408046060340310000801040c29903200009020714603400261030182044484c2f00d611140c540502660342c20590151201042148080e8020020b0500600090707607075034007141c3d04503480c5a90305030911052407811a1850b58070b00c0200c2140b54003001480359081c00c02d40c4000c540800c50145400c0c0f102c210000030041e00252000d2049010916040d40c0210310099102c2d80d5940300b4000302c40d03070300440c0c02c8854a40710f1220002580368188070800c03032040f034800002c0000e400321101074a42035030607000d04a910b80405010010f8082059501d2000b41d5580008118029200d11040c1040c640c0d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 414040026 1250 414038776 414038783
    0x10c05070e0f010512010618020c01020d05130b161b0203032b0b060711060705070e070f030b0d021302030705091c140a03020a0f0f150c0233070912 65
    0x84004000500e02100070880b5040d40345c008001c0c3c0750030825110484442074003c550280c1d00040c1c0c900380c2c1d1100754100c0d0a1241c000c5020030250a000b0005034891144901c2036595034a1000485d60b00c10009151060800d0186c946c050030010046800c0b04c0b20302c23141003e036814041070044809001c0f140c1c0d02100301807195a0813004003d16507004004603883d03100d580303025603820701c0b600c0b000503d05025500c0e0804100c55040d20707001c0c946011450700c0b11640014031100b90f940701b40501c0300c0d0000302e0303220342190a0301c0500c0454100380c01c0c41910028110040d5001c41310340d0906001d03143d654010350300403005103401840c10501c8000316584400340240d00030f50100d02010352003404444841e400240000c100500300d21001510000c0da10226003202800d0300b035902000004000404041c103c1c02a80015103005004100112000810440c003407000540100e01c3e41c546403038840d41da406c1d18591a00030080e042c2d041007592103100300009200d00248100a1000b059071403101c405030104a10 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 414041276 1250 414040026 414040051
    0xb10090c090f060504031703090c10032705030d1d0a03020f1209012c041109040c09080307060b0a09090c1a07150c0c0c120c0803030c030105010c05070e 67
    0x203010194000b49195502100030040140001d0000400e06606c10204c0c0651081d403035201d46415140504042a4541c0c107035114598209070a0f100790181c10102d40c90311410070056141d0b19a0034520040801801d0040641d00100000c900d5410340c1e42c084280c2e402d80d049070410844542c0ea05a107002562a002e8000d6407101c280c02410840030841c0342d6107107030400409420700d062100007910140d10711114943c42e00000c100780078903e440414010481e20014400d01000543d210b208138940d10842d405402076042134030032a18030f4020007084085904440c010351520400340c907a40000c0804a681341d511010780480001d0860300e231300810b0380079801007100880540c64101c030048003003c00c15020988003014070410022070030420020612181841d800b061101c204c80c41103030302d107a004400070a00d00510304081001d03429040031042c1c841c030440c2d6007200c0742c1e00c03003d02640d2800200d84240780e480c410001440154071400480e465030340b0450489810a8440c92500030040c0219250454001c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 414042526 1250 414041276 414041279
    0xc050622081e0115060f02010f0f020d0b1002060604151206051e0601090905040609021e04060501030b0f24030c130909030c060b1c05010b100503090a0b10090c09 71
    0x12165a10008039a00c08402048203804e0a82d0410846100380b1410041c088050841d40006000703400c2200d05540b440b078104107100001440d00002d40200f2040d10f412454120400d0b0305040014181c086110a50000c011070f6a409080201414400000740003119a0050000f214034180d14100210380c450603000c603180c41c00c010030306501d441c0000803451405203801030141a0741c01c005110b05461070218003107029920780c2041c0c00901500d0200a4105800848610b54401805680780b4058803c41d000d02800c0c0d0344400440558201d10001d45c0c2c8075014110600ea2403400325541c0c0c0350440e1030004810f0701c00e81c05034840c0150b002201d47d508070040000301032507407101440e001170284c0314900d030400200c1d080b40c030002d00d2a0047c038001070452381e5485603590701d0364900881081914a482030624003420500c0c0c40c030b001e0400c0c2050301d401001e00f4444060214028401c2e40d108054400003400d40741c41a0721690030220019154110b15a80c003030010070409614010649141596281c4011a9 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 414043776 1250 414042526 414042553
    0x302120705360f040b040317040c030303050c0909010504090309080f0109050706210b0a080313080607171306090206030a240b0a080406020408010c080f130c05062208 73
    0x29002500240742e06100400b00f14524004803000d541140d040480c810044d621403030140c030306030303094a81c001204241c070041000700001901203106580c0329035414811034403024400415030164100076030307210406400500c00e42c1400d44c01520480d00a1820090203513035200d1040c2400690140c0d016165143c2080700c0a101c0100034000c01840c550cc3d280140c90005c183c01d5071004000d0103100078064443c0610030450340c40d100300303001401030002900c2d907480c0c0d420010300c1104000c1c07280600d1405480000f801c5640502d0001c1c20340342c440c042201d1156104407075420b01030640b4208551590355204bc0c01c000d6101d500c0594828801380700c1c0014031114644029112807084500c28100c1000030348103104038610f140c01d49031083c0b11400c0500a544891034100040c0c0215000b03002c2e198030340529000b02d640e001c078650b80107040940741e050b02e40d180c03810101e0003a0b1000d00c0103410003411980421041c207110004007684604c0309101c404440529820b03234160220780e80040c01650103044d00340200d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 414045026 1250 414043776 414043849
    0xc03081c05010b121303140a02070807090209010f05070c0306020f030405010f3b100209010f020d02030322051509010e2b0203070501110a090506070209010302120705 73
    0x14003440f41d42070341002250111100416402815000c03d040030318500c1e020180541d0380c60041900340340c441500c0700500c0800075510385c401d10440c4900c3c45601390000c3c80c84594070880d0f500c1d00e41a542d01e44e030a008680d082d103103a0300a840460f064424558000042951417010f02143c0f441c0d11003080c0da90030941412401d46d4043d405602d8445d141c400011003803a454082e204154000c103521951255604034402000c1c0c02040d84030145000c0c00b5401040c12040794010201040700b6255401e0f40303042010202d039034010054140c00541d00070400f04101c5000311400a50b0b045c02038074084452060343d501c081c20800c95104882c2004000c0080c490070400a0040603054010100240740c28010070000c80b1200d0f01c1c0d0840d00001142c00740680105500c00d1044800752a0407030002e02c84000042452080390b031003652081e001075004680860b061404400321817000750018031000559096400b00061510100c0c3c600348948034191002810b6110030102e56021092400902c0c50b80c80700020701d010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 414046276 1250 414045026 414045029
    0x4080304060e0105183106050301140106121a21100e060c2101030c051504270b0a0e180a05120f0d0513020a06140706090c03081c0501 59
    0x1400000d00454920028848881002203170844080e6680d9242c9030303801810385810410701000b4008612000c0340c07182190455012100164000c00c0061005011010049000c5c010b04000940c1c0809086105801d6081582d40c004600300d40000d807410140041c1c010582c01107280c00c00380c2184080e91040c102801140d03410081c0e200c1c240201441c00344155182c510003030091948003408550707000e0740021020800343c5c1c121103221081141d612130070400c0d1550000d100e402c1c030078008403800e204410408420b40b411208203149000c1c5100383c0c5180030078105035910200000c242c4e01c902241c001e41c5d03481c08201c000e24014020440500f0840010802c071100554204100e511031403440300051000651098641a0009140e84600c50700c408088580701c1c010f01495024140024001c00c12101c6020720b055510884001704140d07610101518a018128000203c5c41c1c0f00380020004a040c80d00103c11452040030b004407041e0b16070313903004441e030070400681c4200854403400c2000340c012403140783e0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 414047526 1250 414046276 414046279
    0x7060c0e06040b04031b0302220e1b040515060d0e0f0705030a0209041e0311010509010c0816020102040e0a090c120c0302120321070f0c020d06020a1404080304060e 72
    0x28075240c10329241080134815484003c2c44c94070b00003000c1a207000008600700c00b440c3d00070401907142c0120100e42040703809144000c0078251400c503009100180004182c03146000c039090050104000c102040014940141020180b1218180340c243d15551031006244994955400080c41003103486058940074406c10550784c00e81c4081010f10069070000b03281902294102c4000015a48070f10705485104904007642547c0c8403401204c1d82095080301c004c00d280d40a01d00200b14968894000c1d500341e17070500803400c02103018032020070241c10165280f01540c1c5000c7c00098500b03903481704800c852030411201344188658500c0b0100c1000000c60342013000b05000402050055426121890320209a12000f8461445180784d25060641401a41c14000f4128021050402c2102e140201d0140813152540055100c00400302c00a0090407000f21186e005041c900d404e50300b90780c940000f5840000c42c0810f01110f01203010502c1c20710350041c00a020464040c5440e580342500240c020001451189d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 414048776 1250 414047526 414047539
    0x21203070f080d1b0906022509020a051608040e0a021305090a090c080609060c0c07060c020a1d070e060403080d02030a1515180e1b04092a0504060c0605070e0607060c0e 74
    0xd40308001c1c040d400105449c41808010f0380d4040c407810665040c4100d130201c680031580c0400e80401d00440502600403605c450b50806466504d01c01800300304e200d056480100c440c0c001d81c4c14009400d2100076a5171000d00114002072801e81e0382c8440311000e882c1da0010307032540c1c091010070071100c5d01845078580011000d58843c0c00c11409480c402d4450580c1d02030001040b40d6103107130805640c1c0b0480400020180e0320000d1842030780b107a40350414070b101161000c0208540701d150444c9418654102d4003100d4120001c1400c7c60031600710700c8046c5d030018149003002c03503d403101203424641165100c001409006e043c0b42c481140050068030144031001c4c030080d001c0034018104044102641a0341d40542c000314813080d0451001011403030381c003c9400c500001032410302159680c200355012642a2020403405000012032000c045030580706901452000403100440100000c44070b0308169080001410006001c0002e0b00c0810800c0d04654403d580250b25019696005500000d4840603110709403484c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 414050026 1250 414048776 414048823
    0x20c0d050a1b0203070b07050102090405150d06050402270103031e0c0b04050f011505011202070302070519030b0c030f06010905090705070c0b030a020403021203070f080d1b090602 79
    0x2e0305001400784420014500c02001d03004541e01804510f000e050040c5200e901e40816051541c000e42010604501581c81c000214a9100c02502200180301d802001c050450341103a81c2c0e0f50181030043c0c4204d81007a03405500703150440041e00b0121801241d4003080706558510b007001005440402c0a803094507111688846006070b2007260144643c0d003044407181c05444a24196141c4100b44d514003416501c0d04181e019800c0c0c680c103610049a4090340e44e281020050b0111078124410702d68000d0150b481340e18104031500b4003a041910161400d503903103071641d41e00d0726071030154082242e032441840c5001041089990080044c1c83d00b100e000c0ca013a0070402d0400e03006c01c1c03a01c0000384c5120240200030a080e81003110780307003000020304007407248143c8a05044074078401035041404100d104041d445a080000d610001c241c8034229046200d1003020480350b11079003143d42c842c45212048980fa81c0000c144110b40c041e060351024008da0f1070b61500c510303004001303040c80c0c1d66100c03101c19203c60185 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 414051276 1250 414050026 414050047
    0x30f0a050408092701081609051501030c0c08040b0301030611032806272007080a170709050f04020a05072909010e07050d150905011509020c0d05 64
    0x3030300c01007101501e800b801a06071410048002c25031111500f003152285002142007000403800c0350301007d920200984664640f45640c0644000301c81841e9107803621031092032258441c1c3c01065002d00c650903c41c80030385158a600c2010b41c09500401142403000004104000301c507ca440b5200e0000d814190440c01c0c00c0d00e12410039a001c2c250121781c403024584540341d00c07215034049002403d501c1015140380000000e9407070f4260544030345483c10380c6016214010000301c4400016071401a1214910b412025501e03c28181c00680d401303401c21440625400c0c404404810b95030003446961124526580b4000400603228408080340d8015401030080183c0160040e09545c00c1030f5008807200c0454072054100d81840b450058800101200328041c01744140b810340c0901d9241340c9240984000c2601c038000d00480d03060350706000b031101d15280320342d00900d800d591203455403c1c03160380041101c00c44c010320500b0b000e140b500120301c0310358006034239800b584040241ca440c0762010f05101d0709040321810b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 414052526 1250 414051276 414051293
    0x10030605030c150f040905090c01091511030403060f0e011a0109060c06090b01031208070e0a0501230a120501090506010503010522020f070615080d03020d02090a030305030f0a0504 79
    0x451280a54200201a03803200d40f45000d50381104d41d8031070b1603611a542d40c407140001d440c05480900d820701030b85203100c82d554030a4142400707442e0403116180800f000e40000b00d071502c908030128003960009002c00300c0042d965029200c1d80141c45a004180d00030324840c01408c4498480040010088001022459980281c03640040700c9031030900c4c00c04521076080800c00303800d0b0144000d086038003050011040044c2d0801000300a60310b030303880e04e440e55103000c41902d0241203446180c0c0d1004820000300050b602c02e1000d000d103440520740403949440e40e100d00004503041110f0309000f0032166541940152480d102e01401400591400e01040c01d00400103051840180181d60155200308100840881341c040004019283c2d507400b156219100400383c0740da078100c07a0003100c1450400805a908010200408040d9800c082c003400c490030f04443c0c103800960260200c203808540078041c2c1c01782c03a998040e54900a50007922403550760302c2c1c900c04e4104580d40c01410b4102c410f14001c103100c0843c0234007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 414053776 1250 414052526 414052543
    0x3090501050901020a0507151119080c01150b0405030d0e090a09050a0c180f0b210a050319030b060408071a0412060b10031112060f09070503061003060503 68
    0x2070074000c0c0d64160400c0102d00305440c0308005030071886152400210040c5d849031560444007113540d902500d101c0502143c3d154140c00f107241c0701c221403100031140030404610041084c08522400019000442c071810091580305a00c090700750540441c3c104050308040c44010b81242c000d00d0710b00180701028001440441004c2d00310009199104108005c005080001c10803440d00486103010140c0e44946403040c215141c1c00c20600c4500381000d03580480ca850252101d00131005091820b2045031106d0114407041c1c5031242026489401c040d100800d800b03000811001c0c02c207078403c21a00100420140a41e4204010280140e0341007204200381030010940c2011348080000000c0003e010036214400d500079a0081019840348038690020002554021001b8040c1036807242000c01401400307a00700c80c0081c401441e070f03240c204101d00f01019041c1d403155003e60010240b4944100d4003010842e2444126984808900700006128091801041c3d004500c0c2d4286000e200b09400d042c0841c1c2c48881c0d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 414055026 1250 414053776 414053779
    0x31e0c17100e09100c0c031b05030f0c031207080402030d050f0904180506061005041e15180807030c140a030204020d0f230408280327030905 62
    0x4020100e4004040e101d2400020b000d88045480c0905000b44800d880f064040c0030505072600c1d0904160315140191441c490581c0c05031102d0b402448000c2136024950011303030f02241e00b4001045081380e024102c2010303211010095005603100c0344e80a80344016000050484000e00c100c081c1000010fa8002a01416819086c07030312580740c0d0002d4200710100e0082080040e030080c00e00529402c0c0c513815511004809000e80f0071524141c8680080c004130610140306000025000c210a0054654134083c441080f0b40b000500c994541c1c0c1c400c022011048500005c0000602907114440b544101456250144c40340b0b0002d00070f0246903545002d0300118921400710031030400d100c041150740d2013074054001543c02400555030f6002295540c0010650a41c18640b0640351100c031908c1180c1f0150010250441400c4003801e503210350f21080d850f13400c8450300540e00c0e080f44010944c0c1e06811000c445810398540c07000f20390060845550221400040c5106441c009224000c801280e4882070074000c4410 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 414056276 1250 414055026 414055067
    0x9020f04111b010b090c1903060b030c1606020403060b0a09050702032a060924060d0311030d1a0103060b0c1510170d0e01110c0418060507031e0c 64
    0xa00b020b40700d02400441034020b5001c400e000400900400704d1008000003c010701041015075440c2605404a030040c1c041e48400b00402d00004480b416a200200780102d0044400040c40c81341e030b40d500702640d0250700100c442944419254246062060703100c00078001c00c880a21413403800541c025503e00404028a410101d9070a4180901b140ca940c15447c1c104540182c80c00e07841c1035203803280d403030045404c001c0d02c40351001c42141c0910344110215005103401032002c40e150071151812910407030244c0394060540001c21554400600c01d10880000c410b4940c040b001d42c04889001400300c0d0308a502c2400252420000210058008140200441a03c00c0411207a40f1035146260006090b60401016804c0c0500716411150300020500c440c0c043c96950140740c4441030004449082c000321640e0300b1984042c8000d0080d150503041a1032102c01206a201c4102d642e0f01c0d4101031710000e03a1f0100220380c5c2e84c24920007580a65520900c01c01c0030313090920001c011000000c00c11a85448e0135240400b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 414057526 1250 414056276 414056317
    0x17010c08190b06070503190219050a06091a130c060906121104050612010f1d0106030c0e0a030f0b0109110405040209040f0603050d090909030f050a020f010e0109020f0411 75
    0x43d10082607540301c54010040340d4640508440000109134841140300142c411040242000b201c1c0d03100300b5035007070792103006007288040d10b550b40307800f405007030b9411141d0140f650405110b038801c40b00118421100010140c0c40701c1c03000d04001c5404030040d0407280030054442020710146420900704140c0c1c0440140c002102013240d6021507150040d0340005a01079030004a00d640001d4210b0b03418140d0f110182c4540c2c0450760360845500300c07014681c04050f030161060041020f90700070340c0091a690701c00e09084500da03901400140600300241c200b2900c075040d440b030f88400d01000100c41d90251092401c01c001c2c09240c1c0110700c0c902c1c000d501c43d55108030303000140d6003042c0e00c6030340041c4d0711886144d00c284015a268070300707151115002e215103030008801c007200150f0b5244501880c01e06a4140d140e81140703c10f0707c0e50807551684401145d034154814807081141c071080074400d965684400d0300001400c10310510410888032600303209140b180341030184400d0a0103210b0111440355a8101580201d00e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 414058776 1250 414057526 414057529
    0x60e0c0a23091221030907030c030c030b0f060114090303090402030f0f091b01030902030c0909060106020123011517070c020423010e1f17010c08190b 66
    0x8032042110007124440c6084414110320880d000c1d15000a003114111100340018050340e0f65868102d21225030103203d801600800007a440042d0342010a42013a650804d0b1244c943c038402c0b4566520440d40c5034190307801002404880c1914a8021501e14291009400e00c0c00000309101e03290400160600c10005200401d030303404104032080c06401510542d00c84c0b4140400300b05081307007140c0c515101c296242c000f0f50200004280c0c5020500407403128805040b0110044000b460510382c1280c1510a20059003019038400600c50300c15000301000704129814004001d0a44800b1044004580b150000081d001040402c4440c1902c1d4080d07140318543c1950241151400345442d1002c82e0542264207101c407181c1e1060f480b509050003a541485001c41d52402c4050081907109061444402c03240180808201a10700c00d0300480c40407500304046a02404603002c030b02e032660002c80242d0211a065904c00000e02440980c03001034203000c540303494442d404840c21404880074040940e0b543c4011601c5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 414060026 1250 414058776 414058787
    0x1b07060203031e2a1b0c0f0a0e0f0408040e100503012003040b0705070c09020702010e300f1009021c0812040f060f020a03060f05100503060a09050405100f060e0c0a 72
    0x1000d001c40c3e40442d40801041a15071203506d402e484501848004201d00b03c14203113049031404907104906042c00705d55031015420b6032880058001c40c2e807100d08010026400d013003003034040d0040340c00ba20501121440d08003014216451070240700d0600300d151304000b0507943c400f02aa94801d07004207001e140f580d01c29900301c031580302d08440200803050000021480d201c442d030260000c80d200380c80307066100e40c7d502c04114110a02c00174102d8050b041c00c2400220804a0300200881503103001240e2a01c0f0000b840c8030f090003008001a2850303580e130241d24055180549142c0303e03542501480d0244180da58503041d200e445400d4441141c07c5000011808115401d10442d040b650032800c10005203200c008440d01a61000f4504c8000a040200c0440d071801c0e6200d840045070b0008080309403112948a055805400060980758000c4600100050402050159920075485000544000c0086894940480342480010031201d0320308682400002210601c10790040705210000d42c4825580c0421600d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 414061276 1250 414060026 414060037
    0x61305040204060f12050610180c0c080c2b020303041205090604030317180316110d08030420010c1502130801060f0506070c0b1b07060203031e2a 64
    0x207400806000040e220358174894480d0241d00c0303001a00c0d099142c030101080c0c0d0304100c3c0035800304516650a840015030640d48494840015820407a1000445032501500b68001c1c0c600e416450700241d201c0c02503d4030311201020852442101c0109212030380c40f00030341d00d0100500080096200084141c0c0150050040d00c040b07683c01089140d8503a101d150080640d4107040c280c0101502c441e0101d070f0750000c580000700040803468002c500b000040100820600c040b44e00560b0482c084070b040740c209845a0380010b50013030191078455528241860f08841e40d07100e41e075604916810640116181e07aa00c003281c0300c030072500502200007c910500c1000c009104041c0c990306640103a00c400501c6c69410f40040c4d08030341e6040c5154018564690501c003962280c01e0004050355400380003070004d20000700140a80c0e440c400c48440c0c01070360384804280b406e921a013000c0007580c404410000c4101c1da0754402c1000c00f40089441a070fa01f80300007902c840c044e00040e1101c0c1208000004080303040088113444 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 414062526 1250 414061276 414061289
    0x12090f0619050f061f050c031306090f0308030f0a0209030303130c06030c080f0702071701050402040b06070b0402010c3306090b0a300317010e06130504020406 70
    0xc80a04021401c0e00c0e000c889005036044140c20200007522400b081c4041c144160006404400002c14420300d50250b4084902080d060010a0020350b42c111030070406000b00740441d40c1c101203460b003050800f400703123032540c1d0001c1d04400074220240009481c000c1a290458130854021246886110100001e801551002034240c4404010000340d2400c06c1c07620b02c03c00d070150500e10b003032a8032030381c00720182c540c841502000f1800d1500490140c400d41400d099119940c0e1040c7c54041c0d403114109401e20b00c15820040301603443d0300c04e120a42c40c0078441c1c0e48001d6811205d591030501d60355641342e8a05d41c018000307814802d4541d03041041c081c003162892072081c480a0250525004420707983e6178800b922054003075541c58100302143d1340300f20b4801d10400710001444c000542c0e14104450365034413001140151700400c009803940703060400103c11880e50f4032a032502c11030001c45680301340e5840c1050f40a030100380044400e00021341c41d81c0110000220b1442004129070f40d640c000b06024014650081 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 414063776 1250 414062526 414062533
    0x9010216050c0f030609032703010c021f15030f0c05060d0e1204050d150f050c040302010e010f0503071206030b07030213150519110d0224040812090f 66
    0x40c104803002c1041c1c0d200210490306000c0900d0007009056850300100d8403c480b0307520030820903520f256401c08810000c00c8568071009032080440c003103403e4a10002099016a0081020004800d0041d04a000c0d048803020204114045091202c1c07020101c1d11024200c580c18042450a01c100684500c000d004090b004c2661000001d8550006002c1410340804d140104130b0300b07054811003181142c0c1200c2d03001b0003488444c00e16403101c1ca0f0040da505046c105440d6504e003011604d19940c0225403190180344078460b156491400058004408955080d040200e18500c8902c03035904103080c0d81c2c1181241c540519141c004109200040440d504050b1015942e803080280d6580d240d0003d0406084000311b01154940e00c0450140e4200c00c41c042c207010940c14420b203014032540d10785080410099142030740000c41e0010006041102003c4240010303013200c8031443c1814a960304c0c21580f80d5041e40c42644510306925080401c0c02445c2004480704c2071500868800401007050140342098441034 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 414065026 1250 414063776 414063817
    0x302210702030109050d14030402030303040206092d120607021005070315080601030c2103030c09031b0501020d0207180c05130605070507050a0501170603160b0414040506011205090102 81
    0x72950ba01c4031521b40c1000811101100018400d98002d50b030180c0e50240066046880703581c01c001040c1c100d528841d030403041e030801070501c0b0300382059000c20901d41201c0860075071a0003010f0002c0d41464158950440c0d001900b030055066000a14200c10310142d0b1000a0782d03240c44401320080c01d908150150350400a510100300c0c0300c400316195040724841c510b5010700503070b500f21001e80f803000010210a03201c2120301540200340603411082003005145031581c4030340c0d201c0d51507a440b41010a00315128000c08082440207580402610729504560b00050446514010450007178082e8640c8120440f5111030800c410b140c013510951b018a04000c5500500c581c0314103001b01319800c645025141803042c020b001409080941001c001d6900694914202c0ea60b0900703100c07490740d00548003a40620584204040785d103d28048800036164039040260f0700c80c54208402500c2e500c00c01198801d62512003405190380e0401c0440600686000d008107655840c401c0d25030090294402203c4041c142411 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 414066276 1250 414065026 414065033
    0xc031103040518220c030b040309030b0c03071404050a0513060801020c060702010b041506050c0a0b1320092701090c0e0702061909080408030a030207120c0302210702030109 76
    0xd8040c03044e01c44542540c0d01d00300818a440e003207801c8800182840c1a941e10910110b0200c034401540640a8140f441005940782d840e4502011f045450400012010007403201c030992250801070603c0310002d2240c241070400f00050f40c40c81540c03080c0d500c81d110000c247c4220005540082c001825014001c644a010b040700850b29004122a444015485c0c0800d080483c946441406040d0307440440700d0400f6800c100c010758150f40404c001d0340451062120010009000c000d2841c03081c0c0303101c440c0c48a141094034003032a000909000454007418415030103003803600c50038041944500032040d41e8400c1c0c505440c050a8801c18002d0388543c95003080295014041c042210800f101c0c50f00c00c0c44d104655034030004036140c00d82034601c1c402810140b500c2c003500301d0860304554413540c0110b940c503250540d9102d0303040c03450b8841b130313040c0000ca900860034000b0f1091004010401000c1410304c4108800c0d96038000f5101d0031180452460004aa500c0140c04050401a00c070300c01d80c050001c103d001840e06 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 414067526 1250 414066276 414066319
    0x1b0d0f0308040b0906010f1809050a03030605040e1207020f060c0105010807030227040201030b040213170d02030403030804031b140f160b040b0f13090f050c09010c0311030405 77
    0x7141510540450f01c0854130501c400a10310f4100c030903c40040015604094154108000f211405c01c41c840d02c503040c22011070000d22456600620a07100090002e1401c420721065032a003504100e400d40041364034484060b03100d030446d00f902c1c1e411586242020020300018015002c0c10b10b0001c0d485d80f808002040724900040c2c2c0c1000c0e6402100c080550300d000b1820820060144016141703501c85e454040340065009800c1140e075010020005800c08908038194900f140d460352110709036028044514040e0340c002e20012648000c50320165141ca81140c6018100740c0c4082c2c8024104000070f80c0790900c00c40f24081e140c56965000e002a091901c1c01c440142e500d41d0b107000800990700403800c4440030b00d181045540c0440d190755003044c0c1403a1500c485482503810881000e00f440008000c1502c2810031403804001401e003801002a42c002500c2c044d00443e10020040358000104000201e0240e802c00c1140c000341d9454034000e001c182050314614218001c6030321558100c440f4141c05001e00e43c81c0c4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 414068776 1250 414067526 414067531
    0x60a0f05150f21060d02030c240a0207090c0309080a0813150902010905031c0804081b0a0b01090510030209040204060b0f04031a010312141c0f05060a081b0d0f0308 72
    0x1000f0030310b065250312041103c0f0414180009605501201006040e41001ca68016941d02807405440c002e0b0080c811495072980070040b46401a00700031020300490700d0501c07401118005500d01004551005d5864800d80c0c4510340c511403d100641c0300240300070100900320b841641d4130607401040e03144241c10f40e402400b19001c0032070125a40790f8000c60b482c00d000440342c03c1c840e090075048012200c28001a035a03014090400e5502610420081d1440c1c907016405502d2441520700628030510306081000301000180c10452101c0e081005100e80715511944000a50f60100c40000d82c548451002400405040c1d0154900c160041400180307100c6290280c81145c1c0124041c5101c8601151240f8041d9424040200782d01c000078400e200161146141e015221a0b111810746800c3d00c1c03008003164007940a0808407a02e0301e40008161111080c000c032a04113205130784e105502ea007800c0c02d50b61582e02c0402241e4000c20a8481d2071900da03280ba6840708107680141d604a40b542d50303810000d1010004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 414070026 1250 414068776 414068827
    0x50d0b060a05030a1a06030606160b1024020303160c2f010212070f0201140d0203070f030213090c020709020403080703080606030702100b0d02090a14060a0f05150f 72
    0x2d05040d409080c15411403e0311790740d0002c182c079140d540d4403001c00c82a604a0380c0003801c1e54600d040f07494006080784650f1805081d00c80030201d0060702d840700c2c1c000c2e040e05906000711034001c11801e0400464000059a410051120020711048030402003219202d80c2c602000d0100c0082030300300b003885003103007003e40d4480300c01040d05010648040016070391051044000c400c0342004120b0200825044031035420014814900100c80c0c01d0581c03043e51850f04001c001d51005c81c1c2c00800c0c0080c1c2c0d0741103030f4102141390480c2810350801580b0850344010340c0c81d070300c038100c00507171104c9418070924030030700c110800303815801b01c115100c68403420004141d81180300d0840120341040c0200e1220b15000003500d100310700a9009013284075101d040b150103803241c086400e411415048800d00142cac1c4815070075104000304000002c140d041c0790501d107254100980740c17900906501c1c0d801d00514002c0803c0c3e00584005544001801c00c8064001000d4483e22a01111040d17000c10340e00e07270f9001d00c4c01c41034900440 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 414071276 1250 414070026 414070031
    0xc100c02010c0e090a0b030123060f04141807050d03030905070812030c0a0203070b04030e240a05030606070609030906030c030227030109050d0201090b090f0c01050d0b060a05030a 79
    0xb2841001d681c201c4840c90481da002060000040c03000b400ca4020320001038018002103410328050382811ba40a0380341400300b1060f554403080160320306214141c10b88011040f02d044c0403e0540d003003520020203025201000034464a02c0c1c0500800c0200400c130700411000c2c20403042e041007400d0003401081084000c4480d07004602001421142c0051240b51100f406081c49156403220030010541f80c4c8284098406d40c0014000440454000c4030114820b078000e40300d000442601d0b0041110f5009001101d0243c00d121110010a03983d49105640c03042c000e500702035039a5180c010004040c0d026880d40244490305010560041660002c042412030301280c40034411410002016401d03409a84030050754160400d2401c403101c50358020405842a001d8000581c680c041e0b02c4860900f103015141102507916100d1060800a00c401440c2c0c1c000c4016018103511031048401940f0707045512a06410050082902508185079500803094103c00800141c0d50322482c444c064415082101c000051b5071 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 414072526 1250 414071276 414071291
    0xc040303031d0d050a0306050405010b04080c030109080d0b041b02031308061605030601053105040b0306011406040b03010311041d0a021e1905091f15050c100c0201 72
    0x25041070301d031824400c89501501d83e807003900d4021036894100007146400c00d603c4250029407a113480c1b040d0703800f034240000010b64450070029020b00e41441104440e010741e2400e0080c001180c00c58080e1040040c1c04000418094440300c0000c02034078a09801c40d4508840d080303040f45180c6c0000c020301c9400b0040c5100e03124150b0743c00801f62a000c0480d000400da0712220781c52002c261140d00103680c0001c0c1418014100208030b80d00005444e80140d4000c2c070320b184681407203c468003908440d001010121400e1168451140c0032a0b2521010300c6070902c10b04401c00501010744c2d51100380c034050955040015101d44c0d4908042903040450f071203a030300961601200782120ba4042c54101c0d60106210014101628642c0c01e01c4110205410390004a401c03c0b510403c40c0c1da00c00e410007100307880501e034442d1040d0520782045054040a403a140910300c40d0540a110814140c0707550045844800d0031455100d404c4100750b4451103101c89004850203903118070b002c0e56400358042c0d002900107600811266 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 414073776 1250 414072526 414072551
    0x1107020a1203050f03180a11090c0a050415020307050f010501150c1a07031104060c06050c070c12020105190f0e150f0d020405030a080d050a050402010c080a170c04030303 75
    0x1550701c850250016038208082c00380c80040000a541100e03041c46135090050050041a05195802d90708641c242040c1224500c0361801243d515046600c90007190f281c10141c50340988244039030b10818120310345c4100e05030544ca00920540d560781e03401138203888041080c0b00078680202007d001d0f0038410161160110f0495114000004045500001c05074400c080f00d007071a0740c1150000c181200309511105160110701c4003002810081402c0d49440390740140e9440c040e400e503000285070000d001c0041c0010800b203903550b07038203408aa0891a017840790402a000403a25403140501c040082e40503a003001a225070f001c140c00a4840c500c0c1c2e60300042c1c511100810820000c03e0702e01a03ca4442400400f83c07694440c00100120300d100340740140f90079500e1000c6400d0a42c0210192911480400d104c01c0c81f80300350003a40d500100d0f803030b810082d82c505075002805842840c80301902d2a900464104a602e000e424108082c805102203900f543c9451801e501203a403007800100c0009003081d2a45501 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 414075026 1250 414073776 414073799
    0x40b0a06110d1e11071e080c0d121211070b010e150a0504150305070f1802071a042405010611030c071215050108010507141306030e07091107020a 64
    0x400600c0f0301c680b01090a1941c0403152691080302c084098000c2800002e592500000c041d072a0203d4884900c41c55480c01c20206d04041400380600d01402440d90ba84001640402102c1d80d100312904004c0c2c4c00700c085080250050640d5030052442060001e056014402602000e504035900c1c00f0b030030119507039815074110050100f82c296035003101d01c054041c40035284c1600844000d60f07030b03a184903007420b03075070b4451600c0c007000383e0310440702c2c0c1c084a00144000c052300200c06a0154400c0c000b9858281c0035503440224038605079000165517503441c0481c0c20410500640000c1c04503240c0104501d0300020341d10802403d0070700c11003011442e02d0561441c15103000c0140c0d1038080450015001031132501304007646d911002e500c1150303483d03407221982280c103a444c490309001e816184000039140c074294101501d03000c07080125002840060111140103d001054103055440034640450a2051548445c4c03802189400c00341007541001590161424200c0152484c2e9000f210082074031580c0780e41c403401 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 414076276 1250 414075026 414075047
    0x711090603011a040c03181b08070b04090b040209030d03050906130206030105040506150310031203020304050d0e19061706041413030e0d0f0201090b0309100902040b0a06110d 77
    0x41d0001d142c10f568010385440e80c40803440b0003850070045440c15101a42c5180c070741074290100d844055060b460000440404001e2014042c4200140030103810500c0008503070045110f1004120707212010307104284c817241c064881914000d400c940c0100c0c042c003405400340004858038092403140e140003070790144504801e464001e4010f400540303141d00b01410300002d848000c060756006142c199000404c81d050303c1c0118401d16081400812203130842c070300504440d03041c8898604142c010300600c000f18001040329241c4036140c1c140805082d20620200d8050b0900c0d820003103440c4110500065019001128410b5090b0501c607414a1591040100400c44400c4041201b402840000085138220454401d030f04440c000d0400c9216003035460000b441c0440c90700e204840c00c06640e1801000c55030810100400381c0503000300181113240010380955101b5101c9246a00540c1f0307039220700250b44403644079071030210018003800c2046d62a4100074290341e03100e0f48513440511a20485661041c41520f01e1740 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 414077526 1250 414076276 414076301
    0x307030e01020a091e030f12090618091a060f0c070504180807080702040f020d0e060919031e021c11060103060b220c1206030213051b071109060301 65
    0x4411340c0c01c1c46524188010300000a0640c0c0041c10300c0400400c000300c20705003180340729004413001d40c0e41d010802001e182040e03100c0020300580c08200074039154a1181e95040d2800920005640e0a18600520003080c601c6003142c0c2010000a20b062800340e00b60003010728981e403d048a1000d0307505c8043c0b1040381c8140f1461001202401d05440c00580d040006104c8140242a110b0a0201f1500024101c03030b07034900c01010481d40003030071644480081c09030451901028025010610381000e0091300c3d2183c104620308500c0b8107010100c1007601841c00d28211192002164202544001c8060b540315000b0189030803840e140190000d600d403054a002070003a440300043c040d664655a1460003070051140065400035a00c6c0c010a09190b00c0c0465070b00302d841d10074001c50700845140d0003410f104440c14101174200c2c00c1c1101403000d80ca0b000720302107035680c0c00c03480020955038511110b8100c0c28146800c0d9242c00c40001d0803424040311112030454803404a9880704982c4443e0201030886580c01d40c01c8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 414078776 1250 414077526 414077537
    0x2301090b1906050319180b01090902030714030f010923071404050c0c01020a090603060f03020a0e0a0b1e0301060e160c02010e0d1a061206040b0915010b0307030e01020a 74
    0x2408090f114001441e00014403500701c03d640402c05000307009aa501814500400065079000e80c140f01e05550b00c1d5005001c181810050030b54641c0100c0d891300000c3c01240300c0f200d008081050036480401071102e171484420020440104189860700e0000c00206510035640c04981d420601c509020440300211001000030000e40d42511050101500000b40700804111007440742402c402401e00007030280c0344d0150b8405103102d0a0640182c104c694a401800c00294a801c3c1031005131503060484007500c0c0080501c400c40c3c0d07200381080300548081e104161b00180c0750203101071a407050003200b901d1004120004c1c8001521104580c101c4d0b5400c55248008140b03075031704001d405018013500c0142d01d0040c900071110300c03142001b00f0440c02c0b0300c200413240000702038220235081d580c070401c2035049101101c00d50a900031100100b83d030b0b20000b901c0a85900200c0d030109051800c00c0080c8903082480000410f41740d0b03518500226190001ca568501003820300d031044207002c0f01031007155030912742e6440e070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 414080026 1250 414078776 414078779
    0xe120a0212010c050d15030c0e060901080c0112050402040f2a020a02102330010e010e0a09051504050c030a0b07050c01020c03040b070212060601120c032301090b19 72
    0x222025103031b00708034440f036000089004800301e811124840087c00002c1e00c04603481c00d01030113000501c80305070300203d459000001e2000c100d13039000141d00da41e000a4403010404d0f4803075000103001840c0001c88483c14134600000d040d07040e1802d2034440002c000a10084a200d00d070f040003a078690700a040025440744a03087e41e0101e003800b4420908110f035003103440490b1040300030340f564480d0b0f1080040c000384071401d4001d00407a801c0d032130550241131800030f07010019524121010340101418010503950700003010001d030007641658080d00f0490380020881c1c1080400c841d900302a1a420b0b04c054882e4011240e411099045c005000405a139200321040c90a542e00c02c0212990f030031081c25a5a155000c03c61429000e104002800140220b12205580c8840314030404c00307000c5450b540701ba200c0d0406400c01c2601ea1b0020307204480c40c0d051001c0400c0c40f140781e46e001c400901800440c03804080d14220040d081c80f011444007416038030200e10401240c4841d03003c005804180c010519201254804c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 414081276 1250 414080026 414080047
    0x310060e0609072f010f090c08121207033303140a110f06041205060f07080705090f0402070b07031d010b0d080a0207030b09010207050613031b030e120a0212010c05 72
    0x120004c2c2d281040000340e480101140f82d003d03141800402d0301c69041d03001e030a00480302c092041070601102150f0041c5010149908060b104070020020000c1c07594a6000c2020741d2509880110500c0380100100d96001d21b40803000314403005408240c82d18810b01514042e42e03000007070181640750304403101010602c3d443e410082d05644518101c3e4002a060000099144d80031084a13681340c41135001d064545088001c040f90320000818801c2000308000078040030542060403188040c005880c105c0070030700240b0124001c1d2192030401001ea2500300b0801030860f501d580081100018602c010708a54002030f041c90980f88400552944081100741450000b11200000c00301004140140e43c2040c0e030726124500c20407411101800c641c2d40020301da0003001414000164060780c41c3c254200b40b01034540340104886404000018003500b05001c1800703240c0241040802c030f04000f41303c10fa40301c080300741068071a19003082c04c90143e140e2031080722141c403060150071821002c0743d481e20f00f002142e59 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 414082526 1250 414081276 414081347
    0x1009111c0b061605010e010b0102010902010903030804030302130e10081b040e0c09090a031e09060c03170703020c12070b1906150f0206130b0c090310060e060907 71
    0x100351641c0b10340300300188400901014441d01d00240101c000241e060180918242903e590010040c11139141480701c0006030380040da800d00b40e82c0c16142c0142240e549103015002849100d8501c0424041c000000683c0c0b400300310618414a0b480c00c113001d46a0f66024900d54a03699248400c00d01d40a402910145042a42c0594142035900044805140e01c003000324004c03490903107081c030907038001c40c02540034141c00c40340002800c6820058003030070003020314000303050616601841013080000d945550515109031034003903080200c050810441d00301908060000e5002000c005028051020b00700c000140203025100b8681d00b000904850381d07540341003443c4402a40701000d040d150703164030110320001401402202c85020f03450f40c5a0060400c60068500413004003c640307034140b40340c2548005881c2c501d4280c5c0011001c031106481d03142c0030b40000e0910072954589810f440c40c0c404000f40c440403454400d03010350402c0c0c80c0a80a41c40e07500d41101e002218203400e100140c140358205a020002c070 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 414083776 1250 414082526 414082541
    0x30b01050409081c02091e0a0512010914030d0f0204080c010f020a050a060212090303060f01110a0812070305061203070f15090b063d0c0b1009111c 65
    0x3c079182440d10f0207203007200c13140c0001d015040301c41550114040303009080500c4e44021111400706901c00d82d1008000240380d84205000d400d0150200850386005a50250071100720640c1c0266880b0054000c50030380c40c4c0e650400b24444004508004032588200b10034030842d0142ca0342800549201038045006440a401800c511070451043d4903020020400c107005103c146440350601580c3c0341003c00812000110241042c0032503001001880355999440f80381c1e00d9001002e0a0000d203015905031000c0c01c040c11058080c00074280041c0d00500b51841001052003002c154604000e1916214140324025550000b440e105034010014000031820301c10341c0400c0b0a2203801b140700c0480c08000040f00b030b42c0c00300c0c004840b034041c500d0a01145103040d0210803010011a10741d544800303002c1030b5484000244185001586920130100c220f428441c03500d0030301094000c00c41c4c200c941440709002045021a1003142446450580d080601010060441c1c0d800040011038500451905045030024101c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 414085026 1250 414083776 414083783
    0x1a01120623030a050f030408011103060d021e04060303030b0406140102070b030a0204150201140106021209211e120403080409020315030706181e0e04171204051006030b01050409 78
    0x10440c501001441c10000c4952900105c1c3c003840e200d0b03150140003420f603070b0000c000c1003003c00c05008120003074031b441c880c444100e50116442c0411080384040c051064190604054105007000804424181c242d00404d88403a804d40b41080305903607a040400c100c050718074000d0b0050700002d10800503841040f0246d0741000d0070078401443c02e95500c1d80081c00220300c0c100c0d540543d440ea50f071909580496140c03140107041034005445c00401c080c9070040c1a12541c1d900e07500c2020301d981600c02c400040047c0c0506820110203c13003000750031460302c0c0205c40d603001e101e00241c07148020070310600e8102401c0d241101d03400b46000d810305040c0340b40365001c0c5d0002420180750086010301500c2c10350341000a038008001c50745820f500e943d41c010001d0441410307600000304254005054400011130b0310076010803208101580d00040d2614a00340d15101c00e140007080759654089a07180c00c504014a410740507602c2002101d050000c209841c00c16511944409050507201000410081c1015008002840d10 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 414086276 1250 414085026 414085033
    0x90a0317160c05032206031506200102040f090506030d022e0b0306100602070b0c07050108092109120f0606040507050d020d0501171506040b010e041a0112062303 71
    0x21030000c0c52004822030905540f211314170002c00c02c254040c412100310380c0021b14050090784c1800b9000d04031030000b078621460503820b00d1400002020031350568000e0400e076199030105588e902c10803000307458141c03807803846030040940804145000003100c03544a0301c000001c0703038244840b80e50500000320041d10851102e0b1500e401410307a58050011174402d200820911031900c0c14050001c1c602a00d94114080c07144040000390302445d0006000811102c0900c2d10707180640e10400e91504081101031002011182c070601c8811028200000d064525015a1000700c40d15803500d000707a64111f8031181d440180c12140100340c1509240d00419031202c1981040d80c64026070381203080c100c0e40001c0444101c917690700c0040c4114400c0c03c481481854029005142420030415050701d0303144c001d04030300d12840d80c0c1d46407400c03182d008180c000725031040100200100d006d080306402480c1c031041d1031640051646084030442c08200d01c2580140c85000702c80f00e009005040021300302605400d9056858032 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 414087526 1250 414086276 414086287
    0xf0706020a02010c02120604120e040b06030604090614010303110c01050301031104050c0912030d0e2b09170a03030c05040b07170d050106021606080c121e090a0317160c0503 76
    0x120b04201321f500942c0304070b4091188606201c8010803170240c0c400198401c038105140c4880b182e607140c05698010f80c0c00c440000d40e8040728075064008218048030850b1819024000006242d0068a40c000808110040c0c4085030b05180045810384002d000c01481e2181c4648a550310303040581c8807641c0701e2114803446140a403c01d000484076503d0cc40021016031001803007110500035800b44031000c48141009044082c0144000e600d0415945265644440d00329107002e01c0d103110300b90440c01015092080c100c1a8118403441c1e4403400c0c10070065000c6800c00c4800c1502a00c1807040f20116480000a030341003240d00c1d40c131403085280c01c04610500320000c0c4204145114144100d40c005d2055800a000700340e40c00480092805495004405001c0701108000b0100c0601041b5080c0b11880703180301030300d030f40c4070700c00c01203944d03800c1d950343e01281050810890038000c0004c2a081480c040d40b0b801d16030254a48401d2850350b400c450440c03a1003116071601000d503028400c00c4805520540940c0d0604 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 414088776 1250 414087526 414087559
    0xa0b090111010f02072609190302150406020d1404050111070e1005010801080312011a0c0f0f2a012001020a090e070e0d0809030f010f020c0f0706020a02010c02 70
    0x1941c101c40720760f03031140d8001502803c00180c801001000c0c44003118921180181c036120f11064010010f04038010111120f84200c003a0312626400041c640c001d1540494075440b55031030070386412038000d01c005840b4443c03110280780c0c000d15030386102d1900048507030310703082c200320044501041c5200462114441d00d030000c1811440714101d0391040030081c80c840d001e40d2804000501d8580182d00100241c0c10401110318100c03182210107065503410070b545d4043d1b480030140704000e0302c1040c200c1d10190264980282c24190007081c0c0701c19034011241102e10808001c2205101c000741107405a51200e9089400304595005030b0401ca80c43c4001000101c030180303030522207401e90b40300200e4480040d106001c180410b90b501c05131550094003920748501030a50f52400301d10001156600079012800c04980180b250341c0400420a0041f1140020f10681081600a030701940100e4440302003405200c008141c03021001030180102c40e403c1e80107019140f4a5001900c4010f400e440507a0003440c00c14000203213 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 414090026 1250 414088776 414088781
    0x60f150405041a01020c06120a0213080f0a05070f0e22080408060601080121141c18050d050d03020c070506030f040b06120a081b0a031205010b03060a0b09011101 71
    0x1070f5030308400c4440c40190700d18002800e042e441d03420248600d0080c01412030048407520390641c040001c03a80144e0f9808002ca407001c3c3d2203000c1c0d00556151182e10f0502800c140040352070391000348900100d1b0f0001e504c4610f058000501030154004801c01200020f544c00d03c800c4c807000000204c910800a110110784800c0310f03550003a048420706500c12801c0c40080e5904c086410700425104840051600b84240301e6011010380180180410f40ca911000304401c00500c15804035102095240c550b00304040310280c02040300409240480e03110301800211400c1090f04c692606500c0006440302200d0800150f000b9000300c400a00c00c0d10800e45d01148944072078000718018510b10404503190b241500d40f078644101e00a1190f8014185d100d1050b0680b680000c4580d441540445001d4460044400001d2540c15041182085120300c01c2488107050f00010418040030f007003007050107181e813a0400440c15100035a83d141d00000400420015401e044003c0c08560030145010340138036603026529400d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 414091276 1250 414090026 414090041
    0x903030f0c030912030513151107032304030f1103010f1a0102010f09020d0b0705160b061f050a0c080904050c0c100903021209031005100501030e01060302060403080702180115080708060f15040504 86
    0xcc07410007041d02e2440030383c42c5100c01043da035262520f4542400c50b03691a60345618424000c044d040441403440ca25074080d004542d00040560b804c00c0b0b094900e07102629940e101705442805540b03814510f4016810500402c221a900500728038603040d019543c43c007043c40c0c000c050404114041c4208142808156080000c2500402c0502200c0c10204100f10301601800d80398509207489011484440d41c002080c0e0b0111000c9040144560455085c02c550520030100c502e54010714010030440301140000c00380805510000441d01c0031040000540116101070b00c020740540d111119454070840b880c00144406c0d85c0140c1500c4080d614880c10000351032095031281040b9002040a220a580c588554428000c091000340121480d68001c81c0c5284598000131b0f0203a400040c1c20015034607428490381814403110359602656a5800a542441007005524400200d59801090a86100b144030341d0242c0d40c003c20345014090841c0400070f0450218441c03041c10141408006500e0351035101ea00c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 414092526 1250 414091276 414091283
    0xa030b07051606021b0a020117070e04151a070c0e0403110f010b030606010302041a09040902120607080c0712122009030f0f100903030f0c030912030513151107 70
    0x10780b642d05c0d0040002c140201c00c0303815642039020031600305c00341c0ea0290035070300305080c410702038031685d01d5140d022a4a415841e100b90b402c075003400440b55070194200d034400121150032851010340100d03c500d08400c0e10844502818451443d8000e118140d1a441d540f41c0040c800d08192800d04110380d8000c1c248070003a03c54003110313550340e010710b5481e0509024560340620b091078110721309800c2900c2400000a5a813a10b0b407100c1c004241084140c8503688030104c2c0d00d8001340a4290740c416212440d55400c1d04440e00c5000800e09004070b03d100c0950704c1030f00e64441d0301c0b0301b40150110351000c040f581d0300e011000d12000183c80c1d202100602460320940c1c5164411648002d82c2e6402c10003d26251408011a00c3e09540c01150b4506d80098085003045112a4950780800c099601d070400710007500c441925203148603d4181c601c0250340c0c0650101101702d00c02c100b003040b214403542007a8201e40c02111017800502366029807000140100c0900000320090900002c0c1188610140318155081440100e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 414093776 1250 414092526 414092531
    0x7060c03090624050405060102070e09120c0f1006030c0905060a090c020d020114091f090b01060305070e01030912030b0307030c030b0403080a090f020d03110a060204060f020307020a030b07051606 86
    0x114403082002c890f1018000503503090015003007480000b0343c0c40c4154400c0604203511040030130f0001c20301740803010b02000ea00c8034294032441e16025958882810401c1c102032031107400d1041015503040e00810702143d030000c0901300003901d0b1100750340182400800950740280300082c042003000b218491540d02c1c22503035004011582d18400c0103402c40c1d50b50701c42118185020810490030150010302e481c01c448420903007070380040038215140040d20614000038548000d450011540039455032150340b041c20705075250308008602200550847d0b1000f01c003d001500303003c0341d0214050180d003146244550107422206440d6482d120201401e8694104a44601c0440140003c0c5070f401342c100e0f41c04c40022802048000ca80e03030b40d00c5600c1135045038000d0249914034040c001b41401107059069007010301050300c22041651030503c00942c494001c0d50040b41e2260101040984000306565030700307602403c001c04d40f900f582c0320300c50b03002e10040020003042002c010020308030103404000f03201184a810003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 414095026 1250 414093776 414093821
    0x1290f07060608031c06152d0806130507020c01050a09030203101a030619050a0e061510021605060d0213060809010b010518010e040605120a060f0c0507060c030906 72
    0x200441d515244181e840c001c0d05140c01802485801481d0102d004603600b08115002604c18a01c0300043d08c44500001101d034081541d0300361600000b1480c8550710499491111a00f602d002c10205d420a440740c40c010b0780855203101440d40031b54020716140005040c00158a95240c1c00030385800d242c00100003c081c3c481c045050800b03068030308204107440850280c25245004860100100004030311860150707202c0000c0f074074680301540020140d102007000d4401c40c4c40c0c280d200464541007410614002e00500010054403131010520b50145440c10055000846c988410001d01d90010740603442c94640c00c00200c3d40d500c1d020542d03207004111f1070300c80c00080c2c035010724046d084810400340c10b41480001c00440040405c01040c0748942c4000742007030201d1911480100300180155049107421281140400c00c0001d8005002c0020510540003440704404400d040c0040e140004001c1e0301280050040100180040d04640344c80c981e2850001045a190707114642503400c101c0101c1c180400b001c6a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 414096276 1250 414095026 414095047
    0x306060504051005100c020609040e0109021509101107090204080f070503150a0207050a05060108010b040b0406030503032a030712050703060b2a0a1a01290f0706060803 74
    0x941a0700024010600343d4403490000410760080710030101d0300170000c0742d944c100b0440da1000d00b60703009214040c20812608803c02c0c2d005009100002c4180e20942121203400c044128880840340c5805000d09410020200108280d4001e914400ca408aa00a00c1d4010411008a2001e00f00815081c00142009213040ca6030a00303019070383e00028000e40100c252400c0801c9001011741c0c1100032080c00698034186070901c5820031504d85070007040c1d80105d000016405005412084030f042c4126410021941042d0800c8121000c44c4401001d6400c140000355840245410301004400a80a580088001c001040c7e950b58003c54060021422a400c0ca030300d440d540703211b0395030b014400741002c11902d0700340020b9060b10f010301814040c02e2485030b4100000354098800c3ca5115040b040c0c101c54003465a460305c0d90310300003502c03080652810040000143c00c0003030914562036400804c010860403551105195103503014850030b8499800070000d000000c4c0305e900c104c1d401041410701440d1144000c14 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 414097526 1250 414096276 414096281
    0x50118030f0302030405120c010e070801020a1704120339030509010209240702030304090e060f0708040303020702210601080d03091e0c0b030406021905030c09091f0306060504 77
    0x1c00202010320510801c40040c0d00002e54014110100d0051b030b46404400d00c41030301600880f4034075001401a80d00000e1201d105401078214a441034450809022100c80040141d00b000c44003d4134400d111004001d2041c0250b001d205299242206400c40e0051a580c44264054030b505241c0c80c641300d010550b1041c0c0c3d140c81403a1300074155074000d6181c05a0600025140340042010002c40b04141451250308440e41c0c04845205a014041d02c0d1103a0780c81b100f1400800b4004155070f01401820300098003803401700c00b10b138800c860f103880340f071401c0d10759845c214000d42000c2022a0003070001c004011541e00d00c400b44d454103000b00d030300400302581441c2c01c183c1000e00b000c0c0c81134189400c098092000943d418102e031902c403140703948802200d4180c01c3c08101e0b1100c0d680840a108070020600091202d030f50014000e04029480e1803407265490041141d0310310041300e494a0510051210300407a04e008000c4942100040125003e54186a00000004a000d41c0102d940c1c5944079020041802c02e070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 414098776 1250 414097526 414097547
    0x3050a0b0a05151329100905100315050604090c020d02011b050309070f080d08010503070e010509150303130801060506040b1c091a04020f0916030e030705011803 71
    0xc1c1814465400d042c2d1119503c401c45400c0305100b150000c004004042d6076a10000d2680302140c2410100a84604040a81580c14100c10301418020800700324080c00381034500c045580180402c00104481c0400b100140244070340d1840c50240e60b08005100d56491010704050040000c0005401105940c081c2c83c01109140c81e1040d6410403102c0200d420706201d5032400381070141880359403a516007844d541800010f8001004010b054400490000000150840c1c04801c1c5e80b500c0300d481e46c1315020103a440c4031901c40c03525404000401072295082c2880c06680046c1303118100c0c000148080300190540d08518090750300d03840d409400308010076003405000000c041c04c0e82d51300e10381401d002d8103004a00c07420003190108542d130f0240107200401c6600c41064903411107000d01090000f141c603010424801c4c0c074140c0c895106454103180c9868000c5146018044144000d0f05072440c081c0c00740c003d020000d01c03c0344140070611541c000304a080c05141c0c21110866036001100100e40b40141141c1c2d2803 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 414100026 1250 414098776 414098791
    0xb0a030602090420041503290901060509030705120c0d03260f0703053403060503060907151b06050919080313020d06021305040509010b0303031603090c03050a0b 71
    0x2000c103508038041c20442e02568000c1b290000c03c10480c100550280000080f140e03000b0008028030324075603400b11000304520783c0c1110045030b00c0e43d0f542d1045506000d5114035590503041580c04200c1d03407400722030381c0d10311b14002030584440b003544900003003819600142c103034040f40c4002c0510074009541120f404000031540c080c203070582008020b8228449008208100f8190f903100130409843c00d03000584030003064a000362001800800c2c0e0611491007850480300424100714000ca06490086080391158600c6002421614588555a8001741100c1c0a820921440328501c80a1540c81c0c0080c2d1045405401c0200382410402ea8580c5881500000e0325004600020f0306000900140200ca40055003031026080100050001a100f050ba081000f081c4a01c0003400380004c5032480000003c6420440d0701b08102e80e56269032901380c60741e1891159050300108001001c444070190710f50000c0711b01d45030011b070150f0581e03603980626034503400907a400e6000c042c0b108208005000200e89c88441c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 414101276 1250 414100026 414100061
    0x30e0102180607050109150b09010911190504050301020c0f10060605040312050d0203071121041a0f07030504231c06090227130503120405010b0a0306020904 69
    0x30500400c44102000c0c140307051090344000390b540f051203000d400011400c0e0b0030040709144001b045000e68024000718805500640034400009a420590f00c1800d40c0c00500c80c11052a0110100c525401d0413034114020090080501011806813002d00c041d10310340c3d408000925000e01d813020040d180018900c0e4981400c2d0915600340b00f042d9019090305c080b00d038050085071104140b00d50a0703030799014401103040c00f58400300420801540c4558608011405401139803180301d8184100c21400a007601407100e4010104402c100c02d040b17071420118101041d5150794201040f0003034000c00d03648401003d0b800544c0100d03040c41144040400c81c440b41d00301c1310300454800c8001000c90b03441981503207400ea03034100e849588824041e0720b03005a240c45a005100403040894010000b40b80c2c0401c8290315085039180002801301e8085080440c441e41d0000002c48c00c002e091440c404505d10020400c803455502ca00048200f80c4a1034507000c051846000c0160305c640c0c1c040c1c00e002c1203c546000700020403c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 414102526 1250 414101276 414101287
    0x20307020a08031603050c0102040e07030501050906090c0a0f0e092e050307090207060b0d05060a1a0f0f0111010c0f1b0b060405061203030907080d05030403090b032d0601030e0102 79
    0x500e08606451350503410305000e07482e1020007240030f00a0145a226032000c402c580100030040354142c0c886416504100c0b101021510f0710018005100c60072030390b28070040c070300304640c042140c00350030344102c03551440ca01050b0401186d004a03005040a5403040b66490f8880e40c0c004100e90424207401005c000c10140c50401403030140020b07501c603607503c241a403003940080d0440c00d00c1456000030041820103400410b08c013004e4589035903103030412202840410b2800c120030404030450441c20000c21401043d80010456450030820b4070102030200724144036400c200d84035420000c3c050230944120750703260f04032310618000001d49008048000c0802900c1c10341c07044000989082c242c1500711605441c0018142d0b42d40b800b181e4508458a00110a480044100b1042c500300003070712829104420151104003046800985103400151002004107440360418800d0842c10b03030146520042407038041980d00207548030000001c149000c8000003004050420040d560107010b11b140c1000d19000031841d01 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 414103776 1250 414102526 414102547
    0x13030503122703071b2c0a02130905090c1f080609073924090f060c05070c060804050f120a0503060f0a262107051c020307020a0803 58
    0x30f103d8907070000e0002d0b245c416100c204003180104103014100e46130300c00d02d502080300100340a5110440200300740212880001c0c40c9001c450007901c03c0600c40100c584041414040b004c0050040101044468819070381c010f070603650345100d9042c00c4d8454281e008078010030741c03500800203c0024040c2d1700a911007801e05c100140d12214100c80c580d00c0542403001041071882c19500380d42c01d01c840b144070709655003029080c008590b10720031032000307014182c10ba80c61050b0f610405850f04801d000c2c045c600a488828081580c90f003005a20030201c0c500075250078095502c2840024803900301c80300094060007048100f007400c00040898400e10300041031042e42c5004400c3c01880391800c52420070401101041854440a8500f00b8040b0004c090000640c1c494a170380c0003400c03a980f184000004c0181303031840700c3d883c086101039050071000c110085001901c502104582c1c03080b0303021280703441054100d90f54009041082c040986070340d03014556400580c0100841c2c0c0000360020f00d4680c104200b9810b06 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 414105026 1250 414103776 414103783
    0x90906060c021804030905091014040626010204180c03050f0f1f2c010b0408060f1503100b010e010e030d08100305060112030f0f0c0305130305031227 66
    0xe280750555065600e41d503a185c100c9807116613070f1110ba0000400e00500c481c89a0a8281074142c0d44d0350b08a040344a41a82c04000aa030b41301d104081d05581e54015009440d81c0400008100304045000036180c242d0341c070750b00c41040d44510418804075544150615103190301d80a41c9400a032070310b4110748030b424a100e000d80d1038400501106440f6103061600710328040d081203810000c1960258a840481345210320340c1c1010004141c200d08400408008102420a58203941c180c0307109400a001580d110b40c02894006c078094600703492010380d07009001c1541e80400c030500c0112a45a000700b004003a083c0054848040d004030700d418000b2803022006952030005a01740022410700c1c01e02e113541c44030301c00b0094041454001410034000c140010440241203200b01071000d10a40e1007410185142c501200e802861116920008049005071030203c0c1c0f050700507103040a121a80244942d0380c80d03441d140366030312108624600e81580c01c10446406948100d6171015440e8420410f2a000b81d00b242644 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 414106276 1250 414105026 414105049
    0xc04080a0c03030816080a020903190602040f0503030f0a030c090b0a02011527091403120114040504031d031608150a020304050619061d241e0402090d03090906060c02 73
    0x4180e0780c040f6080c1200d680411042f000d1180e08458151301d4103142c00c1140c00780d40305000300403d1030b0348180c00107a039003400022145100004211641060502041107019145a500200c100210303401d010602015100041503070412607000002c0d0007214183d242c2d0050b140d03074442ca1600c1e0520301c00060448800040012a0040d4040043e52000c0d07482e1004100e49400b0f00c0f14660701c8080345100700c3c5884849000c1c16104200c080742c26850a410810003920001c0b10000c0020300d0214030b00810869110a2200c009401401d9503110306030009211035200c400e500880896010803403403a403034000f80c0446a0800b000b0344080d480c52800b0780341c07150b650074040c001080c00e0004c1c48050510fa00301c1d9200b100502034403020940d450200c00000030715100266103000103007083c2030300c0040c04182c2190b040e03607440003e412000800104140820500d980624075900280c08202e103900719034400c00c6105d6928401d45804070136600300040c0c102150040d811000a000403019450090794070380c00ea126 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 414107526 1250 414106276 414106291
    0x130c170106090c02030a0e2b06050a02070206070605180607030f051b040501050a050405031f05090706230d0507051309060f0b03060409021002100b0901030f06050c04080a0c0303081608 81
    0xc141105030100300e0464200c0c00d81c404240180c0c0032031084020584c81d00500309d008800600245d181c1c60804400c038860142c00070740c020820031580000819a80042e94858010b6070111701640c6484944e6061000864032070f000280c2e034104500b0b152001f40b04858100010702e8904290780e83c06221200248200d000e80f505105010410703000140c81441120003908000e01900d503030083c1807100702101d19074943c04403c8942000001a40200b00140310400c80b019681c03110f2040b513a0f6945410103807500b20750703900204801c010003010003400e4011280a030387c4c140e80d00c0d580d400c15005101d81006040e00074a103e10b00303091081207001041c118000c140c9404038030071590b1b911801c1c001001490710b201c0007900420b0300c000c0c200300240c000c00d4034807122101050502455000a04020101d8000d000040c01582078003035400200b0300940c40300303500036808001d4501d81600c60084c2840c11140c0a81114504800d070414010194029400e03034201003200c0e50074104403000c0c1000703000004c00600c0403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 414108776 1250 414107526 414107537
    0x2d10051b06012d180507030b090f0a1a04240b0301060815011715120102041a0708120f10140603040f0519030e0a0b04080312130c170106090c02030a 65
    0x207400c800c1d003140c80c1000b048040c60050030100c1c680d00b0b02c4040d0401b00d0341d05010070b1a2030040c101d2420100a0b99104030008682d1021a6440e40000401808150140c1500d50712000e9403120036220b030b1082c80312540c4200300e0008c1d00c008000e00c840c6184255000b9a25416043c40100700581d00050119084403101c3c060356025a50700e07004898024408030600c20000c0e0010600540c080500ca244000c50820b480e035240c0507040d00c003020b00740d108510941040743c2d041544a25200410310242002e2032154411600d007080d00c140210305a201559015944c810100a000e1581c0c914248100200000e84402c105800980c000510a000042010b08601a4010b62000b0410148419144090605907400d00e000075070900070501440e0103842030180d40d820b5008214140004165002c8540040065181400d107503080e4502a40241030b0802007007901c15080c000034402c1030000041d00020b030281e001300c0302c9c0407a003a0035980d05a025044051400d40f0003111aa801720403280a00c2150801 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 414110026 1250 414108776 414108839
    0xa08040f03020a0c0314010f1104030305090d080a050301060e04060f030809030f01022b060b160f020a090506030c01081b0a0509060a0314152d10051b0601 68
    0x9034180f14107440b00909400c0d00034004000c11050380e90101800d61510f00800120580c5070302601140d011640d270121b0308070f0603c0f003080064420001442080740241840503112101e03501e200ea207800440b048400300d0300110041c0310702507000e45940402032088800f8040382d03240a806d1482d1081500001d4058070000498a80307646080040c00c0d489003901d402156110701c0001065460705071a9544001c220140d925202d000e0800e006440540d002e002c0518a4080d031581c1600700c41c4007000c1d089407425600403440d0302590707036040784400a044071000825245012410503041402c442e10490620440205000310007801003062000b450301c00d81403e0351200c058038140d405000c2c0f2000310f030b400000051400d03c5198140c007d00f800400c121a07107111a1035941810780030224070100c45030000801c4019070b1116602c055050121030310f0038000c80c41c210314500440d1036940d11800c2000070480004190660a8640242200c096414000340486504200a8101c03140c115107562070b1350707003101c4c14 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 414111276 1250 414110026 414110033
    0x17040b0901020c0a031809020301150807020a1a0f06030a120e01030f09080c0d050c0d0e131a1516060c0e0a030506091b060d05070306180608010606050a08040f 70
    0x1100c961011910484c1d0382101e4515004050500340c29001401001ca42800100380b4030324004e5038142c4403d04241c280c85c2c040d0343d20031500c4180041c01681141308803000300000c9041100301254201c6809083c2c3c8881c64404d1440c540c0041c060515030103540800501c1003c2042046103860780c54051070300321b10721800b00340100c01400a2442040c0c5103032404072020204484c3ca00102001079101054070000264102c05990902508132180c0c450340125143e400590300c651204198400c00410300c502801e031100d840000c840b40b0f501001c0148010451101c1d01381742c6040c00c040e1581050b00d00720f2a08000c02c40d0008806400b8030300408064a84500c078814502501044188601c0031784401c40c0ca980e20b04042e543c039030046d509840540a4600c900f4a14500d80741d030001c0c0c000c0301520003172a01c00d80c0f031000001400c0041c481d00805a80702070204013403003000005c00c200300d10444080780050601c58200d086134096400390052003030400007040314940010207198050740005d82b10070031480724203 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 414112526 1250 414111276 414111281
    0x1208091908010c02060901140108060f06010309060204090e0c0303090a0b07061805100f0b010f121d1506182205060a091103070303081b0d0e01050f0717040b0901 71
    0x100460929401c10050f044400c3e40002c0c1ca501c117680c501c0082c00074140030a045a0390100c00c0c003468600b50003420009454010580b4001c0e003104062500048034089c58440c60126000380e0010b5001a4075403c2d800180340c02004001001c4104a02641c6401042c2e000250307034507914407d03105107580c00300b10b510178001c1560218032045011b81e00a108a005450016143c010640307404109600c0d0450340d00b0616000d2041c0a0b4001c0306031103418400300003a034103903070308900d1500042031540ca94142002280c020308500310040041c40003000038400300180360f1210381d002082240510006050010311404050f6074613041581740c402689070400041a01030380d06805076002d00548203403002e200d096861540a0025030340948200114800c480c0101500c40a05110241c00118400082064203a0a440c03030740704c03166006001440c2c400ca0801060a076940b864000364142d56030020000c40144641481d5070000701483c04c88518071131050690700c54440904007900c80018800007948840095 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 414113776 1250 414112526 414112529
    0x170708030f040315180624030309180b03030d11041a0409050c0901021f15030f0b0702070303052205040207060905010609090b040212150103030203040f12080919 71
    0x900580e5a1040c10503207040480d44903200c2251842071044030320407007124520820305202ea41c1681901e00080a8070740c0300c003030003c21360007041f00302c4d10071030b0960851038858420300114800c1d00c43c0c1000d40e16000c4025180341d600058880d030759041c402c94400543c3d01200b118070010302250005a01007140e003201c000f41c0200d4000107818200b8082e20342411381001c000e0011030395480814000340d5107040344000d007070007034410003030140c0d0129032a01085c5009901980428916410001d201d4043c60b01e91000c9140d00ea001f40c1c0c078403440010050a0100c600011903110515000a0400b1451641e000f001c42c411030210034124844614410007a4500703036844801030200a0095445040c00d04144008141010084545620301080043d80001c1ea0042c12102c1c2e800103081001941d56400b03010014981d2076110030b140c000d90310740d035602c4080c8281c1140030314041c0d8019602c2d070b81050b24914081ea030940001f000038806110701c5c1c00084400d001c82d02c1c1c2550a0750001c0b0407094404410002030b046 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 414115026 1250 414113776 414113789
    0x31e0b090102031f080a060e120a0e030d02010507080403180b030403030f06230f030a240506010206360106090c0e09040c1502030712080711161707 65
    0x1844140311044405402550242c550395000e408903000100302e18984c40350910640201c1e8000c1c0071141d004c00e006500c8803c24910120544552621144c00d9060780ea00019025001c5040d19012255606041101400503a0079000801150510010250080750300500c02410005200c1c1d4180c0040502c0109000a15030020350716105d0500f841c024026203206511450b015141050009070082c5150f00c541441240525494480c44a07a082c0600800300707400c80f81c0c0510401c5d091000280004c401d505103511148981084404401d521009840c0081c09181c1150b12820920540320f0b00d080390001640d400e0005159140880c00100f092074104025064180d441c01c9000112114103802500034144e007656061480454142008450001510b010b880148164818044000b003680000c0700c3c13014600403203041040c96a01d0132203080c0c04101d5440000d24141c14001d140360445601d484500002014001250041401000c850751610a0141070501318040d00f804250074032920340508071 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 414116276 1250 414115026 414115043
    0xf06010b0405010f020d0e0d02040b100305040203070905011a0901030b0a060302130b0408030d050c07080c03040e0606091e0f040e010b0f010c0312150e07080106020111070c031e 78
    0xd48115600941e0054891180403480130280b0340340756440840c000705002020303165040b00b1444401030002d00070f0a8031080360066660740c0c030f40520703070764544a585da081031a039004681450107105150504615610103903499040200502000d002c000c0c20010b010641105992240c80301c40048010f040a40c0c01c0a400c035841d0b18022034110390503002850415880300a100710207a9417030007458181303e24450b801c02a00701b0300c0000e0510289410082d003001140710f6032801e03c101a2205416544040c00903a440c0e03200041c200081540f01594aa002804880769400c02090303d02103441c54138554204420300b008102e141d1503070ba03602c603000c00d20300c0000360040102a15900085009003000c054042c844d4079000a40840c0350310a0086070011395150f03a43c952004003000403200581041c8074008444131201a001c0792031851111050b1203071415503103140095140050180c02c45503114400c0755070402c10001c0e4400319409107070780b004580d03000c9a0f01c11644c01d4040310701414602c0050040c00300c10b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 414117526 1250 414116276 414116279
    0x1083007030c0303051b03040f03020715121401030b04110102190f050f060105060f0f0d0207050105040c090e0c01050f0c010608070f060309120e122410060903140f0601 74
    0x141d10003084404944252010401e41c0c6602054121a60001c1b100b1803010302d0410002d00020140c0f40468001803081c0100c1e424039446031a0840300c21000c02c107060029900400001001c01c4038001c601c00c00c40d0401142e507003541107840345180d03080c3c0103102038500304030340d0000788050f403007004550a51a00940c602c0100400c034509124194985001650320b0700c50001c0001c81000b0108100381260001484d441c0340840c800c205007025013100c1400300c0800320070f0200c02c1c260b14160009041c0a8403400002030f040c80d051405d030702111201d03002591402d1034103903110820000042c001d068074000b4241180c8076a04420301c1d80c56481402c5080c20365509000c0001480400083c07554262070440203440c00007915070508034103d4a0030300f800342084840c0007007042c1341801070011043c01398018004820b40b200d0103110301e242403401c1103000c0d1084640d0304010318107481c00c68000e400030640660061040d15040c8028003103105800040c01c540d42a8030840100ca000b04600c2018000e141c0a442407036 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 414118776 1250 414117526 414117533
    0x40209030a0c061710080d0809010618022502061c11161202030901020303180307021207090b0d0c0504110c010507080a1b090e0a1103090d030c0801083007 68
    0x60131aa02114440f55003100855109503150103000140c42480004101000c181c0500301c86404005e00815000c0d56101c1c0040341030b83c80040c1c2e0302c0302024600c101503a90314030205d41040e400e1482030701750f001c40351901c04d110050756000205c8480601c1e01c650f100545034035100345002405411000100410001401d54020702c2c1409000525030149003941c00344a032a40090b85c42c0c3c4202003405006030400c00c000707503907500c0c83d9030040080c803003034800ca03400c2c074150341d01088100800c40003900311540080420070a04405001c2d03407035071440680710300020010307690314480101854056a032090b40c40300c1000c440c845041e011b03103c01c000400b00901c803070b08019001800c103000640e5402001400c04400303c85403100c0304d00d075296514550361742004042c035044030b01110340c0e0042e0222800a4503002c8404e224440c039170245005009100140201018400019007111200350111043c008501c00420101c8d00c081000da190600e41d0000304400b240102c092890001501c064807404900490080c042c03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 414120026 1250 414118776 414118787
    0x1d060103200d0e0a0f02040506060a0912061b02210a021e0a050a0809040614030a12031e061805010602031c0908030112031101020f0f130f0e0a0606080105010e040209030a0c06 77
    0x110700035102000a501d9249c1882502e03c42d0002d048003007110b0703081c02c1180c4500d450540e01841d0042c0e44c00508075414031007090300782030040103210059000240c01300558102c02301c1c6035081201c03400705078034280250702c0c040d456001030300281001100d0003003010b4011505006c40e40c29070360b00005503110700c140391511068580200144c0d41c011860000041556880c44036242101c02e0000d00a2020f0841075490ba201110110308120070151174031561900150405030708000010000c401080d41401d0140b801b400032942c0120031402030505004000054012080f200010710664503000100c032910402d0004e0005110b00800703180e400400020b40803201200311407454481e03a683d554240070010320034241d006449002c03480003020010510f0b940201c00c0100301519002d076080d00000d0b540c80707001d000340c421907100440714407810040210040e468455000030309002c0c10321101e00e5041070002400f600c1244000d5010f150f00195000440e50f0400c4007080c1c8990254414070902d4607150000c10 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 414121276 1250 414120026 414120053
    0xd030504140307061b020409080d020c0c090403080f090f10020a0e0a210c080604051f050907030807080d05090f07060e03060604150f1d060103200d0e0a 67
    0x1d0303104100c0e00c9a030003480d010400904071149540c446520314103614042c29126480003003241e002d40e5070741c144000502450050031100302080b400603100c000b042041c500701102c0c2c0b400c00303225410040410000a810450007034108503c0c84941100d1307901d040c1c1c1c0e10318061201008241030301c110290100050342c0ba800420342040380742d5450708000e5444003408520302d028000c400340d100c0c80300b900f586440300e40c05a5041c040d006041c5c0d0b0381a95958815281010020f4a05403599005070070980c03290300108c00c01046600758502d08021b40d00d0221002902e445150200510042e800920744080c046100e00b610140c44007030740b0401c10b030306018000359a140c0d007480042241d4010450b0004c3c141c1d005544042c1d0410b40a4060211540c401040000402041d000550027017002440801c400030101010300c0500807107012070520ba01c843e04074643c1584018010ba0405080588007000c4083d0baa10b500c050061b1284080c0d180c40382c2c4403001d4054440c1401002503807107154001c20074040c8151440c030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 414122526 1250 414121276 414121289
    0x70f0809041119050c1014070e0108010b04060e0f102003070c09050a11030924090a060903030b190f0603020306091506190507050d02061306020304020a050d030504 72
    0x1142c607030003295410803805501c1d142d198211054402561090003080100b68600e1010252100d0300904248107044482141c070349114a00e41c441049101ca80000c481c044000003420170442c40d61501d9030703c4905205600601c2c040001d08100380390dd42c1c0b56501d1014048100400d05035919109070001048980888030110b09044c131142c84004a04005c41101ca009400844055200381802516805404040c100350340055032180e060801e00112800740d4002d020102c080c00314402e000788441c10507101c1c9000230440c6082101840145207000494040640c0e201030003041c1060325007410340003812401584c0341c0047c0b14030160300c0c0c04004198228143c8414501171640c2540342c460032812400b04035800350300301c8401c0c0301003500341f05201201d118609001f05428500302103507955801d20784040e0042e501040011904000300042403220b1464105a44001c0507203107040044400720700c001540161440c0c0d0300001180c05e41d00c1c1d00e80400003800c406844d000c1c0000c07080c600103141d07034000d04c19803 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 414123776 1250 414122526 414122531
    0x120f010e130303110706050c04140604050913030c060f1d010207110127060e120c06040915030203010e060712050402010806060f120c0d0e06130f0305070f080904 71
    0x426500c0c2024209805110400380590103840140e074281d0041290500c01d5040c800144070003000164030340100ba1042c640d0f407051a0300c580c03400c40d00b400189030b8103404038841c450a0009001c1070b120194040c4d405604101001d50510031401c080d1442c203a801c1e03002c0d002c2070604074034a900700800c1d085460407000c40c546181300b40d200240840d080380075040c0c000380410181c0b603200910b50701c25036001a070108241d040d40c103070414405600e0122070240e84117101003202500c0709405071606601000c41034074910b0250006485c1240012001d201d5401090211a0384d444040907c4400c5150640030710ba016000300171140c4c0725034905580302c0084803480c00240100204040003002c90103260300596041c1c5580c2542d8661b80b04009460b0024140112800001d22840e041a07441c2540a030044c1d0300084050354509d2800322600c20380e40c540f10007450a60000085c00f190200b0301165500d5250000740c42100c1c4000383c901128280301703803440900b1071840c9207415400e10840c080103045441c0200e508 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 414125026 1250 414123776 414123779
    0xc06110913021c0501030f0303020309030c06040b040c0503033606120604061514030403030b1801080d020d0905100504030209010b090301051521071d0f0106030207020d03030c02030f120f01 83
    0x40f48107075102404001e2024043e4209030300081d00a8002e150041e03a42130550f4104844140810b207000021682543c82d214504144420b1100e0310603003001a10040d0003451401300030030790003a249907032440042180345042800a40c0b0002010820076890740c01041c190750b5085604810720103402c1038442c0c52059180c08000111009107604000c0003000030b403a011800082081744032156080184150249070300c6200780b44a664078154003800301e55103400c41e80142d50500b14400c1c83e21a04200050035540541c02d400f2010360406140030840e0001c80d40c9802801100d40200c426018a60000b90060350450010070503414004c05456005404e400800907641d034183c0b04250500110707841d41d044412406040702078422036594421500c0c2d502c0445001a80d164080007090005d61074600b41c406125082c001c4043e0820020360040c00c80c0c0c6415420500f00350000b0321300f102502c500400307040e580d0f18060742090091007034411075600402ca2a48510303142820314081c4134221080440640304800 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 414126276 1250 414125026 414125077
    0xf05090601020706020d031109040603080d1d0c190f08060a1103070e04090c0308030a0c03050f0c0405090405070807030c0602010e2107030903080c010c080c0a0c0611091302 76
    0x2e0110131520554018200e1070000312040e00240000e5041482c58542003080c402c1d242c543e4000e0000961198405076910600c1204a1044806189002d004104580352910036540000b4490700081c000700c2d080b0038603501401070301401d100c55a0100500d410211400206a5004920301e40304102481c1e040c06030b40c0c2d08034108165444125101c001040400600c0703107607400c251303010280703c0380304800c501640e5840b9100d40314903400c02c5a1020b11503403145501d02c5043d80c180a4290410403035104c060060405200844060045005540c025044400014180701d400c1100c500240071490075107500d103490f810304203e40683c6015110240d0300303104d04040e40c2d03240083c00400d4084280c4001c4450400b1610205081e44401003d4082104002d804408141810018604496034000010758030b980c03031501404111000300342002e070007010b06c120458079420124050141c3e5101d00005541c100e180c20020640c0070b0b0540064211030300b62510310680b92154020410110740b0180c04030141e18081 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 414127526 1250 414126276 414126283
    0xe09100308041a07050709051504140703020307050427060b03060d020f01050c03030f06040e0a0809242205060414062d09040c03053306040f0509060102 67
    0x40020300744941000308006680049000f000780c22880008140307000070b83d8603080d00d0450f05401180c0c481d81e507035091182c41c1c2c480050f0944070a405a40c02d0018035000700101801100080018092603000000500c416206400700c0e03024007081d10080c011415420340c00e002c0d4024150f02000703501d00e0310300089000b0281d541600c1c41124000c2c202d00a03019941d091040107801c50030307420305010091041040c1c04205101441c4038452000d88154180f03400300401007910742d0580030529680107039100740d01095210040b9035591605035140e90b0100c1041a0121000c05c0048428512450200b403210340c241e800c084c0c0060b00070280d44410641516401000214400c51154028010200f0361941b00760620b140540301d90700b121400ca40072900c202d003407400441c652040310707440303a00005035202c1545030070312030700340e00c01518a000c20181ca0200c40404c4e4203d0f038a181a0601c21014801d52202e0036980110350300300d84040c100c152180c0c6e458426403882c841500960380b0030028040003e85070b51000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 414128776 1250 414127526 414127529
    0x50a0b15030613030201020d110309011b02030a0c021305040302010b091005180a0b031e011506050409021602100f0206011a0a05030c1909061710050126070e0910 71
    0x1d000d40100c3c0c4400c800c8428900110000b02c0c00c1d55002d01c000741004419100e451803403030b865411035542c1d1400c28003c1e821142445103102c80042e0701001c0c84c5a0350382c000240c03040c1d02d14909021030780002e140001103d2800002d64a98028100305c00c210804da419046045203010658480c403030754413001000309903c0c0c802e0203001d400040c001e44065112125030328960308814040c4c000070f4100801c002184c00d003803d11003c270140d10420001da6200000c02d204021079035240a250300d80150811030020510f1107680301c1c0c1101240c020952100c18801404202103181c2e0080103001d40540c81d44002e00b980300c0ca1b03400d91001d80520000040d14064051040d1180488203031282d140c140290801e0352503400107001c02d07203085810301032040c0c40c0150b000a2092191103407191400945003000081c1414034800c2580111100c220034040c0c1c50301d8401038101918424209a2407034640390302c040a08443d00c904070400ca00260b424000c20703d0304202d4405519000b03842221250750342c1031100000708420b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 414130026 1250 414128776 414128779
    0x70c0b0703032d0c090e07080414030a140901033312120507050a050d0503040b0916050f030307060f020a0206061e0409030905031e160506070f02060c030403050a0b15 73
    0x42900c10f442c55041e030b000550b03580860620f20901a2100a0300010305421200440842d03000000d210500462a1b05418446e00c00c500640c903000001e00001c00d000c2d90043c031b81e0940b05022a540b94142e000e0303001303d850078a000c400c82180101d00c0c4408030020b46040c3c45070071405000000400c241560f261f041000030781140300241440803018007117803d42d01550302652a0b0003000d48000c0050000d211203114420180e480360703180c0c1402c1c24038000d401d101605940440d80b0880d0350782c9991312600484400c40c1c45c00c644154448800300c0203c0d00314864010000e0031613140c41060b02401907150702a0809542c69400c0f0303815642c459090280d84444034003d440070315a689851b03052441c00c1d81050707980b648030b0304e00410456503400120f49014800031111302c805404040203d1907090070000c444c1000c54003200e1101c61440c00c404105140f2907910080d0000380b822201c002552a00c9080301d01c0100c0f8242140d949540d00e050581d1604504030040b00c007243c80001040c400e0078070301d0b6030781c400410 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 414131276 1250 414130026 414130091
    0x609010902130b180c040e01030b100f030f03030e071703070b01050f150715020f0c0d0f1706270a05070302090619030902130b19030308060d08070c0b070303 69
    0x1001c0081c0304c090740007851031520010411001c9581103042c0a0076000714807881c1000403e0500b0140c5000303c0d00d0302d40000103c1121703031000304041110b1021052907079270581400a045c002e80000c0c24100441c13500070b0034040f0101000d0a0082c0c2c000402040d0550260211201c0c80c4d0300c42c1d0401600380951180698008012554070481038072200013040e038584503c0e40104412640810442640c120715481900b03400042280d40007414144000d0750b40300a03a02e03002074942e001d007070b000d00720340c003164090607002e02c41e42c0005102da1a2840c3c01d000720085400c41d80c04052510518818044007125405c002906110100e22024007038000e1f6811484010642c5040c900c0c19003800c0620707410039282d90304050f111070f601000341e26503190302252446400c202240c03a021850500205003401c030026038981c42488020400300794441a4150401c00c00c98010411200d5803c01075030314094500b011707003042c5800d4030015005500100608140d8803c3c1c41c24818000c0c1d4040c034200040e0010750401c01c041 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 414132526 1250 414131276 414131299
    0x2300d12050912160219081e1b03010905100c0f090305031e12040b071b020a0e130501020a200d0e040b0613030804060e09090a1707050609010902130b 66
    0x2003c0042c00e0030f00c09208840750040c0755034000031540640700180c5650101038010034008005d0034024005120910a1110300300800465142d0707035822209240c0784545202d0003e15403607130703003908401285908202281c49900c40480a0310081c03070176030b0746003020402581c05040c07001c1c05030b481c200c100d9800c50040c3d03003400c03a5061283c11020f820460300446400801c00b440310b1a10781c1c0174a40c0603034014003080c001894129009401d101070b0f4468028411901e03100d2000590328441001c082d21002c0112048a4607061180b200c0d0410500b4000c00035400882d00c82031803944030210340040e4011410240480c8000704070603446c3d0001820507000602c062210000c681490b4010382c081c17040150070240341100c20200d220780114541c004031042400041d00b004120b902800003090b11004403010b5016040034413406035180000500100901d591991803115450303d40240c420460f00402a900d6502d03008000d94024908036000300c2c4500703c020342c40c0080380c25505ca06c860000b400b070910001031 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 414133776 1250 414132526 414132553
    0x18010206011a0331110415120303020c030a05030403030b18040b07090815011401050301052d0405070f021219030b030c030d0f140306060702300d120509 67
    0x2640010301c8124403001c8540303001842070995507519500b1030500c11200b405070181c41d15160090002096621036400c100c4040341e00442c7d00011421640740ca50001504102031800b03502a01501c42010a01d000109003a203265401070000d51041d4131942c1c04001c40c101000401c900e804e0a01101008000070030005000941c3c0c50844030b400c134400b8102254896501c800e65880c200d104107070100c040b8507000041010040a80410f2003000003403c283c0e04540c1890041032105980000d40701010040c2012400034408640e0070071b048400241c0284030b07a241c440000f40a03030f100741d00d0010051141382c001d4480c013500141628a0360f2300c442d04a0840d602c2d90340c403ca01800c0c0500350742da8540a075001100c465a0100000311628005486038041c840815030301070700842000c4c080300c5001c01c04004003c4c0995404003110b94403a4100c50824101030301000725020075024590110b1901d5a0000c00c0400c0307400042c003052071101c1c40e520740101141480e00b100070340343c003910180540d0f0f20070302c00990f58 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 414135026 1250 414133776 414133829
    0x40206030403022d0f0703020d031215090501150c030504060f02100c0801050a0f060f08150a090e120c0a080f0f0a0f090e0603060c03090c060f1801020601 68
    0xc1e000e44101c42a15500d000c03003d035000101c0142d40d403d00e039903256013944600b082c42030801030000c1c1c0001d00140c62450b008503000d100d081200808110320a0b04940700520703154481e0151040c10201c0748100ca40341c03110107004100a004503c1a205540c1c6100c2d2018070819542c40000e80c5540c03802c2c201f62034540c094581c02c100082034000d42c06a4800c5110000480c441e0006001460b95400560352411007030150b03025a40d00324456842ca01c50f81404001e80004108608205526190340705070303241c4041c22900d41d01213000c0c6500c003408a900007035020458000a1100c3d04400586d0110b90140d105068648200b8104005035040250600301003400c00014000400040d03800d81c0c0307061880072611806a02007281600400e520362142034400b80d0003070144010341800c007130038205402d0100009070f4844006000b00c030310300c0d00000002c89040e000d1107841c018001c0500026100c05d03850710311090b1038115400c00344802e50480b00ac140c20b5880014243d040714011820010800380042c1240c48 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 414136276 1250 414135026 414135031
    0x3021c1514040e060c0702040501061701061209050d030903020706050909010e0603120a0309030206060a062c061606140412030c0302120c070b010906050f04021815030f090304030b04020603 83
    0x1482a0b0703d07200ca0060760301c24000c02d44206201103110b07a90302100d104101c00c039001a0071000801c01000110303584500d42400c458150741d11420603594004074103242c40060003001c84010203601807104048141034040c4c0115010314426000d03a00b1306901c500044800e801545103050303000c0c0c3c04070010030113285140c802c41d40102010303098a04c01a10072a240c07a40e588544058800a90368600fa90141035051004540098044400e40720191034458010901d0700c811103001200884055103074080c0c410b200c00d40c0400e00c00607011644401c1000e040c1a0311082c501c000f981e50509008000d11000400034080d407250b9804012340c1440e1150440c210020440c02015406040c0c0c2000f4142d00322010132429032140d200003465603a2a00389240003040e083d41a480b00e081036040c000c2c2408240d40743c102003000990b0941d40180c4a03151051408103206842d00003a0300414422070340c84ca40e482d5140114030600d007814a03c002e035158280c62603580e101703134400905000360090200b4014a0400011034 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 414137526 1250 414136276 414136279
    0xa03050f16051e030103081206030a081210081b0f0d020a0b0310030203030f0d0c0e03061b0f030a0204060908280204020d05010b0d0605011430040303021c1514 70
    0xb1043d1907461204030b2640e1080e0010380d42d01c0d401003100d070030014201c140c1544c854800c2e0050f00600ca81030361504143c3c0118841c01d41380c108039030006062280002031040003808040115000c40780c00315004108044107443c0b103800341e444008400d04074102507491003603065000e4541100d1038070b403031a020036941018000b41000c1081c3e84000015035803c101034140200075004250740c44106a4050040f40e142104542c01d005c0c101c842e2402c01d42c0c0104009910105200c07504590604c0c818450100d44103000c0c4083c1100b9001c0103002c9141c80c20350240043c0c0310140c8443c0c94103511a00015920304a098035026a05042442c0300401e042c080d42c409060fa10107400035041c40502100002501c000b60400482c41601050441e006656402240000d10082c20898140250070b240c0301210701c900d162425400450380a14034294025035000c08945092042158040c140703858000d000c1d50214221202d8040900152002c00107070384951203000c00c0b5040c0c0d007075034980341c113062440300040b840702907 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 414138776 1250 414137526 414137557
    0x21030417040f0801020307080a1401060f023a0c11040b0a05040f1e020f040e070233160206061011030f0702130b01080406091e05030a03050f1605 64
    0xb000039541c1414805400300800243e12460b00f144000c000c1c1100826032a001030a010384490304082c51141907041d14907a180c041da10680c074480a0b132425502404604078841980343c9001a1545d0340f4a8110910709100c400c0740d00c00031700804440503040840003618030301200c5540b41d400d01d083d80c002c0c840c80001a01c0303a0209070391000010100e62052240c85602500c803040100c10a29a0175100c54900e0120b0007141050001988c05d881c5020318000c44090301d09000102d4142c42c000c1151100d4481074900701880e080340402100c0c24066a48000f00030b04020501003410b820845400c817800c1c4c0c150368010522955010100140b048007101c18600340250039a83d8061004240000c1c90340c4410305030150782d180000d10500030109241011050480d1401440701040e0703a002607090b400c240c000c40c000c1110100c50415444e800c1e0031852485405800103160300411030007001801801d0a1901c00300078683e40c25804940d0320004a0722115901074030104843c81130b0003000034040d80c03141c2d00d050 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 414140026 1250 414138776 414138779
    0x50304060318060507020f0637060e0705040806070e1008040f050304060f021005060603010608040809060a120f050403020304180e06070905030706170a0c11010c0801082103041704 79
    0x1082c080304e205451850058118a5a106940070f082081941000b61001d03005180d03000d00015005a502c1514a110004c82c000c003588100c0340e86401c9840601603088281c1510304200314041c000303500500c980510340c041e20f00011000c50080c445400ae48401400cac171680410500d01c00c6540e46c100038021641440f44002c400c0205004002400182c110750321049400c000c10b980180c43e05048004044055062070b0030000355442d8101641e044402e030342001e000c1c035100d0b03261102c4180110022150005400b00d1a00c1c096a44441d10002011000c2c4080082c41c034481d0251080c4d40e0103c6028025030b02c1040100302001c00701020910f07549031001d000403505030040c0880c0c2440000e03551000094000b6100b4415071606110b900010a21410102c41e0100703c05240310360741c1001010039061990712001e031102c03907005c4d90280c80c100b01d100000300044809030130081c11000083c00ba070300c15445000302d22580c0010701c1003c25071000c5240031013030444e40c4075610784c4481030003035040c1014494140030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 414141276 1250 414140026 414140033
    0x20f010c0609060501050127270903391209091a010201060b120a090c120c090612020603060607020406050a030b01031a01180905120d0204080d0507050304060318 71
    0xb4401c00ca8428903021505501d40700005001e828548084440100740720f0507404552040d20320f40040307403034814141c10185450500260203030080159604031a007001900300c10180d21070540030304400d4221045c40c03424103110030414806170000c035000c0d100102c3c594040114420203402d1140781c01d94907104c0411a180d242c2902a210b946404840045070800c03072030019a028004c180c0945a0410520f041c9041d03660900307840200604075101c0303140e543c2e0f507000c2404036014200c1c002d054203806106009038640f42c41c41c242c00c1248128502186000c402081d085040ba00c201d030200c1e0014034150a546901003003000f10707446140101c0e030140e603590300001d158482c040350100542c09020018915071541c14003210001c2c5444110134106681001404106404140603002e110580d400082c2d060302ca01d003041c9889002c20f1307010840c1c0b0000c900100400c100760020300544840409a42880c0760340c0606560038005d08000a2140c0c00600040c007640e48640c0c022001100a07401032610020f0549 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 414142526 1250 414141276 414141281
    0x22e0603060603110306060a03080a0207240e04050c040b0c0c090f0a0b01020a030c030518040204080c010908030405090c0a02010612080a0e0d03080121061a0306010b090d020f010c06 80
    0x510440740e041d1192410828012180a025200c01090340904040d00d00107002880c0800c541c04004c1c0002c04c0400e52070001c40c805c01c9400e0240c07054010030000072024019100c0355001c074108903800144d440b801d400c000c0c1030074010303540540a48029a0b00741821700f1406082500102a09100d07403040215091044d500c0b280e949002e40b6280c0701d503101d40e0800f106c0110549980304101c0381594841418840043d42c0404500450380d00b5107469074951039001151100d280907600d00aa12070b002150108200304080356031b10b8010401d81b00c07816402d545c0e1409684034040c40c49601d5002c078404000400c1e13407000303c1c02000520b0041c400041c4440e150035000307401c122101000c3d15951008a1910032240d0007400b82c841d60740f4216210b014a51107030754010034100050040d18503118107440e070071404910494002c012641d1024042c0801c5c080c002d140c182c00e61000316450710a10849000081300f40088017100c0c4260800f85c141122500f140d02407002c0303500340050903410407a0300100300c03020a1891 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 414143776 1250 414142526 414142529
    0x705060a0228090e06060d2a11100c14040b1206011707181206050708011e060302030417030a090203101a0409020a0e0f061f022e06 58
    0x3039900503281c8880b01031103039001401c04900e050001c0796041c4600e240c0d030810400400c80303c43c442e140342c80f03540c3e003404981d280c014641c04418490030200f02e80040440084e4810350403030517034541400413260f0f12089075000f0941841c010141c0101140c000010416003056600040c83d00f0301d10b0149049105400007540168044410108041a03c103502c424508a0940200c42441c10500040b00030051403405070022740b110060200c20305900c0c12160502c10f4100040c00c0c000c14841c01800c407400d2000140008640745400250b004c0004078080418401c1c103240b2030340300d4440070211800d2800647c02540064002d82d840480160114407099100f8010b40c4162111300c0080740c54002441070600d0644e40c03510604215080181000b55901b00100c44034948030200c03804200c80a01e4004034003003502c540c00503441882903400b00a40070604a22035401a101034916851840504081c036180c00750004032a00160420308480c1600030012034120442228480d0001d1002c040e02003803c00c44031903 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 414145026 1250 414143776 414143791
    0x3030705100605030c0411030f100f080f1005010e040321020a02030c0706021207021c0f0b070f02030405150309010b1e0102010b04090b070f180e0f060109030308130602070506 77
    0x228001070001c0c4c1030a006081d01c12100352414040240c40d65518503460100038005c02a034412100090140070112150000034800da50702142170700d80322010f89441d0400b2101c10a00380c420601c19840e0600d4901c078582c12a01420780ca011203032a656070031110350b00c071504014400507078400717440d8002c00180b00400c0750340421b400440d81c6054031040581031401c91b42c00b503015034204801c140900080343d4212422181d040718554940d0140f0b0312201101e03c4031660290080340d85001a00801180c145400c4c0140000d4031060703591195100d049940e8403483c022a40c100c10741310407590750000010007440d04a030781000040381d400002c0d00811483e4990404d0941140d0000640c00c50a50b02881414040b040035501841805140c0e1241c1801c260042c0648041019403466400d03a01c0c425100d030106121094203250038243d690745ca840c840c4200340e51504034043e124002c101c0940c040d40049088a501d601c0e64a107582d500c00d002000400f1030f50059a400c0e408100200010b40d007403021900ca41170 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 414146276 1250 414145026 414145031
    0x60f031202070f0902070206120c1b190b06010e030d050301140108090c09190f0917090108070e0607060e0304090507020718050a060902070606140f0f0603060303070510 74
    0x14504102000c11412100c0d0415504aa401408500321500040041e074520b0400542d6031803481c0f0100b030750780c441c2041500587d1040c030700340041500d94000510250000081c4101c800c01c1810005454038007191380d0071500310504e100400005d08800c052544520141085102c401c0e00402007414850b0705038903100003640c000014480361648404c16013280c0000c2c81c02100602c1c1c07581c4203643c0c85500050461003001d885000900101c0707543e000c0c2c50701c0f0501039414004505194140c80c003400034500221042c04001c02e4071021006002c0940d4003440d030503035902149445076101910401552208190080001c010500101c1c00b42c0c0255650700d1201e500841c0e81e240382a6081085407070107032100003150800e0700200311019100011200c0740032000800503403a101c80400d10020840c82c2c0c040c602c01d600101e00a801e01c16207901c041d0445031441500e01070344070030f88100480c0400394503c465100000008881880c1004030142d50b00078809800c803403030032205480b9a890292044954a4400e8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 414147526 1250 414146276 414146279
    0x50a05010b0a08070e0103060905030912100c030932030c060a060512030a05030702010902040e0d0305010e0105030a060b04141807050d030f21021303060506030307080a0f0201020d060f 81
    0x140401080b000740b900b4000782035101e09098401412850621001c0d0107240c0b1980c00c0414481d0500031210b03280d034000d215074802075102844540b1110782c2c2404201356450081035614a41c081d000d40c0d05015070082d031480309018001551607a001c0f0202c0f0065510350118103240011604000810200342c1030002000c040c40d040400c003069801907000a402145e41940e10b02d12500700106561043e141420f08a07120340c0d030140100e0051840d002c000e075000d802c0810140c602d4801040c0030002c0c00841d03406014a0380c0f2600104100f0030300b8070402d43c16a000703440400224808ce80076108e0284010000300d00a40101800040d00c64180d45112400e0005c0502c4d4030714120401c5030000518003942d0542042c0f40c152406046030140300600c2044c4020002ca20f0b0348a0914031040f80300c502070314011515070a0400714514400c003d07010803540f1a151201042c807901e0000152401d060340044c0c00c071b02d805007410f01222101600038000c3c09541d0240140440c4101074018032001c1c0002c0304400c0c4015 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 414148776 1250 414147526 414147529
    0x106060c0c150203092103030406020403230c10030204050904050c21030909060d05010f0c030b042a0521041203091208090f0102040806070e1008071407050a05010b 72
    0x2401c056200400341d02c902a00481c800390040141c032906401265140350242c05603500d00741241c1d2039a20610180030000401042218590280042d280290705411074041c01e01000003100c0101c10044865a2220064082c0b82c507000d41c16010583c824540541040c0d40c520105110100581d01201c80d60486200c041d07883c1044d44294108009080c2114101d005200c80e17aa268030907201c14901411960001605580702c0752424000c1c6540440204090a114034510b0010320000079030310002414080d50384428034103800382810320504860844064152000040f43c40706800d03400c8420302c802403200300b41d52041407460011071100030440e40c13658546031510303448491340005408145403611040c140070514080c0c2c018001602414190201d44071210001d180071848685c503001507000103404a184100031540e20700494107904c0e220b00c00d0004600300450140e0220a00c00017408000c001111244034130b200c8503400500358191403a18146498a50408001c2942512940c1d1240035140c01c6 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 414150026 1250 414148776 414148793
    0x51201120b0c030c180111100605030d0203041802030a1d030408060c0304150e01110c25080613020609130c0e09070c030509040f150303080106090e180f0106060c 71
    0x44103002e41e00f8a146803406580350a4000d01507100c4001c500318240341c115034051590010948800000c40d090303040c1e16031510001d0480d50007154001e0013405141036035a03000006460681c0c0324800d1402c001005030008200079040181205120364480d814800b605c0e0003481c2d44a200c20342400030315a124140000c251501501030004220004204100700108448000b50210305116000c0400e400110313030683c0d4054108070004144000001682c0030480074001100c01c0c10906104a0300c0007845020707564503007440c05110f460915004600020700300002010154442440241564102440c00c00890702a88804000756511660f84200c030161a070440301901c01c0a000f02d6480440d441c0c104001000c40c0e11900000341401b0300442d806607136680e10f03040228800f141344010003c60103050310850a440507840190007194185001161a911403615800bd4607020000c8940740d88425040c441113003160b5040308000c0c05a004c1000c030800b000c3c01080000d004555608001e0390342c03420b00504 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 414151276 1250 414150026 414150031
    0x10f0c2a031e030f0309050a0b0a14010504020304051c0909060b0315030c1320030403020102190216030828020f0705040608120f12040506070f02010e0c040c051201120b 74
    0x1903080b1482c001c1c0000070341c0800940c0b8030801070300e00400c0d07102d50b6203000e500e00240118020454444002002041c400755071050480f111007a40c8040e4a07680d500078042203100940b8040c03ca600002d8511035502c0012282d18229140c0e03240140000741d4901444084900b95000302a485000005005490303a11402e40000600c046002d01208071048000620a11040c40c082c81c145444050391440055600d200c81a40c503076801400d5503a1a00c0c0c03800038000d501a41e8240130000c102c182c140601803000443d2603500350707420b298030ba1403801c5484158041d00b0035002451a041001012100c080310039610040c12519900181405010a080359003040c03016040310307000c1c80c07a00f0300801c224940090b000c440d058440e25801c0d030b18030240748001b403d0b100301583c0c81c5d200106081484100080081c003240315040c5569804050401b11200b00d00740c8620103a541010f9003e80015001450254001c14400d0404c3c2445881e0554014030400e400400340d000150140a0142c840140301c1040e0042c0e0703 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 414152526 1250 414151276 414151313
    0x40501050102161a0d020c03040815011206020304020409020409062a02120d090b04080306010909090b04150f1103060a0e01080601030807060902040504110f040209010f0c2a03 77
    0x180110b1180d602043d03105220355000603101c1c0d0400d070340e6110488200d80072181c240c0303400c1d13559048000c8a10383d00ea00a104013103035442450f409028401c03070810030030b0682e04015084a5000c01c40c0d11644040d400150040e80d100b40d9a441110060381c1c0c52080a560030311840d408a000728000b840383c810300d09d04407180d01182044844245500340c1c049442800b2512402015844101d0203860310028184064010000641309041c07205020503034020318030a0100342d03200e10240752258180c1041e2000704900811042c1c2040100340051540d648a6143ca1508400050f00d8290306802009884080d80c6510483e4800000c1c0115030401900e903401030641d1406c42402c5500d045d0320247d540c00144000f602e022000b160040800c41140c04c4070903078540080043c4072504050800740c0485181c9121700d84985c100c402c1d00041400c05000350b03984c4c078005854000d40b002d40360301c05490f102050401110106940a0b4025442c100800c10841111084000360a03245c15440c1c5051155021000034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 414153776 1250 414152526 414152533
    0x8090a0e0a0b1206070f180503030703210615050d2a17060d020d062c011a010905060706020d11030403110601030803070309140604030e03150c0f070c0e09030702040501050102 77
    0x440101d0f04211b4651360781c8510b281042c40008485050f0079085d1054028a605000018141051540c030104080344a4038002009803da4201c0c1c2d01501142d1040c858948004040d02c107640d11140603602a00c81e1080c00c00740800c20006084c6042500500c041d9006030f48600d8100a4001c2a446084591052000440c99546091507400030b15200e900c41c02c0240f24800a4800070208445a0400720340d040c000354180d0004640903140008003444028510740b19842d001101c03d0741e01d1007805c5440d131514103840e154207043c00c050500c0240d9112440a9030b01c82c1d000c00920858805512940c4ad0701d004c510703001078036400d1500d070042070403e254803e1400c03a03001400500100f03415034100c276000381d042d06000035104000d1404003490481c900300094640a900c003000b040c1600152514801d1404800340c4115500882004840081c19295000c5805c424007007941c02c1d2045500402d46280074000020b07070155036403902d08115008456040c010b030030100e01c000850405014441c05880240040c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 414155026 1250 414153776 414153781
    0xf130c08030c012003220b010e07080703290102070e01080304050a05030708060c090f090702150703060602100e070b130e0a050f041b260601060f0c08090a0e0a0b1206 73
    0x4c02da55800040c10400300150b21281e904203090006180d001d5069000380b10035102c1d80d5075140c0c207580c1c10089480c013021944080006130800e119114014450b03065006c1e449034011715841c1044131070340d86144541076114001c00401c90034910301410340242040c0700110b940301e08000c03d001a5000d1940314900a5000940a104442c00400c91540c0600405002134035003440d480024048801e01010680100700700b000c0c0301250741e01052540f29280002d06400452f29a004c00301d0485000788500c0780160810095a218044180c104244002c5110216803415440700850000ca9100160322528200c81070410130110b0144980180e03c801100401c00107464407415800c1c241d00d00800042200d00703680d2201030f0b840300000d04400500032094017005600003602e440504007540028040c0c4502c1400d0000806074410280c2c1581905c281e83c4150307001d07146555801c0c0a80201469540c0300e00c907800c0200c0c8005400801d5845070503080e402040300098682440f001242c0500e10500d41e81080c402c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 414156276 1250 414155026 414155081
    0x415020f1213030b0103150e241801050c0c0c0429180a020c15010506040608040c05060f0406171017120703020c120601050102060f130c08030c01 64
    0x1240c20035000c1d2072641c1075560849501c0760001014980008100440da000040103122041c00c0d400b902c40d06ca00001c00285401d081c8896841580c0514803100c03034882016000a650008521078114032182000310540424010040c01d440f01140d00b400c0b0b810001c40c1c0302c21405001c0244140c0c441059504100c0e1081070b100504890801c01c0c0c900710654503061762111980c96442032140a200c50030544a1a410f2000c1568080d62014403854801c0c403c90910002d0326481100c414100c60004080f1840c040c9085010b40b40480000c0003500d100044550008203515110700038150300c1d00002c1303403990b1242000340160101008041e86c070249880c0030108014003040c0101c2d00d082c0c81e91050f2103828103483c00401c500c0c003581d1165104401034045160420140c000030080900390040703c0c2c2c3d817114a0342c072507481d580360403d00c6a076005034020f030003041c41e84c280c0369400f0307800001705404201d00c980c941c0c6481000350103550122019a2000840c1c40b940ca000303200d003c4c40062000d0032440f41c110b1444 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 414157526 1250 414156276 414156283
    0x1e03020f120c0705150612120403020d05070f030b0f160c021203091305340305130503160b1506090f03190506070e06121512120415020f 60
    0x907103842441400800c080d201c004094a8125520800b20fa46482003070f880c882d20084259115401071200c818086901e4501040401580b40b20b0401c0904062854007088100c4910400c1500c4500508601040c05044880118080c60243c0e81c00021400d00345480b02c5490320060600c00145a2060418401588048513185141e0120b072203000c0c0110ae0294107065215014505600c180c1d501c40521300c103070880d0480b620902d40d000d0102000c412880140403801c0745255040505645900c040038194060703400550000740148030321258100b04c1e61101d155900c02c0c01000d001001c907001100402c502e01840641c4a55011654105011f0f140045205405250f0342a4840d403001034181038180c070100301c160b44140000349224203041150030031a0704d82c8001d07203184000039094509000e8500304501210710200303005042c000c0c4c55880215140746a100c0d4200c030f0350f0000c0449510800c00008110051214440c2621580d64a2a01c3e0024650000040c100810764000601c00b0500c0500031 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 414158776 1250 414157526 414157537
    0x90f09070e0f210f0d0801030308180106030b090a02030607030e1f020c190303110307080402040c090305060a14060a030201051c09060f0504020f0f0a060c060b060a1e03020f 76
    0x5560200402d8110400200d00001c43e840c080c003420201c0303101c9a140800028041341005001c41610350591201302c4c1210504000d0002030042140a40810000355213015030000303d10701d610000504549943da00c03000340105803620580c0d5800401084250701e0144000ca070813100343d080800201041c8100340e80c54420040c08240480003001602c1507a1106030110342040d0364103000d59540205000da203030790009031001d0603000285441c2210201e1401101140d024a0b904e8545010304e558079800c10001d4141380200c1c030104090704c080040005e50802c0587d0140c0000704000c11940300d0003010112078000106414401c908802042015076008801c48804800c1d00b451041c07203106500c1500041c4c030403080f00034800b900d0403507a100f80154542c800e60195100f2602d14031405942070804c030050f1500303030754558002081101002824014000f08040c1d6100e0003020490300c076902c00188203500700d14180000f1580c1403140c0e50043e140c00881c009645142e090071814201d6071210740e083c60180 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 414160026 1250 414158776 414158779
    0xb01060315061d0307090606020a120215060f030a020a0308041401020a0f080c070b04030804030c061e0e130603060203060a0b130302090c07021009050103050a270c030b0a02090f09070e 81
    0x540d42a09403928181700340c6000d0040d441041c0f01895035508001d695010201007551001a01c204c1d8140d401e1011540c030701e03400c12401090025072107400070007024200c40c603c00c0750b061140c80405001a00c6455170340d0002e600698690340c445140080700740440c40c001c07100504541280140720700003045150256a596006034106488894101c0c0c900e143c24140c0e00407050b0a4400b180005c1000300b6600100f081c0c078400c0d003500e5250341d66154240c41144694803408001040d56800820140c818044120b4065000700b050406090340300b0001c2c00c688881c6c0040c0d0f400c5e40c0000c100903250400c0500f40004080010841c0e00d4a440c401d40840303a031441703000003071040e080314000c01c40f1034003c1c030b084d1a9607d4008041d0744820403103c80c06071117502b5500c20140800e052100182c8004020f208150782e040410070002101200720311402c620301c0d0898011540e0855404000c4045114405200c2c03003105102001030340c2e04c1c030070740403c40c0c1c910f0703000051840b840d03c940401c0706907980304c0c40349041c040b030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 414161276 1250 414160026 414160067
    0x170c0303030406111e0c1c080a09050c0d0614070c0c1e09180605090d020a08251419020f01050d110a030c0801091406060f04050d0b0106031506 63
    0x803844c541006841a102c4603c12404603101103074104030705400a043d40c1e20014115404162100300310714550021020354408240184001081000701c1d07004101d401e0b101e0810750b0383c546201000115590082030040d180e1654a40381510604654002c09800c4506400c1030b1240c424a941e8203030f850101c1c1e00417582d0344d400710240b641c01808100514400381201ea002400003052040e02001002402c00007540c90340d0824001c180c0c0050003152182807000349134040c2460b501c0a803510101e40d8041d151580c0d550140700300c59480d4955429058041e14400d0085840341064180c0b4603150000305404c400d00a00074086130f000581c1c80e140c4648001400b0b0034056202c1c81d940000f60010001000003080701c450008503070700d04c141e00d907112040c42402900e41034a0703640c0729442030b002c403850001c03841c11880402011407200c2c500100a44050700703600120702c0c5400e445c0c8003c110310a414210071264041c40c500103010058243c01880c0e021040c2e0710303506444501d0080001e005280e000d00c009000701 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 414162526 1250 414161276 414161291
    0x302060703030608030d1406010305390a03090302120c03041502010906060e07090605030c0304060504150e0606040b040b01090b460804030f08070c0b07020601170c0303030406 77
    0x600a0708554004c10104c816242c56201d640600000380c52081c000c902101c0310711000900c950301a1040f0f60054000395401c2c03214445031f80f140901d078018000d0f9640100000b002000c8018040c10080150013030540d400300d1203200c6440d0281c54031740240503000d150002800031441c1c0c0d1000005460843d40075400e010035501140c40247d00500c11144054429400c01e100814128401c0c03805a00a040b240c0d10b0758820f0307070744200072035082c0000c1c1d03030920411004002140100e00c0302e400203a0414029404181d200b24600080c0c4d013256030101390314029030002e00803c07505140601c282443e104040d076090010001c0840000e24040d884c0c06404508a0085440007001c10080c80c20040341681d903044940c011a24008a149031b00318001e01e999807105414004140e0744541c281d00d008035415200c00c410515068420786208900a11482c200309000c0819030110b8074600300c1d00d0007482c1130b4019100550500703d101140b4a0303980c9076121540d2203841c80c01c003944c800000b1298442c2d000400014100c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 414163776 1250 414162526 414162533
    0x3061d19120302040503030a0f020d1701090209060910090306110708070303111309060509011715073f0e070e19050106121b0503060108060f10020f0105180703020607 73
    0x9000310f4002541602c408034892380d055402001154140649808884040c0003440e822180110503008014460346100e004001c0d00b07001d1f801034100504000c01c4141001003403804114242041941c20000414000c020818000c4500c21443e2291b00c05207030b5071808400340c84401192090000080801da03840034401d0010b07182e0f006075030350350703401c194030f000c1050384c620790440502031900a240c13080c01c4200c00014001030f032020040380c0d1616580585100003604030203400c280e030010b10700e005121072442e119150384080c445c030002011000d101c608118400140c8000d800000f110700803881c5182c40e1800604400003d40e600c129030315450280541d640b50301c0700300605c200011074041242d040000100d0354580129000034080302079141040714281e10940c082003038083c100302030003084042001c500075501c107082c140e41c030860203010780585088810124601d5884c8040c8100140c1180880746030300070081c0504e41c1c1240105040d980103140494a090b22182c90f0300c0001e1141c07c0000390364040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 414165026 1250 414163776 414163781
    0x20907030915020705010e2d0304031b0e090105250509100333061b0c030620030610210e0d03061205070b16020301050103061d191203 59
    0x40e103501001d92410204018003020103074008001c110790300d5003000f01c001a07074030002071003c00d0780308c9008161860326030355080b624610f09000318000d0180400c01021010076810316032840500241e24001d1902490840b0041592030040e00c0b03000705905190501030701020081000405800101001d20760f07000c840015115449003050042d0030007080d100c410321540d05039010b0700d50444004001d40d58401c0c1c0103002c0507c0c5103044202031001015000a200030380c803402444800324082d18051143c1441c5440b040c80550712030340111120351700c0e92601500340008240141148165801c240c0c1541410380015002340004210101000079030000c0c00b550242b503511006a640e070402c1c0400004018410300c42d00c030360780811a400480c1c28114002200c0c44001402c207034440e04107024000b1182071044143c1c090340803005c41940381c0c14070802007000d66000e101e40c50085204280000382c140c01c90490b94104410728503c113285800c0801c002c6150301001c071032901c041e540038800c1d490300c0c080b0344c000351700 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 414166276 1250 414165026 414165041
    0x5060d02091e0702060c03160e0616030f050405030303060d1b080105040c0b040b0306010f110f030405180c0703030902040609050103050d030e0102040506180312121b0a080402090703 80
    0x6220000500380000503021903180d4034210b40c001030040c41a540c1034000e0b80e541c071056455801c43c010802c0005c40000f9602500c02c0b21800074030380b4000c044504c030300168160b040015041002001d4104003403c064208103000700b0913a00d0700f80f540c00e052030080069180d000080020340540502c3d0211810003001000d8010314194a5510301c0e28607490710400c2e0300804084404131501418001c000c288041070070162012269424040ca00e141da85c036004549010000c8030300700c24081e0090450401d035209000707035848440f0000080d5282c40c40c040c00c005007401d22070400d115441403002802890700410044440b4550941004121302c800da10110707009000030b07402a451940f0b020004810042d000c10415580d10055405004101c13071240380343e0807803096100311a404038040200d0804c20300359008450b016000141a079440740c02110010f480b641c04158403503011114070303080100044e40c2c4619030080fa1040c801241c1040c0001c0070107810003a01400281c494040742c00003545542c440e800104 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 414167526 1250 414166276 414166279
    0x2403090109020909030403111c1113020c0102090f0d32060a020307030c020f060106120617070f120308071407060c0206090709052e08070609090f020304110405060d02 73
    0x3c90314203841640e4403078000e0b01040710710041080c411612480e12103501600303070940c00d0b00700015041c00c0c4d5030100281c4040369003039000121341c200c080d95204070340301400c2c8903020f41c000035075525800d0081208000320644103912803000c0101c0d240110300c0080044003154a4880494003032841162400c4e41d00c180b0380110f403100c0c41460208030143c542234001d0350083c1080d4800340701c8104e0020050362070300c9503110560059440b0000401c017040c49070500c001010b100d05400140e4540310f030b445200c10011010b500c0741d1603200300000c1011701080140b000c000d0900220700f9400340711030b9400518209010301050f00b001040920400c5000f03020742201da0a41d4000003c00c64002c5000d0080c0d26400122501201400b42240c00039000095000e02842010404403443c40300110020324103052054003c0c0031401d80c40c4800c0800e070001c0800180f4058005070303c070007110900d06203030381045d00e4007800700d034444030700500c180000103420550f0300310f4241d400c407404203c0b50354500100d0031160310080040d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 414168776 1250 414167526 414167539
    0x30307060f0903120b09190e03030f06010207061404060507020f190e0108150a05040303020c0a11030d171810180506060f01120c1404090c020c240309010902 69
    0x3a141c4128942c0301030b00b01c074800d4644040014050203d50111a152040140c11015041c001403002282c94148501c40d20024800500c5451018601e460342c0c01c111003a000c251340032824000360790b80402812009218600e8108803030011182e2007906030240c0c0c40f410061120201e2004215078500d1801102164040c041f0140c2c1c091440c010060740da200d1058800b0540303a0000480e4244020984180804200031050b045490307a141080081500410580400d0350030701881c4c60b600414040201d010303011b40310560810403940c04140c01c1500c018407600c2409881c007003010403482d03c401c0c000d510410b003c03484148058807034005428000c2c0c1c00d4003a03410382c5c82c000586540700403920221842034000c0b0111003240c0d895005004440303c14a14082c04030314600c0c8400a070100507040b02690707911030b14107a410b0b24115120740009070081c0d003009190b17540381c0802c0c1005a60400c4000c0300040101c40c203103007000748491841403030101011080c0311024000006105200b003500044103203640600070 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 414170026 1250 414168776 414168791
    0x6042711060f030a0522030c060e0102120115260402010c060c110c04020304051239010c0e010806060a0e100203040e070801030213050a091a0a0b030609031803030706 73
    0x403035910b62045134800b140b20b00d04008100384034161024060340000008001135550344548042e1a058486003044444540b58a544d4490090a00241450403020b40700b081641d41010050b860103503683c1c03684820012429082d1002e030016a111a403c1e502403101e140a640711030004850074922410040c00c000e080c05060760740e080e0b009400c495040c08200a0381c04038204407081000741d00c01520050000d40c007035540c0c8020036814000070803100419120884004a81d0051001c9206001001080c07411501c440c0030002c480a000c0c0c074004142c10301c0c1c94040d074400e540000e046003d014090901840010841d11286401800c41e5016650b000300740140a036003100000356079502901a130302103000040c010034001c40c003440c4c13070506899000f05140e81644080c0c3c0d400c4002c040080015090f10f444a440713801054955001d11501042c8191075551031500c2c810807801d80f0060b80c41107009a1201041013005040841541d84c00c0e17250000c01c1991001c0180003d00c0c1d8040d0042c003402d9140351011 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 414171276 1250 414170026 414170047
    0x3150e0403030b120601170f07090230221205090111070f0302041d0307060c090e1005030f07030f2a0f093c02042102090604271106 58
    0x1842412039050181c0c7c100d00200070280b55403565505034100010b0f50000d8410301a1160036005080c3e03460710000e15100b01100c480205075a1025200c89104001401c01405803020039400d20f88090b0143c00910356440029a0301e0194420010544808012010450782c0307580e88134803003288103284508200c4184603180c8080281e80c001c01d200482c4200d25144403203000c1402031020003020704004001d541001140c0e01c0301c1028100b1002d803d01007001c0c184010440f070521400b1103000d4003804040541c81030800d4103245c03510700e162040c0c1c20340d584004020800035124541000d20264004480035905070313040ca80502660503a60405c45600c4110303400b01c0c4000d80c0c01404012241011014443c1505a80d04500f980c20300c11100d03046009055103281c0b200c0400540d0b1a0800f69101c8018a8140d652001d544008490095610003410a44100056241c0005d002c0d070401340844082000ba010321500000d04400351910100c1c8a814021020900404040c0781c40d00c03003c06001c0075a070340250701 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 414172526 1250 414171276 414171283
    0x5030a1e020d0f05130b070f03110f0309010c110a02010339020d1d0907021005130209010503030327120d0b120d050d0e03130306150603150e0403030b12 67
    0x1401d08001500d13081c00201550382030707005000b110303400c6200c680181d185d01da4212486450b05110784c0c1455100c0d070148601e12130b010000d28a0301c4800403016100e050006010f425500c0d0406000200842c980550a5482c8081074003109260309090003c1d00e00c139013411482201e075049882c881c502c8503000e5000e01d1401c410450300c1c521896a403c0e104141401c0c00281c0d134101d6522000c58454011400403100c0e13040400c503150308016240112400c481100f0000000d4903811202c1113006030910072610110300703180350128058541140138509600c0c041005c030100b07100003861201d0903051702d242800042818814101201c408c5600c00c0c0c1e981c8a5007096a01a00c682c01c81e480c052008100156050440451124813850b40c81c0d48040c5064010a00240603040c070800c0d0a50a01003040091039450542900c0b42c015485020701080400380480402054020742d40541c0030b02d07061208401004502000e08000c0d00c00c0070041050030307103941c1000c07801020061070098210701072102c00d44d540310000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 414173776 1250 414172526 414172541
    0x906010302013b01110610230d0303020f0d02030f0609240f040e0f0607020d05030403020c100e13050412030c1e02030f07030e040b04090305030a1e020d 67
    0xf030302c409070800c10300e1044031400958488540e40b08401049165000868540840503440051501148966012104a017404c409907480364000400500802400c214540b080d0b5030340d0090000c1c0c0e03075624640008a2207140310701a0090401d036000a02410803030784074060362100c50355801304548030700e000707840c1440b500d805a40462142c00240005003030142120008012042400030401a0340c000d0028003085008450b01e4a500c2501e5402c031041354802040300380c6500c11720400800f001c2c2400701c0e020341000c000c4101401040360400800010035000a084c006040041d0b840307014060302c00c1021188001a569241e502c120340c00e943e80c545070140d80149000718003455040d0f90641002000380c0c01c40711400c0058020499000a0002440da980040e070040030050055034034051003401c400c030703841d80305003403c50200c1c4402e004019141010b20409a030000e050b80c0c00c0102c00850b440c00b130002c0c04000c085001c5c042c1c8903c41c40e0021890a040c10103280b03500042503465000c8000444003605c030351f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 414175026 1250 414173776 414173779
    0x5010e0303010b041406070f0b040c05061612020a02090f04080904060311030c0a060c0b06060702030102070b04060506030723120708150a0216080d1104060906020f1605040c090e0906010302 83
    0x2203c81d1045c0e80d01e040700c202c940071540920070815207011a9209040040d00070025a800700c2d200e2030020b0151141030062860700700b5210140309410383c526000340800402d480c042c0465102e88101c03401a214098455080300001c03803020002d079140e2030040c91301e01c100f01c0b13070540260401c20000200900c2d1902484801304c200d06807924002d006c01448440d581900c15400060740c0c0f00448004940030800b660f801c040c01601a40c54022b0769004282680e0082c0e001b150300740801004c0100340f2000c0d1103007a400c071300e0031000b070140913280c0050400140c518444000526240c1080c0345040ea81d88403024101840c54400e6880c0ba03684d4118258660b00f250341c411101c6d1003454006445010701c3e200301c420f011100c0c010700300700600907100e524080c0c00042d441c054066440040900306c15601c00030300010503040c0d43e8a4282410550000d041c040502030310300040c0d208035511018100809454020b458054500007a618960074081f00c40300829481060202184018010214004542181660300 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 414176276 1250 414175026 414175049
    0x6070c080a0c2903070e0103331403120904150b130605030408120402030709050f010312031a04110d0204080c030106050105040b04180b060c071401230705010e0303010b04 75
    0x243c611039600040d4141c00d00b14410303401000041c4c000c40c0181e284d41d01e5054113140006034007c0150000d55403c40151310964608032400e01403101000b000b101001921042d11410360892030200403ea40341d5110f40505640c2001141003805a2a2a07104102c4071240704aa0401190b0302c0d254540c140d80841844070001556450200c0d51030302420032039008907071020500346041e09100002a642002410499140c002c4050005074201e09004103030040700784801c0f054683d490f614007205100e46100440302414144400900c0d00610b000301500921400d847c00320b10366010360006481e0307200307086004161078800310300450030a80010345c490569030254020450b09440318010b484500403441246280039007000144a07000b000844070b54041e00d411404504026540d001518075040010014210351222908210703131000c21080100c208400e0030400e0044251400b40681c92401c2740000c480881c0000706082002001d42c0824251030b101800d0766225612080121016130140c81074646150 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 414177526 1250 414176276 414176309
    0x506010c020108010314030c0a03111c080f10050301021b01060b04030b0403030c0309060f0506030124140316151101020a09090b01120f0c031b08010506070c080a0c 72
    0x140910840c04039140c050310b850341541e1866950b1001c84081c0108840c482c04103000020281c8010020400345e540300e5180c0341294409440c409141110000200300d400c13140303036000e500c80c1340c0202d0080d4111004154107002c03581d40c030082c50010f87c3c85500c820740642c80081d5103060030482e00000701c100204071000b489a169105000140d50255010282c5840b074400d01040019009a1002210040078100441c444803203850309012164441003400c035140d00c031003c100d42d40c5001e101e81100d00485240ca010401a100099917480080e401100f6140ca11000141c1d155542080680650544a5400000541c40e80c0c098055500001c624601040c000c1c501004480410b0003a91100143c5a4800f01c01c240fa001420b80a000040c1c1501c1c1400726003852203251094501803441c00c03000307141d404a25400d09460017000c481e140c01712026a0301030844219082a40141c1503411a10205c070042d8584204e801d01600d0300903d81c0c40b100c00b0303102d10741d0300318200200c00ca694421500000d0b581e10005 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 414178776 1250 414177526 414177529
    0x61503053304030519030b0a0608180f07231203040503120910031107020901080105180109080915040801090620030708010312170a05010302120d09030b0411180601030506 75
    0x2030810b89004000c100240080c43c0d00201108007189108503510300844c400c80403501007042c10342c080d04410f000030b05900030001c040030480c0d00c690760012010020503110341c025600d00d4030741e00b480c0240010a881e8402c000c00801c03400d0080341801c01c00030140e0108080c00f91920f03aa03940944250380c06030003640b00c9018691303120307810366540c801c02405204035a0701148086001300f00b246848001340806000c1e003070140e11011a0507000e06800d100006982c100a440b0700cc00b41206128081241c2c107001c89540052104015100e22500643d000b165801c203101980f42c450180c2c0e045803c1541c42d141000c402e01c0f0035500b00c1c0102c0c3d06041124001d01242c1c0f501c68181d0300c001c1b602c1502082c082401040004c0400403007000388802031810220b44041e441d0300d03604200f01034609020b100d0316440140300758500010420b41d20140701000b8031103002c0215019144003801c0c40042c0c04180d0020015040c8003c011b1034000c1450002e0200307451494200d0154071090040e81d01d140064a440e00040d4207 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 414180026 1250 414178776 414178873
    0xc100c0507031403040606240305090d0c080309190803160e031914030a170105030102070b07210c0201020a3027030f03050f060d06150305 61
    0x810782c0556031803070300100b0f06402a1055002400440e43d00d81e8412000400d0072a600300309000f0b11044241080d43c1c0840c050080680e00088c11004041c0c1040c0900d0802c1c5400c1000c072025207034040c0b13100da01c80e84c07a41c80841c240b520003544200c0c0d882a50140d441003000110065214034420081301203681900b0300704842090143c14030780c0d09a400881c1007005501c4d50710840355464440c012a260807180380c6407207400c5420904c070040100c0d01c140811810b00320185405405044140d00031402c046150300c66000b03d10020300403105001c01c0721110111050196450300803809250414054010341a01c000e000390300400100c000100c202c801649654120b5240c62100584281103080c00c0d05800c0b41c020041403031806107540101c000c604c40c0c440103074550420b20180c1c0213882d01c07442d100e421000030741625401000148a0002c00d02004070340c5c0d581c1115043c44d0b0740c0080c800907503000c8940740701c0011a01608042c101c2d105107500c2c41f4640846c081511000003a0990380109520115103d024 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 414181276 1250 414180026 414180037
    0x13290907080d1b0807060b04110c1014070f170c0306120f03190513090203040b10030f08070503130b1c050606030f041e05030702041d0c130209060c100c05 68
    0x1d00e1140c60151008910300300060f0104502845002849000847c009011a022850184900140400d9031a6a00310a00ca22025a44203100070b00640d0f0341248103401302c840c000c02160a112082400542140c413034504040240710300980300400382004540b10100ba041260864030618441002001d4a80040b6500929142040081d81005c0099010201c1044021005410020148040550726848502890050030002c2d4016642d041c20700b401c8191038401842145418a944001c00c00507800210003000300b900701004c5521160946050750652003180c5564514025404000c580d24000070020068802c5426044803072a039183c4c414810f807a0304498083e0302110030300000310901c0d84070910703507801031103644903801802d50300c94507a5080307502440958055001003821000c5003441d00c0740d009401d0894000c0070944040b0f10800d0b40c0e40d001c3d6442c03d801408040d001c0d0010302c000f80c041e541003207402065207454060144003140e48619000c00b26016500b05207104a40700e00942c11241d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 414182526 1250 414181276 414181307
    0x3021023010e15030a06050103121404150507060903111606140a030b0603070201020a031103130204090302010b1509270103060209130207060f0c0813290907080d 71
    0x22440c0c2c41c08952000740705000f040c400d51524002800c0340c1d1030b601803207001c80381442181c1c009815415030a010f8800c140060106040c0000703181c610402c210a03106403400c8410005204889850790502140c1600030110700408042c02c00341240105604a041661031440380c0b0101e484402c118a650650b80032540304810200740074401c011180c00407000244100300c2142030124100d0703000d202080c4654411504000140d50106100e06040d5050140d0600700ca0b021084a0450401402d00e9078044200b90000b48240c0d0303640303c1941010b000390448100100001d200300341c0d4207140b58117148180c1c0141a880c1c441d2038080c40301101070701d0646040b003440d040220082166825a941c94000303611540c03400d5232006034036005440f040450300040102512504010a140d03141030604c1c401c1d1030b0403e40791024400000c01300b04e11580040100345419401c5105440106404403a04524010f034450395940c0300190342c100940702800041c100112050042100e40060912804441070441a070006 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 414183776 1250 414182526 414182591
    0xb01090306050606040f0b130503030708040501030f060807080f011401080c121f0903030b0d02090601030f02040b030c0c0607110c0d110910080d140f2104030210 71
    0x180049565070784025401078016104900d403944402201d1307a01b2007030384d1006549500003d010074206186c081c000001b072000b074000307605000d0240c5c2c508116001b00d0240701d04040e5180d2200c106072000d5000340e4010500369003654034035a11074034600d4644c1c40352030660405600f000d02d03461540d1508000f1134100c404000180465190350800c0040d204101d05d03d01d8140c2c80b40580507100c46140100d032030a075100d502d1001480b00354500e4007500303440c148204140f0850180c909200980c0780c00070580e034080c2d002d20300001c601e98403640a000034052a04561030201d00031040108083e0780f00300400060265400311225a0344d080f9044480c1c01c0810326007016500700b103101440e1030600050000c04a0310440010142c02c11940108070042c4040315440c00001403c5005c102c4820248500b0700800464036000102c1003101d03000c05c0c05803084020a907000400041c4418907640012822018002040440891420035040080d074541d403020000b10030500c0c14410705040452242840560407450244 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 414185026 1250 414183776 414183779
    0xc1505040f0306050414240604050702100e0307060e06040b06150702040b011e09150e0f130902030703060b1906120c14070b090d0f0519021018020103050a0b0109 71
    0x100d502808000d0400c46c0c024625400901204009000e00144400041c0540140040241c41c800c5241d401801c5580a145440705018a0590200324a40d41d0b0385003040c04121f94502100301440c621400c030019025902c0d01420407082c0d9004284540181d00602c03000e10252180f008200e490254603443d001c0b4588104070140040c10140c00001a06205040c1240c0c04040340d50340c0100034a8040e230450005540007010300c0a52207441141c0b2071042e0074079205009541c510301044491824050361403003407074810b025200c283d800350040030b101c9602805036482280e0388d141050140c181c0720001c43c4120762038400780803008100e8141e10b044507601c0c1c1d201801c4005400d0360740010142441080104915140c1200e50810050024161b141c8561002e040605d0a011342c6410f00c501020080100301891804401d40759002d01601c0c44072120600b500310b58002c105043c1d1030252404085a4000d04100743c59007030940a50710305032424003e0702c09224580d514014401221010700202d40804d803c07540 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 414186276 1250 414185026 414185033
    0xc0c1203010906060201110d1802040504030c02011403011d04061b0f1119140715050d0b0f03030a1107081605040b0109210f05010e0705120c0a090c0c020d0c1505040f03 74
    0xb02c038027411b49002c0080c070503004202034400c120750903130203e83c845403044110751740320800c040054030850ba414119414510103034004000c201c60f8101e02900400420240102c0b9031200c00303000003100707454000c0f42d20035001820300c0f1601504000840c0303010300703403490303080c070104860304104d00130030410704041c40b26580c0303100050480070f40e50f007180310300351004c1042c011000e141c17460300c1150340315152540e041501348002e41d507031304000d540940c008000c040c40c140c80020643e10039080b1818201d048007a600003c9103825442e030300581e004d20039810300d06031481101d51a4002da507000d940c240140300c8a0300041d200044c140c40741e100701c40700200d11903007400b034454401010140705101140d20501c05855113820748000d6440358241d40c0102504100900d00000d80141c010791010240500180007000164800b5180c03042e40250b544500203501a94071454145414507401010b01c0714180c824184036102c0002d40c01043c00741c8101c150081406400364040d07034103c4500640d40d803141411542c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 414187526 1250 414186276 414186281
    0x2030309062d04060213080304080c0d140114070306080c01080c0c0a02150c0c03070b03060d0f050f010f1d03071202072c1e0f0c0c1203010906060201110d 68
    0x1030b00c0d18000122280c0c03660351403032807240030700960146034003503200e01c191400384200000b107078040001503004010410080f01c0105142c01000001c940e003101038821400e102c0c040f06040d000c40d03072055291084038802041d01c0f0007214000c2405a508110040c0c4800b85a580c0f401b006c0c4219000c901c0da0b4002590802c03030f200042031440d43c0102a20500003503036000c41c00b14000015851034030840800c1c07c01c001e1200b0002d8801c070b41d8080b00140b12446ca8192046401c1c03101134141402110042c02401c140411600743c807403465400000c480fa80310303401944070300921541000c0f949850400071020304c80081500303e60000c0318107070051490045039a9402d804440b0030b6090070203500a0150001d54030480106849054a0f00e8040102c0703008844280381e850031008000041582c0883c40c0c5516080880c00d10b82d0340901c000601c0354481e150401c0d4050b103030081c408035100341c1c410300d0f2200c444408424040d45c1210100b840c14800552611011b07400d841109a80340c0c80a8400e00c084a81c150294 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 414188776 1250 414187526 414187561
    0x20c09040b0412180612150b03181e03070302060609060a06180b0a02030a031b050403080328021201120b160e0d08090f01030b300f0601060f0203030906 67
    0x14140750041c2c0c1800c02243c51134144e117520840c00714001c0c48050300e0194140c050b00104411100d40d0805075402c15210380c0c801c2c00003a210042403c849041100c02a408012001d0036414040d0380c0c0c1707220070903041300b2a504e62102000705d0050145c1c00108483c0d050809030f29000d498000c11050005040501c100c4040180006852a00070440b4000800c410b01400504208095901450b5510300115001d010307101801c2601f104c11855000f4071340c900ba0304c10151000c1e20352100313905603241c1b034981d8030180c0c10b034411003012034480020f2640030748180c1c40d0f80103015490482e00780080a070f83c2c841c188203806440c05005800600c0350710026940080b40b039080d0015604604040c00600b2080b400b00c0d8198866080458400e040060001c00c240742544125010000c00d00e810700c41e82414401048200e4040c0000e1a1515030804000c0513414144c3c2000d0507000303c841c21568040d4101c0005580c40c0030a20519021540c0680308441842c8003000b224814000308004083e1621130168226000114 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 414190026 1250 414188776 414188813
    0x2102010612080408070e10090e0f120903010f060503060c16050d03090c120c0504390305092a01050c0a06050906010b0c0a020d1406010603050403020c09040b04 70
    0x314600400c0010301c0750100081c0c0c6000d400310319125404c240400b442d02d903481d000642001d0302c1c2d40c00c119604c00312548034002d488450741d010420188407200a49401482c920945047c002c481c498040070100380064024403000300c0c0280402d0303000c01200d1003220f010340071b515015041880043c0c8941d0b40c0000502c807510003000c04110090765511201c2c10016030200e15000203456030f0a00c010300807038403103580c041c0595001c2504111410303a0744a40c2048284141409a03407500b405110300c035000d20480134480c8499550390018002034001c06400c841c03104185010078602804034034082c4000901c0c19018010268403c0c80445102d424103146520780005410818100300d44408500240311500200344a000c000c80c0b60b007455075519060081c140c004280f14a0284200194401c0c0041c100c1c80b09031b01610520b40300c00584c10008000c0000c020100400d2040c01c000040860717044c1c0c4031910683c040c1d03081e10000c40c103a0080001068094030003414440d03000d000302e80851841822600308112 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 414191276 1250 414190026 414190031
    0xf02090618030a0510050703060e160f02010b03030406020f060a02030622090210261e1308070b0a06090207080708030702010e0106090b0906060f04061107030614180703210201 77
    0x10140d68407441c00e01c44d8411017503881d84071001e1080881c2c2500503c0302a100156495259141121500c140c0d44035503070a405c00c020902c110715561314002c0d0b0240741030b842c01030150b03583e482c0c0ba5400650342c1d41c130005000a55101c1c0c1c000092400c45148252030040c0c2c401030207040300a083c03000b40102044480342802d2110769030740d07280300166120308202b03101c41e13002d80307402ca03d845000c1c02c0c844201020380b00a22498000e1400c101070101e1248208070400e11000316844561218034800d188081c1803000144254000100103052045c0b03060744500c54052983c3c240a016112071300c04060780284400180503410a2101c90b0020740707144051980030905100004481e641d10110070f0035a000740d0700134079146948040000d82803c10610f040c0e4424030544885107400324402c258410362089100d040d00f00018441291194681482200e00440e00004180100b1801841c0e210300e0400c00d03100883c0c019005040d9004140c00840c0000441c1e0300700b490040c003070b0851a504101214040360036011550f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 414192526 1250 414191276 414191293
    0x141216020f011d0c030d080a15030503040605040e2401050913050c0d0c18060305042402030f01081c080a0603060216020117040b1f26010f0209061803 66
    0x203000d00c50b035034040ca190308442c19040c120780100d5050221262078503021b41c005500d112510f541104540d6081080c4241c006031500a002900011098641000f802c42c0000100000c1c0c080d400005007083e80c0080c1d01010103900c03111560646441105c041d2140d03c4180309021140e980190b007e8038251030f01401010b0800407440100044a600f1102d035031280c080861650343c1240c0da0722401c5501001c0342458410144021000381804c0c00a03c601010592500700040c03c1000d4407441d1150800d030b2505080d121641c0b19400300194004072100078160101800000c0c07075071800103150b000140e4450b80059400c28a031821a0907140041000b55102c1d22410000005089880140910034000c1091080000e840c4001000803002003a12011030401000b80408551800c1d85181c200710050800130192144000c100062001548100065407070036022101400646051981c1c1c130110074004c0008040961011080380108820a50010b400b03001c0001003500d500342020400d440141200d904d034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 414193776 1250 414192526 414192553
    0xe1614030702160902090d0f0609020d030e03280b18070609050a060305010506041403010b060c0115050102010c020c19090612060501080703120e13061514121602 71
    0x15401901d0701c0c0300680c450f50a520f1400e01d4901d60101600d242c441c1540741014460020700c0da0000180c0240c5101621000f18040004580c0001c860580c0503201c0035001c082810f028040d1000003500b1382c000d0280795462009a8031a0072403400c40480d06000403040782507038071110302c0400028070050801301c01c410011019442001200020300680e40d414050320b04000070b0021f41c18083e031200c820700d8206801401166203010594043d00c001004051072603c40303400090142c0f240381566034108800040c1100d4507001900120000355410f648810426a102c004a080b6070040d0a01d00c01600b03c0061925103240c03500000c55000f810001b034003141c80e254280075049442a5105040e8101642c08160030003a960180900510030b007405402a01c1c03441d140e0001010380c0f40c03450000c00107900506a03807540d8120442c3c02d085110329040200c2ea4440300740b40458021980d003400828041c0c64000310001c800021207580b03628880f03802c051600e680c5ca50504003040710000406502444581c80a00c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 414195026 1250 414193776 414193817
    0x1e051e040902070c090603050d080406021c0c030c0e09130c0f08010507090b070305120618010f080f0109050706081305031201050f060c06040803060f040e1b0a0e16 72
    0x50109107100590b00c01942c80e0014211180ba4010384030a400d0080400100e140070400d18a8900281040700b81540c0b1442c12200030722680860703290f1100b07031400482c440d03452503001140040181d1010007060840250035140e1030701e9007020a07800525080000c94002c038049080101c1840f54598a00968131007920a2403503880c1d07042204241e548000300144241d00640482c02000701d1030081e03240074042e48009180340f082030788116a81904a000c105252100403d036030f4501c170b8180088205503140d940359001112075101d03014030b611604810300c18501d018400c50b1100c950000045c08044d10700712042d100820300408240007031100034042004a40288020080c01c80100201c0f00c1b10340c1080d04014228400032040e5021700400d102042c28058000341040c0c100d07410070007aa4495440c0000682101802c0300e04a82050608984602c6954001450b1024140b40e0000842511700a418820805068415114009241c50120b03a034282c4003856907001074030501c1c0030f400040400002050b07 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 414196276 1250 414195026 414195029
    0x50402090d0204110c0f0102130e010f030305030705072301050a1512060e100b13020a080a1a0411121506041701090605070c06050c0c0706031d06071e1e051e04 70
    0x2c980c0d40000d0038820000c41701e00270002a081e81c1d00e90030702a506001d900f0099181501004044c00360000c003180085000340305591040f6402070b001000c940001428018120300b811680849600304404a03c10f0003050003141c0001c100103041c8103000703240408003031104803420400d82e0200d5662552112851040c05a254100d40c1010302081e0740c0e040b00141b1a8250f00c3d00508040307184140002c003802340e4042c584940201524070702180b1840c13407580185680c00d80b00c03850b81d8082d01d0a6140009150b0200c090142404081001d20f003954071080c00020180090030708071f81c0f101d070810003808024000b070380c082c60110142000182c0498281d03075403030860300141c0d509400300d004070f0903490801109004890348a045000901e0070117610a000035a510079901840e070a164540d8001103540b10f2049a249084048000300d80310360038001350203003d64814040a5000f44005900031000c00e025564881d0290f01c140b0721039985514942c8119400c2d000a80301021040c50071454104500d4038001a00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 414197526 1250 414196276 414196303
    0x501140310170601030c090510030f0515161202040e0105130204080a030806210c0105160c090e10020f070618020306160323070f021912030501050402090d0204110c 72
    0x20f8a5044d07041c010a6044150710164025040c541000f0311800a440d00004481d403101989102c80d0700f81c60400e080c41007121800d00040e07007440410402c64804156502040016103d146d00140407118001c164441c9000b03102c4d54000050040100e802d20089040304444c01d10001810584c48988041c1040314244041c0c0000b220807050207031510f002450100e00541c40c4142d88620700b001c0d00e80c940c450b20100c003034030b0510001103101a095644c0501750000694001a00000d450301c50086900810407c4200e0744144a883d22080f00e1042c20f00c200c903007501c0c0d0f00f4550360034048a0384d5108050310a02c0d81075900d0070354010612006850400c10280150302654840d4074401c0b006400074101d50804d060015030030310304034a54841c006108445500600382c0e02d00150b101030030090036854a070604101c1601030352203c400030203000c07404180e0412101e0320b550520207643c0e6030703040000f40e014280d00e43da4000d2002c03503000300514099001d50200461010f1a83c00c10380c1d90003095041c0200d090b0a403 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 414198776 1250 414197526 414197533
    0x1204030309050103050402090c0904020d1821080c0f071401140a06030c150e0a08060402031c02030313020a050a0f091817031e0420030601050114031017 67
    0x1801050740141c0120040e240030302e0100036500e0681c0001e410400c0c060300c40f83d008240018901c3d0f16458a030101da040c011441404c0c050325000001421031445059000c0d10b406590501d0941003810000c0c109588005550381d0300145e8480a01d62080c80c0c0c840c4113103400c0c5900400455000031103481c2d00f14000b090ba500005014032694191507120701c001040040d03e42e2601409000103144800401e0035140b0354021703a003100540174016520805410300c455070041d203503030001462590004100740f0a078400c0d0140c40100b0102c91030f00c2c00b0000110200700240c0c0044c00010486981113410103407150005225145080e510b101141e003805c82500081d03080d0301c2c20b000a0080040718020040314085000e04a60310300d003251034924041c00304411400c3c40d44000008210690050301d04500c4c00b02108980c070b40306042c245000b81021110604504c4007103031030007440d0260303d00820824101c4006844080411420011040756a030004200c0841f8116442c004141c05171301180d500307000050300005 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 414200026 1250 414198776 414198779
    0x809032a070b0901050d1d0f0d0201110403020a12031202030c0403021903080909090708120a27050111031603020a0b0a0b0d1e14030a090f0f03140f1204 67
    0x30941054003a41061070003007010400401c0c640d0741701d01141c5600040b454000740d109985d4036041e0700004102e4400803075118040c100455042c001c6520b0901410317680080014100c410304211050145101c041c0d03200300c0f2060200b040240181041070050700c03c2ca020241020300f51860b40c220380040c0c6030f0101c208008201401142040c0000c10b510150706013020018901e165500c0c3d90340d10079040140c0c014410403000c191708180420400d000303001c464058841400d49503120a816030082400c040c009500740070907500c1402c01c02200e101600c80c001e0144c5806003008015141140c034480e0104280c0710801450b507480c1d1000203004c402034400d42c080e05401d41c6504260400000240c040d9134501e2810305080555501c0c920520b08807540814880940d88014450100c1074481001c0034258912403030241000e1600400203011048135034850704074054071908508801d1000d0f00401044140c50241403010441c4544560742000040f0704071802d040088101e103040001d040041ca00c00740e4003080 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 414201276 1250 414200026 414200107
    0x15050708060f0103020403050627010204080303060a05060a0c031d031c0201050106080925090903120f02040315020702150d09051c05070b041704030b011703090102030307080903 78
    0x28042c080c0c00b403905500301401e644806856000191005944900003030340c0500011940880c0040308072410001c64541750750f0103140f81c0381d0340102ca50070f03c61270920307001241600d030200039109036004075078845660415a5400b0341c3ca00d8581100030002185400d02c1c4492950304229084101884000400082c0c0c0c40e260080d081d5901a04210280490031003080f03040400060340c001d80309043e000140d04164140120030951109400918400d8141000703070082c5034120a080c000d000e0943c0c42040b100d01181181c030200d008038000103040d010805022030244081e60040d0040c5400200180e0340200103803220740b810790060304a9101182c8070103248051141c24882800d000b1121180ca41c14444a070000a01c0d61091000040c51400348802180500c070402c0c1d06200728408210711541c1d12034a0b801c10f040300400034480c0c15004001c0400503d03481102100796408850306800440c116102c60344140c0d2010f034010800081341c401880301c0000d00541450002e02138661803482c05103007800c1e1a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 414202526 1250 414201276 414201289
    0x302030c12150a02070c0b0903100b0f01051e040e33190e010902120c07030503060922080903160e01090b130905010203100f0302130203041505070806 66
    0x4281031044501c8440c0064110001c03400752080d4010700b01d03680c201e07521209040004c0c084c0b002c0c09014401c01e48804154000a00000c02c03110008804550214483e07000c1c00c07050b41d5007091a81e030050341411682a041d406200a808081c2c6c103031075442c5150001020400940d085980010218144034003405481c00361103015805601280c41810001040d00c045401401c4044504030701840107407868508104240440c0c3d006000c2c00f0b00003070301a507981c8048d00040d4201602400ca44515100429501c03003644045405040c2c1c96160a8216a070701002c120030302d440240f0b10984400c20030745070b46171005d03d00c050794250b81c8106013094171101c040040c50b15109004000c2c80c24842d8500303081c03290112030b0b00801d044a004100108540ea1203401092002c100d070304e0301031211410145041d040180640143d0b2203082030203895188550b4600c61889006810300c1301a400c01e25100404043c15400d40045500034000c0300140c06958a2b100c040c006c640e000c6690708005141c1209100d454940403 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 414203776 1250 414202526 414202543
    0xd05010c1103070201080610020a050109030e0307090b0f0103020c030d020a0302120702150f060d050a0b011d010b07020402131e03030e010201021810020a0203060a060510110d08220507030203 84
    0x41d402141802025400a410184080c04040c0f041c40c801c005250900d01c204556544568000020b110901491401401e034080c0100000d220b0b015030302c00490340b64014402da00e03503000003c080204200182c0015402944080d0703014060780000c000c0760503018080d0009042040f070540e80160340b140c240c3c02041c03000700060070010071900310700c0d03d42d491607440402d01504460540c00c0f058043e1a9000040d02e0020f481034010480d000c0d40144000348550506024103c0f240c11030840c80c0b0000c25101035400b00024000d0060000040c070110f00035080aa01516007083c5030005600039541320b40c2150942a8004609104011119428010141e120b081c10a00d00002e000a40c10401e06200541c00b420700030400500487e41a100c90035150301c2088100d60494000c0c040d54252f00f0f0110b090340140001d07006142c001c0c0e00600e609881d040c8a0030205456182d07240c050440d60701114801c5070615000b03014503105651169208001540e94484a204280304500409415245105242c1056202e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 414205026 1250 414203776 414203807
    0x60609050108070305180d0c21080406020f040b030103110a050316050d0501230103050d0807090e0a0b10020304060305011a0a1209080d060e0a290303090d05010c 71
    0x2141810841660020030b441d822450030708004c945e55139901c074010600303009030900e04101c0c802ca00035a0380b503581001c0e40c0311000c3c2c0200f00611403540d04111014120381d140b40c4200c0010003000000b4007058081e8050403021070321030185403a080d6241d2003800660030a030810303103848030f030f00c4260351141ca8116202c0340104030907809000000c40c0c05081640039481c2e803007818025078a0080381400c000003940700c4141200400c0581c0100890440202d100b07038000d000480755481001c000c20101801800d0700c5124000300d035103981c130031800c0c0300303043c40f854502510840301c16031211016901c9640300c0000c2103450f800c0d03034001c54885180a00040503203d06a008140343e0101048131120b180000c001c03210b8805c020300b8142103c0c508840b02c44020000f11202500b1070f000890100380c607402c0354100b501216800200c41800f62504c904500c21205440308203502260003040f071215400a034105d0003803140004054a0a059180380480e85198a005040f038481c0d558401c01030013941c1201120119008 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 414206276 1250 414205026 414205037
    0xe0a0518030406051c090605041211030a0509041d16050d0c0303051c1104030c051206042303030406020408120a1b06110c100f020a170a0912050408010606 68
    0x4011122a40701e114502414040000008011142020700d411081c082d00300440f041100c1c0c81c05080c140020142554220343e800103010b50082d13030500c514040065010590050742c42c21800010584140d030201c06100d170400c0c0c56643c0b400c40c0c1400b212805660003003140142c0083c404802100c412010700340c010a00c11201c0b04940000328080180d400b003500c3e89403c05580e10f5080409a060189042c8044d500a03030502e60f8005210f10014007902c1101d12074001040f900d03860300100328013080c05031444d8401e940001d0001e8041042c5d407000811080c0c4171030344c40c2140f0304066243c07815503000321810b03100301303030000b074100107940c01000201001e003020001103051503c0840000e10882c0c4054907110101601c052050500c02c1076405107160b011842002c950320f03508812002e07215000001d09005492411071946a0400540222038141d0115130b03808025030519040e15041220180401e0703440c0340c0d10a0346a00055041c0c00c0740c0001c5400da1540fa4449191010071425100580c100300100300 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 414207526 1250 414206276 414206311
    0x21021816022e051f060323040b04020907030b0414041127070315170714030a020411090306011205060105041b03021c0f090209060303070503220f0e0a05 67
    0x3202c0c0526244651110300701281c0c2c0c1e103503915003070940d0790802080212503010f002c00060384c2d03030590301813003007140c40010140e85110340d04400500d0003000c1701d000e010024444000b8005181110031154800c2d420b06001078449403010106c0e0840d442591080e40400e03040b024002400300c2c1400d01c1c00101012100e0f081017030a00d0b420000d004001107440c102228054000c00c1d5103900a4100303244407071030700100045907640e42d1400c94600c5054107010001d4005c0e20004a0801d509402c101142c03100030b401030820340a0740d8240801052003400c00d4842c0142480000115542403140b00d00034000c054541c1d882c1131481c102641000c4041e030100344101c0c03a0504e00c1e180a0402503e803240040d103402c005884451400c0300703004000075980f1550312140360008442c07400440e076100c500414001e0b6414100c598414051581d24483d048020f001c90384148000e06040b052095001c01482407501e24910445d40c454400312150030503080903401d41c640404104454503584105a484070f2101a04861030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 414208633 1107 414207526 414207583
    0x10020d0f0603051905150f040b070e0d11010e0307030501050a15080303130c0e0a1a030102280525060608072102181602 53
    0x24900e0200340c40294001486220103032588034000388207800c00c44481d480040c80440c422101441110039178405102030000150007102a17030803101060601d86802e85211900809480800120303202c0e511480c0c0e82c1c00c0301c1c54501034001c101c0040c6400024012140301e50242051501845060000407c00c141580718620520440d8410840340c412003480515541d030b14420446554010700c04238170301604089000d4240c5219080700a4025035032140c6d2241102c0071204030300d01c0e5941307400d040003c4006d0720081c164a04214000c40c81c0411442203182800d0310601c5603913507520584025062540104200c0310103a4000f400201e00000300c261081c04044445030894001341410800104520009112010b0300c40e560a840c40c000108503d0a092525882c4280c1e44295044500398001c0c020300c0145004e01007242c900310008402c1180a858070620009820403285c0099409196 = true := by decide +kernel

theorem cover : BRFrame.Cov 414028776 414208633 := by
  have h0 := BRFrame.cov_init 414028776
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 414028776 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 414028776 ≤ n) (h2 : n < 414208633) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
