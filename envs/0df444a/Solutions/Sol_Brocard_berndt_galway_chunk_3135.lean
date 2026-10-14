-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3135
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:45:42.394113+00:00
-- url     : https://prove2.me/submissions/a5a5bd62-a719-48b7-a19a-f400792de02e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 563669064 ≤ n < 563848920 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 563670314 1250 563669064 563669081
    0xc09131103010501060509040b0109150c080f0708040e0f07081306021e0307140702090c130b040b03040b07110d080a060e04050307020111030f0d0b0a12140c010e0d060c03 75
    0x5500e000f0000820b503030060018050494100d5040004140000c019a2201100c0c040d07801090a442c3c030040d01c0b1401107105100d04d0f40590550740c200103069601040c140d00410045038012808101000155546810306030008001070780c24460b89400034005043d458001d03c4a1201d042e6085a2820710456038111406500d8032441c40140480400b03950b00c4943c03040d1490300c0059451200c0b00c07000003028090b1101c260b0f00800103209600e904e000e072070441d04800000c44100c00e50910000b082580c000003040102082c541c915181c0c0f41c50704142a106c60000c14604c14007100d852900d422160100e130f480d05054082c102071307480b91500d8000c2c0c801480c00350098241941d244052105000000018281d024070036a16803140c403840c116407544078040c0c80f0311300109250a0100d1b1085240a42108440030303405071015a00c995a03000c4a40280b0703403a4400d544038070100285080150051000c0c0800034000c0c03c000703080103424000f003504280c200b540078081560f01e0788a00c03001031007500b0a014 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 563671564 1250 563670314 563670319
    0x60705060709030b071409090c12090a0611070201050a0f020708010c08043c020f0925080c0d0f06080a0309080609010501032a0b0c1e0c091311 63
    0x2068548980301424035203150006480384d0340030100244089203d400c030303148610702484902d4105040c0c40140842504060001c1c03034210f038140000800d038401903c00a01c030340e07084401002401414107040341101e14883c0015000c10b030800c13003403004d41d070454200d4400032114a010610368120800c00c034149185908100c2c920f509101004011a0f800151a809540123841d043c002c80903032071152420708245052891028100605101c0700380140c42c40c04025800134100708140801600001e800020407101c03450003003100c0102e2210205614940c104031000c909018040c1d00340810251064050892000c11081d1201190407201d22079400044c020f106500c1210203002e41c0f403a000c1c103403190902a07800644038550005409650501500d030480380c114240c0b00f408030210f06080440e00c0c50b078030b0100b4105006000041c100c4101001000d0406217040038240c2e02901405191805a425111000b82c0d40000f024902a6a44030007664118000616490032106185445041455500c42869 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 563672814 1250 563671564 563671573
    0x21090f110a17010b030f010605010206041401021c0903230d0f06080714100201050610050a0e101e0e090a0b1305040303020706051317030c070206130f0608040818060705 74
    0x41070b003141500940c40e046421010b0318821000740c2e4896080358054401d00303005a00c00b01c0071401003103000000e00d44c0c2420040002d45801c0c0580c1d29001c5c40d0a4030710203ca9641e50390004041030580c8201c07268014080500a0714185034180c10f224281d000f000d00219000c1d96414070244881801d80c8032a0081c4842ca050b107000c0b80d500c1107810243c51818070610301842189107052004c51046c86001c3c851074004004010310901020304841075044100c500c0181300c0b042510040d0340c0d80307400c4038000101c11a60760103000031035106a040380f80e0055504009100345914488490b559081c0381c154000d003c900c00183d0404010002a04241c0010500c040d00b0302d000284414594542c00400d4403d02510081c0031a4a50110841420403000b50103000048100145c0200d02c10711002190003021000c01e42c0e0074890960001046944086a007a0018100394000c0100444200c1c07200005d0020b820321400354a015150344486104031443c55611160401720805660b86207400e82e426203410000f10b4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 563674064 1250 563672814 563672849
    0x10020d200f1b0a050d050709090809030f070609080f120a05070c06080f070801030f02041d070902040f050d02010207060c03120501090f050903090a0306090807080a21090f110a 77
    0x10181c04085140107003e4441c1403804600c905082c103155034100d602400a0255628000181c002000c3d1040b0486080d4805c101c401400e0f5002c00409a400c00b048015096080c40c00398064000303c7e2a0f40708000341d402c0303002d030f800c840080440c0c9000f054205040321580c0c1c0b0351424044545115241e4001c040084040300482c0840d801140e1500c64540c2020074803803034035035460075150070500f40320041144162028910050420307420160300041c50b51400c0c0311800b00e81d070585082696079003000c014190302103010007980c04142441c0b4001d20040e680301d40000d095400007500e504c224010703042408080100f0104140c071420501c21070b003440b40c17410011075841d40c0089002e094110031115140d801d000201d52017103004000ca440e10003008142c00212880d60b038900c0040c000c194019558407009100c1900403e034220020a08060141c0d1220207402a03085a0b040c01500f049564050038030f003400b85070014180040c043ca200303420815842d0401c0800740050320740b12007504071320039490415020 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 563675314 1250 563674064 563674093
    0x30403140601140a0b04031b031401020d2405060c12070c090f0c0905120304080a0308010e09060c03040605090f070308090f1c03051605030406080610020d200f 70
    0xca030594110400d600308042400e010131081c00c00901403282c04a000300f1040000410031550346182c1d6900d002c0c044000d80e81c9031140d0307088031080c0c10040400d0b50001042c101d4031025215042c3d4420100c000c0d440400c036941035880c41ca1042d4006c40b4090f01000440e5001e02034200000b01504a00000c4503039142c04030329199050303200c10f1060089690030040e010f600cbc072081b40074030b041c001d0780c40c0c0d0b5090740765181c0010045a61680c0c0500d4025000400c0701041040e001e20840c0781c49400384d141c079149545009099104550000d0042500340c020109200d1010300348812250400e4004102150f80e07202c40c408542860f101c1041181c4c20f1080440000c20003001c02e000d4000d80d001120300341e5008510100340140c01d845004910910f12079041c40000085c010300207005030004103003d10404130000d030fa600d499540250402008204907808014044c40c00e00c0240b040341c2c600c4c0c4094031801e50b00c15005040d40500100300305c4c503105508a50051900f04201e00c841480b10724044540c154141d420 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 563676564 1250 563675314 563675323
    0x2240702010f02010218062113020a0b04080d030902040605061201230612100506070c03060b0d08180f04020d0e2b030506010302090d051506040c090303080903040314 73
    0x24101d021030304000802e0481c0c1d0061081d540c860500c02d100c03108242150040010a40c45000960340c9154407014440c202111504194032a0b94845042d042c000704600410a8041c0b00358030820200204010a1001075000b207040b0009280c6404c01241100182c0b00140c003070034184e000340e500207001040810360607000c64299030490340c18a81c54080c030032030740c2d50140488070b0201302c042d0052010020803030042d542042895010115403107050400ea00d4000103074213540301e81010344502c800150284140086e52052010415003110465245940c0743d440d614580101c08800c03000f42c41800e4030140e5500c40028502020345c00400856944940c60007801c002d280742c5400f50003500c0b800c0a403005040d60120350245045d0140d44a01c4d4641c0c2c0c0c1c51048010b42001400141015020300014031240c136500c00d180441c41c415009010b83c2003942041040628006021921441c240203007140c1c1241c200d0b1b103a1040e6509483e090200e5035640c1e0300140341d48600d43c0020700c9844684002c8407103180115 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 563677814 1250 563676564 563676577
    0x507080a050901050907053a0303110414040203040f0204050a021b030403230f1504020306062b080c0a0606060f030510181d03040617040503160224 65
    0x60341049580c4030440300d14200c5030222048042513000d104140a03602d0102e07040301c03104500d10803c8550400003903d0154001c3c00724104510f800c41c1d1001c410803d47c043c00341e56840a144c00c000d0f400d2074504440c6920401143d040f4a020f685d0000110b018003c2e025600101036030054814010b0741400c41c00d250096010000890307544110400c1066625404000c42d81200e4100c2084040f40e21901c078160424440b00c00030010902c1403400701e46c907a0f203050002d4510542d004065000d43e00d010700606040c14070051290307118940445587c0380250501581c18402c3e00c00045045994901d490050414480c008150205200c1c90301e5a10030418180c0000341a2015543c88200384441110181d00b41e8405a03281107200c480c2200034080812074020b08418480c000201240c035000316224441841c0d01584010b1254000141c2405201d41000c2511454024942d42800078600390711000d4680c042d16180c0d501f83c4c90102d507068190b550b0070f1690203081180d07040e40510785022000340446030744240b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 563679064 1250 563677814 563677831
    0x30c0203161b08010b0d02060a021c030c0818071509090612020301110f03040215270405010506180907050c06010924150f050c030a030608010b0f13150504050708 71
    0x1c000421000c1c0180100c030300e0080003501d01d806c0c05441e03500300f0400d0b410a13001c540c218400e080034440c88658000c02c0104521050300e000403101c0110f00010544900104000600c211641200c200640000340c40d04c2164000b509000c484449164119908504d5a01840c009400c2100c045902996200740d001d040388220002c2007114204444d41c9094025a811040c100c1c20030300c00100035040a010302c15420a0301800b0380d2800d09084140d040f4100300521503e854902180c0820540c101445843d014050407540c850516030000c2c0554076075440744820a0040c000407010400481c003410698000382c5201c000d9402545c2c6620483c002410049500709000c0c00a651085002c01500e83c564151034404000c820782144811043d40c454841103030040c1003120400507000056400d2018042c4400291f402094407450010b8541c2501c6103038507058407030b81a0340741e010000d075103442c0120707448410303c8804140c1c151801d1401c5011243c55200c2c6800a080508202403564801480c0e841031219 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 563680314 1250 563679064 563679113
    0x12010f0e06040807060b030a021012060611031b0102070204022d40060e0a1a04061202070222050a110d0207050709060821090d03030c020316 62
    0x220030203103a03580740680d8040c0440008014110110f00ca50f080303641410303000340031110212000d03804942912a1201c19000242c8540b002c4800341189004120092425103040c032000250800e2443d00d0f4464074044000c1d0f24542e20424088490a40513070300100e800510840d151200307807151103603850302c3c1407042c18406461501c031041480d003002a0360011240a080b10101074003c007803908680608105209211529017600300b913440944d00c000043c02c503580d26030110f08140d03001d0005207c0c2e10f421562131802c0ca105000078080701c3c1420b0f2011680c01b454040c90440c0c0f0180114020301c501d4002239000108400c41000b40d1301c140300224585050303c1c400f00456a9608054011110075009030524288100806180c003031690300500740d0039006034107a0304c8180e84d07845803800311176065204c0b6505420038800790307441c0c10100b050103102d4229108520b240850810000340021042c0c1001014181d843d9500c00c4101d10070000c0d1060424405200d204200c51803d094030030000c240b080c081000c45 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 563681564 1250 563680314 563680331
    0x603150f0303020d08040201020102160516090b0f28030605160c0f080a090b07140f0a0c0e04172d072d05060a0207030e090c07031d12010f 61
    0x8032404060308a0790035901030300400c110541e044441d9100904103034115034091040404034002c5054060301c06210354001c1109050800c0b062024003203a03441f003083d0700e03e000500031607030716a01c0c0c1c8100314181c1141e521032900c003140c100b002d03040d24270300c0d41039078850988001108005650340300900802c0321406c00704032580c0b6001c04403100054100c000707144010b07c0075a140000c03408801340c503012106080503034a0302e455904104070764014180a4484500310840602410030500c0540c604140c280c010300401c0c0e04548625108940c0c40c814601d00381280800282442425400004c000350a040e04643c0c0d950203180b10300c2c0d641c43d02d81111000b45c0d0b5010509054480c440e0803200540d910240300f1801d04c044a03503405020030582d221456100340c070030b1134000281050200502c41c4100213001602c41020f428010030014a0385a4140545503650900220780c0103c0140c95409a151070f1403565460510300c09240b2103420351510390004680340c14920701d10300640000e192072154030802c000461 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 563682814 1250 563681564 563681579
    0xa08010b0405030d0f0201020d020a0c0c0b271f0206090d0203130b090d0b0c1c020301061710090615260403050d02040f090506030d030b030303150118060315 69
    0x21607482003d40c0340c2d0000c048112081d02400444e15aa445030000504000141c04004107a134410861030000807421444c1004104038400b15001500001070f04c10f08003103c01d289400302c420000040c036040c240c06181e45100d0703500c4001c1003001344040f41c04a85c920185086c069580c004c03d840d01c406074003810720121310341403001080c0ca410400b01410b0340300c000c0c80c000b20400160701c2000740035044605074400d80c001c129904207142c022180f0040f803a940c1c01c54031160400b46030344112440865070041004102da980d10107414040c410b6035520900c03142e15000003c111810035940000c40041c1003060002e13030803440395030591700c407251030300c40d004202c92111000c4455a1401180d807940003410021402107071080b000f601542100140040c5041e48074001901c0520041d4040101c1c69100c100b000f9081c1810311500000f400030f414103000200300580002e0712400002c11600c0c0200910400304020703071003803040c040354a0180d500d1010321034949a00030f000d8040401240b00e03102440340f00042e0311 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 563684064 1250 563682814 563682817
    0x321030c17180304030215040612090515070c0510020309010b0402090d03210e07051807020703170702120f0d0f050702090408040e070c030e040b060d05100b0a03020a08010b 76
    0x3030210884821540d1441542c009841c081010000d4501c0248008401600d070140c00c20340e0000001d00c6507468516010000380001e4903001000d0711a42402c1080c000540700082c042420340780100420090340e5511421681c070000d051004e051889011802009116203500a60060807a0802804440d4035001800240d01c07456500c150040ac107401c01102017446070102006d02d450490014a0481d44509640c0907260a500c01d658260002d203010006860400c4400031600080c8014a13000c0c60a004040d4490600348405088006900c032424600c8620508030345e400c60b070040000d20b5281844c640d542d96040d00c175241e16030364840d0b140c10020480c0075109100034040290703629868041c85a003400014400900110303a070700e00074040400c15100318a04140300e40d071a40d441e0323942286541001820000d107504100c1c025803034802c41c40207076200c0004648040741e103d0008030f082d40368031240c5504580107604c41c650381d85010807918000d551540081c02901803681e00d0f001c00741d0703c8126070940c9 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 563685314 1250 563684064 563684087
    0x1050102060601090e0a020c19030819060e0703050a020c010e1e01022b0b120a15020c0705041109030601030f06060510080f18061602011104050303120406060321030c 73
    0x240b45e840d10000740108640e070010800300c9021016616603001240301400095480300e030172000b1441c044104100f41100c81d188405806c1250350501c05503140c1041409011710181c510787c101a162000541458032540413225000a090020000000c0400b030301900c4210400d48004103104a01c1e014044202c14000daa0003017042159900b0080905a48141005000c02c6840321181c0ca0751401101c07641c07508610305c0200000005050300000e14034009040e00c100c2d01142c441a441403000c140381800014584044e01c81c103440c001848109106010914015540010790503ca942d001008200b0103c4401c08280e200301d805002a64a990801c110461540c15941c0000d10f80b000003282150845251508401005084540324541c00052410440e04a41c40308643c0c003e4480d10f00090342c240304403000c104000044604141c05c1c100000d86030b10440d8080c010741d03506170b0085001e01c8420b45c00070005507445040e89104000c0c08000141180d950900000880c0c50020180ca506007d0100c4140 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 563686564 1250 563685314 563685329
    0x70e09010b040f150e032407020615012006070c02031b09070e120d021e061b070302030c011a0405070518041503020d050303010305071a0307081308120105010206060109 74
    0x692800c14100c1c4c500c02500d0200c40d001c00030f0302c900c403490546003031141558440000e24129000000d4000e0300e40715820150140f070840d072040c010030000c00d0700a890a40000342c01d1810000203402101c4c00c443c10806464500b040f4001c46060000e51500541d0042416200740c0c25182e810940b05a80071000e0b5920310015001000d00e000190014030a140c5482c806400600d4500800c2c05040c1c1e1034a0215084280e0025922800c1c100d1090f40e200b01c50f000005400710f008100900d840e002c0200c1c0d095401000600300070010811104050003032041e10f49408001d402089440c2545482e140c42850b13850055004c0c3d40381070b0101d00e01034070803c21941c8000c2d107040d40c40d203d070311100140001408400d03092415440e03000c50100040e55011114105240108010f5490b54114100103040005a500c90fa150030708598030101005035101c15203030302007040e040c021055510340d07900381410803080c600202800c2c0300041e0811200405860107040c0d5000381c1c2154401d44d290001503e406009004126 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 563687814 1250 563686564 563686589
    0x7080306130603141b03010e1b010309050d020a0b0a060b031504060801091401050106020304050d14011401080d0306050307050303040909290109050a0b0603010e06011403070e09010b04 81
    0x40460918000c900300701c1c060074000148140e076a443e120214071010440ca0099080a5807601e00060f103d4502d038203a40c0214001c022055005000135a15548103086020300d01028101500c10b81c00b0340d110200c265000015a000310300307940301c02911010402c2c2d0458001c0005004102a170900f403040c1029118002c18062540c0c135880a583c241c3e200035a48241d00c075803a00c5001c1020300c820302840421303d12498403c036443c0d0701d40c0c50b002c3c29150160894001c40d40240401c00180e900d644002e1100303a0040344612004070491009400342c20a01e16144084020400000d50042e000600a800d0071540c0e908101c402e45500c201a1035464500c10f19a15034428802400b0200d90340c0d00201c06940b00d800c5452030050300006002c948510f419030f010340341034000010004601d10f0f006213a403040c1d220b84c0820004402c2d0b00005d01c07600040c003406458004120008201c2e0740030f0308524070145580e00b0415200c0c44e103240020300c000c04081041e07018030102800000c00908010982c0c05482c034100320003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 563689064 1250 563687814 563687821
    0x24010e010503062404171b01050c0a0b250804020f01030e0c03010606030204060906030c143007030c05030405071401090b0a020604030e010c05150a15080d020c010203070803 76
    0x440d51904003411842d0321035090404129080740d82c620700c5601302055410a80c440b403030415905581e0480b800d0110a6400200ea0440209150944000300c26000d0174040d4680308140030241c40d2031250800204a1603544050100400707500e41c0940e0340340200e5031010803030020101c3c121030741c0300c051300c0c020f4012200711200e070304e650b0080d00023407007200c50b0100302c80112980302c002a0035501207502483c046640010280056070780010400058562410280240a145030000700f000c140c006181d41c2003100072544d0b40c500781c24500c2c0c030240c0641100300300e6641079114100070880003080d09c0c01b0340402c0c540010108964003a4060b244166000701c00f409407145050050080d500da0a08618104041144080340860102e00075156201e4194002c1441d407a203440c0c040d0418520701d10701d03810b1000d525090000264001007900700103494403d002e00588644985401900540c03142e4101c00e44034180108800000040702d00b9002c516901f110018004880166181e00c07070040050804801003000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 563690314 1250 563689064 563689067
    0xd0c06110706140412020d050a05070206041d09070f0e0a0c0221030a0f021611060405150d14091b0105070c03050607120e03041a0403020a0e24010e01 66
    0x44850400303162161880c0c010719075201e00032555031a20032600100c0303d200340014440700100b4007003800018002480307000340f042c1011340103014186c80340040060000e240c0e01191070345816180282440700000001408664551903c080c003100e1100f001c2c030480c17600080e81071002040d0422030303041840701c10080c0c59003000103000e812034803000002d500c40c409180b00e0030103c01240c0d01d02004842c0c5421b40300e040040504040d9a000c0d5094400c1d10b00500401001c440240652600c031544000005080e290f1a00403030440d0003954442c46d403108000c080d0a4030400044010300c1c0c0000290401c000c071000744001140e95400c140c44d401d0b0107a05c4003001d200d0400c95100b103817001d00414141a400d00c02c5a954109503034003070f500111280c0d00000140444550041000c03d240142548140032a046000005640b03015074422400300544c884021400490084200c6006d19009440004581d8480d044031030000c0040c1c6036074071482418005071130b800071b80c400c59401c0018140d5400a628410000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 563691564 1250 563690314 563690321
    0xc0906030f0e0706080702060a050103020105030c0d0f0e2104030f1203020705011503050c011106070e0a090f23010e060607030516030f020f06011802300609090d0c06 73
    0x1c099541075540c0310a40d61226040205400400655641220740d16202d88000c0c00c0c1400a050030401c641080010b00041c2c2c0c0010550358032503054040e40d40c42c1d201c01c0d85508054260440b00246032072030b00390119559407002c10400c030055568040d040600607486d02c00c14180c81203110248c01070303c0322040030780002d1162201401401c400d20340513003400c3c40c07900d646084551001c6540d0a03144030f09420070070030100740040d200c0e421003401c02e0120001d40111003a1035042c0105036070200300702c006507590340781e5842082d40044c011880c0c0c1000140c0392200b00c039000340b0b0280b080c3e00a040c80040c16241902240312500c3c16034034101f10300d880ca41c40720b0085c81003a4000300411000c1c40350501070003113110402d020b551800d034040e5030b841124024040c0042e050001c41e05000246420010060007001042052555030030b104140c0140d0b034001080c030405150402000322130b004008462914401d00f83c4e105402d00440302168400c000382c07248540199502210100b11004c54070303844060000c0b4081343d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 563692814 1250 563691564 563691581
    0x140301090e0a06050a0f050106020a05060f06030a080c060411100f050304030e0603150f060f04030b040503070209011e090603023a0305070605090304060804110109030c1202030f010c090603 83
    0x70100d448031492030baa807105031081120881212541d60612072030070b400754001e0a00404081c0050410030380e00f529040c0d100d4070002c0c070407030100e19440c000c9803050302c00b001003011440d001241181c6490584420540320300054406540c00c08c07c045010442d840e0002c1a4000d01e6071700d8440001c5c1680c40712098070240c000820640901c00d040d0001042a05c5540043d40321301c1071080e100c803a0020319400c000c030340340031030810901030f07036061000340100d07020741c012602540e8020040d0904e036aa0b502d011032451007000c8000750004101e600000b86982d075061301889200003004002a9161605d08603421501e403488065032040c0c3c056404100c04641e41c000c0403003140000c4049010a14001c00300e2a00000c00741b04400140000807a1418403510344560754000300c62001071482c09250000041026802400151107003c0d00303055034203e680030780c0340e002c019036021071000d0104d59070308842c03842010703441d100b41d010740a01240840300220600c00c41240000e9500c90310303009428500124010520f00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 563694064 1250 563692814 563692841
    0x180e0d0903260c2103060d0807081608030901060b0304020109060f120e0a031d0f061c15170732181e01060503060607020f0d051c14030109 61
    0x2050200382041c2c200001e2882140050090051030b2002c600201c5030500401103260401003441881a269104118041e0071504410040c0d210500703030030460401c1c410750038144860003c020702c440410514501461140320044002c04c038650b582c0401c0006880100d400034000740c004c4c0e030248200360061050404034125442e0a4140100165076801201c114808044090340f02c00040700030540d203c0c0c004c0d8101c0035100000b0160580b41c20100314280c0301111120311518000c65184200c2072407401105166015036014809075552000200c04121036000d140780040c1d041c0030f0300e04488000140311040358050b81c510303c1204110800080700500c40910081c5441000b01e0140d0603585071301c189900d002035568601d40780d0a00000051007a441700c90644100108400102b0280b90003d0135203a01400c19a0035603a5515a880045c1742c00c0103001846512031090305e02c00062000c00988c600c0a100d00e000040001400f0701000e07110142c46004902c8860f5040005004959058002c0a80350014 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 563695314 1250 563694064 563694113
    0xc02060f1602090a021312080f071704030c151e08130501050c12311a18100204050306060d020103020408030f0a0314060306040303150807180e0d0903 66
    0x32540003903005081510362240b51a0081041026005245c40940040000000d000d8940b049079440008e05d0113884c4c000e48041c02c000c81c1101c1441000c03005900c03c0f4944803901942e680e100c8c40c0c00b03c8010106d006250320320317580103000502ca07402064030400102c1d00301140317582c01d0281c420403181c1d1800145081d410040c82c3e2071002c0018400d0041a00606225580c0c0c1c1e1101061000c11001e04001040d00c01ca055020764501990004041c01400c803696000800e00e21601d60300f001c01d01d01c1c0c804001c14170308c251140100072040f00c1006a4103002c1880c0400c4d0340b0245040c000181c1a40100e001d0035078590030242c0420114030f0311800d0700d010319106050150070190741d00c041505503082020b0400030f007a00010595502e41d414480e002d1005241642d6400d00e0500c500465690b00c00108014240343e40c80c01820301c030422035608200100118001c030b9140c130b40c68000d40c0501044038401c1c81c04103803c00400461408000c505c0d05248091592901409840d580b2041c90808600407482e0f101c1c4c29 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 563696564 1250 563695314 563695357
    0x20c040c0e090c0c0f0a140705010c08030903190201020901020705040221061305070801060915051207090b0c160b0c03030f0c040e0f06130c050a0f02072c070c02060f 73
    0x3014082d40c5860003491015060304901407e1003c5211004540034407150005003080c0300c160b030800d090303195064000307511503125903607840c0b650f03c0c41c410442889521401e02c0c4a008203280d054000300b1a6680aa09440c4042d94403001c2c002030303000706110808066801c003503100c0c4000d001c2d00d9569018a0042c600b600c00440200e403101125070640c0d04030700085243c8014032001381c120349480001c0034000200700e2601100c50000b4028090303e50014410450b40d400702c1c55043c49081d0000c050f03c502d0003160307540d400b8000c00301d030340c0c0c0c41130050710f087c403076910000060004240d01a80d0503654608041e501d95076803035426191040b8010602220000d080c0000f1444a1031904043c0c46185015039000442c2445010040b80c4000c140d18840c0450401d00e08904450b44202070355400c01081c2000410100c20f0042641001010b0304a0380c410150151310500300030884407242c40650800030445025264040c007120034204008001e900245c04001c0c80748885980e40040c015040c0f4090b100c521b401 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 563697814 1250 563696564 563696587
    0x12030e0901030f23030a1412072a1e02010504030b0411040b0f01022104081c0306060206010623120a0c110114010315110a0f020c040c0e090c 62
    0x10802c2e00203032207045580340b8920030410000750040361051062580400c00d90200d0241e6502d20400074100204585206440c840017845000d680d1150881e50301c0101515081000a1000c031202d0040c0000005030b00c1110150b4140ca4171318511290401ea141d030310220282c0100b40c1b0400c103603d08a0411004100c0000803074500d03072081d0700452140c00c101842815035810030050b40d0450020501c10904002030412070703030300029a1035000d8500c029410040c1e1000032501c0700303401203920010442c060700c1c00340f03541011044450f005608081e1010003c0300c0c1c4501e01241e940000340648008034225030740f41c4110503008101e00030074000c0d07078008a00d404521141c603161060103441c14050340780c80b02e43c0c00d100389401c040400b0510704074000800c01405c100e40c204421080600c0b0240c884201c07485200e07a05c00c60764000d580d030308907241c110b43e6943c0c419200060904030050b040100601845000300258502805208003a0031240e42c1c1c0c01280309181c0802480310301c003900780141c200d02045a0460700 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 563699064 1250 563697814 563697829
    0x1209060f03090a1205090102010b040b06030412030b0d030908160602030a0305040602040306090f0b0a1806050402030c03150123010914030a0b01090204180b0306070c030207081608100605060412030e 87
    0x601c0301d5417010340300c80c0319400183c01e50714500708241c8541c1c00d00407d42444d454520640b03a00680183c030325058485900c0080d801801c403d86410b401a010340c056005050300034002000300da0021003251603610b441100f020444c042c9005040050700100301100050b4030070b0b0046038000e8040c0100602d02036403a5a10012661103a404581806d0064810414406402c003181c1d4003c1c5801001d00c111981204a1220880c11040c024001030b92040400d003951800c00c00501080400b80440780c003800502c03800b41e00c1c2442480b60400c03501d03502500c44400c01614010320f006220684416000f44d00301105c25421450900146806109214003800410300301403005009184960005940e641000d0000003154965415a0031050034840040341984002400a5000c216440c0c015200700840c0f40c00c0b42820915170140101e4403030309000140611026134810b08845134101111501050140140d050315040e11402d80c2c0000d090000f00000c03401114948042d6200386070107001d19032a0340001e8401c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 563700314 1250 563699064 563699093
    0x1f090618120c15170a110d0501060804050d020d0212030606070c060e0111031801141b030909011e05060a030b060309010b04140114040213050d050105091209060f03090a 74
    0x10030804101c20408000c8055800c030540700240381204c686909031a020303404950283c035440f10641c0c0c409046050042c0344080d10345030000040c00b40f0041d6981c4200900300302c4261015030b814003540c4418040b45e4000508100b01519035005041e00c8004d000702c00b0b00740d400003809260043d031308000001c0026101280540600a151110700c070780e4850340c000403d041c090208441e80d80e84204a21800c0c1e42c03502000703044420f42480c18510220346c40c00804001d01441d541702d10214140a00030880c0c6c2400b00161034110380c10340301150340d0780e60f40c044000c0311380c60040241290003003844c00380301e141040382c01007807004490305011900071054800325010760310460f00702070f05035960200b5469030301e07182c043c0c83c034518440340d2013500c0d41d41404202809101d010880070312590340010841e82d130b001c0010301c800041c1030003803580e8070340305440c2003a0b40601011210304a030790192945244c02660964282c4040e280b02a04403820010088240c00250380058039000f17092282c039018200099505100c42c0c86d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 563701564 1250 563700314 563700323
    0x1121e050405061308031803070c0906030b1005011d0301023708060a0b090102010605040903050c07060302030c0703030f06120c03030905030a030e090619080304051f09061812 77
    0xc040c034141c10414200880508000180084920810302184051060304c0d00b251540d5049046000840c28884c42c3d441039040041c40c0180044001655581d254002400c490103545440c1d1156900842001d82030764a020781400b0681d410181107406003040d0112440d01006000103103889100c4001d0f20409001074814102100010340c9143c1480c500700300030f03084003154102100c02d4203003040003440102c01d03030282c0d5a8804010400740441d0303100b500860014079020380b00b0400c405940c00d005010b03600c02c508081641c499900d0005601e84a4422a449800f51418443c200f100b1550b044025109403c4468400c5840d00d1010501500804072101c03883d00c100700304644580b4500c2e0203000c00c0180e80c40684660400d03203803680401e410200101c5500412104818540e03100c900040c000c03070890341804c0c84030191000c0410702e5070001008200b079a5044039031145014620440b0b070344005c420340500300003503400c100400500b409803040765000005041c2e51030003a0380301c110036080591032240a030f5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 563702814 1250 563701564 563701571
    0x150e03060901200306090c0a1812031d0603010504020f04051806010215011503090510090305042315250c0906051801170f030c070e0f10030201121e 65
    0x1054001610108900f1901902e96041d031a000000810006004140652400740003549400d1580318001000b008146e41c0d01403030025444001c0f0050030742c003445044020810320360307030700b504820442ca20350b41131040188440d140d0381c00c2030305006c042c4d0000741d9486c040407400c2c00085495a6440030400a41c207146010101d18130300030000901e03010401d1048510a242a00140080d04109000c1210801c2ca03007808941078045240185c40c02482c0c1c80d85810031071608070300b0401c06a201c4020300481c4c42419400a101812050a4609041c031505407a07004440e4424000184041310140003844040005070385807200d280300002c100389010030102c5118000200a0220301100d2190a01030a0191230481006030501c0b403004c000e440c180905a141d40e2040c0c202c81c1803240821030b01400d00b880500362a00c40c5514440e60742d50720310500802008901400024034000e030900c41c4c4520400040c0d15440303210b86103400560741141410003a03800301340ca417840e140e24481c0c044800102c0e20b01850001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 563704064 1250 563702814 563702831
    0x120e0d0c090c180b0a0302070213090b010314031323090103060b1905030a0330050a0b031204030303110f0304050f0705030d350705220e01150e03060901 67
    0x100100d071000307420f9010019214003071116012410030380c1c50a14185c00e00580e0389006000160038486c605607150410340c00c000d0050204401903041c18100c0b0700c1b510880c0e03032884400841985034000d4018083c1f65011600c02082403010b2480700003444000c400d1031a211086140c04140308000c00d0700b040d10017940b203071081751803400c102c05c2d00c00114030041c00002c000c1e824000025111000c902d4041d040150400120300008810860441121221940e1040341c1c4017040c072910141a040719581c2c40c0c1d82c074100d0701b414607040109412800744d007000b050ba40f0341130855800360018498100c8103070015400348011100707080104003c50060380100c000b04102000c0742241c51409026401150080d00104045c000303080d007080d202c0308840c50840500940c0c1d51005040319a01c202d003605078060081070814400041d81241c02003100041080411103c41500a041a110b4101c0d00c559055030301d481e40100041c80441c85003901110141c0703403911f00c40b0f02c1000001d2600601b642c09607071a95480000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 563705314 1250 563704064 563704067
    0xf020306151b2a0607030e0904062a09050405010b090904061401170d0e01120f092a1203020303010918060c0509010e0a08100e16060306030c12120e0d0c090c 69
    0x15004040f041368202d1402505550040040c24889201d5015a4544007c1000c0203040d410100d05c00140b03801e12034018003c0380c030150100c000c04c1241c0340400c6011401140c0c81c1441d0280905030784d1900001450102c6001c144024040002d0080d03901e9640c030112280c11034820040e0030300900484910800d1514680c4405007005d00d045243c0c014007480010341c0b025641c001090140d101035041c0c00042d0a1100d596a0001d02006d103170041c0009400d0007213200381400f016805500c01c2d8004000500e858a450701c0d025100d81858019000d6401800104440d00380c07500000300c684401203842e2000180d0b07a6894080c0c4554401201c04648041542080381d60b201d52100081903045a90281641c40c0c91400c0c0c0d00d4405003014100745c2502c640b0a600181001c02c01d0030701c84182242c100248656031040200203061900040b54400106400003c0c8140b042c5140352029400001451070100e0142081d11800c2000a1158000c004c102e00140414182d07d001c0e40141482035020a504441010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 563706564 1250 563705314 563705383
    0x9090b0901030b1e0903041505030702100b06090409080c0105071d060a09051003050405120a05070605150d05010209010e0f06310335070605040804030f080d0f020306151b 75
    0x848c101004000d108000310340350b001078004442d6085000014a558154012071024802c1106140d0002e003841048000c05c0301c3c84004101c4194620001c00203600d80840882e0760714400c04d800694054101404c0d01d031460030a00400082c00a03041480030241d43d200440d151820204410022a80e228200401e00006000f001c4005800d00340d0315152100d62800900503000780c1c0c2018042c2a5100700040305207032440420f818254008180498516461401034043e41c0002d00d91400100c405440e00403070308060a41a5000100519250519540c900c140c50750050480751103500400c1c0c0c89151400c802c2c40036005000c0c50040011606686005981440742c0380340817819003404007400d58080c222540e020170354652950003031002c40c0a03161401e14245500694001a1094013840041810055440006c02c5004122001032180c8031608007a00102d0008445454104c3d4100d40c515440003e800c0c0204045620b15150590741c6400402c143d2521010080e26036444149099100c2c6102c820309 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 563707814 1250 563706564 563706599
    0x40c020307110a15080901020c030c031c06260c060d0606031b1413091404050105130804090207061e0603150c0914040e060c04050109090b0901030b1e090304 69
    0x1108545410301e010144000c1c4d1500418901c100203200c0042907008500b03404943c40001100112920384100c03034643c0d0b44036444148035a80100030303086000e19250190003020101c0303000810410004641ca04118038039119440120407600541011004541c0c80001600d000c410400000640d1070519030003a04403064800020380b0f00420f01e02c040d00326680429059184813214105035102c0c51000f40030b0340d440358240c10013085641004922400030300701e6103610f403249000300024801915074000304200010002e1004d0301940f17041005000944241e0003c1040c40c0c418030001800f0030000d500d00c0303050020303129031039801510b6010070018408280c188450300b61f0070110400140601c81400303030400b0301c81e00ca08084902031024185007503a480c1e126140c6441c0d4881650311515104181c0807055020307019013404140c0912000c90051100d1094059a0f8400f0b003145110340d0840d103800d1030400004009400707201c4950302c40307800b00241d802c145004003190702c0210345484c1880074540d442051076 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 563709064 1250 563707814 563707819
    0xe060a090b060910020703050706030903091211191a120105120303010311010e0409060f150b070f080405130b040507050c0a0b0601140a0c0212011e02090a05040c02030711 75
    0x141022650782c1400c0340d442c000f0440c1e018a00b0988564207030308209440d440a0b015010300c060010f8040c0c0c050b00040701041c0700303941c1ca0707500d03c0d25940052031025103100d019240300345034102c11000e4244050303d00c800e01389a0840b2800255a02c200320415a904c00e51104060300114421040900d00300066014200481d141514200e000304c86c01c0d40d0740414030000e00034010861002d21141d004070b900300242c860181c018429461942000400340000110f040b1010745041408074012500c10308200698401c0f08455142116a8036094010070754040d0a03510705004220000703075981c80700740c0302c40918080340000c5501c4042038200011103000400c82002d024041000049045001c2400c000c8a5170248030003e0507100c2d500100c1e00031000c0701e00280b5404000500c0c00e20660880400794816108494407241c000400765081d090f54507a00c0139480c00c1d540642c510541c0900c0c1d0700a0094500040c0410107210341d184000340c1503443c4001c450015810024000c000c1c0f14400c0380c90764004805 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 563710314 1250 563709064 563709071
    0x533090f01120b040f020d0b0405060106050901091e09020a02210304020603070f0e040f0b12010c1704031b151802061606020705060916090e030a0521010e060a09 71
    0x1442c003050489019200010f10306038140b00050200203100d1000c107211070700500200780340070035882d01c580003110540e4107407400d200d13040002420b1441001156840030040e0b6a4544a92416441403001c000c5000862071103c11060040360a062510180800300321070345c020600c500d85220007000b02c010350000c11501000800410000d6120042201e80242c0d040c604031b45440d03006d100c00c90300b00c602c0c0000c44e07510504042d113108946000e5041240d80880486202d80c1001480030440d0032a08007a010307502040900c2203008440c802c1c4021264840d020381004014141101c0365a6107091540138102c416542c01a01e40480c00c01c54404c2e88901c00010031880000c4106400054442c010f040078048101c08003454203081040366015100596882000c983c0e407410800b9959031981d01041d940c1d207200c007007554000b070841300c9405800a5030440303c024501e410130030b09040303d460348011244403d400c902c5001e40c5007002504001c900030194102044c00c175040032410410070007800d92101400e20305 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 563711564 1250 563710314 563710319
    0x81209030a050a0e031603060f0b09090607031d03040905100506070b010e060d0c030f05010c090f050f01091d0411012a0204060320030c0d05060a0533090f01 69
    0x4110003151550103079424070013451011040002e24020901140d6a03007031000c00000020000903400101904907009010b000351500c450074850b112004660390f4030300d58480404521818000c3d403281d4540311411000d40c4a440b2884c82070340c40c60f03205034441788203683e6402c100720100005042d541d020f84421103005103001640c2d100c1d0040224180600031622000c080407941c0c0ea600c4070349450345241d0003a2000451550390404800c00c00690000340c54950030b003e0500c03403440c0b01c0c840d56030a031000c100c0c84d400414180070a00c800801c0c2c03001041d051226040d00461040c0c0b280011404140d144510382800e0300c0c1924020003134000c007015150501400840c4120100c5a0481104084001e4560003c007203000b80000b802912203a80044c3c81251032078641d11403140c8248a616501005900319060f0340d0007c02031214200380040e02030002d070400d00100e4242080d6400007038011640941d101d0269400440548081203040d00810006041d02400b03005420300e0285c5507403201c140c003509100d0b5071 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 563712814 1250 563711564 563711567
    0x501050304021e03070f0803070209010e040b04060e0102070c150e03120a080907050612150f09041e0203120a021b010804030c03050f030f0f06091b07050118081209030a 74
    0x4511904581070202c5020781c3d010b41c3e2810402e40004000c1c100c0c0c03240d003003a602c201158581c1d0084038164082d124050000c201d00042e51201809140d0048415501d640c2e207484040c002c1a16102011495408112820210302031141c030002810804060074404000da00f80900001e04c10034089010f41c04c144100e4510326048000d99207070b5103550a11030304a990b10315505003855100c0d000f0303650214011902c00046010803c2c00f42c03041000020070403174200005c0030440c011140340a01c65100c021040003800107021000081c1c401100c1100b1943c2640b81036000034102080e500c02c2c00307a21a0003158200103036904120181d07540c41c1282e028081c075141500003d068a000500150510010001e00400c15104004547c00c2c080c1d0150f44503128242016006542c402c26510f180c294031030240880c05038034000c0c4209002d0001d61811820315100b00421030b4490708114416941550fa503102d41c0840d0000144804000784102009a80d812801805000048018107200c2c0d840d07101741702c4100398a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 563714064 1250 563712814 563712829
    0x9070e01120e0a060903090806180c21151501030b090619080607021c0201020307021b040f110d062c0a0f0903030911030d120905120c03040609050105030402 69
    0x180c1034440c040390305150002c2032031904041c5640181610320f041240e1052590015012040d20f00c10011b41e0820303102e00542810340722902d4220182038000b400ea29409240002240c042d542c0703c40c11107144416000002402c1509180e24000d8807905202001902e01c9800c20244202000342000c001d003040c00300100d41100750052055001e6500e10b04040c0480d50040d00c554010f0801c401111000c1c50320107030007511070780c440c00500f101910504c1411a02801070090fa0303c41c64035603005004030007041050210032182c80c203c05030402d50301c24824807264080d0242d800140c542207605541c0700d201d4001d800840e00d4550051640000c1d820041c6035a200b100300c00c2c042480080e40c2c280081c2c50307403074a8000410090300c8a820389468440f0001c201a050707006101c040d4043c4890b0303543c882c2513905058942c051504070704d000078104094808610403641c03100010703500600440c0c0c4811101e00342c0308103d500082a01d00c15034808a010020035903c4090240580400e02c0c1160030742c10a640401c007003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 563715314 1250 563714064 563714087
    0xa03020a0318200d0c0509151c050c0904151d070306061703030702100c0e040c020a0204050a0605010e131b050301140d110402090d170a0e0d0f021c0b0c0909070e01 72
    0x6902c4d01002c100348c80e0f1b00350010142094001c010f10492003d580100c4010040305004031198010b11070803c1417480c1040b0072510032600900012405004c0d10302c0c080003040d0b5000c50904180b0031a10070340e1003510070040760024500c112130005410f030802e1103261a0317040500c03008030079178002c1080090341a0302054003118400d007800e01158492040506440358419a170070603030020318080740919503a600050030940503000390380412a503118a200f1006842d00c41c0038442c041360460000903100d042a0450794090b001062000a030070b1642d00109618024514801700000c1c40800140420107411000c500d100c007045519020749015942d07207008101d12007080504c00da03404160136500740c4441505000300742d0300c0038003101c401d100b1078100005a0400b041d001c0c0000c0b0742080d02c43d00d906190b0203c00211b41c00181107001c111059081224250301a0000ba181820000d01c1c080003030104a4820300030364900e007007240c0740c7c0c8103c001c0c4030060f0b01c0105128204510103182d84850f90b08150810f19 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 563716564 1250 563715314 563715319
    0x3020c19030e09071101150302011704021c030203070506012418060c02061c1a0a0308030406090c0b0712031103130b091906020c070503030c030a03020a0318200d0c05 73
    0x42541c0b0204185e501c3c5203008401d443c0c650030103c2040307031000c0703102c1c2c10401d482c07003601c440e030445102060204240380200c5000350444030307518004070259403622041e402c142c480e204503454146507544084c1000000e0380908a10a54001c948040c0c241c0d2182049401c4918941602d9104244e443d52201500c5480303034100380130003030f440b003070035501c0705411610030318082003a44141800040da0b55000b80038001041007144c00b640c0d0381e80001e20745220140d04903900200c034207080da25540c88200080600000071280f010343c48c6400200d410064024021140c0900751142d08015000700240584034100d081a8505100304100034600c020240e00d0341c00d058003d02108415610214850b1a05801061010402c920321030000c040201c036400401403114480103450700c2e10343d2001810394a0241d40019407aa80040c0541d0b88000d109502400b50141c0c5860041030b95134030742400c40f80ca07010100301590704040e40501e1800002031113194440c0e070001524115411050754551003859000b078001c851 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 563717814 1250 563716564 563716579
    0x50a060518032d0f0c0d140f04050622030b01080d030e0d030c020705030307080408010c0309080f0a021603260a090506090409020411031005010c1e0213060603020c19030e 75
    0x4a201100c8070030340341c1a105020510799101045450b03c4d42e2017911044110004070442084486000003c1c1070f100c1c00290031408d00d003040e0501081082c550800403400c01083c041d50b082c100800d02c02c41ca02c400460060f200c045071541081a842d00f400c810501e01001c1c0740c00c00c9607508030080000f031034011107074192400040f4035074503950403401c20340e0562145030702d484003142503414044000c0080c41105c40749c0c0c000304284c80c502003040e4251842550064400c180602040c20342010070350082c0b04442c10352040d525480001c00046010715410380003a0ae40e40b44160810b58114402d50000385440c038072403016400d020394010002c0144883d40140c500070400400d041c00305441c0c2d50052103004da8000d2085c00340000c81d0001001d9904100c41c00c05003081c0690000600b9402900c010702c580e6004102944103c8801c4800c0703181c540d81003812038002d50b5204410a40814502c00c00000e0b044030350700036941d949140b40c0586450446900c40d0b10554280802c94002a0040d14021a1000584000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 563719064 1250 563717814 563717887
    0x30c020606280816051f0807080a0e1b031005010506040b1e07030507031e0c0206030606070f06060503010b33040f03060f0513150e0a050a06051803 65
    0x3840c900d070b150b40820664403c140c104184510142c20708815560250340710341448a150401000441c0c55076000d201145e481c20105918900c184103480e481403420501040800032031084528080c0031040c08404818016140c2c0e1392450b0a02202c0745002080e00c062045505140014210384518460351440326000a81c1011819083c26400508081a0141c6488030001e080c0a40668010001240003074406c00080510080c0d0f100701203086281d903034403035101c2c01543d401c1c48065400034228a41c0518140003080000301e264100140c103d100b80c0002c07503203610f00410f140c20b54958284042c0b0441010700500b021f03075000d5803104600130f0a29107020b040b0380744140b8201079115640010072031401003180030052101030303001079884101620040010343d03114101c0d0680c02c5001c0703030020000144d0201c10801c0b201e2940200e0000004241518800d1416a03030f80c91511a950100300c5405440c0c4c01000540300c800101ca08402175644c1c00f85151402144030010442040615100022070b48841c1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 563720314 1250 563719064 563719129
    0x714030307080c21041401060f0f091d01051003140a051b0a1d0106090504180210050f0c100506060309101e02070302060603250b1804020301030c0303030c020606 71
    0xd141e0f4031380d08201ca03036a46003418104000c0010301c030703007480b4201d41c2001030001d6007001c107201d44030840302103100f5038030054101f0503190090200245040f188915001045181440038440c540c084c1a90340d04e400121451031134044110b038442a08003807507030031248070344011030b0002c80d09101d40425228481e5503503000c034002941d442e00d0303034110295030340c03084c404027150f03400b00c0403190b050f00c09948604102030794600410003503030911418500441180c0c1048401410300e044400400809414040d0409100290590705908160b443c0c0c2d00d55400a40e0b141001c820318403d40e5000441565410320310300d0815595695020750455461407165a0704100d181c4142c41c42030303014100310346c1200355078404080c20b000755a4401610b82c2c80c8203002e000c5001c012841c034044203007003152400c04501030452800c0120382144e006075010050804c003456080c0b0341a80d80d27100a5028500c00e0340c03917429990850800804880c41055440255804502030054a030b6401740300800600b100400441480100c400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 563721564 1250 563720314 563720347
    0x70903030818010c020a031806140705012904060801060e06090c1603030902032e0f0b030304060305040b0a0b0303090d0501090501050a0b010f02070f0e0402030f0a080714030307080c 80
    0x26000303e52901a900c2d800075408220800d08601940d1007507001b41700d03e4085105034a0500c02c2e480483e00303898940e2002d03000344002e018501d000310000100078100d020802c030034080103440010f03540721880034810b00e03140c544030300d0002d072401100030402d050170614007030f12041c000b90041c0d115560120010302d00341c0786101241c0340501181d0041481c80d40e186809000b030104007a0413071003030040070a140c0c0340503003242c121040680c0044071940340290b031442e0070300107000f0125000880b0340c5440c0e4400840c1c404000510040042c1c0d0780002d800e00d400d040909515030050129034407581451178842c0710313550000544441420840b4008a40082403a040b070040c980240001d0041d400e1904002c1e420fa800c4e805100ca0640a0300c80d40c0c0e2001d1420300480e10b9418034042e043c1c1804c0c20794401d2003007a1410203819405840a01102d0030480700c8a0001e1405980c1942242c00140c0040c00c5d604009441c5004042051b0160045013141006100034014a200910799621628045a000344444014a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 563722814 1250 563721564 563721601
    0xf0c13180f0b010f1205091204080f0c01140d05070329030d2a08040b03010312021c02100911060d020903010b030303062809020c1f050709030308 64
    0x196008035000c880d034040509a40e209840c0207528110000b0303800c3d4081c0340e1641d489081960360080182c0c00d0610400140b00c00340007144603204032901609544040001400038004030002441e040b000201c4061030588011326150400204080403500416807500340e400d54402c108020a242c2d4892404034000c00c000849240300001c0d1009100f90301c10090004250000f040d000e55926000d50700c004e44848044400c0180c40e03450b10301d103d0005c403184104e00c00b10203220300440c51a040d62482030107901e400a03002640c0d19010502c45496040d010055103421040f03103070691081003c0140302a446049080c079442c0142d4484040c03a0410030f0075010301c284108000d2140f6141c10a411000c402500b1864102d4000d618101080c1b22915000041d603201e42801071400000641c14691403208240c8110683c1d800552440040b8034480b003800500f0104110360014040c90740002819040721214203210303d602860081880700255112100742c055903010f0130000200e84a003002011840c0c01b80 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 563724064 1250 563722814 563722829
    0x1401030308070e090c0a08060411180a03020d0506100e0c0307120e120403060501050607050a2003190b0a0603110d020f0901060201020307080f010503030d0c0201020c06190e01050f0c13 81
    0x200821890354400000380c85005917641e6001441d85e12230050000300c421410070140018824801c0380c04141c80444484003140010700080c022540e0381d404036402c03012060045400348c2104041040c8020803030800b8004020754000d62000d0704001d02d003c0b800344005400e400810140224100d0028003a80050507291002802c032803201c821207440000a401900040751400e06140000860340b4040003940c0304a50040d018140c800f4040c2c2e100101c6c0b42c0d2440070014040e109000c442d1a40c0d405110726144803d109049550036002c42c0782c50005640010100d5690518000f414030215465680002c5640c401743c504140808050001441d81e00d8566402e41c2e10803032410000ca075850303040d00a275009104540342c600498035803000d01503414809001d40e94140e8405d102446080e11140c012004403011030000510344040c441005003403d500315204600400104040c0302e803180b0920601c0b4604206800800c0541040c115401d8562405001003000200206250303041c0c28400c1000d40050a00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 563725314 1250 563724064 563724079
    0x1090507091a030109050c0402090a030611070314121f030b040c06020606120a081c02214519060f05060d02120c03030711131401030308070e 62
    0x29100e071403000d4150307006a982407442e1019502d031542814050001081c0d800b40240054490318010301000350031480480c1d80c812080f18000002c10311501c03941e000000200c0d40940d88480c68180508002d010803920090030904000429800c1c0b110180580c1103541110140c2c08000c1c4540000801c40b650f42000d4810440001030008100f20007800f442102c4041c1c0a440342680e44504019030800d407800850441e8200b00001b0000524400041c00c000f07118055031a0705000c2c40086100300d81200244a00da11a0700c8603800921b1038580840c0d6000c081810018005103920000040180402039455014291090805101c5480c0c0c40b4034a600f801480848041151000103407221910114054030741c20b28002d038445d05404903002d00e9200f84c2c0d01030031023070300b040f034030b609000f0207880345810054140a07461046509541c10310013040000c4c0618203030003840682c0020000c50b0030074182c044089624107038030030070440d815019440c1142e8040c10441091f03540ca00e8213450040c440c14400790310844 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 563726564 1250 563725314 563725319
    0xf0213020a0e04050912180604090c0509040f02030108070909172a01020a0f0f0c060f06060810081f02120f07030c0e033d05180c0105030c030901090507 67
    0x20702103000840840300710740030300058035540030f046c0d150a00d032400c0c841c0382c104c10080d240e554030801401c0900780d48054507080c40d10384d586000c0d00896805280400000d8000510040181742078024000100c02c3d41504500e194034103000e4a564040703e105610392940c54541030000c3c0142500c1c107405c075101c540c48941e510320410b8400c1f48894075000d1901c000102194a148008205200f550031110304d070b488441000b40c9007401980c4150800a955007004001c660020020785103016404030810100360105881d41450000303403c0d101c00400c2d4042d25600d09404200441d800074881c0803010b0100b007502002001d40200ca000783c4140250146182210414000086c00303010300c0c948103444c00d603801c2040c050802c00803180c00380600764065040e840481c05183d041e10f440c1c06a00c0a64040c5440001403081d161040340c0914100c1750213401d10394130020000441c00b0104030701441c0740b0803406409102124000600320b40070181294500b2900480020181c0100754000b04c201c40d084403c8820256 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 563727814 1250 563726564 563726567
    0x1302070611091008221509060b03070506180f18090a020f04230a0f1506031b020a08030402040603050109051606020d0c0f031e030e0d0503130f0213020a 67
    0xa000d003202a00511a0045071500c00c0d10030201399003d1800f02405521125004104456001c0b0303181c1d0030f860f0746070121021b401070318862140401c040d1041c840450720203403d100305824105280c2c845402460704108d9180c000305150480a0340000403a60b4900e54513541000c2880030400908407508043d0b40010702c503002d000003a0841c0964400c070f41c44071142104030141300680f140c00000c02220400b6401c11489207940003220b650201504000040c00c801d00e480b000d040d240d41004008041c07c50f0f0070107200b5540c0c5800f40d806c071451042c044252280c04100b00035540d041090001d80f0109011001c40e08650315608950025a0000c000f4400a005800e21540710190218220141c1c0781440c070003d40d00d4002b142d542010700407510703010035030802030711610003c07000900e0440802c03180303560040c84503030324032191952000d16a900003001c41d221301400c1d1400414113444401d11409004016140588030440c90310b081e4858810010309105101096840b158031a5011145001141d0036900ba03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 563729064 1250 563727814 563727817
    0x3020d210518100915060b07020f03010e150114040603030813081309240b0a030506030a0b010303270e010504020a09030c17060a0501080a080c07030203030a08010e0a0c05091302070611 81
    0x1d4044c5c1d900010056400c640c41003164010b10a0180a840900409000d46004410104d032030401600108400200e89403071402e1580c441d14512004100f00010300441d1140d10034821070b80c0d000d850411001c0d08545010303005085c020041500c0a80004c1c000301000409401d0300c1114000302c0352800d5054071149580c000d000020a02100c0482c03040d100b054046800001104039608049d01d246022440300717045001c0d00e0001d0000741c141c842c640100001840000f0303180c0c000c43c080e9540d50401030002c2104403040e14500f4000400e12580390003030007583e032820441307411200b08a074010384e14242c104064410030400c0d4030281600c84034070740024044c1a0800e052600007207170030644081d9a544401a82101c1003801030f40300c5075000146c010005490b081c000c01e6602e40c3d9404072008140d40f40c1c0040d1542e4410b46d850f40009440400411040d0070901c06c00d90401d14021062002403000c007130080c1180070300c4404901c1000862142141841d46034112550160230080030b104004160704480780c2c5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 563730314 1250 563729064 563729081
    0xa170a0516030c0204110d153b071e05070b010b2a07061101051003060b150c0d03230402040c03021c06061b2a0506030a0903020d21051810 61
    0x3e080c10245400f82062002c6521025106200b003501d00d0051004100c1080d240100b083c01d01c1d840280c40445024001121028031071800c3d503543c25660707001e00501004070052f0a1450781032040901c5500b0004a520351070350b0650300202226625002510340c40c03089132003035811030500c49614608910300600d0101c2c5203016900113484800c0f00000000516017218811210b101081150010a00009469410900311503200900c401c00d00f5840c40310b031841a0384040d200b031190398424003090070342c0c94142c01003140e01c400007070301403106030b245007480040d450000341b000388119916050040c805000348d042c0c0e07214020710b441c820b001c219103c07444c05c0140154040c4501051850740c050f80031081d2441422030259000000502021144900b0b0410807500d4103840701c4200440404a40c640b2143d01451151030350758000300b1090b08a00f8040d0a00302140d551400300040c031030306001010410384280c400028101d00002d410742d0b03901c0c610384202015280c02d1b141d6008001d0012850300381c1c0c2d0450440d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 563731564 1250 563730314 563730337
    0x6070c14011404140d080a020c1c02030606012007030506100f0f091a1507060b0f150c0c060a05041809121101090c080a170a0516030c020411 62
    0x2000c900800151541d105038210600d02c035508010520086040800c0840c003050068403065150300180e6903900950040002a40142c1c00107542841c1c2e41707080641c010180c0031a914003441c61050f500440d448d098010010b43c148409500380500080300380d204100d14001e610117031fa000540364505952140f909680882d00081c0d000c5001c105421422003090403140030440c5007000528218641e0090f00c0c1750494460794040b0b6408203c00303922042201c100c5011040300c5242c1e45d042c0780ca02802101c00329505e4038040c42c1c000407115440c0d1617100c00d01c54643e1041800b0b64131a0f82c080740162914914800c000e412040c04141e0600c4aa004400307041610380e41085100c8602d010f071a034008503848000050413180105180401c421f0240600240600c503031070021078441001d486442403808180d0000205602c92001c0c003050003500c0d0103014442950209492428010700c40c0204140110100d80002c4802e03803052004041c001d0408015855014100f801404042002101c0300d411400b0003a8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 563732814 1250 563731564 563731589
    0xc0918020111070e010302091801050a0207060e060105130b0409050d020c01091d0c18030703051c020c0a030b0618090607080105010e2215090605013f020906070c 71
    0x402c0039010844a0a540903076030510016843c5800b080800320b0040c0504100c40700082c601005040207000d4144280030012000d0b84e174a0143c5803d4044541e0344440c001180c0108006121a50702c0103020600307046031401c0400e0613408500014000c103400274004029120302c482090900c1d0300802c01ca0000b0380241c80d1460100e40d5268000c18582e6000780700d5901c0e10589001424a0f0319140c0a00440035001214140a58540010034074101407a001a50a54020301c1340000c3c920741000454101002d88c1f022307110b0401c241c00030078001d18031030000401c00c09920002880b5500c1f03c3e0320068185030b441502410a041c4013400030b0312000d0944800c07001807001000030650354000e021855803001c014040d0800d121038183c40d85c0540c180c80340d40c0c00f105034442e9012900000e1100802c0040c0119407000110b20349808009002007413610304181d5084d00031180c03001c502d040346200303002d0150410000303506001c541c981540241300d80d0561541c0f100c400306040040c0000030300d0340402e07200c0400049 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 563734064 1250 563732814 563732837
    0x8032101080a03080721053909120f0312010509010b07021804060b1012050106082712040e07080106021c180f2403110f070c09180201 59
    0x1d0346400214002401103007204000c41c003024400c8a03803241c020002d815100c10928207003000030644105850701607c901c0251180c0c0c03c04004401c228100340e180c5281d6825003400c0310440d00c1b2a000d030700c40681c802c00300b406401c00300c3c0c0707820b220340503001c2c003c6000d980c0e503040101c030302000c014400c1c02801d014155000000c9408003d04044652040c1c009011000000059000c4504100001c00c211744154441e201d00301c071521510414a180e8003503480e20805410100904c1e0100c80c4140d00c100100000881408020b911303540c2c0f101c540e40170310005c050b906c0540801940c50041007a600350002c2da80014002105c04410802c6406030700c255840b084142d036920340403039551043c0000342c100c1c00d0b0201c0c480c118250180c2440610710411000d04510070b50344240c81c40441409078403c2003a01c000008418180d1241111180000c01c035040410800c00100000c4074640640c400d69003201c04001482428414070035070110051180724002d0101c9200030542a2a02458010480c003060751020304 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 563735314 1250 563734064 563734079
    0x40e0106020c0901060e09060d140a05210702061b03040f06180b161e050c0901060903030206012d0605090109060c0203101806020a0216090e060703021308032101 71
    0x445040702e009076904403030406d4038810416240d401500300c0f58000000042600042c1c0f18082c6045481c80d410080e04a00445003840750600680c40b060841d20044894001c014003842c0c2c00f95003c00c1d0301076a40d29110b0590098503000f01080c00c282ca00144004200082d0304010070107454261000c0391307140c031540c0c241401e0800c0d081003980030b09111250240a50600300106801214006008807410960307030245040307401e05818019019210354010080b0907040b81400810f00b40106240d18082d080641380d034400030340720070301802003510320840c0c0e890003590301d1484485100b51400742d00414034120368491000d040c0745e211200c12404651030140000780f4900800200c0b404a40190203801030003425010007000301070b40300007044604500031551021030303402c3c406014041c40c15002001d062074040361101c003001f020b0f03100030f09035030034030a07851180040425031940040d203500340540c50f8100c401002014000c190850042d912000c42c4803103a421b41303030b030000340e08005104680a042c0d0302d4808 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 563736564 1250 563735314 563735329
    0x903040e1f0e1302100302160b061504030b0a05040303090210020f120928031502070507121a2502030904150b0708130909050a0203010b010914012003040e0106020c 72
    0x400710b0060f080d070050600907080180301c402883c1c071545401450040e104011007550f540129081d01c0c2004a901002042c2c2070046200c0c15000055040505062075950394405501c1d0046c0f1500e00c0075140c002250405000750090030404c0d600609004010040c01d000959840b9800c0d51011288180d40e0b0100050f030391041240c9403400094080d080c11680b00c9800a02c603003102070540030520f0072140c000085413810190100050b0520800360b602e020504149181180300c0d000118020038007000070001a101000007902e03001c0110041d81b055a1b4004403507407255140922031441d000d044500102c5641c04001021a20400c40742008400010640401c0400b031a008424003010700b040f0740b46c00f0500c22805860300c50140381d60710300382d10b03198101042600d2074000101d42e140c2c005907c1c00114a070a001d1600541c030280383c1000d030146400c10410f40c5003e032860207414040d20032100c50700060003640084641d00171004403940c4d1903854040000500b801d00c5140014083e044640030b13180342025 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 563737814 1250 563736564 563736571
    0xf0501050105090d1a1003110103050f01050d0309150f020613051e0a06090b0403020c12100f0b03010e0a030906050a08011404090c0905100b0309070603050903040e1f0e 74
    0xd50b42818640d0120610a43d00b40001301940c0a20001a10301c18600310034450078424400281c261000328514981204c078151000f40082c180342c00c0808005189840c1818176044440c21250b400010b005401e060712921071a400c000c18191013002c0d81d448a542000c200c40010724103500300d6449644003007040d08a2810950014402d400c25000c00c3c0f0282e00100261140341e000c0800e4401d6180d0580d5100b0071164240422a5082048802c000605405200c0503001c61760580301c079030700601445c202e05e8aa00c0e802406480040d07407007140d02495400c940c007080540c0c5024000b00020000000706595680380b10100714001140e415020410912840984502c2405a00c1e5001680d003409400740b00400842d0301d45400c036541d07079040d1002c50018a401001441105130004090600340e0018070118000d4006940110080040c4158034100240d0b5404803a0145000a031a0319600c01490451049900020304216120140b007495607080094441c406c84007508402e00701c0d680c0c01c99030b03500e030800c5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 563739064 1250 563737814 563737817
    0x70b0414010503060102160f031203180204020c0c0603040b0406110f1e0c0d090e160206060f0f1809150103020121110a0905120f030301061107030c1401030f05010501 73
    0x400c4a1003940140e000d5038000c2c0701401610240c2d010501d164213140f1040d0712003030109440c3c1d03030b040090104032100395011083c02d140c00e2001e40442045540340c1c50741c10300f00030300803907002a4103480364106110038a25007500900340d650f00c0c2054209072820300000d882c180c1d80d4034a006107808080c02c0349000c0f15449000d0843d59414040100a0128038a61200b030400e000c81d810800f41c0081c0006011100308042d85445180c1041c0c1008504414802f000b0920083c044d9044800c140181c1c0004031654005021a2000f5042075030401003a5505860003c854100025415031841c0b25001e070120388c410360080703003203801c20b90150b88203140100d02848007a0200b4110010100c607240f00c04046202c01420070130114140007000f500d13034905da01203034030072000800d00d040c140400d141039030010300400c46210080001e1010455031540740d100610650381402031a4001d50400c42080c800d1600840d0402802e44034950f4403d84040f008003900c0425000903e001186046054148100d9042c0c4406 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 563740314 1250 563739064 563739089
    0x50a0501080a0312020912070906120c03080d0b10050d06060203030c0f030a0f020a0507030f0c0f0807060b100c0209060a06080106081306090b06040f060b0901140405040903090303020f010c020a030e1309030809070b04 95
    0x2940c484000507844030795402c105503100d44180310390340c640802c0203c03030314212c0e03548581d5102c040304140111089500b110003150020070602000e000140295601040e00038a49035494550301181e6000705048000c00e81281d00110740e6107101a0400b000d030081d28080d44858502c4c1e03c252031304460b0700108020040c8a44d03a5894150f0215855070003412941c1d216800010b43c0d2010040028103030b07030b02c541d02c200000d6046250f41c021401c00500c08d42c1c1040c41aa2921006400d2803030150120034140a00020032907031000141105208800c0c04501c2600804208070084aa04060b0903a80f404c0f0781080c0520f0800418508291640c4244000c880500c982e050405484900440f01c000580b900140e10300018040170540d03075203d1280c0700c0418403a41f80d03107243c1ca10b9031602909100e4001003101059240c01007003e20383c0d4010aa110103150b041c60600500e5030b45000083c0c00c40314101c0e001c0140c3e45072240b5081090b4200341d08601a1780d204041303540103035681011803a81e10490140d40203c080 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 563741564 1250 563740314 563740319
    0x90203060105162901050103060b090d0b09031201030501020405090606070506150a33082401110610081e07090207140a0510050a0501080a0312020912070906120c 71
    0x201a04082d489201324040c0007848001000d40c0044407854242c002c20040031070040000d507801d07100d038000428142c041d082c2091f00000c00145024024400a0040703241e18000801440003403088500040c1c1c50890000d1558503410300300d0007500709004684c0a80e0b0b40320701155651a050056032003144d803200060400782d50381102451049000c000e034503005a0701e810b01040c900c10940c40f0703804801c0c81d825820003150200050038500151000c0c3c0070240300c07048041c492803c201e402f2040d1080710343c0308450030b000302c2e0000489000c12060100711103070050200703119413034031119800011200810700719190201d885110340e41004c61388442489913030240408103c900180d03005070611138081c1b00d0100c0701d4510440071b2810481140740032502508042c515034100f500354810b40d9000382c0c14000410042d070411040d15918400c0510207814403100c0080a1101c10154040710180c030300c0038000c048401c107042c0c40340c0c0d80c640440c02000c2c02a41400c0001c2070842d0a0381209002c5030704015481402c52 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 563742814 1250 563741564 563741587
    0x1d0105030a11040f0e0102030a060b07080a0e03030d2a08071d040b0a29041406070c09061502011d0d050703090906180f050705031501031508010510090203060105 71
    0x4515182864003e0303211130028202501e10300c41e90320341c115588009a52403411441c40c4046034050342140100400600c0348034041100e150a98804410a050001c450340d026000a4554016103403100005420286043c0460b804110a030398081504c2c1c1d41511b60007140b803001d03a640913080701c1b41d40019482c0c2080514080307407190303850200302001e000040d80462220210b0750061058001200f119914403000b0741044000c030781210202e031a50456400c19040c4140c01e140040020341e400e10400010445205120418201030010901c0c140700f003051036520b41407074018042e80005079015500e0701e00c1c0300350b02c2080d10b501442030490b148003504110001e03900a40f401d412a58065003040180140410340081500c540005040700440b0032090b0b00100c1d01d44416100c40c0c000d135925840c181400c0c0403040e030300035003038071b411100700001004805086401240284003c406641c45948000c000183c0106e040d44118000c15400f40320342d01c41c6855071075a000703038401070f506140012004c108036405070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 563744064 1250 563742814 563742833
    0xc03060a0902011103030f16210506041e0605041d0706051c02040f05040e0f071403011424090f0c07080c24160905090403020c1302041d0105030a 64
    0x2c1c814146100c03000e003112180c91841e00300715021120322010070140140c1210301d0444540c829034a02c3c1c503442c425003100102226420303110040540e2a20303000800c443e5512500400420b15400440039090800310070380001800c3c00303101d81c41c002c034503100c00001e008400841070100c07002c0740402071801924220048a0a40c000a0350901c1648140300c1d602010000c2d000900061008070b0381c12900c0b9040000f000700700d0f25100003a482c6640642070000324a035000c642481155414401d1424180524020a016002d03240411154a02b400c0c1080500603040100b003948508400c218204850724000340550f1030000c0d80d440c400040518009103c070b01a42000f800720301d21901b000303418141c000c03191900d400c0081407040c04601011419803c12425206400d911100c000561301500c000780d44041d061881c14004c1c1400341c8403030030000342494020040c8683e040d0028164012103542804600300a4115000f404544289550300c07003400c0c10300d401d003941a180c00070080c280c8030813a82e4031001c80 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 563745314 1250 563744064 563744081
    0xf020906010e06030f0702100207030206061009091112100302150a1715100305130f2d05060f060609041a0603070917061510020c0d0807060e0c03060a 66
    0x401c0662041030b0100d4507090042d41c0245210b280240044c00c080d080a42810301c4040092442c2d4030600c25a4042980021601d400500c146c0c1e0300120f070b20900341d003220340031740c91b800013f6460306060b101119298240c008000e0b0300201090808240c841c0d107044c07a52b21083e840003952010515242070381040c8400e00030590021142006441080c60145035880f14908485442c00f00c02008a040c89508000c201034000c01c0152804124501e407541095145521401c00909111030390404601001041c8ac10b1040700c0d42c04011440b480c100900c182100c242d440c5801321068026180802c44402c68a6040c50058a008103010309220500d8203100c003c1011100398810900065003582c410348511000f940500016610402c034141090f080540d882c0b0045941c000326070214007049442d201030b02c011003512400311044141201c0b40740041f4544103200c5440c1d5403200f9610344070010088220020002c1c00e210b2041071103c0c10030603240740d440306c0907842810f401d9003001000a4003001e503903110b0030b02d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 563746564 1250 563745314 563745317
    0xe01030b0711120d0b042706111b160f090b1804060516020703020a0303080c0f03010609030b060f0a03110103061701140f04050a120e180f130f02090601 67
    0x90240b942103480c14440e040308440c040c10000d080c50683c04240504224000d059034140106400101d0312950f6038080b0f03554640c0002e005a08000b0401c1d6908124001d07540e0180035038441004000501600799202c0c00701c00103108882d03001143e0012440700074100d41600c00400515450829800c0242281018580c2c1c003890501018074043c00d01d65442c0e00a50080ca000107103071402140c0703001c2920440c400305080d90b02a400810061761408000310907031f079161400e43e000c0c0e2642e00d8110300318000c94144203008140440003003881ca42c00a560012280901a07400c45502c03010280407204401e01a01a0030030030b81c0304d0074004106003070640d0080100c185000220a55103983d24000303110b00d4580640f45944a203e5005001240340c00e8540084030090356031428201a81c0d0641d48000380d24004040300711100780c11110034018108021092400b1303200c0388400340070850849403804100d6415840149410110b0301c1e00d105000311982c200e5200c0f5441c01185155020400c82120040c0380301d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 563747814 1250 563746564 563746577
    0x9060f0c12040606050d030e190e0c09032d06010e09031e160b04050d020d050d050619080102030a0c02071203030e160f08100203150d0201091e060201050c040e01030b07 74
    0x40c041d00c800003005171b161701075074404119242180c10418102c000076002400a10844028044000c1c0340701c2080d00044500141c6503217180b14000710307042814004200d0000040c9004409841d09103c1c099102541c0348400e81f106a07803500794008441c601943c0e9000264800d10018030402c000344000c85200b051910101c0c1010071002c14004c118569400407250003110206000401c8070800c00c584152030140040c1041d4004400010524004e42950f4000c0702d44900105480e6243c00301020b10b41d0804050040f0815107a66501307010754030550340084041e00e02402000106d102081a009940d0358284401e0369000945049010f0420150710b0a294090017160900004807461008000c00403185600022807524840b941844294001e44201c01d00400803c00382081601d0381340d4000c03c048039034400400e05800120386504454000d50000f011040440d180222152042c03011076901d84d0003401035681d0641d0b6185180903031301c1800c030083c03e450014000180c15a1704258045034500c0d004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 563749064 1250 563747814 563747819
    0x30603060c02030d06090203010e0c030a06080706030207031806080c18030604030e0102100b09160203071407050a0501092418090c27060305092409060f0c12040606 72
    0x40c41100d22061030301d00582e000240d29180a03105002c1d00c8001c0070440c004505640c500208103014042c010070790000920004002200f000280e80881c1c007a08109003200d002c07035158040500207500c05881500414480c1820181804c803404183c0d09803041c07903441c8040c41d15400440301198001407940c00c0c103010350400d40700241d10700f080b00500c02c134000d5480e11001c1d40380398006814a01000c50742150b003420020030360800c7c4c90b50950250003c000104c2440e036890880c0c0c040b42140550400140003148201141251a0380000c0d20700640b042103a41010319507170340c0010b4a500b2900d216240c804c1c030344000c0c02c81800f50207249000f4074100790300b0940000e02040102d642900c0103500f10701e070803690340c40100b0030040d802150320908000e000f8030001240004601e071981c1e01501d124000c1010349507030001d05007035828009009400b14100a0001c00d010403400d60060710f00403210b070703105403048200040310081d451080d18060805a14001c1c6003076184d490202e001c07000204190361107034880701c00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 563750314 1250 563749064 563749073
    0x60e100e060105120d020a030e0105190905040e0309090a020322140601090204030203030d0b040227031c09030611070b0103080c120414040203060d08030906070201050c1207050a030603 81
    0x40035410024103015022540c10001004640071042d2054000755210010000429800090345018250141001e181c50000d80c00125410312561084001c51040a074039201e0240e080001d210595104541c14002503400200305596800355440f010f60111810b4045080022264001c60300000300e100882d0801c05031410000c082c1c2c901e081c044032103002c0302031481c02502c814400c10340500b92002e03055203050300e50740010781d80c0c2c0650740b40054019541d00e07035881d0075900c580c1282c0e00c003211220780068405c4110328184030480031081c024001d00078418628404030124500540001e001d0326545059070554070f8540c01011075000510715100200004400715901d11415030082d845102402d507511034080309182400c00184072a40c00100604c8244800b0041c1c0c0e23122380da4100b00b6540140c582e900e0b8000a45e0308480310b0b801402005001040c058031102c080b0f4114814071281d002400581c490310840c0c06544520592525000584000704803498031800041440740e10600c2c01094481d101e445 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 563751564 1250 563750314 563750321
    0x60819170c0f0303041203051b13081c1e0507120201060302030a0c14030f03190c0606030c0609060801050d0609050f011a01090609080712020d0b100e22060e10 70
    0x300c00d01d0b20b6201004000804c00c0320005682c2c004001c3c0f6050019042c207040b10940607800960284804101141100c1c0d00344004852100910341031301110680840007043d60f5600d480e041ca01d0000034150020841016180381c00034120381c0303a07551000d10301080d0751580e254003114801001d00319500c966000000d60b42c1000307042c415a0180c502e4010482c40d1045a140c090540e01e8454002e070440c81225040031404000c1ea032042ca00e030104807050705409030045404415100004184910741706010090000d02403030761082d14015221704c50050340b900e605460744903003482056401446207584400086454001aa07040c0c070030070403a007041c044091103609440600704c02c0000c020207010313a0034496a010100d07c0c02808942080368074076042c500c18644601c0217008a80384100e03c000d040d411511440900700b007030b45e08100901e54a00b0300500b4940d80314500d209802e4400c0c41c04010540d28240c00301d038100c0c9001c210310388403e0003d055803174101406c1400c0c1e43c10141e008241410038824010b00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 563752814 1250 563751564 563751583
    0x190b0d060c2d0804020f0d050f010f1107080d20030f063a0302030403050607080a15051003050c22030b13052107060f0f060819170c 58
    0x21240078a420402e00c000c401c40328082038082810020b241c41d01d0345142c0100368541c105406450084a41226802280d60285e03103200044c034901c92a00e451017041810b60146894906458007808035034049120001309000301003001d03041100800022607032000360b83c04101308101030014404000e003100c00e40d0426810403030b00132212074010b200f0008540303055056000411601c01c11400506110303031120108002d80480c031a40e1a152000760130915008001703071402568028120350b0710786000b240c0184280c000390b03081c0703209500b42001d00320b80403c91500c0a0507030320054443c104101c0602411006004080d20480d8a0207007044642e07501a00c3e100301c82c41c08001e0305040040140307185003520384c84800078200b02c03c40d80c2402d40c0740d0016501203040c0c0f003151a540b110115903280c8142e0942648200c0350002c140f58500a540407411006400003004261140d604201007a5134050640d11070003008100d080c0b940012101c42c00040e148141070004045020440d4140481410183d01e001c1010 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 563754064 1250 563752814 563752817
    0xc0d08070302070b36492003011a03120c07062303040c1e0303090b0c01020708120f0112021318060c0e0414190b0d060c 53
    0x240c02020701d50100004001003000f6010940b03090f00c1d1914440c5a80300048074402055016481480c29080000d9102c0c0c818100420030021004108414005a0425603500700d82c040706090120f40c0400010000c0e03030741110310f55494003804059a82988142d064000c5800b40b642a032140710140d10700340300b088840303114001e81c040d2140282c1c08062500080d8505e100d1800da040003061045800400c611007142c64905140c1c5072110104a50b41c90440c40c1c5001044400001c4200000d005441c2c1c44c000403103401e000d00b2010a1440000203079548607900005c4e021030740c0410300b00700300c1122000034208000c10500050038650ba542d10b1070340980c41025214000c2034480305100350321315084002d500419890860504510241e40031602c503250b4044c140a0340790361000d15541601094406102e0641d010713a00300901c500d452070142c10360506002560186281c070071845003540480d42d180e4015003490240c040414078150a0070b01500109502da074010042e90341e90f0b0001a0980500c014138070343c6 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 563755314 1250 563754064 563754067
    0x321030e0f101107080a030506030a060504060f051e0f0907030605100801360212060414060a14011406040b13240c020405150a03111f080708090c0d08 66
    0x84045081650701443c08589200310400c00c0300c000404000446a10792140d04020910355900b03000242030526080c409000581801c08110400600354460b5078105640e1000b00b00079111006130090490040004000c601c011f80302143c1040c1d80c2b402c8241e485004d1200b01c504060302c0b9650201541e03420395000381190300c0c01d00c062018030b4081c080d80f402042910b0754801b02441d480da501c603030524210122000311412642140035912260514800303030302035004541050501d40f510311262200000250044d0084c0c8012451140c014015401024154100c2a442ea402c12031000c1c000d211040c0255800380d001c0200040f0000250080e124010f0141e0680e90168074146030009075050345020380d00b040e83e0030b00414481c3e942040c40307510713040c0c0c06072800581942e860f05183d03891440d80702201d5001a0312800002000401d12814490301d00a890001c1040c000ca00e85045a480c80b42101d40440d554a0000f007507180300b035102c903500034040c03070844032140103600105443c00c1394140141c42d031410 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 563756564 1250 563755314 563755333
    0x412030905031b0612150411030a0f0e0d051b1903090816090b042a110a0201020d0f030204030c0b1209060f16020102220302130203010321030e0f 64
    0x4062101c1c84211020400521030b0040140002e0307413034851107207840780c100080404540e1b0103001404850346484007038400c000c1c00032041224040c0d5001244c8513003a081c00d000b894010210540110407003e5030003801408680c496000680d030640000032804048811000003070b050100407c0f00210300034018141d41503004a03818002c0020700f00f83c1003a42d542e44540c10b00511000742c40620b4086690200d80001c100f031a800000b005002c0d40d00320302c0b00c459001c1e110000030403101c030034040a0500648548000c0031a40c201e0546a070748100001e80940c002c0c46405115500803c9410032040180c5001032038541c4a9032141c6400e20700381c02040d4011004501000c0600802078541c0e0401401c000400c40ea1034a0796443c8021200180004081c584146240c60628000d40542d500310748003d500700e4002d14194041e02d003100e914401603206044e84200303011300c034030307907100701c3e030681780c00102e4030030b04161260906000d001010f032810701305503843c030410315640011b1000c4034248600001802e001036 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 563757814 1250 563756564 563756569
    0x5010602060c03090a0303110c0109050304180b0a05040513051b01121b0f0909050901020304021017010509220311010b0315011802040f1401090609060818030412030905 74
    0x140c00030400000d2142c01c10612461300d0001900a04030faa0614000ca0740300c11081644009000c0c468141c0590740c20302128030708101c8040003400c240c3e211148160071041c0c103141c1c11402e840c89071401c550003102441d802e2040342099040345921251241c07106c04021180c0c0d0b80c8600d81000300840b1580015440c02d6440903680c080f261200c680a1000305000d07050219103095441603403508840d05104925641551480c020f0f100c540040201c00300811081c9844400c0c28080d500c1220300324415803450918080c8a0302034003212000c190301c140a00341907820042030001d603040152554100b41c00584605841c03100341c2d407104000e10b05c07036540c40b0304c15074503080c5003801e56140da02d905120381c01c5180ba81444080d02180b10f0b0444250784403052091040d014128000e1040e904840b00071113051341c007c50ba100365058484030f1b54100303a070380c1d005c02d42e51100110b507104180e001c0c070f88c0000c103945c02180240003070403010381324002541d09485c42c1070f40d00c26441d80e003402c03805001c40126900e04400c01052 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 563759064 1250 563757814 563757823
    0x804080a060c0e0f010f180602060411091905040201092403110301471c020406092313060f171905070b120a0e0706020d0c1a0a05010602 60
    0xd164604041402808500000300007004d8807600c68100103c00c01a074040c240308401e0b54900010400050a0058441d42c0007074a604c0200c800307448651104103c4942400d241030100d120b6011042072120145178243c00d503000d0000030744143c0c10402503140c08181120300c0100e888045d28080300000201d0780d20031020f002d6a191958010030048180f00401c0700c268607481d01025080c81c880030a0a5450041c0c04076980380340340c0f4652038002e4001607020344074840b040080001c03451103007403221030314034030b1100c10280e1040b80112400501c42100410100042c0048421060840040c003242c1d10303005c001042002210420700310704a07413101820400e01e09140b96001c05085001c9050728040c4500107165038807041500c01c10f070f0100c019541041445000c2c89100701810408ad5241d07a500c1103c11680029442a1604214540760a4002d203050000207852003c0352829005802a4840c000003640c1d94528008144c4280030050150f03400015444492403003200c1c0524005800c0d41007010017441e2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 563760314 1250 563759064 563759081
    0x3031519030308010603091703040309081006150e04020d15091d030318070b0304080702040e0607140a050d0504142a040f0b10110105090307030c11010c0804080a06 72
    0x24604030100501c0402d900c003400605444042c140412140c800c0d14190300700100c0724840390300c2d2a1000c0300380030406501900980c101c07944441182d0100541f680d5840840340c0d05c0c403400b4035440c0650901041980550f8441c1c401850040005041c41404070910007900c1c03000792202d4854100c0c0e8014809826244141c00b0703803000c2080401910020914010381e244006442e4502c083e0311000341c024070480821500015000f1a49044d48034142440c1600081d005084120b10560070305070498041d10002a41500c80c244640e0f03040000c164002c0090700691001190104001c0d04124503200340265000c0c41c0c1c01284280c5d115655030844244560401034030328104c102c001000b400700a00018151303003060180d60200c500140344c12015441030010030314880b181d9001042440070801c816008840c1d01003200720080244441d659a00c1104c0e02c0f44a03020008011802c107140d00000b28120400c101006201810010030469654480800e1031b080b0780d1100130280e0007003803010100443d03402900823 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 563761564 1250 563760314 563760349
    0x1e0c030320121e180103060e0609060d1e0b01080709020f040612020904090b0f010806011203050c07170d020f12070f050a061109030601051e150705030315 68
    0x600d140c1051854440c100b100a410000e00049040c0b0842070321420400c1c5000403665409581d20b0801145504071014545040e0210349040030001c1c0c2c02078249106446110000d207281050740c4c50380c08008cd0300400503000c1c3d580703c8000e8272018240100d00c0728021141e0041000c801150724211803281b5042c7c5907001b4070840782c014494007100b8203030107050b41c05440351400d1036200f200c14813030150000c1c00f0b80c1201540c0b0a08009040c410704c0010b050b154018400c1e126001d005a8840030300c0e980d203800a205284c11a4040141a408244034101420a40d078446081ea0350300340c0e5400c04030003a450000500d101c02d030010b40f01d2606481e010045106100c2d0210082c0c00f81401c0c01038885440e01807080040c10342003146803540300b0003070248645c10066a000710304000040d0700005854064007c01c2ca02c41c0a4400c100010610780b0300b0f100a811019203404a0a20307489200050041400c1c0425400e0001802400311074001941803014500c00c80c2410416400841850200418403550060000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 563762814 1250 563761564 563761607
    0x608010c0c060f0626010f021801031506270305010e0d0f020109021c030203190203090114030f01052103160309050108160e0f030a060b0405010e0f04030c1e0c0303 72
    0x840b4540101030308043e503101c852008060308059070317071901411a4500780701710f180c80010001d00b1140c0d03480d41d40c24110b400ba03a04104c200d840711442000324016000d62400720f021030740050908149060540c181c140303c00c5580000d0b543d6966880d094810000c0001100d40010b010024640d5001340f14540d16180f601c004e000741c9040e6000f1802c0d801c1c3c0c00032102040f0603000034000a05000708122420114000076021044201d014001d48a8110080460010711004501d0b804d610110094a01602c0940000c00407030f407900c410400c40e40420010940340f10294030030040000b1090001e00481c00300d00e13202100003903a900d00102803038040d410160602c140c407070030b01240300180b60340c09054418609010750640c161400185e0b03105030a504066040c8146c000a10401c14250490b00001400341c0b0300b4020780e6200c0ca11981c940c00d0403603090020090a07030014022901c82c0507108a010301510001c00e425500c49a103444083d0303000410303506a29044010410564091841006c131500400f028 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 563764064 1250 563762814 563762819
    0x903040320040e0a1205090a0e090d020d092103020106030b010e100501091202090604060503030c1501090b010215060114030108010e0d050c0a020f060c0d080106091406120a0608010c0c060f06 84
    0x156540d09203910f171500300680894200c40031307111000c600780640685420081241390014034a4ad0301d0760307034400100c01400b0b5546005003442c000c4081d40c0c2039840f94031282d41d0002030308020041356081f0032404c0e411513481c3d03500080421040d0300800d001c1c0c05040040600344c5072010031480504080c1e444039040000f0fa48041181ca01d4000307008100d82e60441d01114180c81d2800058080c04080c0c00c140d070316000008030b40e0b42c42440003c001204446443c1c003c42607a9170b0b624401300b110211105079000d80c0110210960700704802141c03551040050501c034220042e0041110410382090700102d05580d03490815012881d420440f0140110349440c2091410803800c2400da12032400d19002801544d41858901c0c480e941e460a813014000710708101da2a075903413400700a048440078441d80002c1540030001069091840d401c4d09030120000c0d010341d25000c0742410720012003100408440080d940c40e03501091091081c041c03020b8000b25940c030812120170608001007121164107803080e4113850302204 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 563765314 1250 563764064 563764073
    0x10608120406032003130501050912040b0c0115060c051902011e030e150105090c120411060903010623041b0305070507050f2805150903040320040e0a 66
    0x8880985505180125411004100007044c0381d40010320b00e141d0340d801200b002032091a070301403103ea15005400902482d190890001d444041e580303908194480108818001040808005d12195601d5000028544404681c900300c480058000383c00184100b60f8400c240401009114041601c8058000e07001c0c98640c0080c068a0100302002c0c0c92500114030600d03041d000746e0100c21400500400e54010003032030038100b60007403024081c0b14421032002000c01c4491403582d0a40744610f030948100c03071281e216a2130f004c01d112414444258049000c004107002510280644001000b04a045410a519041806101c00010414940120304c0c0411204290078030000b0101c1e03500c0d03030b8140050702d07484040b402c07a0648202d110141c414032850300400160580050071a061808501d010035036134545810350080c002c03801382c016040e076101e074458166810700c4800d843d81240b50202103d01d010350320f6a0b150044024000000080700400484c46050700303107406a01c0c5940d074004050601ca100301d994 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 563766564 1250 563765314 563765317
    0x150503070806190e01120224090d140f0d11030703090902090114040f03030e060306062a010e010b0406050f0a1a131715100605070602040b0301120501060812 69
    0x407445081402020b003401c08500010300084c2066103210f400a40c1c594080d49011200c2ea0700c00c0780150032001d6100400051000009400c0c41a03108081c903068036102000703401500e64000740d54103410801200c880440811440c51440d80d44000303400a0080d224002e460148118078440c81900100304003c0043d074020556829030701c440c0001070b09d07a090000126410f00140740c8240450100140c00728982000c03106004c204c0348a561035054490000050000500003030340c0c00c41d00002d05010000c51070f10458203a10f018039104032540207481d034503000d86003903403005440d501c45655580c00080031070400307010354006083c0980390080088034a01c0840c400100620419001e140c08088924205c81d40b0421114424000c0317041d110801c2e140c88000c0591424a03044450038860020640c400700b02032000e5900c03501c4074400c100e40141c5804019122030380100d904031840f603800c11002c10091801e1001d1800381c02303004154000c405061078100c0c2110030700e0700409010b910407099848000c00741c20 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 563767814 1250 563766564 563766571
    0xb01030c020a0201051e0a02070305010e071202090601120c180e2703040504150815060f10030f0516090f03050d050a020a0501090308060f090c030406050709090c05041505030708 78
    0x39099079200c0080c901d51b003c841242600c039190102c0084d00565655000620750300392400340e00204103040c000400b4640c1d4807000d12440c000300401280c8440540b40c00b82c100c0da84400181030404007520f2580401b4102d4661000c41004150381d000220700c10b000210041000d401f01d140c02400a040c040100b8500100d494426525011400a015030405040c42580c00030b01010b801404022400300c02c08208480c01c2c06041c003030307101c0ca4100c010b0030140311050a00864000d401c0c2c0c201260071105200100c0030404803c401e2585400843c00890410310031070740f2a20020140c41d18940d90414010702c41600d40d4824420a40040c0040c804900c0100d180454000300d030400a94a244294042e410f000407890050302a51030305500f6010300d40c0010075076101e1a000c0710340707182c014140c0041000e1550140d6841e003540c8070500c0010001281039000940001c3d8500380701c100d580e41c62a07007a003600d00e080c40820020b0804101089035940a180d10007100c585400c015042d45005040103201c40e8000b03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 563769064 1250 563767814 563767817
    0x80f0f15060d0f120e01030b0d030302030603030f070b150904030522090510060305060a061e050f0703210606080f040c080706021c081b0309031c050a0b01030c020a0201 74
    0x31000c180155200081000001c0d40082c242248040f00e0400c24090384100b02c1070408203d100314540c80c60362003446035001600c4020681980303d00113450450080d0402080140c2620081181500300d614400281c1542e620039241d8038511302d0603814000d200c5400e100590f005100d0b800a000000b41c00100761062014404401d400d03c176a5038009069015069000d00300c906e1620301803000d901c158040308415200c0c10b4070103000648410b800d2103201d442e54820100018005101d141041c441c038407403050500342a140203814284800c003a0b6851341d1081100310081203840c10402100317540c206d60f040d819980ca644c100100e0303240240241c8903e4004207441d40350600c450010341045011480e04001c1c0c114281120342301c1d80c407008043d50381d80300d10083c0c41e510380c520100f11034600d1107070b60a58031554540740407280e804a41040c0c0c0d0750300d80002e00303a04200c4c0018440900c1c80c00c1005000303c042082010007040300d042c80b06410080744c40000d0351604040c182100481082c2e0005400c80420307a0a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 563770314 1250 563769064 563769103
    0x181e070f0e0c0f1c1a0108073c110106090b13020c1e010617010219050c03121e090114070e0d02030a0b010e0a02090306070f0c0507030606080f0f 64
    0x182202c02030303244109440000d14200000c00c65003c0461a0b011208074804010210021010b95005641e01f0343d04542400000344901411150050310110f542c109042c031160100ca00c40c40007056502d6046003085000015032000c010b280111024010710b801801106070401401a4080c04101d030b049407007916805e0700e600000e06890f02c603c100020382002942c00c070b2030391405840004850180145201303185446941c00e0240040d001c0610071542d41d10303401003034200049107a08007610300d60420250012903003c180030841100c0c0002d0480780c41003055015003580c0f0706200b121074a1010010f4400760944c0e2600c0309045405900c40311880d0404a00c2c00c0c440100d00341e04000480300440640000c0d054003a008440040043c0343d108241070320000700036055165101d40b0440c00304e001c0c040440781d041c1e10000108008030f0181403401c1c4a100a49441e5544041c16140c1d985458600d501c21110b096a0741810000380c00305006800140c43d018014051440c3d41503000d0343d5407040f001c40075440003603 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 563771564 1250 563770314 563770327
    0xc10022703150a02041d1003020405060619030b01030e0a0213240305070608090f0a15020705161404290a150305062115181e070f0e0c 59
    0x207080010344151245609419082c0c40e01d455410083c0d0058070401c052000c11844140c08668040c1042e4441d18911242d900701c94035540803c806850054a0302d900854200140e03400b4544041080c000304560342c40104000300c00900043c1216005441440250007640740341380160f036140f06d50704c0903030a007800100d0104482c1c907409504002e456465510b01e010048000200003010400314220b401503110f20169545244c080b80e00c032a0b035211070300701c81d401540c2500005500400001c1c2d04266846005040c155260f0301d0300e01d00304070038070700307280c1880f80481c20040d1a001030107038400780c1c205950600840709605045480081c1c215664030a40292501180d069142c00c808640180b0004c00b03050161840f50102034001e02059994501440d02c3c1404500c1500c20000b01c0c07070340422100e0051680c9408000030400e2000054189840c2c0d40079050364100318003007000002c0c4240d50fa492800d050b145010102071903c0d50580c0280725541c4174000c208146401d4200c0c6942c042843e41040340d40c1d69 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 563772814 1250 563771564 563771569
    0x806061b030c010e01140c030c0406050d15090902090c131419030b01090501090b0604030615171005090708060606180301020a05070501200d270302030c100227 70
    0x900b80e0158040e62801d1401418403805400c03031700074111b54071503404441d207803c501e43c0718900c4110303260786030414104030420009115200a250180620302c0004403500d4280d06075000c2141c81e0b0103196900d864402603010740c507081c00090303080f0014030308007031500c42c4141544811480390b2060122310386017501211042d4a400c600e00a085144e041004082e030b4481c60b250500c0f41003801070b04a224540800880d40b01400d1085101c0440d00801103403c06d4510360f60381c805030082018488202c140d5400c0060344520380542415003030741070406808201942003050301101c1d4010aa0186070b4008502040414404550709070820340a41d4020360390050400000010800d0752011501588000740500713003036900c000900019441400280328403c400740c00c504140403083d60f000c0f000c07102044865483c0d0310507804082c486003000308641c006c015079002c508400d050104180c0258100059200100d10140040e040d0601c09035011410900c0b568005141d1001c05040c4070901402c003c140300d85507 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 563774064 1250 563772814 563772817
    0x1d0108061f060c170a17130503190e09040501020301060e03030306300607080115050c100f0e030c060f0906130204150504020c1606030218210a0615060806061b03 71
    0x1965581c0d21551031385c3c0c0300c400605101118548540301c0480300301080525101c82203108000e600180114100714103804a60b0703c00f221100b50005008400340c1120080c1c41b0410b2491282e401030700011380340c0d0b241a00140c62407c030f481a803407007a0410020081103545546041d9800c20902c1180210300b40010071122441aa400c0002080d03c02c4c0c1b4100046030b540851914181c4250340c90b000d030045080e000c152882c1c0140d500400058000900200c1e10510f1a88090a40000c0b440c001c20b01100744403d503402d540c003201d20707406160404400c1000c030030070341c440c0950025045e10081207285004140c440e014046e10310020f200c3c1d81c4480d24494034643ea10060005424010700441d66002c1c68605c07281c0d0f03103881d003602000b28450a500001c440380244281d03040c0018070500c0400204160341002000340481c03400314411900700300305032074204082181e241d807940301e006c0024411000c501c3c0380d4500b13446640500104043d1508015032520745000380c0d01c2062400e1140c00c1158000145182503 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 563775314 1250 563774064 563774093
    0xd0c05070915090e0f07090504120305010605090409080d06081b0306091005040f140a140106050d080c10051023060d0507110303091b0f010509191d0108061f060c 71
    0x68851171b0004284000e05030710440c0198403c803101c0c00300600c2d01d03509a007515001d10403200401c80034021f00e501400c141d0040000603104183c01813601c1c0b0070098480c2100e000d900174214540c0030010714016581100c0001310290401c400404480c44c0c100358180d5108149601c0801079134480c808201000880107000c1d0380c65602208940007200c140f0030042e42c6128104040e98020f5000e2181e0206e9041032003007000303544000d0320120b02e440c2c00b500c07503504aa020071040d0740720f8491600040c081c00011311039035005041614650040c0751908a20328803c0858800941c0f0090594441000e99030f112001c85160b6429040d020610780d5601009880b140034040d81c4210b5408004100b0140b84004501d13180c0740008000000405102c03442441200d01c0950031040c08038500b000715044500c3c0010381030000c10340c0682d1540c11180c89070188515600c6021a48686490b040c00500040c40103015280c1d100a100d46421824801d41100315030860032031040000380020308030a04240030381c58610350f21 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 563776564 1250 563775314 563775343
    0x143c04050112090b0403031b0e03060105010c1b06030b100203090a031509021305100801050408030a051b0f04140409020d060c1214070207050a0807180e0d0c05070915090e 75
    0x2c04d032400d410080c02506002410401e00340450016a106902030842d0310345940d000b40003860b080c2c0c202001075a0400142c2c00c01e840b490540c1491000800a13080e0203c0603180d1541d020a0000c0c0000c2484100c4007030248010654009002021b055201c4446070300884c1d4021400510b004103440549000b414103401c040e40091068a50888100c6c80b42c105500810f1011202d0801e04e13911220242250010303180180782450800104070400c134260841e07070b0040c01a01c500c0c0314001903402c1e0701c442540604107044d030807030011500700002d00030903604807815a019101806010040d50000d0710f0350001002c01003989035034011529010f40300b20406401c0b86070040081107900300202c2480096001103502c0340052042441c085041d08001002000311214030000740300c443d0604900b101192031400e0030050060f41c4003c603058042c0108a960104100c0c2e4036650750580c0b59080c0a4203200b09a0003014410741402c0007070000041040071007080719011200011030703c01c0c1c41c070710b1800d0229001c044034 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 563777814 1250 563776564 563776583
    0x110615010504170c09090708071202030c0306010e040303050f07050306150c01020a030617070302011b2618060c12070602040e01260c0604090c143c0405011209 70
    0x3401d039840015000d100d13920803504446141d690b040301640d40d410074040c0300c0751908501c0040084402c21000503000f24802020b4840302000d14000ca403808000764404003000d00d030f281c00c1c8424140c1505c00d254210743c500038207803c54030b4000005030031440060645070040c20000b21140b4095414010b0340d18000007039000350341d580d00d0804014040c200c5030107440100c3c012101c20352000540010001d00300d0354183c44001448102d0481e840916000c014251223002d03104221961442190301503161421901e1030140c0c8a0308211b419000c84c0d205503090701d000e80c00030012000802d0001034202400701420810703694401440c545007010340219403043e61502d41d800000700f140a80580704445078403560b52050b2103170441a13002599411a051200d4000f141080140284c244039002001a41038074108100343c05400e840003441c0d40d00010400c4042c9035000e1001e010034400c96049100450038050074403250780e020f0280c0807103214a124503814407160f55400d4204e01c0c00b0307801038407545801900702c4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 563779064 1250 563777814 563777849
    0x1210020301181811010c05030702030a200a0b16140609012909040204050604021204050f120702060d240303080f01050405041203050615180f01110615010504 69
    0x106400d60401019141107828006075503a00038440b45903d450f00d800c66400c103034003107643c001503d0701000d002090318107010800c003840c0541c408001c003105262040310050900c45040700b10720f40030341c603003100103202c0c2840c40c80402c00c400032207040c2c40122251600c1d020076011103180a420b40b00042d11000442d000c0d40040080c0204194840100003080311001c402640740d030780301141b240c0a09020f00798030074000c1e0003040150070aa0322403075108001500052509140031a0b0904180c1c04981c202c0782c40d03115416280c80d035401441100700c5070b80751f094030714281032059000850602400d10324000040d507945440860444000c1c6190046049940c0751080315100d00b801884d02004440740b507491401c80c000091941807521500c4d10582d0801660f40c0c008900b69011000780c003010300400c0d0b00a410311a1803c00c8820b00006100d455615040c002c464280642802001030b0f1002c44281032241c4185400038140c4085015540607094040504204079102e0060b030391802a0703004a0f10070400102007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 563780314 1250 563779064 563779079
    0xf1121040303110607021c0e18010f0b09060d0c140d0903090f060210050702121b060105040207080a300e070b0c0304180209062a0604020904021210020301 68
    0xd106580c0665100c1c0c410fa200d100f4000d81c0d61300180c41d840700603440307078082c010b054081012510403c038062419a104444c40c0e400a0a4004811040344182000170700400c81c40e004c1040d40c2c0000c20380042d105003443c0c1040000380703450003001d8480800700c0e01c5403a4116281c2c03044000d2500014084446501c401c1c7c100c52500040444d210120081980001c010510301ca445c002801105e410398014440355110100700c07030152002030810030941c4a546540000010101c01500200e01e6004808480a414881c41458508180c0c0f01c24050340c4100100740c0801c0c0380004543e454416400e100280001040700c050324540e01041c002e030520301582071000040c00580082402402950846100c0d907114040034910f44200140c421044d03004200412210901c110604003004100000506029141000c9034032584a400c5d484aa10151801018100605804e0001301030103000182202c0ca0581d0110700500d40280002c0d00c40c2030300704610490302070b04000714241000500019522544d68409 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 563781564 1250 563780314 563780317
    0x110603010b0309061e16141b0601140105031330030e0f0615010e030f060601020d1e030f0b0307080d26130c120c090e030306010f1121 59
    0x18000d00a01441300070403442c2500e80f404d06800c01d402410baa905480741410a100d0719840c503600d00a100c03603802400150f03c020b102403e001341c45a520910071702c2207608002d0611005030002100100032104050659a011003501d074410703203c0802900f004c1c903c0c101100010200c1e40c2c51402e00c1520420102c808914030104000480b49403024002901d40d00d003100d46480c034540302e1710030503480b140004030101d020342469040c241c412f04103180648a1400840e0070072449035050181c0d80d0000f800d000343d55030704202007407900515150000c1a5002d28102101452016a0810401d41c4508500c1c03502444c90b4414019414001e0484803d40e80d82e130450b60b280d10215400001140440c001d0b00100921141c68140340014400b078080c00340d03645660106c808402d0081070381c00c07109021002c99401340c03a41c07003202014003421045c2c035268a801880000e542503004034070b1250b0018028811140d812980d10b0000520b2402c140c40c1c4a40386e81c000c10300d81402100703401182020b44608001c40ba40110 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 563782814 1250 563781564 563781571
    0x15010b2a06040b151c051203011d0402011b0510051b030f10121109181011160f1403071a0603120414031006061b110603010b03 56
    0x200e840d80c155000038204418001540c1000d002600410300140009035400074466105005400e400a40c4a00801203000808030503441401843c0c0305090f5002e0000c1040190301e05000006c40918560405207003410107043d20008515600c1030f0b102040c11a1300980c0c2c0308012445000015101c00d1881c182541d841c034485410708080761070000810720180caa40200d290750a100c803012461922009180041d0440051508401c404d0155011505017007030404d07014920302820541910004001c20043c05034009090600b000d040d008800c40307a80c1d004503007202c0c03000d8a21800138001038030700e070b6290061094001684004e034020340320b1803c00a4418040100a0242e0442900b80e641700305000d550b880f84a802511046003082445119199424020390100e0090156a40e109030035205c034510f81c0158115001403113840802660605003001744100740b16094038148005440d00c0006020f250340c003406c1d0f02c80c0720407449242040c82151501d001c105030000d026203036203682d40c8610441c9900245c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 563784064 1250 563782814 563782837
    0x5070f030912060212072f0102091011070f24030603060e0d0e060304080906030403030f0501061e08070f050a0215010f03140309100c0f05070605030a060b03012615010b 74
    0x78000f103a0b50a01c1445034a0b170a5002c0300100e4841f80e074840025040030404a0220029034080041091545030b8038a0040d400f0307103d0b06d4075000c070054500a80d06190f03442e0084500c00a14030400c00c6402c0c500c0800e00450030301c00303a02c90030002660100300e018101507000980f180741414000800150002800301c0b99050645d5146045d100e0001040414030059601526034003062010204502d00103008507040b9109050016908947c10519400c0d140241c1c4510046091200c0804100c0315118003002140310500c0c04054030b00d0800000780070b2000000c0e0901c2080400702e621203130540200310001d100c00108005114540c1d40b203024805603009408103d401d4130318803010100d458400001d942d0100c100822040041c01c064504a0381e03a44191300a5030007900e510407604c0032500510207100944000e40c2c80503035900e0720025010079240150306c0b030705c1c500c14100010821450542c2c0c034038100f04030b40c00e0803419110316001d074585050103443e0b1028406005400000c2c9a85043c1d00a107401c4402 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 563785314 1250 563784064 563784097
    0x13050d051306090b1b070e0c0403020f0d0302061f0504050408090a1203092306070609050f030c070b071a09010e010f0603082a01140609100605070f0309120602 70
    0x1101c500301c1d004040d6100350907030040b092060417030440d24483d690541c0d1034001d0440e20800d507500c0d182031914105403114064848001024000e50400358800000050181c075016803820041c0e40c02981c03410010300454502c0b040b04040d0000607a048041c100800d070061051100b41064145500240e01100141d4402c808032913001032500165002d42003560b8040e1109800301c1d00d0b103441100ca44890701074186200c0320090650400d90ba82801402d5203a0040d080000c0620344c91a2903031422440010b0000b143e070042c04500d548400015920046d41c030740700d00c108d4807200c0a00c0c0000700484219942042104400100705942c4815445071400c2103410000340004c000c1000d29800320f402d09d000c00340c41d440d03040104002d000070781e880b803061708811000041c1140c81c4141605003100c1b01441d50388035240000c01440076910300a6810b0303030422100451480700d40e142540180440c4101440100000900030605c17042c14001c0c0c03400802004c0125460b00c0c030801516005000354003401880c00380c00301 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 563786564 1250 563785314 563785319
    0x30a031d0109050303071403191701060e0a050f040b0a060807080606121512010c051e04060206070c05030d180b1005090723070609120c020306070813050d0513 70
    0x401c07200390782120f00280240d4075083d1180c58480e8486030005583c0310500c030420444501601c4810211180d01c407a680d0f100d0318940042d081c40c10781506074000020088041d14103e140e43d644901c40b07045032800c036402c120200346d42000c1006003004500749580480031440000e0380b81d4200903010b210351510b607155031855849108200140c06140035030750301100c500b40050b00281d80d180c00c4c1d60506070018034104001c0c81c180c01090a48061031500000141d000c030380c4440000044d0a075104030b5048200050506052201c002e40d0307861700400c45d80400400707000304020b0100500440b1035103145010144010080c8a000b4010510640c3e0100c81640c110b90000e880100d0261000c025190b008080852036103800204413081300303402c40355000003018100006500081a4010404036110721780104036000c0c80c1c00c1800b805080349a040e0140405000d84a006990106090b03a0005081c00c1c9070030180c0310807624a03150a6901c900400505c50b444941020a422030301a16110401c070b484207002a4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 563787814 1250 563786564 563786567
    0x120209071d0906180903091207030f030f05040b0301060903110d051c2106060e0a140d110d230721050111040f06120b1c02030c030a031d01 61
    0x504440c1490341c04000e84450340061411040c02c0d030b08004001e080b51100300b44003c1c0d4a008202c20f44048071103900000d2805005d050503000344080701544000340045500c0c4d91180603095404000090800200348918140c1e1800703030060750b0160100b070a10f10380307039a100e8001030004207040c001a07581800e03849d48001c85151416185000030b500c203018002e58115107041c0b68500f60f030103210400b4064003a40c20111a14404c01d000a0520790080c08a555841c0c400c01502c01641c5550a9005205641c42070100520401000d42000c20075074001c020510700742803861490310305220041c2d00c014425035a000b44010b42d80c94052201c62170b003290800403207080405540c3c5119121f0141c184815550407041c0c410240310080b5000e010350000b01d14a41d02d40c0d2503c01c1c59000750002c5c00c0d0100e90303042c14000780394040c00d01402a10202c1040001d00c0c06038002440320300c403103c2496082e012801c2c11004644081c00040e0b010240501100d440710311614028050301400c2028081c00705961050712444d6 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 563789064 1250 563787814 563787827
    0x80f042108120621150f24030705060f0310050a210204060312230a0c020f04090b070507020f040b090c0a0908030a0302040305010b0a03020a09020a02010b04050112020907 75
    0x1568480d4034180341c0700a5807401d602080b8010500c07640160541008a9819146640b001c420200100074185807590b1940a28104501424080c051402002001303092841c402141c9075024814800407a050342500000346490110303003080b40c0018020400500030312080d40030714007500d0400e10840076a502c0d0f40c00e201c000c0e1050300c54142000c1482000c400407030302c01400703240080d0002d00049442d43e181d403101040d0200440e00b01d0005070604c8486c90961352085900f0580168465041380303424884c0400030000c0c9844100a482802a40851903030b039034039940035041541c0c0c03210710000b0b1403a0401e03000d0020341009406034082c1c80201101e40c2c0174036151103440203951000f004000103807528400b420a54000c1d844910901480c01c00105803440c0c104080d08824540e5034000d41d489041d481d100d400c1d030340701c000198010354054000703100503990f40f0040c0081c4d03250302d50010b888100e8810228003402c2908012a085407a0078000b0a08105010310b140b1842d000362a009241d8842c0314040f07a14 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 563790314 1250 563789064 563789129
    0x1b080a23010902030705040c0c080f040e100303020a0201080a020c060a0510050108010323030d1802130903082406040801060302010e010216090b0109150201090314121909080f04 78
    0x54000040500c02461f0070790095640c88228035050149003000c0e50f8103100c65000f1a003060031001d010038208040c0200700105640041844d07403608485142d680c01a60754031191034028148042c100c0012030094450741503d0036540f6200c111041424028580c82c000c00064948802a40e038208000c641c42d4081c41c0704504807680302019170b50551404054041c081c8041c04040705900080001205858090140c004185c240203481e901d0303601c1c01d104104542502000c582c85013070401c4a00c1c408070713070440c1c0c0181d481000c80d440d031490360440d50b01081c8680f007800c0301181c2c49030003c540441c00680542c449400d0300e1003a00e0b03519140d2005401a80d840040403d200d43d40e04015100740a410201d40000300c1010301810000e503070b5500c44070b910315044251850500113039910701c040014581e110640c0030075801d865400d2071070001801d422840313848004000a401c81458a22440c007121640c0c0320201040e00300c80c1c0162901e034034a0042e1020381c0700c2e114046561081c0d440d284070108044201215 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 563791564 1250 563790314 563790319
    0x20c030306100302070c0f0513180215090d0b180105060607030e040207060c05270f01110c0909030406090603060b0d050403030f021c061401050301031b080a23010902 73
    0x31980e410040041c60422452001c1c20140c0030b014100000303403d0300307200c0090b1482c21510a45181010f091140108510b440e41030321500740490806000d0b10241014a4107405039201c1b00412404084a0100d1080d400350981140c544c405031414410445101d0b0300901c286c402c559003104141100c1403d0341d4050b20442d904c0380d803c0204000003802084440305000d00500b02504021041d242c1c24100c86e0351808000100e000000e1120304030f100101403e1840c001c4852043c52074a150340030030354a03204202c880e81070000a4103070180d5840c080018141c0c581c0c0c010300d1004d00d403900c108407035281c0d08244503640105d00d55420104259006c0d00803a42540c603a05041c1d41080d000000380d80182c01d01620503000c2c1030b43c41c20158000f40303481c0020080d0041c4000240b0070381c98442d02c40780899070607a000520790b1000711150102d5a91000c21a41140d80020071144011078410940310007407070551241c2124400c682c10b140802058031943c2250b1502ca00c1e4040900c02c405e40720f24240c9001c01c90096 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 563792814 1250 563791564 563791567
    0x703080a0924150906031101020f070603020c07030b01080d02060112030509130b0409061505040b130c110d181d01030305160804080c0405060a08030f030601211a04020c03 75
    0x1d40824428038100c00042104011445846034610074241030f1264000c4003215441e0403042c420b1250341902803224090038030017450b810800384441516454140541e81c00c2680000d8800803000c4104620000b0b9900286000309a5a68050503561122082081c102601589000040c011401d0382042641a01929500c0c5441990010041e02d00103032052085116034414040742035450314810b8043c4544a1440020155181c400d090a460090361119202d40e082080c002025102c14400c00040c0c02d110308003140b8802005c0c5c1c156002001900c41d07444034070801c0c9803036140950190040c03510442000b0b038101542d07100d403119031403041d80030044a1500f41d800010070010303105000074a252401c0b42101807514155a07681030003640164014061644511000c0c102454a4851550840c0048407642500341c603019000342c503402420100e844c20741002c400102a40d01614028208201e447c0c01100b0340080c485601008140c6121513003490450740b1114805c074209842246d4810f4000c0f001076 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 563794064 1250 563792814 563792843
    0x6052b080306010c051b0109151b0c0b070606030b010b0f0a0e03240108011103190c030f06080a0b01090539040308030901111c09020a0e09030703080a09 67
    0x8a89550000e07203080d040004d607a1005001ca2000e02618605e90500c07000400529045800145984510b4210760401007030028844e200c5504000c0110100040b501c040f2610704843c1001341c030154403580300c40c0101c400051010b00300030182d03100c40183c92188640540603629290ac295880c050f030320440040388000c0001440043c020014075000220040445498514400f070a00360a082d501c051000c03c0c011000501c4160028000c02a401900929540c10b503c1e0040d07286a00d801d008002660840d07880c421943c22501c00c0c0c01c002200044010705200d82c5948050340c0b5510b00141c0c4050702d03602500000030910f51080c6c0a0140240c41c2c030940100800303a500d035030791603071000000d001041c14420920320442200f00b20103400194090105151a458000c041c2030940c0d48088400c5a030100070401520141c160100b400440303003001100261a801034030110745510b0160f002241c1c10641d010030000001000402422024070991350109107498520004069030b215100040202c1441c5089 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 563795314 1250 563794064 563794073
    0x4020604031e0206161a06031509030c010501061e02070b030a1a09040602130f05010207060f2f011103160c0503120f060108061816020304090f06052b 66
    0x14080b0305000c400d0608000d907a41d9000943c43c0d4004c002c01030800645013801402d201c0310544910900848a180c24503d18006c3c00207500e842580001042c2300b042ca0001c12801101042961190506200200503558541038040c0504011901032491a10340c01c19100c1c034030344003041c5081102d41c0180954110b17181d10404002030a4090f111010400003140d013800c1c50340e204a4190f0243d405a400103984917001540c080035030706290081440340300c80000c10022070740c3c00144c1ca01140d01e54a844a000b0080c054111210f4162004c01c60f240b1214598104c40c2241035034030b1858100d55040200300113228010501c0c5d1130302040324400c00c10301090021218040c020480c19403428410400c1d82d1800038918619402400c1c2900d0131820a803032081002165600300150342c0d00998200c44104a00c2c003124102c061a120080604540304020018100414000c0080e00d028040b07690b0107001880706180010002d0420f841240e20958441d0540c1c003690502030042c1000c1d47d1244181d10b4801040d803207 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 563796564 1250 563795314 563795333
    0x1514010918051209031221151f030c0903050a02060a020304120c05090a140a0e070801020a05090a050109030201080a02030c1201060f030f061d1314030c0f060402060403 74
    0x1207504440e10100503010000340c041c00b6036600403000c207041640341c400034810f0516120001400c03092007002040030481030104980101070680c40760b0800341c0305075502c900d0070081c82107000e0619001014901c1230b004140c01807001d03504009107580c0c2004500b0840100307c500003024030000d05190086003c101c0542062002000c011034103004481c076040d0307920040c668038541c100041d12048280311050085143c030074003254000302c0c1c845003800f058000d61722a4080100c05010201c606545041c402c0070000240030000c020111341000310b403140d15890700500543c0c85803d00741d1084c2030b00c18000c600b42d800791030701c041540d4060391080100d07038860303980c18025070015180b090010303005d02110f102407a44292741d6000c0e000540d1200b407100f503050f001500b51903144400715002814040144800c416482040c000d18950703600c002072031348490b411460754500000c005404840321041403038501c4000001442d60020403003c0700c0c0020440741c0359580300c03041920025401070307081000b0004110307840c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 563797814 1250 563796564 563796581
    0x40f030e04061833090608060c0d2a02070e060913030516150b041404080921010216020a06020a0b010b0304031106010306052a0d09030908011815140109 67
    0x5004c10110303c445030070804210130101140781c003074203041c240441a407500a0350000c0800c040182102c2c14a0305115417180908004e92800907600c43e2559500d415504441000c00101c2800c54945110030320001c0d21a2a00d0103542100c804175004a07940b820454007940c0724420222403450410110340e004c0741d09910075140b45441c401d081a4000210b5080154000030001c4148009480c1c10708109010688080341406109212a0810040440d008104441d22400115000c181b14840c0d007010095415040b021500315601c041501510000c2810000700b005000b04e0300c2681d20741e40c0c4d0108990740c00704280010141c0341d29030010456402d5203405541c01a110341002c02003005980034113842d00700242c4c0203079201074907041440b09000300f001006050000f960074441d1035003420300c0110741b00e21070341c0d0021800541e070310120014144070380c5001c005099488002c1c44a04070b0020114400986028180c4030b0000d01142407001020300c2c0329080803141180c00d0105c9a030b10b403060f8400240b9948 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 563799064 1250 563797814 563797841
    0xc110a1103070f0801090308061e090c13030803060a0e150d0c0b03040c0e01090c05091318050307060b0d051b040608030d050a0c030b09041502070209040f030e040618 73
    0x1e0b50041008400c8101140c0504211000040d1180712400c0c02014094080d01d40c1e03016104840e00c00d0071000103082d85002e5010300342d41201c00d607103541c1119642c1e44100125604003500d060300c0070081114801c025800751004031002522240c981c450044580810b481c0d010b410b070100d0003800c420341009203507000c401d805403840d01c040c980c1d08c0124007026841242c0845559008020a02942c00c4d007000d0140503020140003008a20705002014025210f8203400f01d11580d084000210310183d203401c598411100b0729500300079882c0710307e0016a20303000003008440301420400c488921b410109000c03074003c3c1e00440101010071401043d601480351982541d070f007050300d544010850030320400c010700304145560700c005024507001484208440c20701c4070740320400d820417a101004c4d5858072112900f098010140481d1510000c842d08020702c90150001c0d00100c1010800041c8041580140f074054001d844103803910302c40e5801c0104075641801a15480c003115a4244030048441e4001c0c03940340c1c4e49 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 563800314 1250 563799064 563799073
    0x1701060806250c120314091207080c0f15191107080304020d020a0f03020307090c0203030622140429010b0c1e07050a15050a03020d0b0a060e040c110a1103 68
    0x544400703c4500c0d21604d0000031a44401040b21048255041e0315481081c42000d842055510070380c1d19242e115103907000d401640c010900b0405402c2c01e1000181c1e200300001155038515121603049030b09c400845100c4c1d503100000784009031035406805514484040b4007045480c10150340e594a4141d0006441660440c0c00510403100607111803004101903d000c545460280303180d0b10415280045582008882500f4003079010002a0000309580e080078044030b80c40403c1c9071441403011940c61001a0741d511504085200114800c41e021150146000d440081000b1500008083c10003001c560a00d00c080701030030040200340221405040042003610507212010119290620a440c03030b18003422964204150807c0705150031881e00008286810f1351681c01c88164034003070214010380a14100f4143c002505856109a6030301c03014a5003c0203010700c80894440c90010030704594011000d00a600c1c02c2c034141d220b07034003034074000c03050b40c00d054002d02c90400300d5a108039582c40c001450fa50944107 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 563801564 1250 563800314 563800337
    0x10031a09040506220b060108040212010204060512010801150303030f060f090f0b031516030608060f041401020412020402090604050d050c1e010c03111204170106080625 74
    0x2250301003607000324001c030001d0440741400d1410410810440040c0c03080740a8a506000000d01c0946800d680400d090070244150303580e0340003246003402c1401189580303510018001c50300d2074004014140c02051410304410b46d80c3c89061050803140e0313020900c03a880480020800001c0e00c01d030400000c401c4166008909541e03104140d21095003141c2010a401d40c440d10100604182880380d0110748030101c0c0207149184103070609203100c0c1d001410540c0d44820904150031000c1c0240c02000040042904441c5a40b42c26a10b0344c2018030f0076038040b18403200d090520795400300b050007035406440f042c42c460a43c01d0565070801000398014101c480c0c01000900000501d82d440400009401c0e01580c043d04000200108000101180c4034580c0240c0569010304080e69a009140380400d84d810b0a052009000380e4230f5503840d000d0040c840d0b0085220000c2c2c007090482006200d40c01c0ca1503100004c2c082e01c0c0c1c6030000552a84400c40303080e55181940c9404c1c012148a040410524800300c0c18184800380 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 563802814 1250 563801564 563801569
    0xe0d14070801111e0405090c070f0218070f1d060d06090e0604061815020a121d010f02030f06010c08040902030a1e050105060d0903020f06070309140a0210031a 70
    0x1d22003100600060030201d10050b4084d4400e10802d004004c40c42c1481c079182c01c1ca400100310b00400381140c017030309070003083e48020000a1aa10b030714450700103041504070381205445803154078045408000080490b500c4800c818010081900c404600d4003100e03038140401c90a000040d0055000f1440d00c6496810008400c03000380300d86075111076114060b10840ca0300b424000c043d81c203c403842c030381610354408440000c1407819030102c03506110200d001d40c0c1e4140169040701d040b5400d041e80082d184c60000d0340300c1441891100d003040c0395100380c0280700b003441c804042000c90104952000719582c603600018000c0d0311510040200700e104050b0b907801c15480e00710450481e04120758110000d0b0f5070b85079904460440076404800344204000600c4a03604010105500d030240b403400400c001c0c0c5481800007014028000245d82c1c419290449840745045440140030b8540070070160344100c015070031900c21650100f103030308001c0e40207010161401c120501c12030040003203c101d803041e546440c1445c00241e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 563804064 1250 563802814 563802821
    0x706031808070b090610030c0323010e0f100e12030910290916080c0d0f050a0b030703030203040e181c0f0207060c020904030201060810060f060e0d14070801 69
    0x6004030104202071600300c00003031428002501c5403020b40c6c42c0c03220410000c0d24502c4c4120980360310524034907130100c00d415040111031040c0e55202040d42012815000f000000a008802c00360040c200d411500200c08070382d08548442d02c0b0018140c0040c981c610b0100b807040000c54000440004845078a40a407905030304031032800d1540e4803020301704003030440a0001622901c0c2c81d148121500c280340c3c106298560001d401010201c8184041000050310110752801a509800c61165081c0505c080602141c0028442100c183d0707481c500e0102d0300e14882c100003078000e050302d074190015803034107052a80c09074501c08002c01580110b601c4a1804006c05402e21000c05441d03810b44d810500040d421a010f410461040700180455204210400206600010480303000b50140c0c0c0e400303c0f40c1c1310390600f24090041ca0304048902d200c2c8641d599401c0403070b54001821601103d484440040e00c80c282240e01415010b003055010b031644000002040c803910f0f001a5007109035048403810b56880340b0242c01e4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 563805314 1250 563804064 563804077
    0x30a02010507140315040504020301021b0a0c091506050c010204051f090b2706040f0e010311220518060c04030b010504110a0f021005010b030105010e120706031808 72
    0x5035150801c2c808182e800014410741041e415800c00c2c1945400001c540d1708684603014541305941321001b040035501e080d41111080c0301500c100c8210030040017052980c45031940b004a8195040140000380100584545c01c0c45400041c20707001c80600d403000840e2650442084030b02c455508110005030b99641a99051a00d040088a80030484e0440d030064441c50307a552002070031a00c1000444a00b100303d0180407941810085a120030100708001710348103004a41003001807007084070001c203800762a90f00c0326040b83e02c2418103c2401040c1018840500102501c1082046071051206080c80042c2c003c280e00c900d5181035003107482140d90358146800b0056078800421200040c0900501c2247c00f011405013034266401e0280c40c1b42c0d92481141407103001c3c14007040250a941440b41c80340f0a02c8050520740e00344000b070200756142c14605007183d102384281c43c04a141010f041c0c50302c0c00c0907811210618800d030007800e004c0b0711f04281500901540c1429001714800080044002440304000d0401d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 563806564 1250 563805314 563805317
    0x801030b15130504112e09030611041707030209040206070f061b02010612050726030d0b010f171810020304080d0e0708060a02130b12040c170a12050903030a 69
    0x43c0c0e810300307040107680c820300034604078020182610940c139807000700c0040380900350000e00c1800d00e14a40010440d00b014860300001c01c15820a02140c0701c064801004c0c10645844815840d00614141001c5035940524800250031001c2c0000013170162074003d01501405000e51002080051580d80b03d40031a1910000782c40c0e0401c0303290400400760b90900c2900040c050840c07009100110f2034941e2559074003280728140c607106400011440000401041814120b001d008403a202e2140d02c5580026101c2c050183e030000e0012145040b0341407080c2d04002030042c4c02e040120b07594841050409010301485c4080c82213100d0011100c00c0c5410501c0150300c564050b556694460064190400607944800e0a24045510503541444007880c0030071303140d8008044c2c190059403060f2071403c0c1d440c041660fa11611a86002186101040290a5609100d140700340f020104054840da9882d0800d03080c524071201a5010840484c0000e03030090000d80b40440c00c2c244507081403810300000c1d1856000310200390 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 563807814 1250 563806564 563806571
    0x703030e0f0d260604020f090a0b03040b0a0c3c0503011706010303050d020a020a0218071101060b09040504060b04020712110d0c0204150308030a24060801030b1513 72
    0x90982d83c441e19000c110603c014803010f0303c00008500c00750b1508003901c26441641e000a0415201e10200304403440e800d006080c0342d1106550340d00d0f02000e031708112410388110084400085000b440c1e07220340b00e6010313804e4550ba1150005901272419805240f51750168001072001c07200c41e00da0302084029101c82c110f541e4281d40e0741c100100c8401c880001d01d454012607008100500005e80c0000c29541032040c400e0300142c5448180004030318000c00ca00010390032500060380c0541004e440340005204014584410f40b5280e24144120308a8100e03124103440c544007401000800d15003030b001250410b0003004c02007650700c1034000090482e8481d0504039860034820b402548681d8102140700d6a19242c0c00190031b0035286403c0182c00d0086555000348541ea450345503210360107601610704090754020740c54a441e07113410300050b0b0080200d00d42c0ca54907410b050003c40304071140b48804109030780c1c0e40d50707550a650b461644c85103201c01015010000c0b11201c401d89403642d88590340540003a860141d03021 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 563809064 1250 563807814 563807833
    0x201060303270f12030306081b011412011212090311010c080415090509010803030c030c1b010c020d140f0d0b031f05060a0608091c03090209180c01050319020703030e0f 74
    0x21b000c46130160300c508515004201c298400144a2049114400003800c0c10365441146018a540e40c0c030414070700300d50780800080003042c0f48080d03410340c1203914820071803440da20002140035180c904c0e0600c0020000c0d04020086000c43d4800d441032401184100301c030b642020340f103c0d50000c006184544050000d11440c504200c0c91808050041c014110304000e94a50b00348094a098548001401800d0742040010051800e05c5c0100c8101c0c401c850210007007003001e0f56410000d4840c50004004400281d031611420301e150320701412915010b00c401001e0385408019482d20340a0306c50206266418020701c010810091020042a148000103a00004480c03800200704852800c690b044001003003044020004e011000041114600c0e0b011000600601c40189089014006c10031000f50000d006100f80000b00104501c0d040c101d85021040c0d80d150340c407800044425000c212444000c0c120328896602c000d84280d4020012503000b49001302e0403801c0005480d2609402004401359944003c40c0ea = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 563810314 1250 563809064 563809067
    0x30c07030f0309060906020703080901050c0a240c02190f050a060e0d030203040f03110c06120609150d111306030b090d050c1f02070f0b07020d0201060303270f1203 72
    0x401000e004c01c0d00380203200500340351000356110f5503400010202e40340040c0a50b03040e8090819601043c0680b0300310b505034102890f103042c0780315201d8034030608414015890b08412549000f076a209005540c001c00030041d1400c0110705885113864250381a21150643c1c50219000344052900c0a0040d1408680c003a20120158a05403400d9007820426105000b4400090020b2841c00c20b07464040ca40f442201c150b0102c45410300b040060129440400041d25aa44100840940c0e00c545000c581d0001039035141028515000d1b0039165841d4081c07242c40138cc0c80091401c42d95032400400c040c00c404c9004460019800031100280c20a94003102ca2104120b03504604100c0c90444065600d806420004491045641d9902c0660f60074288a1105800e0003501d10f540c0c150f80c0040d4020441c140309a22600340320f02149002d907403440c018010000150241c1d801402248100c90b8141e455041700314040d1151000441280c0c1d500450030f500c10000100d10249040500117071403040e45203070543e01903150 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 563811564 1250 563810314 563810327
    0x408040b2b0c1407031404090b04050c0306180a090b070e09130c0b18060f030708010b0f0a0c02030a02040606030b03250e09100207052d0d050903030c07030f03 70
    0x15615070350740c1400082038120307038082400d5400068080285899120a2405590341c0c5290801e1484011b030100300018502c4844c1c220300c45508040d1000c00268070307003602440c11448100d030301c50717000301110034404815484806419484000030703800042d05016650368044806d015034013440040d0340750000e844c40b45000019a9004040c14403042d00c0e2030701903595041200d540303203e070380c400c940081740c2034420310780804c038500c09014014030705076030741c0e03841246a1007a41040c5c92000010703444c00008255138401300d003102c8020792422141814607034640c2d0103c0d80315112100482e01401801861401a00e450103442c0103423950761801308032160460145031501584506429031200600c000d2120021000524419907034080c1c603105240d942c800130180783c024002d02440313004e440000d01501b8060085101410522280c1880b4248448410703038000c0d050400b289450341e40c105031003020780706029400406000c000a002d5a0400800748480d81c03d01d101c03680b06581410310112450201a0f1000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 563812814 1250 563811564 563811637
    0xd1a0a05040c0c030509030111040902070c1e03080711090a140601020307030804121707021c30110703110c061306050f1201180e011a06030408040b 65
    0x780e080008022203200188920480c0c80b003e028020f00003141c102c252000e41090b4000015400c0055039070382d40d91075100082d071101c5030070703185012682008a610054502c1655007041e200c0e68101d02d03181181c461003426804880119140d00c42c00f101c18501c0e84840a50718031502003007000107030310084840800c052030300003000a4110340040040c41d0001c0c5d0010320541e000382c0c000c00301151145001c031050b6940b6021080d001c40d990405000c02004079400500000400e02c1c505000d149501e09401c183c0c0c103c0c0200649080030380c1c980710700c142a0700d422405c011506c0c000c2100821078401900c008160b60f4054013064001a405029410716940b00b081640b001c075030199002031502c0845c4146900d15005402a002040800030f041009062490251103001d03189104000c0f00e03594035159211103d0025480948207400c00004601c40d40301880348a20100e0607009018820750100100642d9520041080354020340511008c92042a104003902d0b054440011448140c50007452030181c0c801440c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 563814064 1250 563812814 563812819
    0x1c0209010806061c0b0d0501092009130803060f040f0207020315090d0c0611030a0501061106091b12010c0f0908010c0c11010516051f151a0d1a0a05 65
    0x2040008558403c40c41038904080b5080c0002036000300250000328040500c406c0034203258200860401403100300407541510220541c1e0316240100c240307052240340241284d88640e03e0007aa40c1c6040450800b070b0046034804c5000b805507058006c60303c002401c80b1018030301e1022450780802e1220450804100d111009080461281c20600d403d40445a1b11419103a10000700500721b1012400c11000ba0419481e020b22021784e181c403441c0c15620400105001d100708400225001a0b0700b101500100f140c5008a502d600500740d100d601c0c07010011103440042c03030150042451041a40070314400e05c900c5990020380c0c2d440740011032000800030b2650340c55820428013a4580190313085140c3e041000400c4076940503085490010b520001620580070719614000000d040042c0e00c0c0400c2030201d85802c028080c4442c06000f04c0608a00f0001c03565940708000403401072520a0066400d884140c543d00d0450394502490408003c08402c10340300c52000d81502600368040381c641c00e103011072846000d400305 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 563815314 1250 563814064 563814067
    0xe1f0201290a060f12051501080f15040b0a180c080903040e060906010e03010213240e09090a1a0412111027150b010201090302060a0f021c020901080606 67
    0x1c0001003a0034154800c981c180010301008042d200c2c0201e1403040c18441d610420081898010810710780300c0103610000f030004120300e0001e540a6002c0113214052100c58600c2801240220240300080000c20381069210040307000000f0010300c0c10041d80b11344040c1400204180c03d5806002d0f0200034050240c5183e5081400280f001c100a078881c1540141c084801c403a40707444c0c0200503034810060010b015059400014543d540107400c040c01c4040f01c00174484100e0002240061400600e0305000c0000006c042d001e003075680c5d1515081e442c1c0c00c12001c000351032940100303036608100003003010065a441c01d0340300108801d00100e11f40a01851b0900c1c1081d50852003805207250325031021007440418540d4448402500c1c400604824070b210705a52800008003101f4102010000c0308013007091503080c1400c0c603c0440e948113008010009604be0028445030319402c1b101c00103404480c24101c2015805d01410f181c1c110319030013104512038102c5006a60f0901c02c00014140b800007041c1500a500 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 563816564 1250 563815314 563815391
    0x5150403170309031c090c12020102060a0e1506040b1f12050c0a0c0311100f1d0304031205072013060e0705070c0b03070306260604030e1f0201 63
    0x70048121249801446000705d409140f035500000140200704004e01640107004011980a0b0f441030340072140b0b03000343c01310340e80d42c3d40f8842c2480a850700c20b15651243e4020721620440c1c801d515100e20b411010041012540c4120500490580720740300c1a00400301c0d0030a90480c0c00c0a4009071019580700c1040018007661400d10308001030b61007014000d400304810f00e4601000c1c18851361408042d12116070981d002c018802051002412601099505c558606034003406085420909961a119510040d609152031500d07015219480d413a0300c0c03014800d0030000e070303000198901e0302400305004040e40950b200080205100202c100d9845a221091801a0502c0a040d540e0300050b88000286000e80d40e800852911103210b42041d031101c0b4030500c003c42800038070f9070075400400c10f8400c4845482c00d80101e00f1440c0d88015040042103050350401e1002ca4003213441651500400e0300d003e0103441c443c440d244a81d41c1d41d0120f1031005001070b5520380301c01030b41d004406603450f1600c3d4030b42400c280088 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 563817814 1250 563816564 563816581
    0x909010209030615130509010e010b06090a06210204060206011401030b0d17070503120604180f02010c0f05030c0c040f060e010506030907050a0b0706050703090b1f051504031703 78
    0x54014000c02900d42d081e10301c1c00f659035100305d00c900050351415020302c40c07400d01f040e03940c0c080c00034505088019401c061a0b50001d04212058403501031004280d100f91a00c0c0c2582a101e0080141c0b130f0300c1c07400981c9003090301525242c0c002000109141c0c2c2c014922585442c1c0346034003a041051055041500740f8000c9c00142d50340c100481c281c41c1d0001840624a40b24107a9440b15125081b4014224000851403080008c50148001d03ca490195801c2c44040035032001d040e840441400c005126160a50120b03000d94031405070600307250321403d000d8103100d440362241d0745543c0011940c42c0b0705600880051403582414040c03850000351060007440342a0070701170604050340e070502440c0e00546012002a1940604002410007400301424004580f511601900e605a01000064440320f0400d0040f4060512030b219070b0245540211249046071140d200b44500d02e502c0b0001e1007405808520b01103141da4400224400f51502d01040301d07a15481c43c50802c0c007001140449866501003442000005d0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 563819064 1250 563817814 563817823
    0x10080105100f050c0f06041403070503040605180405040f030e15070308040c0e10060f0e0108041511181e151e13080c0d1106090f13050402090901020903 67
    0x140e040b070400c050020411003086407240036001c24102d2500c03640790141c3c0d0320030740403600c6401640104104501d03520852409030740e0703100d036040003031496004103c101b101314131450290001c41c07404184042c829082c072000034103840c0c00b9182912001c40d895040000c142d00000c0c111340301c801c280c0d80c5042c0c1c1e0002c1841c0c4c0b44140200100503007807041940000d001c00c0f21310040800030309410400d2259a0904501101145069008030408a45012111071a15014440003211080c051f92a00804d55803661880415214608250480d0f07468207545103120501802500c0118980300c80600b802c0c401d50200101c88043c00c50780c1c4000c034840e042c100c990742c40301072600495184124241c0d550f40d00000d4103403e80300d400c81c2000342c040320108500340c08400c440c4240040702e40f0740c4101d6002c540a0400c04c42c200048103401003444d4003800f00c1400300d050802c003800042d08000c202c0e151b8040000007054900f4810700349903081c1540c40003007004515000d00803c2c1c00142607402103007801343c41404280d9a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 563820314 1250 563819064 563819089
    0x903080a0b060c0303010b070213141902070b09030c0c0402070807020d0206120108060414061510050f03090f01050f0408120406020409090605060f0d0203100203072c10080105 77
    0x80e488249007000c54440004480c2440b0702541100d90300e42e96030034007100c2900903000480c030401d40c09900d6080322002e030049400540704956841990345030340241d0707040c42c0710b80394100039215000d002200210f8244900b03a403090141e00c01039941c0e110007500040c01e0206000d0102c4c4520b00c1403000e0b4000c03440c02c00980301320a1703040da594020f8950b2400010094006e80c07290005d0b030000240042a21080890700c107001d90310070110f55030304c0c5030120811903d55200300c90355040036155502c03011151606404005c0c0c0e018540c10218034091000320710308066401103ca8807043da100341d0100b0001d1009108050781700c00c054100d040c00e030406170382d081c0b4a1310460b41407140c9010118049428046a40e0440b001403050703041c00c1000514520300100a40801c0700d44600c600b04100080b00070703003015008001010ba0003000303410b100d61602d40450083d0400b41103001000458200804e64030144200113424411481491140b10b088500704400441c119261004010211004001c0d503291540c45419 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 563821564 1250 563820314 563820331
    0xb01063905070513020a1205040f0204050402040f090f051b060d0e100612020901050411090118031202030711040b060a0804030e0a0b1b0606030a1e080f091201090308 73
    0x141145030808515261141e0001540a03005884507401d0031300b2076009004030700942d00c0b90325071900b1001800049407012200600600391070310255006203442e502890b8018402400018808075014504040340c100c103400f00d6201805043c40ea083c0002007145400c20070080c080001401c101c200841ca0714054039440c04a855214040c0112010007800061034000010740b0404c4041cbe030340c4c1c0114a4140b00ea84c1c069004110550001c561030500f402802ca4034142c0000300c519105628004544180c2c0758540e100b0608400d00001c0002805000180310003942c41d0300550b200d13245800d01c01041640814407520642c45e0030303510100c5407550402e4801c10384080c1001000b9903501d0400750b44210810042513886002d128011400c0c9210744042c04034404034003d141000032161142030340c2d0754410340d9001c1d032550103050380074000f601001c0403c0225034030900b8101111220341d41c02d00140c011042c0c25421020100d05464079041481040c50543c032024002c1c45102001e0b10080c002060191a405 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 563822814 1250 563821564 563821667
    0x3090f0d05030d020a050406030e0105070f0e150d0b0a060804021305040501021615060f051507081e03011a030601090905060d050a1109060a0b030a0c14070b0106 71
    0x242444030030702c1500c480d004014030070355441c0e601107402807156106024070350100c2d103045601c085100051248612400315a102c0c00354884110340150b62821801000f60780c4480c2c525100103070b441c0c03144c0181000d40000540880c4680c41082000b07408001d581104040164420402016960741d415900007410040340006294a07a401e0507800791180d400140300c61000c5590507010840c00050003000c4440d6803004200e420b44801411030303220018401c40b9482403881c440446070030141402011080d20803d80f042c6000c220901520a0700040a03120081c948080010090280b603203600c91607007080080b146103036180c1800040c00c10f050600824030744035910030029006480c0d00340d03a0b502c1c40760804101c801e400b10078541441c0620b83e80c0007450068201102140990501c1c8406c40265450801d42c1421a03071880800802030602000c0c201c100485d40e44901c0c0c0b43c91002d0014000103006641041d259070410001900300c114080d5030386240a01030340e4005d01c0e00b0205406020a404c0141101c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 563824064 1250 563822814 563822839
    0xf010e040c0806070c03090b04050604051027091401061709011d100c0507030c0b070215010305060a0e30040308040e010614191b1e110303090f 63
    0x10680403642c01149031445a001440700c0039821407903100001e84640e40c1c5100441e122800ea1016000c0c51282c9038200405000920052401640e1904015070919008007441281d901e5248050407507042c809400a50550500c044401c40c0a24484a004450030a0103945441c06c018a00709100102885042c4808042003440c1402c1d0450703106503005102c090311540003401200d480e03050300c0d040d1101182c038000b02c00c1c0208d4010015a441c26800d6120311402d05226200e000308001e0050184003140038480700f0406040c01290100e010f5800768000b0304640c503140820000301e540e04055114680d00200c03040700d002600c3e161140415880b130164000c031003900764440304140111340008204c0b04001c43e0114944409105c01c904a070103d5075192981d40d11540000f440d4440c441c40300c603248103038140491b0014010900086070300340c1c0c1c40b042903020f21107442e01c0025140586468500c640000d05680030f0191002c100514000118081d5103401c1d00321700041d0121660200c1180220a4040318 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 563825314 1250 563824064 563824073
    0x340504150b03181b13060614030c04091b08060406030b06120304030b090f0d0507080d020c1608071511060105010e190303030b0a150807030506030123011703030f010e04 74
    0x36420f40d0083c00f11082c808214000c41c040580c0072643c0d0740a100010000000c46200e800340c0c1085501075280c01c0c01010f0714031802203d5a03c014190030f414a070800c800501c10000d4820001c0300400c5c5584080c5159548100910101000d005c10788124100001440403038001c5403001c1c1c0000c001c03903400754540e0041c10660b00b1070080ea400540008401d0f010031066010208201000c107640710b05031480c1007034400040d24503020362140a40000002d0220442455895000b0406440d8440c05c660003e800c5041d483d101843c140c0240195070000390003008035181c09006484204c0302c500f44242c0341d002140001d90b0352041440303482d0400421444440f0961501c101c4980c0e845132540c0315609140c0c0300e00300900500300881c1c1a03406501c07411400140340e840c101603c0a502d12a5507111810b0720780007401c0303014120140195034595030b2001e9400304540940250320a1090b48000800310b507142209040054202060300312480d0410005c020705c561030095254191801140b03a02020748882c02c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 563826564 1250 563825314 563825341
    0xc1e1e0e031e0a15060302040c05071104051003050d110d05210604090f060606080112050616022401080f010e030703050a0e09070804060b0f031905340504150b03 71
    0x43c0000e108044c11151803516500300109585c0241c905100c0b1b05181c00c002c49683c407070000050101c02c4098030f101e10358a0325400280c0c000c0e00256a10302690b03180d88999040048860102e00460984171040305100418846004040c4582c1000350614402000510754081c0c1402031750b030303184880e10016000e50707910f5000d804a01d42103602450525560300e40440240442c0c0240070101d4503000001804005800d030080e412a030000144c00551035040882c5103c03101051420150701811422081c600840300300200c01e40c0c6000c40000e03041d49031010781800d04940c0c200504082e410840309620004000084400d6280e01d07150550340c590488604803004050182115071194519041c803621560214550340aa40034480c104110110a070070070030034a0720110642c1e05030f0808012064031901b000103158146004400740c030001e04e18a84280c1c8162100c48181e030100c900341c04840d0b181041d8400780800307854296802c1040c0c00e030f5160025070048c410b2190800c030410000c00982013125408 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 563827814 1250 563826564 563826583
    0xf0515030a030c1406070f1706061602040b042c060103030503010b03070309060204030809031902030d110102090a060804050d080c1207020a1704060e03070302060901030c1e1e0e031e 80
    0x1005e882580c14440c00043c60201e11164490004421808840e805071170029104e02481004026600c1c09403041611814a1100300c0142d034019500d034030601454541340500380c1174442c81c50300d2800402142c02169a440788601c00b500c3c06502c210018400030340c00a08a03415110031b408119103c2d60b82d145d04801415040380001c01080c000301e800010080300130060080c040e000c4059894240b20040d011000122110029525a000810780e0702d1003800b462084001e510600000740c9011801030215803031800380e62148001030121002c02c41031000074044883c2e4645945400c5681c1e01b06800411600d0107118201013072002001f0120f100b01e0f008100342da8030258403050170111401c4010324002c03590424401c0c403010600c150001480c602d0301207040010340f0b900400003801c1c00450001100108500d807294428460111101d400c00b00340d1045940024050396030350000040d000d07202540e1505d90300903640c1446480003008146a4011461880e0720b02c1300d00800c00388505503542c172468030003142e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 563829064 1250 563827814 563827853
    0x305030912043c0501120209041a0103060819120903050d0201050f1003020913020f060304080702100e0f090718080102071e08041809020604090f0515030a030c 70
    0x54005103c0c10580e40c8141d40700d9406032070904500c00201c0c520b030b1104014075803460b030361191041030001d98040d180310501554020001030415035a4008a800c40da07800342c43c05552039080046580d80d41c1d060041c0713800703041d08502500e810700c000850f404d510000501c00034500003140d025000e01030f00c640b4440c0c3c000d607045021a419200141c0c0081c0c000c0c10300303881c040d1403d55864002840300c1a001000000c50342d01414640455681180d480c1c500007400c4812030717004059803602c041a039181c402a5000302c0c000c2d0460795940300c0c244100b24814450184d1001401403181020700d5990b00c8600c612842c900940748030016903250b580448041140908450b62515072060208003000154050014544180040408603850b1023040c203910600500092001c0002c0005005a1610110010581464500c00714034440d00da400901e442c1c1242d00300341c1e2060795035260b0414958860284d250041da64149550701401e52030040303915181b00401c09001d008904509900b040b98080c0901d4510004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 563830314 1250 563829064 563829067
    0xa0b040f0c050a080708011d060d06020a0801060206070819051801150806010806010b03010b0c0a02060d091509081b07080105010e01150e0d0f08090a060905041d0a0305030912 77
    0x10001c000d40160451018080010034203000100d49500507040c060603100401a001d0b00050f0b030038241250141c004205641000c4910075240c000f40050029050800031a01c17944440e6051050003840c008004014104200a0b481805440c0c0032900809608024a440102d03141c3e903031140e04443c81c03018041c004201e40c81c2600c0107401c040340c2d000082c2554100401c0e91b400ea42c2c2c41662643d101000c2c0504542840100010001380c41d154005144500f040019590032864903000200d0a07045651149200f0361655883d10820000e26007480d80e10250000070003100c07006c0e880350780d014000da6016098000e244400b50055503001c0120800400894000b0b21807581c4400e04680c0114003885106030394514200340f081c5160241c0c1040d00501d50182264502c496603444207c903001c0944803d40750000100401c9010380c80e86200741014110b01e4460500c000d240409100444d0034001a0242c02405610405c1c5420004515a002d094161800946035103d101682d030400d2034140c02603d02150 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 563831564 1250 563830314 563830331
    0x1b030f023606070506071110090c0510020a030c020f01090807081c02060f040f170c071a040506031b16050606040b1002060f0406061a070c05040204050105030a0b040f 73
    0x41030505840541482034070000c1da4014105011890048880c0280030360805000501014404e40d6004c59410384203003112070340071103031034108101d504480042e5440260b000d400e00080c100079020481c082e8181c80100b4004209444c0106881c0700d0400c001d00c81d803a07610001e103241e03214000c07110181a2140c251103000f959040300c03503610350b1403850301d080c1c00180180c42240b0314004585a171045d802344d200110300b555941d0b14142069510700f000c40b04207105811105294500c280900110550440204600b82c1800c1d14081054200003201c2400c0008020030300254803000b090700e400040b440512108a0b901d9048520b042c0140311818001c040175024600030f0000010300384c2d014141c25502040896205010721488000008221001d80d00140124500b40e924200d4150b100d8061000010340a07254a202c8440540d4034940040156000c40c80105004280e41503000604044408600d02894070001810a010051450081d5030380e80000360600d8460f5044480304800d045401c05c40c451 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 563832814 1250 563831564 563831617
    0x30d050903010507090e04030c0503070f06090203060912120405010207120504060e0a120b0414010e030a031104080d0c0f0f0f0b060a0b093706121b030f02 68
    0x800c04030456200b0b40c00c100209190364000c050b05000d4401c0fa20b840032466503291016240118130010132201031000b0095900890903d05003100c003d0f12642001c100c2400c640101072405c03102510351300c1c07150000d120688041e1040700442c3d1803500303524030741101690349061186c024029660060035000845629010465001e40104140e59064490720030107420701e0103001d0b1000305801280e08040c20300d010000450b402c0c1501e20b81c407e124400080c44540002102401c0d2912020352110503800450702080564050180c0780400f4410580315090a1529480660700c0c944003c080080c02911426407040c08030104400c1280c070340004825020408900d803800107481c00c402d0030b0742d0b554500008900903203040d061503001c070781711098a00c2c10486090100300405145910510300c5440c40c64405010180c61810701c0014551501c0604d52685000b0028218042508035040d000b4079080105071091500d4001c004540044c2c64006651000c04403924000d2180424480209817030001c00c01c80607 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 563834064 1250 563832814 563832817
    0x1090602030610030903020d1d0a17010b010302120f1008031909080303190b030106230405090607080a0504030e0310060503190215031b0d060602070515120a0b030d05 73
    0x3100243ea0703840605950000031004c4842842008005801608241d03540038030a640c1107010200078003180001c2e000000c00980c21008641c4401000c101c0d080b2903030820075081c0f2600040210030700b006d514003c80e142e0000410b0030001e180b6029481000045140d1034201d140034005024000d08803941c421105041e28800b800d8606e014002891034480410082c4000c8240d0703002d654454446501c801c000103d10f00500341806e0010341542d80c4090024618030b411034100300c4540c46c0c1003a00140c0900b072007844140c650040c02e985455000d0750620000c154014040b13170344114020800102a2240d250460300060a403040030381c94803509805e074030340200a520020844004800b2590001075010100110811040003c0d50200440c09261180001c20b001107500079a510f4105050840c0400c0d40d00d0581c00664000ca5101c0d41ea44c800d114031a010020a0041d01003240d0807004100d180201c1e401d07500c9484015200d414002003c2202c240c603d8020190301e03807004040c0c8400000c00c031030040c00d5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 563835314 1250 563834064 563834071
    0x11030f060a090603241e0519020a02060a0f0f06031505010812040b130308030c190203031b0a03060528121a100306060308030411010e0102060a0c090302030109060203 73
    0x151803070030000075440001d031103010100c9170f220780c24003151485450100701e601c2910f02e48616042d269510010000e08070204118a08204039000070241070100a08104044998014036024810800580899000289194070441e01c06004c2402c2840200740e8003d440704407001c4860b01c0c1030074000700c100441009680304c86090210304011603130f41c903804569612079800d03040005c24010441800801c80306c00041081d050000c00c5145410341d40c1d030b90348005510031501d401007070202040040c2c6d10314032400f0f140803102c10b13417008508508000c42409801130180c5910401c0d400d00003046a2064020b40001005140041100c207000c0030700d12040384038003448000080421301086010a51b24414030b500d035842c9030802021840001d40c00300a46000340050644010000e00400001c00584e443c00790101551080c180e2a4803130810b8034240e40c504c613140c0c400e2414000c0182400e86c6a036400969140e01c0b1940f02c1000c611040d01c64010344016001e45c101039059400c0042e070105020154004501 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 563836564 1250 563835314 563835319
    0xe19030c080f090a230406050109290301140a06020304141e09071808011a0603090f070f05010f0201020313061505031902120601082505040c030b030606010311040b03070311030f06 79
    0x54100c2d080c010001280d8190248c0c502007070111f18180204540d03050300c00306480d00c01c002d003000c1e0004880c0c041d0664200740d0218080750304000d115419801c1904ea920010301b070500045060500f82954400002102507401d401280020707241c180700d80c00d04060b100e1891002d0128541400c0000c4001c206c14000c1900030180359450000003891401407040c0c0d00b024007401241c042c500450b100f04201584040c0492040f03204100d5244c0c403030b140c180301c4000102610540e0b10221440c1000141c00b900c405040901076910600401c0307102468100d85ca2000fa600c41d00024000c2001200782d4044602d80c0c200303c0d0507201c0c000c480000104941552850760340202c903250b2942c00e0100c0c01584d40c0009000d80c002540000e01c00300103007041400c400c5c140d56201c10203000d950b512100843c08032820b51b100742c800030f61100480e001c10b04051002c103401103c2840d050101940b40c900c0d2001d0740c440e07441004007040c40000018103442c86a885000201e5245005540d03900b00707012000c1c20751000f07030382561 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 563837814 1250 563836564 563836619
    0x501080421080a05010f06080406020307110708071d090607030e011e09060b0d02031005100e040b10080c0d0215040f08030c071e061815030e19030c080f090a 69
    0x540303040191b180394202c0b042580c0c0d4030030b103a40d9540d40d08060741002d403611084c003508114140150784184040005440560020290359260a44a010041e00c0306103501500400c80c050100608010441da5408552401c011454804c0300120030b005102099002c0d28001e440c4060780031820140d0400c603601c2e40a03405c284284c180b0b5004100d11401c81300ca00940c1640b1400c800088010160409648500d0804900091035941d00c501017982c40125401c40f40d0300e81601c20052008408850300010300095001010403042600200c1c804140c04480030b4403c0c05062009800485070f8002c5401030f01c4a0701400e03240d2a50754000c07946e00e800410004026010784600898098070f030078040b07004210712424030b075411480d007202960003103034000142c170400e400c0c0f21003c510300c242040e8842510480c1c0d9030025204142e6600d50f401d2001d4243c41c200c56141c60b82038900403a84c0b01028038649504058800e540d5140c0b0803a88241d032060b00b010719000103009400107001d000280c00200112050394801 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 563839064 1250 563837814 563837819
    0x20c01120612031803080706050915070909150503070b0415050a0e0f182a03010e1620030d05012909040227010917070501080421080a0501 61
    0xc03094840368019a01004002a41e12010901c10000301203100400c50b01d28000381d4907a150418075500c408800d640007900c0720203001181c24108021810000010054500d03801c044500600c540458458101e009803076540c80303600021509681c00c02008002c040b9644540d503041c17007484582052040d0811500070480d070b9501a80240100e07007041f80b15a90300700000754034500b0400c5e1100c20401440d04510804024104060b100004500410300b04121400c56010000c00c1142004514940c0100200600c0100b00710750041c149190002d0581b400b2403a49001c40004072074559402c2d840c402c1714030b241603640101100c048020901451480f0041c44242e80f2054071000d81c400c91020580610f800601030050080204090801450010405481c0c5800005074180d100c0e4816440007a03582c902019828030360300150748600403c0424110103d40481c140ca042d12502c281c031070641885941400170701000002d99905088003214401050a8480008021320b514001c403040d004551509001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 563840314 1250 563839064 563839097
    0x302120307020703231014060406050d080a031410030b01140f010309320601050913030806060d02071103070801020f0a0509120a150c1e230a020c01 65
    0x1128452a00754000b45195495551000088588100c204880c503118a0001d100300d40e0600c401e90b11841512004640030b8505071a020b05141c01030130003885986002c06c10406500d9000748500d805800c07044860301c601c2c1079a030035405004440c1ca44501400000308202d807001315880f903001940d00603800030125070f0b251984040c0302d602d01a0015480340b4001c8181c646903200b078008007401881001c502541d0554918401c40c030ba180407940805800c106820948410800c10103540100760440b00c80e1120700744014121604c402d81c000150411001c000040c2c44d80d00c03644120390b2200c80302c00c01150343d14440d01b04103030364a8600c080d4611030300a11000080c038010500940e201c5545d407440142c82c0c0300506030141c5590340451200350304106096074201c2c8040c1c0501490502e180220100001e05c908498001c003102d240c0c80090003030209013601e802c04914404210440c403080e50504001c03404443c80f50074415140300d805000c204d580000c1000140380e0200c2c1546a10600781c0328008001c031254403 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 563841564 1250 563840314 563840317
    0x304030f12060e190e3708030f180a06050403180806180f070803030f1e15010201021204030e030d050301030b0609071b08040608010902160605060f09090a030212 71
    0x1820b442d00c612503000c1141d650003410f1444d18164028000202c0c100748642842c107081181c0e402c0104c40d40401442200f0618107891540400540c40c0400c6500c42039941d180c500f4080500707821081c3e100400080c8410260304a08103ca815003801c8800e240c0e003519048003c0e080441d000c4000030114901400c0000340703040654180c2e02d10f0342c09800d4580d2181400f0340180801d1007030380164030600700c01030242102806440080c12190026695a140c003980403000c01c040a050402d032503038000340c091041100a000950000e80020f0602016101d03540101e01900034420021010800d620a100405403c040c08040e030f180c082c1c003681d046425912043c0c95902007484003401003c01c40001850500e08003804a503c44018203015422003000a4440401f50680c0c604982550000a00707001041d003001825005040c10102545440d5202d130000c0c201a01078080108030325252004140190344040312803203005030240c1442c4480c508080c0040e0b5460b14103030140c000d0b010700c074002014a00c1110 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 563842814 1250 563841564 563841569
    0x80703210219060203060301060f24051305040b010903080c0109030801060f0207050f0d0c0303081b0705030904050604021b03040e1005010804150618020304030f030b03190f080304030f1206 83
    0x86182c1641c20b484240280d48020708580c2e06568604020800810340720b02c0310080c00d489000c0d01030348001d0011003160440445405418803c040c04176650300d01142030040251117045c2c801250f031002c2c000040c1e41403c0d861f000140103200c04190748014120541c043e0610502070b03516407000740d80e00c3c281038480d901c405c01c4040043e007103003605009509001d4240e903038058024001d140d0802c0c15071038516501c0c4c0960412800150580b0502900d0040d40703480d4080400004c81e858603118a607030303c0303c1d6680700d1148068040c03519007000440306e9071168142c03924401c150302c40c04d000a031404601901c03540680119803903000d03140e01281000310b50044100641d0010f03101c028890319180c030380880030041c50905091031611901c02184d0106140c0a25590b04d58030000035840e420940307809014090b620b0f500c07600700741c0780c240c0c3c01440d941d001038085040c1920892120022805003405000400078000140480c0f00c00000d01040680c09501168640d40e16601c25100a400d035070840269407061 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 563844064 1250 563842814 563842843
    0xc0406061416110603040302060a0b03030306100e01020a0c35031e390a0b01050f01031401410105180a1401030c02070e070f090807032102 61
    0x14403240c502c0360031a0000407079003401141d5114078040800f0004106520032101200140c005000f8421b005620b40902070703c114044024600b14035041c808200803000d50705140d810406400c021070b400d07034000d00140030900e8001c8071400e4400e40301d610100c1001030311105214110b041031581d4410310700e01784180102c00c0c0c1030809540380c40101d00b00b414080074640d0402b0518501007080c08105410040e441c140169468104411829410750340790030040402c0b001d400e503070080d6401c1400180c09030309460544108032258001280179030012002000207290a01890000100125002d81c8100d84441031740401c801200300440c0020650106c03800340346103181c031840d59110381c45456001d20090000348415003002c000c2500501d0021b544850320342c1c400c0b0280a103c81c1920542d50f0700d40601d01e0f440101d0b000804000785000742030a00a10f00912200402411104660041d4801d004000040c550b042c00c48281e261207045c150004080c0c00911900c1c0c0d00d10401a1011038000715107100f40c0c0480 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 563845314 1250 563844064 563844067
    0x40203100b011407050604120f1e090314100b060c0c040504020402161511120112020a030c0f15030b030c010e04020d020d020c1e030a0f0e0904050c04060614 69
    0x544044016201c0c4031103080c18007840c11560300142d21054054403c45002c0c00003407050f42002e003041103911f01c401c0d07807817001c02200940032920039410041014103024a41e01070f440d10088403c080368000b9094100030710482550b03030321560b44400000c147d0303040059075104114039144101040880d208104203801d0701c0d000956034260a01e0305078403180d40f090000c4c201501d0300030441c03810210194441c9003210000030021003c1c0a544561040c0340c041c0b15800300241c41e000d01d03c0c001c801f480d281441810745066030349101500f192690b800742c9000350703400036a0fa2030b101c0d107495500b00444028040c00d15120802c4d62111803042c442d00540041480c007a0203010064044801120360800c9160a9034000d03408010001100702544000c0a55001900c00140ca8440c00304c0c3c007500300f00c000c41007000c02d82840071700101c94200110445541c4086418405030b0200300c90000c0d6042054906410b0f4071070502c1c41000140a00031031031100143c021102081040d44030034003a10713003032002d5020103081c100 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 563846564 1250 563845314 563845333
    0x41409070207090216150203090c0a05060d0209060d06030309030b0901140c0a020703080c010b19060e100315060905090a0c0801061808032a120304020607061401030302010c021005040203 82
    0x3010390003440007040c1101143c841c0c0009841320007248890b00d43c41b101e2280d0001c200140a00c090161803100507044683c450341a28010003e04030b070160b0b610b440300c0190300081c0d4003000e42d950070444d03088912115050081035030b00e0402814200032488192000b010a9000868009040c8148404901c0c2a5151060b03510b80c41045a80c64008031002000c4d4800d15a000c00070800c000f004c0c01206400e1000400c00100c40020b0125a081c000403000d10100e803400c0900405411900d00780710418250740d10308048142a0f070440242101c00c208240642c85000b001c510141d11056100640c2e1003681d03040e2250319095020021100c00034010000650300c40d00600915200d50700c00030042e4556040d00c14020303151354079242540d0040d41306402c031207031080003c00301003800000c0014011040d00074291903480c403030204a0b5444000c2c070003441200700007001420803000e03074405c03c40124402c101007400d685900d00640280415071000c005031003140403c20b440318560040038411a800f80107001c8104 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 563847814 1250 563846564 563846579
    0x3030612190b040203030912010f0c03060806070507020d1e030f081302192303070509091f021204050136080f0c06041b052704051c05041409070207 65
    0x10400f80c4200d906000400c100042c40e550700d004a0040703142c060002645400a040c0c0c5800c03118811625028903003010b004101942c40071503102c1d4804008d007015903a51a1a100045100c1550080180007040e0180e50403d02c501030100c17007484500c00d03200e00f07403407098030201500c481004031038141c0880502e1003100018209801002c00c1c9940c256103203202143c030f580c901c46004120843c2003002040044091500d4601088410b006190030ba03100ca2440c100700142c2600c0341c50044951170700310800b071900c5d0b40342c2c1240d90448402510440740d000320390420389401070282c2110b0003410345c803112010a480701411045070280703000d003a0b40c800307840d0900c1c940d0b10400342e0b0300300d000c400400d94800d03c8891221502440454800c920034982d00703007222803401582441b60440d420241c09800c014000d05c0b100c24a0f2400e010801c50501e02c2030342c0944e50b40c50036903d801d94400400f030450b806084039407002508000a001038400803001510116070000c2030100700c510407505000160b2000c0030803c0f420303 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 563848920 1106 563847814 563847833
    0xa110a080304140607020a030b15060a0905010809070f06170f160302070c23120f030304020d050111040f17010e0c1002030405120303061219 62
    0x12030414000e036070349020718081c44000d0596426840c19a60720034040e540c1c2503a00421040c0c4440d2a8541090302c0c00054801e000000407503480c3c61610310300441a00c86551241d0303035041c880b40c80d207001100c4008010381485043c2c055050041000881d03095400d020301155110080f4100385100c101d10700003401001c5914400801050050103404000c5201c800c0d1803e10f009a110006030820300c00000041e4400d103a40c4a0101031a420074075004444d04c6461030440300d03c40d01c500303580159912051058645441608100300060041c5030101a00c2c03811070250f40009840110310f9803565155005402072445c4040748602080071508104402200e028010024003e903684007040c0b83e42c2e003040440139480740640340d0340b0303141040c82003041e1401484001c140280c10040105096169482920014010755a4000c4072814620020303030b2610080c8030100300b1318452119100d25958 = true := by decide +kernel

theorem cover : BRFrame.Cov 563669064 563848920 := by
  have h0 := BRFrame.cov_init 563669064
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563669064 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 563669064 ≤ n) (h2 : n < 563848920) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
